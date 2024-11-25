/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FlutedResolution.cpp
 * Implements class FlutedResolution.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/ResultSubstitution.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/ConditionalRedundancyHandler.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "FlutedResolution.hpp"

namespace Inferences {

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void FlutedResolution::attach(SaturationAlgorithm *salg)
{
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index = static_cast<FlutedResolutionIndex *>(
      _salg->getIndexManager()->request(BINARY_RESOLUTION_SUBST_TREE));
}

void FlutedResolution::detach()
{
  ASS(_salg);

  _index = 0;
  _salg->getIndexManager()->release(BINARY_RESOLUTION_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

/**
 * Ordering aftercheck is performed iff ord is not 0,
 * in which case also ls is assumed to be not 0.
 */
Clause *FlutedResolution::generateClause(
    Clause *queryCl, Literal *queryLit, Clause *resultCl, Literal *resultLit,
    ResultSubstitutionSP subs, AbstractingUnifier *absUnif)
{
  ASS(resultCl->store() == Clause::ACTIVE); // Added to check that generation only uses active clauses

  const auto &opts = getOptions();
  const bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();

  if (!ColorHelper::compatible(queryCl->color(), resultCl->color())) {
    env.statistics->inferencesSkippedDueToColors++;
    if (opts.showBlocked()) {
      std::cout << "Blocked resolution of " << *queryCl << " and " << *resultCl << endl;
    }
    if (opts.colorUnblocking()) {
      SaturationAlgorithm *salg = SaturationAlgorithm::tryGetInstance();
      if (salg) {
        ColorHelper::tryUnblock(queryCl, salg);
        ColorHelper::tryUnblock(resultCl, salg);
      }
    }
    return 0;
  }

  unsigned clength = queryCl->length();
  unsigned dlength = resultCl->length();

  // LRS-specific optimization:
  // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
  // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
  // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.
  unsigned wlb = 0;                        // weight lower bound
  unsigned numPositiveLiteralsLowerBound = // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur
      Int::max(queryLit->isPositive() ? queryCl->numPositiveLiterals() - 1 : queryCl->numPositiveLiterals(),
               resultLit->isPositive() ? resultCl->numPositiveLiterals() - 1 : resultCl->numPositiveLiterals());

  auto constraints = absUnif->computeConstraintLiterals();
  auto nConstraints = constraints->size();
  Inference inf(GeneratingInference2(nConstraints == 0 ? InferenceRule::RESOLUTION : InferenceRule::CONSTRAINED_RESOLUTION, queryCl, resultCl));
  Inference::Destroyer inf_destroyer(inf); // will call destroy on inf when coming out of scope unless disabled

  auto passiveClauseContainer = _salg->getPassiveClauseContainer();
  bool needsToFulfilWeightLimit = passiveClauseContainer && !passiveClauseContainer->fulfilsAgeLimit(wlb, numPositiveLiteralsLowerBound, inf) && passiveClauseContainer->weightLimited();

  if (needsToFulfilWeightLimit) {
    for (unsigned i = 0; i < clength; i++) {
      Literal *curr = (*queryCl)[i];
      if (curr != queryLit) {
        wlb += curr->weight();
      }
    }
    for (unsigned i = 0; i < dlength; i++) {
      Literal *curr = (*resultCl)[i];
      if (curr != resultLit) {
        wlb += curr->weight();
      }
    }
    if (!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, inf)) {
      RSTAT_CTR_INC("binary resolutions skipped for weight limit before building clause");
      env.statistics->discardedNonRedundantClauses++;
      return 0;
    }
  }

  bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
  Literal *cAnsLit = synthesis ? queryCl->getAnswerLiteral() : nullptr;
  Literal *dAnsLit = synthesis ? resultCl->getAnswerLiteral() : nullptr;
  bool bothHaveAnsLit = (cAnsLit != nullptr) && (dAnsLit != nullptr);

  RStack<Literal *> resLits;

  Literal *queryLitAfter = 0;
  if (afterCheck && queryCl->numSelected() > 1) {
    TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
    queryLitAfter = subs->applyToQuery(queryLit);
  }

  auto &ls = _salg->getLiteralSelector();

  resLits->loadFromIterator(constraints->iterFifo());
  for (unsigned i = 0; i < clength; i++) {
    Literal *curr = (*queryCl)[i];
    if (curr != queryLit && (!bothHaveAnsLit || curr != cAnsLit)) {
      Literal *newLit = subs->applyToQuery(curr);
      if (needsToFulfilWeightLimit) {
        wlb += newLit->weight() - curr->weight();
        if (!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, inf)) {
          RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
          env.statistics->discardedNonRedundantClauses++;
          return nullptr;
        }
      }
      if (queryLitAfter && i < queryCl->numSelected()) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

        Ordering::Result o = _salg->getOrdering().compare(newLit, queryLitAfter);

        if (o == Ordering::GREATER ||
            (ls.isPositiveForSelection(newLit) // strict maximimality for positive literals
             && o == Ordering::EQUAL)) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          return nullptr;
        }
      }
      resLits->push(newLit);
    }
  }

  Literal *qrLitAfter = 0;
  if (afterCheck && resultCl->numSelected() > 1) {
    TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
    qrLitAfter = subs->applyToResult(resultLit);
  }

  for (unsigned i = 0; i < dlength; i++) {
    Literal *curr = (*resultCl)[i];
    if (curr != resultLit && (!bothHaveAnsLit || curr != dAnsLit)) {
      Literal *newLit = subs->applyToResult(curr);
      if (needsToFulfilWeightLimit) {
        wlb += newLit->weight() - curr->weight();
        if (!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, inf)) {
          RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
          env.statistics->discardedNonRedundantClauses++;
          return nullptr;
        }
      }
      if (qrLitAfter && i < resultCl->numSelected()) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

        Ordering::Result o = _salg->getOrdering().compare(newLit, qrLitAfter);

        if (o == Ordering::GREATER ||
            (ls.isPositiveForSelection(newLit) // strict maximimality for positive literals
             && o == Ordering::EQUAL)) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          return nullptr;
        }
      }
      resLits->push(newLit);
    }
  }

  if (!absUnif->usesUwa()) {
    if (!_salg->condRedHandler().handleResolution(queryCl, queryLit, resultCl, resultLit, subs.ptr())) {
      return 0;
    }
  }

  if (bothHaveAnsLit) {
    Literal *newLitC = subs->applyToQuery(cAnsLit);
    Literal *newLitD = subs->applyToResult(dAnsLit);
    bool cNeg = queryLit->isNegative();
    Literal *condLit = cNeg ? subs->applyToResult(resultLit) : subs->applyToQuery(queryLit);
    resLits->push(SynthesisALManager::getInstance()->makeITEAnswerLiteral(condLit, cNeg ? newLitC : newLitD, cNeg ? newLitD : newLitC));
  }

  if (nConstraints != 0) {
    env.statistics->cResolution++;
  }
  else {
    env.statistics->resolution++;
  }

  inf_destroyer.disable(); // ownership passed to the the clause below
  Clause *cl = Clause::fromStack(*resLits, inf);
  if (env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(cl, new FlutedResolutionExtra(queryLit, resultLit));

  return cl;
}

ClauseIterator FlutedResolution::generateClauses(Clause *premise)
{
  return pvi(TIME_TRACE_ITER("resolution",
                             premise->getSelectedLiteralIterator()
                                 .filter([this, premise](auto l) { return isEligibleLiteral(l, premise); })
                                 .flatMap([this, premise](auto lit) {
                                   // find query results for literal `lit`
                                   return iterTraits(_index->getUwa(lit, /* complementary */ true,
                                                                    env.options->unificationWithAbstraction(),
                                                                    env.options->unificationWithAbstractionFixedPointIteration()))
                                       .filter([this](auto qr) { return isEligibleLiteral(qr.data->literal, qr.data->clause); })
                                       .map([this, lit, premise](auto qr) {
                                         // perform Fluted resolution on query results
                                         auto subs = ResultSubstitution::fromSubstitution(&qr.unifier->subs(), QUERY_BANK, RESULT_BANK);
                                         return FlutedResolution::generateClause(premise, lit, qr.data->clause, qr.data->literal, subs, qr.unifier);
                                       });
                                 })
                                 .filter(NonzeroFn())));
}

bool FlutedResolution::isEligibleLiteral(Literal *l, Clause *cl)
{
  // ? what does it mean to be *strictly* maximal?
  return isMaximal(l, cl, l->isPositive());
}

bool FlutedResolution::isMaximal(Literal *l, Clause *cl, bool strict)
{
  // check memoization
  auto ord = cl->_flutedOrdering.find(l);

  if (ord.isSome()) {
    return ord.unwrap() < (1 + !strict);
  }

  auto lit = cl->getLiteralIterator();

  LiteralList *lEquivalents = 0;
  while (lit.hasNext()) {
    auto curr = lit.next();
    // if current literal is already marked as maximal but l is not, then they are uncomparable
    if (curr == l || ((ord = cl->_flutedOrdering.find(curr)).isSome() && ord.unwrap() < 2)) {
      continue;
    }
    switch (compareLiterals(curr, l)) {
      case ComparisonResult::LESSER:
        cl->_flutedOrdering.insert(curr, Clause::FlutedOrdering::NON_MAXIMAL);
        break;
      case ComparisonResult::GREATER:
        // if exists a literal that is strictly greater than l, all the literals that are equivalent to l are non-maximal
        while (lEquivalents) {
          cl->_flutedOrdering.insert(lEquivalents->head(), Clause::FlutedOrdering::NON_MAXIMAL);
          lEquivalents = lEquivalents->tail();
        }
        cl->_flutedOrdering.insert(l, Clause::FlutedOrdering::NON_MAXIMAL);
        return false;
      case ComparisonResult::EQUAL:
        LiteralList::push(curr, lEquivalents);
        break;
      default:
        break;
    }
  }

  // if l is not strictly less than any other literal, and has no equivalent literals, then it is strictly maximal
  if (!lEquivalents) {
    cl->_flutedOrdering.insert(l, Clause::FlutedOrdering::STRICTLY_MAXIMAL);
    return true;
  }

  // if l is not strictly less than any other literal, but has equivalent literals, then it is maximal
  while (lEquivalents) {
    cl->_flutedOrdering.insert(lEquivalents->head(), Clause::FlutedOrdering::MAXIMAL);
    lEquivalents = lEquivalents->tail();
  }
  cl->_flutedOrdering.insert(l, Clause::FlutedOrdering::MAXIMAL);

  // in this case, l is maximal but not strictly maximal
  return !strict;
}

/*
  * Compare two literals.
  * Returns:
  * - LESSER if l1 is strictly less than l2
  * - GREATER if l1 is strictly greater than l2
  * - EQUAL if l1 is equal to l2
  * - UNCOMPARABLE if l1 and l2 are Uncomparable

  * The comparison is lexicographic on the following properties:
  * 1. Arity
  * 2. Maximal subterm (Using superterm relation)
  * 3. Polarity (Negative > Positive)

  * To be admisible, the ordering must be total and well-founded on ground literals.
  * Being (2) the only measure of complexity that can violate the totality of the ordering
  * it will be substituted with functor comparison in case of uncomparability.

  * If only one of the term is ground, (2) is considered always uncomparable.

*/

FlutedResolution::ComparisonResult FlutedResolution::compareLiterals(Literal *l1, Literal *l2)
{
  // Technically this should never happen, but it's a good sanity check
  if (l1 == l2) {
    return ComparisonResult::UNCOMPARABLE;
  }

  if (l1->arity() != l2->arity()) {
    return l1->arity() < l2->arity() ? ComparisonResult::LESSER : ComparisonResult::GREATER;
  }

  if (l1->ground() != l2->ground()) {
    return ComparisonResult::UNCOMPARABLE;
  }

  auto t1 = l1->nthArgument(l1->arity() - 1);
  auto t2 = l2->nthArgument(l2->arity() - 1);

  /**
   *! All variables are equally uncomparable, but choosing the last variable assure
   *! it's contained in all the other terms
   */

  if (t1->isVar() != t2->isVar()) {
    return t1->isVar() ? ComparisonResult::LESSER : ComparisonResult::GREATER;
  }

  if (!t1->isVar() && !t2->isVar()) {
    // superterm relation
    if (superTermRelation(t1, t2) != ComparisonResult::EQUAL) {
      return superTermRelation(t1, t2);
    }
  }

  // Non arriverò mai qui. A meno di non ammettere <_s come un ordine largo (nonostante il paper parli si *proper* superterm)

  if (l1->isNegative() != l2->isNegative()) {
    return l1->isNegative() ? ComparisonResult::GREATER : ComparisonResult::LESSER;
  }

  return ComparisonResult::UNCOMPARABLE;
}

FlutedResolution::ComparisonResult FlutedResolution::superTermRelation(const TermList *t1, const TermList *t2)
{
  //! Temporary considering the non strict superterm relation
  if (t1 == t2) {
    return ComparisonResult::EQUAL;
  }

  // If both are variables, they are uncomparable
  if (t1->isVar() && t2->isVar()) {
    return ComparisonResult::UNCOMPARABLE;
  }

  // If one is a variable and the other is not, the non-variable is the superterm
  // This is assured by the fact we choose the last variable in compareLiterals
  if (t1->isVar() != t2->isVar()) {
    return t1->isVar() ? ComparisonResult::LESSER : ComparisonResult::GREATER;
  }

  if (isContained(t1, t2->term()->nthArgument(t2->term()->arity() - 1))) {
    return ComparisonResult::LESSER;
  }

  if (isContained(t2, t1->term()->nthArgument(t1->term()->arity() - 1))) {
    return ComparisonResult::GREATER;
  }

  if (t1->ground()) {
    unsigned f1 = t1->term()->functor(), f2 = t2->term()->functor();
    return f1 > f2 ? ComparisonResult::GREATER : f1 == f2 ? ComparisonResult::EQUAL
                                                          : ComparisonResult::LESSER;
  }
  return ComparisonResult::UNCOMPARABLE;
}

/** Assuming Non variable terms.
 * Check if t1 is contained in t2
 */
/**
 * ! The paper implies the last term contains all the other terms at first level
 * ! even if it's not derivable from the definition. Can it be an optimization?
 */
bool FlutedResolution::isContained(const TermList *t1, const TermList *t2)
{
  if (t1 == t2) {
    return true;
  }

  if (t2->isVar() || !t2->term()->arity()) {
    return false;
  }

  auto term = t2->term();
  return isContained(t1, term->nthArgument(term->arity() - 1));
}

} // namespace Inferences
