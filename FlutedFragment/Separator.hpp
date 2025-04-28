#ifndef __SEPARATOR_H__
#define __SEPARATOR_H__

#include "Forwards.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Classifier.hpp"

#define SEPARATOR_DEBUG 0
namespace FlutedFragment {

using namespace Kernel;
class Separator {
public:
  Separator() = default;
  ~Separator() = default;

  using Evar = ClauseClassifier::EVar;

  struct varRange {
    Evar first;
    Evar last;
  };

  static ClauseList::Iterator separate(Clause *cl)
  {

#if SEPARATOR_DEBUG
    std::cout << "Separating clause: " << cl->toString() << std::endl;
#endif
    // Partition the literals of the clause into two sets C and D
    // Saving upper and lower bounds of the variables in C and D
    auto lit = cl->getLiteralIterator();
    auto currentLit = lit.next();

    if (!currentLit->arity()) {
#if SEPARATOR_DEBUG
      std::cout
          << currentLit->toString() << " is ground, therefore his set of vars is always contained" << std::endl;
#endif
      return ClauseList::Iterator(ClauseList::empty());
    }

    if (!currentLit->allArgumentsAreVariables()) {
#if SEPARATOR_DEBUG
      std::cout
          << "Not separating because FL2" << std::endl;
#endif
      return ClauseList::Iterator(ClauseList::empty());
    }
    LiteralStack sepResC{}, sepResD{};
    varRange varsC, varsD;
    varsC.first = currentLit->nthArgument(0)->var();
    varsC.last = currentLit->nthArgument(currentLit->arity() - 1)->var(),
    sepResC.push(currentLit);
    while (lit.hasNext()) {
      currentLit = lit.next();

      if (!currentLit->arity()) {
#if SEPARATOR_DEBUG
        std::cout
            << currentLit->toString() << " is ground, therefore his set of vars is always contained" << std::endl;
#endif
        return ClauseList::Iterator(ClauseList::empty());
      }

      if (!currentLit->allArgumentsAreVariables()) {
        return ClauseList::Iterator(ClauseList::empty());
      }

      Evar currVLast = currentLit->nthArgument(currentLit->arity() - 1)->var(),
           currVFirst = currentLit->nthArgument(0)->var();

      if (currVLast == varsC.last) {
        sepResC.push(currentLit);
        if (varsC.first > currVFirst) {
          varsC.first = currVFirst;
        }
      }
      else {
        if (sepResD.isEmpty()) {
          varsD.last = currVLast;
          varsD.first = currVFirst;
        }
        if (varsD.first > currVFirst) {
          varsD.first = currVFirst;
        }
        sepResD.push(currentLit);
      }
    }

    if (!varsD.last.isSet()) {
#if SEPARATOR_DEBUG
      std::cout << "Not separating because FL1" << std::endl;
#endif
      return ClauseList::Iterator(ClauseList::empty());
    }

    if (varsC.last.var() > varsD.last.var()) {
      std::swap(varsC, varsD);
      auto temp = sepResC;
      sepResC = sepResD;
      sepResD = temp;
    }

    if (varsC.first != 0) {
#if SEPARATOR_DEBUG
      std::cout << "Not separating because not Fluted" << std::endl;
#endif
      return ClauseList::Iterator(ClauseList::empty());
    }

    // Check applicability of separation based on which set contains the Xm+1 variable
    return createClauses(varsD.first.var(), varsC.last.var(), sepResC, sepResD, cl);
  }

  /*
    ASSUMING D has the Xm+1 variable
    If D has a lower bound less than or equal to the lower bound of C,
    then var(D) contains var(C), therefore separation is not applicable.
    Otherwise, the clause is separated into two clauses.
  */
  static ClauseList::Iterator createClauses(unsigned vDf, unsigned vCl, LiteralStack &sepResC, LiteralStack &sepResD, Clause *cl)
  {

#if SEPARATOR_DEBUG
    std::cout << "Creating clauses" << std::endl;
#endif
    if (vDf == 0) {
#if SEPARATOR_DEBUG
      std::cout << "Not separating because one set of var contains the other" << std::endl;
#endif
      return ClauseList::Iterator(ClauseList::empty());
    }
    ClauseList *res = ClauseList::empty();
    TermStack args;
    args.reset();

    for (unsigned i = vDf; i <= vCl; ++i) {
      args.push(TermList(i, false));
    }
    unsigned arity = args.size(), name = env.signature->addNamePredicate(arity);
    // Create the two clauses
    Literal *negLit = Literal::create(name, arity, false, args.begin());
    sepResC.push(negLit);
    Literal *posLit = Literal::create(name, arity, true, args.begin());
    sepResD.push(posLit);

    Clause *clC = Clause::fromStack(sepResC, NonspecificInference1(InferenceRule::SEPARATION, cl));
    Clause *clD = Clause::fromStack(sepResD, NonspecificInference1(InferenceRule::SEPARATION, cl));
#if SEPARATOR_DEBUG
    std::cout << "Separated clauses: " << clC->toString() << " and " << clD->toString() << std::endl;
#endif
    ClauseList::push(clD, res);
    ClauseList::push(clC, res);

    return ClauseList::Iterator(res);
  }
};
} // namespace FlutedFragment

#endif // __SEPARATOR_H__