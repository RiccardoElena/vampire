#ifndef __SEPARATOR_H__
#define __SEPARATOR_H__

#include "Forwards.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Classifier.hpp"
namespace FlutedFragment {

using namespace Kernel;
class Separator {
public:
  Separator() = default;
  ~Separator() = default;

  using Evar = ClauseClassifier::EVar;

  static ClauseList::Iterator separate(Clause *cl)
  {

    std::cout << "Separating clause: " << cl->toString() << std::endl;
    // Partition the literals of the clause into two sets C and D
    // Saving upper and lower bounds of the variables in C and D
    auto lit = cl->getLiteralIterator();
    auto currentLit = lit.next();
    if (!currentLit->allArgumentsAreVariables()) {
      std::cout << "Not separating because FL2" << std::endl;
      return ClauseList::Iterator(ClauseList::empty());
    }
    LiteralStack sepResC, sepResD;
    Evar vLastC = currentLit->nthArgument(currentLit->arity() - 1)->var(),
         vFirstC = currentLit->nthArgument(0)->var(),
         vLastD, vFirstD;
    sepResC.push(currentLit);
    while (lit.hasNext()) {
      currentLit = lit.next();
      if (!currentLit->allArgumentsAreVariables()) {
        return ClauseList::Iterator(ClauseList::empty());
      }
      Evar currVLast = currentLit->nthArgument(currentLit->arity() - 1)->var(), currVFirst = currentLit->nthArgument(0)->var();
      if (currVLast == vLastC) {
        sepResC.push(currentLit);
        if (vFirstC > currVFirst) {
          vFirstC = currVFirst;
        }
      }
      else {
        if (sepResD.isEmpty() || vFirstD > currVFirst) {
          if (sepResD.isEmpty()) {
            vLastD = currVLast;
          }
          vFirstD = currVFirst;
        }
        sepResD.push(currentLit);
      }
    }

    if (!vLastD.isSet()) {
      std::cout << "Not separating because FL1" << std::endl;
      return ClauseList::Iterator(ClauseList::empty());
    }

    // TODO: check that set with smaller last variable has to contain 0
    // IDEA: prob best way to check all of this and simplify the code
    // IDEA: is to assume C is the set with the smaller last variable
    // IDEA: and to edit bounds of C and D accordingly
    if (vFirstC != 0 && vFirstD != 0) {
      assertionViolation<string>();
    }

    // Check applicability of separation based on which set contains the Xm+1 variable
    return (vLastC.var() < vLastD.var()) ? createClauses(vFirstC.var(), vFirstD.var(), vLastC.var(), sepResC, sepResD, cl)
                                         : createClauses(vFirstD.var(), vFirstC.var(), vLastD.var(), sepResD, sepResC, cl);
  }

  /*
    ASSUMING D has the Xm+1 variable
    If D has a lower bound less than or equal to the lower bound of C,
    then var(D) contains var(C), therefore separation is not applicable.
    Otherwise, the clause is separated into two clauses.
  */
  static ClauseList::Iterator createClauses(unsigned vCf, unsigned vDf, unsigned vCl, LiteralStack &sepResC, LiteralStack &sepResD, Clause *cl)
  {
    std::cout << "Creating clauses" << std::endl;
    if (vDf <= vCf) {
      std::cout << "Not separating because one set of var contains the other" << std::endl;
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
    std::cout << "Separated clauses: " << clC->toString() << " and " << clD->toString() << std::endl;
    ClauseList::push(clC, res);
    ClauseList::push(clD, res);

    return ClauseList::Iterator(res);
  }
};
} // namespace FlutedFragment

#endif // __SEPARATOR_H__