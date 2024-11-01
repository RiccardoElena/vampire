#include <iostream>
#include <cstdlib>
#include "Shell/Options.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Clause.hpp"
#include "Classifier.hpp"

namespace FlutedFragment {

using namespace Kernel;
using namespace std;

/********************************************************************************/

// Classifier

/********************************************************************************/

/**
 * @brief Check if a unit list is in the Fluted Fragment
 * @param ul The unit list to be checked
 * @return true if the unit list is in the Fluted Fragment, false otherwise
 */
bool Classifier::isInFlutedFragment(UnitList *ul)
{
  if (ul->empty())
    return false;

  if (ul->head()->isClause()) {
    ClauseClassifier _cc(_debug);
    return _cc.isInFlutedFragment(ul);
  }
  FormulaClassifier _fc(_debug);
  return _fc.isInFlutedFragment(ul);
}

/********************************************************************************/

// Clause Classifier

/********************************************************************************/

bool ClauseClassifier::isInFlutedFragment(UnitList *ul)
{
  UnitList::Iterator uit(ul);

  while (uit.hasNext()) {
    Unit *unit{uit.next()};

    if (!isFluted(unit->asClause())) {
      return false;
    }
  }

  return true;
}

bool ClauseClassifier::isFluted(Clause *clause)
{
  auto lit{clause->getLiteralIterator()};

  if (_debug) {
    cout << "Classifing: " << clause->toString() << endl;
  }

  Literal *currentLit{lit.next()};
  if (!currentLit->allArgumentsAreVariables()) {
    if (_debug) {
      cout << "Found a functional literal" << endl;
    }
    return isFL2Clause(clause);
  }
  EVar var{}, lastVar{};
  if (currentLit->arity()) {
    lastVar = currentLit->nthArgument(currentLit->arity() - 1)->var();
  }
  else {
    lastVar.setNoVars();
  }

  if (currentLit->isEquality()) {
    if (_debug) {
      cout << "Found an equality" << endl;
    }
    return false;
  }

  while (lit.hasNext()) {
    currentLit = lit.next();
    if (currentLit->isEquality()) {
      return false;
    }

    if (!currentLit->allArgumentsAreVariables()) {

      return isFL2Clause(clause);
    }

    if (currentLit->arity()) {
      var = currentLit->nthArgument(currentLit->arity() - 1)->var();
    }
    else {
      var.setNoVars();
    }
    if (lastVar != var) {
      if (lastVar.distance(var) == 1) {
        return isFL3Clause(clause);
      }
      return false;
    }
  }

  return isFL1Clause(clause);
}

bool ClauseClassifier::isFL1Clause(Clause *clause)
{
  if (_debug) {
    cout << "Checking if " << clause->toString() << " is in FL1" << endl;
  }

  auto lit{clause->getLiteralIterator()};
  Literal *currentLit;
  FlutedSequence fl{};

  while (lit.hasNext()) {
    currentLit = lit.next();
    if (!isFluted(currentLit, fl)) {
      if (_debug) {
        cout << "Found a non fluted literal" << endl;
      }
      return false;
    }
  }

  return fl.isComplete();
}

bool ClauseClassifier::isFluted(Literal *literal, FlutedSequence &fl)
{
  if (_debug) {
    cout << "Checking if " << literal->toString() << " is fluted" << endl;
  }

  VariableIterator litVars{literal};

  if (!litVars.hasNext()) {
    if (_debug) {
      cout << "Found a propositional variable" << endl;
    }
    return false;
  }

  EVar lastVar = litVars.next().var();

  if (lastVar.var() == 0) {
    fl.setIsComplete();
  }

  while (litVars.hasNext()) {
    unsigned var = litVars.next().var();
    if (++lastVar != var) {
      if (_debug) {
        cout << "Found a non fluted literal" << endl;
      }
      return false;
    }
  }
  if (!fl.isVarSet()) {
    fl.setVar(lastVar);
  }

  if (lastVar != fl.var()) {
    return false;
  }

  return true;
}

// TODO: allign this with the other isFL methods using variables native qqorder
bool ClauseClassifier::isFL2Clause(Clause *clause)
{
  if (_debug) {
    cout << "Checking if " << clause->toString() << " is in FL2" << endl;
  }

  auto lit{clause->getLiteralIterator()};
  Literal *currentLit;
  // TODO: Enum should be better
  FlutedSequence localFl{};

  while (lit.hasNext()) {

    currentLit = lit.next();
    if (currentLit->isEquality()) {
      return false;
    }
    if (currentLit->allArgumentsAreVariables()) {
      if (localFl.isVarConst()) {
        return false;
      }
      if (!isFluted(currentLit, localFl)) {
        return false;
      }
    }
    else {

      EVar v{};
      if (localFl.isVarSet()) {
        if (localFl.isVarConst()) {
          v.setNoVars();
        }
        else {
          v = localFl.var();
        }
      }

      FlutedSequence innerFl{isFluted(currentLit, v)};

      if (!innerFl.isValid() || (localFl.isVarSet() && (innerFl.isVarConst() != localFl.isVarConst() || (!innerFl.isVarConst() && innerFl.var() != localFl.var())))) {
        return false;
      }

      if (!localFl.isVarSet()) {
        if (innerFl.isVarConst()) {
          localFl.setNoVars();
        }
        else {
          localFl.setVar(innerFl.var());
        }
      }

      if (!localFl.hasTermList()) {
        localFl.setTermList(innerFl.termList());
      }
      else {
        if (!localFl.onePrefixOfOther(innerFl.termList())) {
          if (_debug) {
            cout << "Not a prefix" << endl;
          }
          return false;
        }
      }
    }
  }

  return true;
}

ClauseClassifier::FlutedSequence ClauseClassifier::isFluted(Term *term, EVar v)
{
  if (_debug) {
    cout << "Checking if " << term->toString() << " is fluted" << endl;
  }

  bool isFunctional{false};
  EVar currVar{};
  FlutedSequence localFl{}, innerFl{};

  TermList *args{term->args()};
  if (args->isEmpty()) {
    if (_debug) {
      cout << "No arguments" << endl;
    }

    return false;
  }

  if (args->isVar()) {
    currVar = args->var();

    args = args->next();
    if (currVar.var() == 0) {
      localFl.setIsComplete();
    }

    if (v.isConst()) {
      if (_debug) {
        cout << "Found a variable after a constant" << endl;
      }
      return false;
    }
    if (v.isSet() && currVar > v) {
      if (_debug) {
        cout << "First variable found already bigger than max" << endl;
        cout << currVar.var() << " " << v.var() << endl;
      }
      return false;
    }
  }
  else {
    isFunctional = true;
    if (!args->term()->arity()) {

      if (v.isSet() && !v.isConst()) {
        if (_debug) {
          cout << "Found a constant ('sequence over 0'), but a variable was already found" << endl;
        }
        return false;
      }
      if (!v.isSet()) {
        v.setNoVars();
      }
      localFl.addTerm(args->term());
      localFl.setIsComplete();
      args = args->next();
    }
  }

  while (!args->isEmpty()) {

    if (args->isVar()) {
      if (isFunctional || ++currVar != args->var() || (v.isSet() && v > currVar)) {
        if (_debug) {
          cout << "Found a var after a functional term, the variables were not in order or max var has been surpassed" << endl;
        }
        return false;
      }
    }
    else {
      isFunctional = true;
      if (!v.isSet() && currVar.isSet()) {
        v = currVar;
      }

      if ((currVar.isSet() && currVar != v) || localFl.isListMember(args->term())) {
        return false;
      }

      if (!args->term()->args()->isVar() && args->term()->args()->isEmpty()) {
        if (v.isConst()) {
          if (_debug) {
            cout << "Found 2 constant on the same level" << endl;
          }
          return false;
        }
        innerFl.setNoVars();
        innerFl.addTerm(args->term());
        innerFl.setIsComplete();
      }
      else {
        innerFl = isFluted(args->term(), v);
      }
      if (!innerFl.isValid()) {
        return false;
      }
      if (innerFl.isComplete()) {
        localFl.setIsComplete();
      }
      if (!v.isSet()) {
        if (innerFl.isVarConst()) {
          v.setNoVars();
        }
        else {
          v = innerFl.var();
        }
      }
      if (!localFl.hasTermList()) {
        if (currVar.isSet() && innerFl.hasTermList()) {
          return false;
        }
        localFl.setTermList(innerFl.termList());
      }
      else {
        if (!localFl.hasAsSubfix(innerFl.termList())) {
          return false;
        }
        else {
          localFl.addTerm(args->term());
        }
      }
    }
    if (!localFl.isComplete()) {
      return false;
    }

    args = args->next();
  }

  if (!v.isSet() && currVar.isSet()) {
    localFl.setVar(currVar);
  }
  else {
    localFl.setVar(v);
  }

  return localFl;
}

bool ClauseClassifier::isFL3Clause(Clause *clause)
{
  if (_debug) {
    cout << "Checking if " << clause->toString() << " is in FL3" << endl;
  }

  auto lit{clause->getLiteralIterator()};
  Literal *currentLit{nullptr};
  unsigned lastVar{0}, var{0};
  bool hasFirstVar{false};
  // TODO: Enum should be better
  // this variable correspond to the cases listed above
  EVar rightMostVar1{}, rightMostVar2{};

  while (lit.hasNext()) {
    currentLit = lit.next();

    if (currentLit->isEquality() || !currentLit->allArgumentsAreVariables()) {
      if (_debug) {
        cout << "Found a functional or equality literal" << endl;
      }
      return false;
    }

    VariableIterator litVars{currentLit};
    // ?: Maybe redundant 'cause propositional var are not accepted
    // !: But this mean (p | R(X)) is not fluted (even if direct clausification of  p | ![X]: R(X))
    if (!litVars.hasNext()) {
      if ((rightMostVar1.isVar() && rightMostVar1.var()) || (rightMostVar2.isVar() && rightMostVar2.var())) {
        if (_debug) {
          cout << "Rightmost var too different (max distance is 1)" << endl;
        }
        return false;
      }
      if (!rightMostVar1.isSet()) {
        rightMostVar1.setNoVars();
      }
      else if (rightMostVar1.isVar() && !rightMostVar2.isSet()) {
        rightMostVar1.setNoVars();
        rightMostVar2 = 0;
      }
      continue;
    }

    hasFirstVar = !(lastVar = litVars.next().var());
    if (_debug) {
      cout << "First var is " << lastVar << endl;
    }
    while (litVars.hasNext()) {
      var = litVars.next().var();
      if (_debug) {
        cout << "Comparing " << lastVar << " and " << var << endl;
      }
      if (++lastVar != var) {
        if (_debug) {
          cout << "Non fluted sequence of variables" << endl;
        }
        return false;
      }
    }

    if (_debug) {
      cout << "Rightmost1: " << rightMostVar1.var() << " LastVar: " << lastVar << " Rightmost2: " << rightMostVar2.var() << endl;
    }
    if (!hasFirstVar) {
      if (rightMostVar1.isSet() && rightMostVar1 != lastVar - 1) {
        return false;
      }

      if (rightMostVar2.isSet() && rightMostVar2 != lastVar) {
        return false;
      }

      if (!rightMostVar2.isSet()) {
        rightMostVar2 = lastVar;
      }
    }
    else {
      if (rightMostVar1.isSet() && rightMostVar1 != lastVar && rightMostVar2.isSet() && rightMostVar2 != lastVar) {
        return false;
      }
      if ((rightMostVar1.isSet() && rightMostVar1 != lastVar && rightMostVar1 != lastVar - 1) ||
          (rightMostVar2.isSet() && rightMostVar2 != lastVar && rightMostVar2 != lastVar + 1)) {
        return false;
      }

      if (!rightMostVar1.isSet()) {
        rightMostVar1 = lastVar;
      }
      else if (!rightMostVar2.isSet()) {
        rightMostVar2 = lastVar;
      }
    }

    if (_debug) {
      cout << "Rightmost1: " << rightMostVar1.var() << " LastVar: " << lastVar << " Rightmost2: " << rightMostVar2.var() << endl;
    }
  }

  return true;
}

/********************************************************************************/

// Formula Classifier

/********************************************************************************/

bool FormulaClassifier::isInFlutedFragment(UnitList *ul)
{
  UnitList::Iterator uit(ul);
  Stack<unsigned> formulaVars{};

  while (uit.hasNext()) {
    Unit *unit{uit.next()};

    if (_debug) {
      cout << "Classifing: " << unit->toString() << endl;
    }

    formulaVars.reset();
    if (!isFluted(unit->getFormula(), formulaVars)) {
      return false;
    }
  }
  cout << _varNum << " ";
  return true;
}

bool FormulaClassifier::isFluted(Formula *formula, Stack<unsigned> formulaVars)
{

  switch (formula->connective()) {
    case IFF:
    case XOR:
    case IMP: {
      return isFluted(formula->left(), formulaVars) && isFluted(formula->right(), formulaVars);
    }
    case AND:
    case OR: {
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {

        if (!isFluted(it.next(), formulaVars))
          return false;
      }
      return true;
    }
    case NOT: {
      return isFluted(formula->uarg(), formulaVars);
    }
    case FORALL:
    case EXISTS: {
      VList::Iterator newVarsIt{extractOuterVariables(static_cast<QuantifiedFormula *>(formula))};
      while (newVarsIt.hasNext()) {
        formulaVars.push(newVarsIt.next());
      }
      return isFluted(formula->qarg(), formulaVars);
    }
    case LITERAL: {
      return isFlutable(formula->literal(), formulaVars);
    }
    default:
      return true;
  }

  return false;
}

VList *FormulaClassifier::extractOuterVariables(QuantifiedFormula *formula)
{

  VList::Iterator vit(formula->boundVariables());
  VList *unboundVars{};

  //* Create a set to store the bound variables of the unquantified formula
  Set<unsigned> vars{};
  vars.insertFromIterator(VList::Iterator(formula->qarg()->boundVariables()));

  //* Check which of the bound variables is not in the set of unquantified formula
  unsigned var{0};
  while (vit.hasNext()) {
    var = vit.next();

    if (!vars.contains(var)) {

      unboundVars = VList::addLast(unboundVars, var);
    }
  }

  return unboundVars;
}

bool FormulaClassifier::isFluted(Literal *literal, Stack<unsigned> formulaVars)
{

  if (_debug) {
    cout << "Checking if " << literal->toString() << " is Fluted" << endl;
  }
  if (!literal->allArgumentsAreVariables() ||
      literal->isEquality()) {
    return false;
  }

  SubtermIterator sti(literal);
  Stack<unsigned> ReversedLitVars{};
  while (sti.hasNext()) {
    unsigned var{sti.next().var()};

    ReversedLitVars.push(var);
  }

  while (!formulaVars.isEmpty() && !ReversedLitVars.isEmpty()) {
    unsigned term{ReversedLitVars.pop()};
    unsigned var{formulaVars.pop()};

    if (term != var) {
      if (_debug) {
        cout << "Not Fluted" << endl;
      }
      return false;
    }
  }

  return ReversedLitVars.isEmpty();
}

bool FormulaClassifier::isFlutable(Literal *literal, Stack<unsigned> formulaVars)
{

  if (_varNum < formulaVars.size()) {
    _varNum = formulaVars.size();
  }

  if (_debug) {
    cout << "Checking if " << literal->toString() << " is Flutable" << endl;
  }
  if (!literal->allArgumentsAreVariables()) {
    if (_debug) {
      cout << literal->toString() << "Not Fluted: Not all arguments are variables" << endl;
    }
    return false;
  }

  SubtermIterator sti(literal);
  // Stack<unsigned> ReversedLitVars{};
  unsigned arity = literal->arity();
  VArray ReversedLitVars(arity);
  for (unsigned i{0}; i < arity && sti.hasNext(); i++) {
    ReversedLitVars[i] = sti.next().var();
  }

  VArray permutation(arity);
  int pos{0}, term{0};
  unsigned var{0}, i{arity};
  while (!formulaVars.isEmpty() && arity > 0) {
    arity--;
    if ((term = ReversedLitVars[arity]) >= 0) {
      i--;
      if (term != (var = formulaVars.pop())) {
        if ((pos = ReversedLitVars.indexOf(var, 0, arity)) >= 0 && pos < ReversedLitVars.size()) {
          ReversedLitVars.set(pos, -1);
          permutation.set(i, pos);
          arity++;
        }
        else {
          if (_debug) {
            cout << literal->toString() << "Not Fluted: Hole in fluted sequence" << endl;
          }
          return false;
        }
      }
      else {
        permutation.set(i, arity);
      }
    }
  }

  if (arity > 0) {
    if (_debug) {
      cout << literal->toString() << "Not Fluted: to many variables" << endl;
    }
    return false;
  }

  string permStr{permutation.toString()};
  string prevPermStr;
  if (_permutation_map.find(literal->functor(), prevPermStr)) {
    bool isPreviousPermutation{permStr == prevPermStr};
    if (_debug && !isPreviousPermutation) {
      cout << literal->toString() << "Not Fluted: ";
      cout << "Found previous permutation: they're " << (isPreviousPermutation ? "" : "not ") << "equal" << endl;
      cout << "Prev: " << prevPermStr << endl;
      cout << "Curr: " << permStr << endl;
    }

    return isPreviousPermutation;
  }

  _permutation_map.insert(literal->functor(), permStr);

  if (_debug) {
    cout << "Flutable with permutation: ";
    for (unsigned i{0}; i < permutation.size(); i++) {
      cout << permutation[i] << " ";
    }
    cout << endl;
  }

  return true;
}

} // namespace FlutedFragment