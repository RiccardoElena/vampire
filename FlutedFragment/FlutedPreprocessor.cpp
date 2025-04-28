#include "Lib/ScopedLet.hpp"
#include <iostream>

#include "Forwards.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/CNF.hpp"

#include "FlutedPreprocessor.hpp"
#include "Classifier.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Preprocess.hpp"
#include "Kernel/FormulaVarIterator.hpp"

using namespace Shell;
using namespace FlutedFragment;
using namespace Kernel;
using namespace std;

#define FLUTED_PREPROCESSOR_DEBUG 0

void FlutedPreprocessor::preprocess(Problem &prb)
{

  {
    std::cout << "preprocessing started" << std::endl;
    UnitList::Iterator uit(prb.units());
    while (uit.hasNext()) {
      Unit *u = uit.next();
      std::cout << "[PP] input: " << u->toString() << std::endl;
    }
  }

  UnitList::DelIterator us(prb.units());
  while (us.hasNext()) {
    Unit *u = us.next();

    if (u->isClause() || u->inference().rule() == InferenceRule::DEF)
      continue;

    FormulaUnit *fu = static_cast<FormulaUnit *>(u);
    if (_debug) {
      cout << "Simplifying true and false: " << fu->toString() << endl;
    }
    fu = SimplifyFalseTrue::simplify(fu);
    if (_debug) {
      cout << "Processing: " << fu->toString() << endl;
    }

    fu = new FormulaUnit(Def(fu->formula(), prb, u), FormulaTransformation(InferenceRule::DEF, u));
    if (_debug) {
      cout << "New sentence: " << fu->toString() << endl;
    }

    us.replace(fu);
  }

  if (_debug) {
    cout << endl;
    UnitList::DelIterator us3(prb.units());
    while (us3.hasNext()) {
      cout << us3.next()->toString() << endl;
    }
    cout << endl;
  }

  UnitList::DelIterator us2(prb.units());

  while (us2.hasNext()) {

    Unit *u = us2.next();

    if (u->isClause())
      continue;

    FormulaUnit *fu = static_cast<FormulaUnit *>(u);
    if (_debug) {
      cout << fu->toString() << endl;
    }

    /* 2. transform FOF formula in NNF*/
    fu = NNF::nnf(fu);
    fu = Flattening::flatten(fu);

    // us2.replace(fu);
    if (_debug) {
      cout << fu->toString() << endl;
    }

    /* 3. skolemise formulae*/

    fu = Skolem::skolemise(fu);

    us2.replace(fu);
    if (_debug) {
      cout << fu->toString() << endl;
    }
  }

  /* 4. clausification formulae*/
  clausify(prb);

#if FLUTED_PREPROCESSOR_DEBUG

  UnitList::Iterator uit(prb.units());
  while (uit.hasNext()) {
    Unit *u = uit.next();
    std::cout << "[PP] final: " << u->toString() << std::endl;
  }

#endif
}

Formula *FlutedPreprocessor::Def(Formula *formula, Problem &prb, Unit *u, Polarity pol)
{
  Formula *ret = formula;
  if (_memo.find(formula)) {
#if FLUTED_PREPROCESSOR_DEBUG
    cout << "Found in memo: "
         << formula->toString() << " |-> "
         << _memo.get(formula)->toString() << endl;
#endif
    return _memo.get(formula);
  }

  switch (formula->connective()) {
    case FORALL:
    case EXISTS: {
      Formula *subformula = formula->qarg();
      VList::Iterator it(formula->vars());
      auto sorts = formula->sorts();
      Stack<unsigned> vars;
      while (it.hasNext()) {
        unsigned var = it.next();
        vars.push(var);
      }
      unsigned var = vars.pop();
      VList *v = new VList(var);
      formula = new QuantifiedFormula(formula->connective(), v, sorts, subformula);
      while (vars.isNonEmpty()) {
        unsigned var = vars.pop();
        v = new VList(var);
        formula = new QuantifiedFormula(formula->connective(), v, sorts, formula);
#if FLUTED_PREPROCESSOR_DEBUG
        cout << "Partial formula restructuring: " << formula->toString() << endl;
#endif
      }
#if FLUTED_PREPROCESSOR_DEBUG
      cout << "Calling def from formula: " << formula->toString() << endl;
#endif
      subformula = formula->qarg();
#if FLUTED_PREPROCESSOR_DEBUG
      cout << "New subformula: " << subformula->toString() << endl;
#endif
      Formula *s = Def(formula->qarg(), prb, u, pol);
      formula = new QuantifiedFormula(formula->connective(), formula->vars(), formula->sorts(), s);
#if FLUTED_PREPROCESSOR_DEBUG
      cout << "Substitued formula: " << formula->toString() << endl;
#endif
      ret = axiomatize(formula, pol, u, prb);

#if FLUTED_PREPROCESSOR_DEBUG
      cout << ret->toString() << endl;
#endif
      break;
    }
    case IFF:
    case XOR: {
      Formula *left = Def(formula->left(), prb, u, NEUTRAL);
      Formula *right = Def(formula->right(), prb, u, NEUTRAL);

      ret = new BinaryFormula(formula->connective(), left, right);

      break;
    }

    case IMP: {

      Formula *left = Def(formula->left(), prb, u, invertPolarity(pol));
      Formula *right = Def(formula->right(), prb, u, pol);
#if FLUTED_PREPROCESSOR_DEBUG
      cout << left->toString() << " , " << right->toString() << endl;
#endif
      if (left != formula->left() || right != formula->right()) {
        ret = new BinaryFormula(formula->connective(), left, right);
      }
      break;
    }
    case NOT: {
      Formula *f = Def(formula->uarg(), prb, u, invertPolarity(pol));
#if FLUTED_PREPROCESSOR_DEBUG
      cout << f->toString() << endl;
      cout << formula->toString() << endl;
#endif
      if (f != formula->uarg()) {
        ret = new NegatedFormula(f);
      }
      break;
    }
    case OR:
    case AND: {
#if FLUTED_PREPROCESSOR_DEBUG
      cout << formula->toString() << endl;
#endif
      FormulaList *newArgs = 0;
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Formula *f = Def(it.next(), prb, u, pol);
#if FLUTED_PREPROCESSOR_DEBUG
        cout << f->toString() << endl;
#endif
        FormulaList::push(f, newArgs);
      }
      if (newArgs != formula->args()) {
        ret = new JunctionFormula(formula->connective(), newArgs);
      }

      break;
    }
    case LITERAL:
    case TRUE:
    case FALSE:
    case BOOL_TERM:
    default:
      break;
  }
  _memo.insert(formula, ret);
#if FLUTED_PREPROCESSOR_DEBUG
  cout << "Inserting in memo: "
       << formula->toString() << " |-> "
       << ret->toString() << endl;
#endif
  return ret;
}

/*
  Given a formula and its polarity, generate a new formula
  with a new predicate and the original formula as an argument.

  The new predicate is added to the signature and the new formula
  is added to the problem. The original formula is replaced by
  the new predicate in the original formula.

  The new formula is of the form:
  (forall x1, ..., xn) (fl(x1, ..., xn) -> original_formula) if polarity is positive
  (forall x1, ..., xn) (original_formula -> fl(x1, ..., xn)) if polarity is negative
  the conjunction of the two if polarity is neutral
  where fl is a new predicate and x1, ..., xn are the free variables in the original formula.

*/
Formula *FlutedFragment::FlutedPreprocessor::axiomatize(Formula *formula, FlutedPreprocessor::Polarity pol, Unit *u, Problem &prb)
{

  FormulaVarIterator freeVars(formula);
  Stack<TermList> args;

  VList *newFormulaVars = 0;

  while (freeVars.hasNext()) {
    auto var = freeVars.next();

    newFormulaVars = VList::addLast(newFormulaVars, var);

    args.push(TermList(var, false));
  }

  auto newPred = env.signature->addFreshPredicate(args.size(), "fl");
  Literal *freshLit = Literal::create(newPred, args.size(), true, args.begin());
  AtomicFormula *freshLitAtom = new AtomicFormula(freshLit);
#if FLUTED_PREPROCESSOR_DEBUG

  cout << "new atom: "
       << freshLitAtom->toString() << endl;
#endif

  Formula *newFormula = generateNewFormula(formula, freshLitAtom, newFormulaVars, pol);
#if FLUTED_PREPROCESSOR_DEBUG
  cout << "New formula: " << newFormula->toString() << endl;
  cout << "yee" << endl;
#endif
  FormulaUnit *newUnit = new FormulaUnit(newFormula, FormulaTransformation(InferenceRule::DEF, u));

#if FLUTED_PREPROCESSOR_DEBUG
  cout << "Inserting new unit: "
       << newUnit->toString() << endl;
#endif
  UnitList::push(newUnit, prb.units());

  if (env.options->showPreprocessing()) {
    cout << "Def adding: " << newUnit->toString() << std::endl;
  }
#if FLUTED_PREPROCESSOR_DEBUG
  cout << "New atom to be substituted: " << freshLitAtom->toString() << endl;
#endif
  return freshLitAtom;
}

Formula *FlutedPreprocessor::generateNewFormula(Formula *formula, AtomicFormula *freshLiteral, VList *vars, FlutedPreprocessor::Polarity pol)
{

  switch (pol) {
    case POSITIVE:
      return generateNewFormula(formula, freshLiteral, vars, true);
      break;
    case NEGATIVE:
      return generateNewFormula(formula, freshLiteral, vars, false);
      break;
    case NEUTRAL:
      FormulaList *newArgs = FormulaList::empty();
      Formula *pos = generateNewFormula(formula, freshLiteral, vars, true);
      Formula *neg = generateNewFormula(formula, freshLiteral, vars, false);
      FormulaList::push(neg, newArgs);
      FormulaList::push(pos, newArgs);
      return new JunctionFormula(AND, newArgs);
      break;
  }
}

Formula *FlutedPreprocessor::generateNewFormula(Formula *formula, AtomicFormula *freshLiteral, VList *vars, bool pol)
{
  Formula *bf;

  if (pol) {
    bf = new BinaryFormula(IMP, freshLiteral, formula);
  }
  else {
    bf = new BinaryFormula(IMP, formula, freshLiteral);
  }

#if FLUTED_PREPROCESSOR_DEBUG
  cout << "New def args: "
       << bf->toString() << endl;
#endif
  QuantifiedFormula *qf = new QuantifiedFormula(FORALL, vars, 0, bf);
#if FLUTED_PREPROCESSOR_DEBUG
  cout << "New " << (pol ? "pos" : "neg") << " formula: "
       << qf->toString() << endl;
#endif
  return qf;
}

void FlutedPreprocessor::clausify(Problem &prb)
{
  env.statistics->phase = Statistics::CLAUSIFICATION;

  // we check if we haven't discovered an empty clause during preprocessing
  Unit *emptyClause = 0;

  bool modified = false;

  UnitList::DelIterator us(prb.units());
  CNF cnf;
  Stack<Clause *> clauses(32);
  if (_debug) {
    cout << "Clausifying" << endl;
  }
  while (us.hasNext()) {
    Unit *u = us.next();
    if (_debug) {
      std::cout << "[PP] clausify: " << u->toString() << std::endl;
    }
    if (u->isClause()) {
      if (static_cast<Clause *>(u)->isEmpty()) {
        emptyClause = u;
        break;
      }
      continue;
    }
    modified = true;
    cnf.clausify(u, clauses);
    while (!clauses.isEmpty()) {
      Unit *u = clauses.pop();
      if (static_cast<Clause *>(u)->isEmpty()) {
        emptyClause = u;
        goto fin;
      }
      us.insert(u);
    }
    us.del();
  }
fin:
  if (emptyClause) {
    UnitList::destroy(prb.units());
    prb.units() = 0;
    UnitList::push(emptyClause, prb.units());
  }
  if (modified) {
    prb.invalidateProperty();
  }
  prb.reportFormulasEliminated();
}
