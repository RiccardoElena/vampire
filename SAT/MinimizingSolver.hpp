/**
 * @file MinimizingSolver.hpp
 * Defines class MinimizingSolver.
 */

#ifndef __MinimizingSolver__
#define __MinimizingSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"



namespace SAT {

using namespace Lib;

class MinimizingSolver : public SATSolver {
public:
  MinimizingSolver(SATSolver* inner);

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate=false);
  virtual VarAssignment getAssignment(unsigned var);
  virtual void ensureVarCnt(unsigned newVarCnt);

  virtual void addAssumption(SATLiteral lit, bool onlyPropagate=false);
  virtual void retractAllAssumptions();

private:

  void updateAssignment();

  SATSolverSCP _inner;

  DHMap<unsigned, bool> _assumptions;

  /**
   * If true, _asgn assignment corresponds to the assignment in
   * the inner solver
   */
  bool _assignmentValid;


  /**
   * Clauses of which we yet need to ensure they are satisfied
   *
   * Invariant: outside of addSatClauses the stack is empty.
   */
  SATClauseStack _unprocessed;

  /**
   * A total extension of the current assignment. A variable is
   * don't-care in the current assignment if its _watcher stack
   * is empty.
   */
  DArray<bool> _asgn;

  /**
   * Array of clauses kept satisfied by selecting or non-selecting
   * a particular variable
   *
   * Invariant to hold outside of addSatClauses:
   * All added clauses that contain at least one positive literal
   * are added into the wather. Each such clause occurrs here exactly
   * once.
   */
  DArray<SATClauseStack> _watcher;

};

}

#endif // __MinimizingSolver__