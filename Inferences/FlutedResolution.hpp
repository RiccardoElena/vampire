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
 * @file FlutedResolution.hpp
 * Defines class FlutedResolution
 *
 */

#ifndef __FlutedResolution__
#define __FlutedResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "ProofExtra.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FlutedResolution
    : public GeneratingInferenceEngine {
public:
  FlutedResolution()
      : _index(0)
  {
  }

  void attach(SaturationAlgorithm *salg);
  void detach();

  ClauseIterator generateClauses(Clause *premise);

private:
  Clause *generateClause(
      Clause *queryCl, Literal *queryLit, Clause *resultCl, Literal *resultLit,
      ResultSubstitutionSP subs, AbstractingUnifier *absUnif);

  FlutedResolutionIndex *_index;

  bool isEligibleLiteral(Literal *lit, Clause *cl);

  bool isMaximal(Literal *lit, Clause *cl, bool strict = false);

  enum class ComparisonResult {
    LESSER = 0,
    GREATER = 1,
    EQUAL = 2,
    INCOMPARABLE = 3
  };

  ComparisonResult compareLiterals(Literal *l1, Literal *l2);

  ComparisonResult groundLitComparison(Term *l1, Term *l2);

  ComparisonResult superTermRelation(const TermList *t1, const TermList *t2);

  bool isContained(const TermList *t1, const TermList *t2);
};

using FlutedResolutionExtra = TwoLiteralInferenceExtra;

}; // namespace Inferences

#endif /*__BinaryResolution__*/
