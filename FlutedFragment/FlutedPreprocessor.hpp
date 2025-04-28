#ifndef __FLUTEDPREPROCESSOR_H__
#define __FLUTEDPREPROCESSOR_H__

#include "Kernel/Unit.hpp"
#include "Forwards.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/Map.hpp"
namespace FlutedFragment {
using namespace Kernel;
class Property;
class Options;
class FlutedPreprocessor {
public:
  enum Polarity {
    POSITIVE = 1,
    NEGATIVE = -1,
    NEUTRAL = 0
  };
  /** Initialise the preprocessor */
  explicit FlutedPreprocessor(const Shell::Options &options) : _options(options), _debug(options.showFluted()) {}

  void preprocess(Problem &prb);
  Formula *Def(Formula *formula, Problem &prb, Unit *u, Polarity pol = POSITIVE);

  Formula *axiomatize(Kernel::Formula *formula, FlutedFragment::FlutedPreprocessor::Polarity pol, Kernel::Unit *u, Kernel::Problem &prb);

  void clausify(Problem &prb);

  /** Options used in the normalisation */
  const Shell::Options &_options;

private:
  bool _debug{false};
  Map<Formula *, Formula *, DefaultHash> _memo = Map<Formula *, Formula *, DefaultHash>();

  inline Polarity invertPolarity(Polarity pol) const
  {
    return static_cast<Polarity>(pol * (-1));
  }

  Formula *generateNewFormula(Formula *formula, AtomicFormula *lit, VList *vars, FlutedPreprocessor::Polarity pol);
  Formula *generateNewFormula(Formula *formula, AtomicFormula *freshLiteral, VList *vars, bool pol);
};

} // namespace FlutedFragment
#endif // __FLUTEDPREPROCESSOR_H__