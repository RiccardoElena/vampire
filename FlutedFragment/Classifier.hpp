#ifndef __CLASSIFIER_H__
#define __CLASSIFIER_H__

#include "Kernel/Unit.hpp"
#include "Kernel/Formula.hpp"
#include "Utility/VArray.hpp"
#include <cstdlib>

namespace FlutedFragment {

using namespace Kernel;
class Classifier {

public:
  // Constructor
  Classifier(const bool enableDebugMode) : _debug(enableDebugMode){};

  // Exposed methods
  bool isInFlutedFragment(UnitList *ul);

  // Destructor
  ~Classifier() = default;

protected:
  // Members
  const bool _debug{false};
};

class FormulaClassifier : virtual protected Classifier {

public:
  // Constructor
  FormulaClassifier(const bool enableDebugMode) : Classifier(enableDebugMode){};

  // Exposed methods
  bool isInFlutedFragment(UnitList *ul);

  // Destructor
  ~FormulaClassifier() = default;

protected:
  // Members
  DHMap<unsigned, std::string> _permutation_map{};
  unsigned _varNum{0};

  bool isFluted(Formula *formula, Stack<unsigned> formulaVars);
  bool isFluted(Literal *literal, Stack<unsigned> formulaVars);
  bool isFlutable(Literal *literal, Stack<unsigned> formulaVars);

  // Helper Methods
  VList *extractOuterVariables(QuantifiedFormula *formula);
};

class ClauseClassifier : virtual protected Classifier {
public:
  // Constructor
  ClauseClassifier(const bool enableDebugMode) : Classifier(enableDebugMode){};

  // Exposed methods
  bool isInFlutedFragment(UnitList *ul);

  // Destructor
  ~ClauseClassifier() = default;

protected:
  // Members
  class EVar {
  public:
    // Constructor
    EVar() = default;
    EVar(const EVar &rhs) : _isSet(rhs._isSet), _hasZeroVars(rhs._hasZeroVars), _var(rhs._var){};
    EVar(EVar &&rhs) : _isSet(rhs._isSet), _hasZeroVars(rhs._hasZeroVars), _var(rhs._var){};
    EVar(const unsigned var) : _isSet(true), _hasZeroVars(false), _var(var){};

    // Destructor
    ~EVar() = default;

    // Operators
    inline bool operator==(const EVar &rhs) const
    {
      return _isSet && rhs._isSet && _hasZeroVars == rhs._hasZeroVars && (_hasZeroVars || _var == rhs._var);
    }

    inline bool operator==(const unsigned var) const { return _isSet && !_hasZeroVars && _var == var; }

    inline bool operator!=(const EVar &rhs) const { return !(*this == rhs); }

    inline bool operator!=(const unsigned var) const { return !(*this == var); }

    inline bool operator>(const EVar &rhs)
    {
      return (_hasZeroVars ? -1 : _var) > (rhs._hasZeroVars ? -1 : rhs._var);
    }

    EVar &operator=(const EVar &rhs)
    {
      _isSet = rhs._isSet;

      _hasZeroVars = rhs._hasZeroVars;
      _var = rhs._var;
      return *this;
    }

    // Move assignment
    EVar &operator=(EVar &&rhs)
    {
      _isSet = rhs._isSet;

      _hasZeroVars = rhs._hasZeroVars;
      _var = rhs._var;
      return *this;
    }

    EVar &operator=(const unsigned var)
    {
      setVar(var);
      return *this;
    }

    EVar &operator++()
    {
      if (_hasZeroVars) {
        _hasZeroVars = false;
        _var = 1;
      }
      else {
        _var++;
      }
      return *this;
    }

    // Exposed methods
    inline unsigned distance(const EVar &rhs)
    {
      if (_hasZeroVars && rhs._hasZeroVars) {
        return 0;
      }
      if (_hasZeroVars) {
        return 1 + rhs._var;
      }
      if (rhs._hasZeroVars) {
        return 1 + _var;
      }
      return abs(static_cast<int>(rhs._var - _var));
    }
    inline bool isSet() const { return _isSet; }
    inline bool isVar() const { return _isSet && !_hasZeroVars; }
    inline bool isConst() const { return _isSet && _hasZeroVars; }
    inline void setNoVars()
    {
      _isSet = _hasZeroVars = true;
    }
    inline void setVar(const unsigned var)
    {
      _isSet = true;
      _hasZeroVars = false;
      _var = var;
    }
    inline unsigned var() const
    {
      if (!isSet()) {
        throw "Variable not set";
      }
      if (_hasZeroVars)
        throw "No var present";

      return _var;
    }

  private:
    // Members
    bool _isSet{false};
    bool _hasZeroVars{false};
    unsigned _var{0};
  };

  class FlutedSequence {
  public:
    // Constructor
    FlutedSequence() = default;
    FlutedSequence(const FlutedSequence &rhs) : _termList(rhs._termList), _var(rhs._var), _isComplete(rhs._isComplete), _isValid(rhs._isValid){};
    FlutedSequence(FlutedSequence &&rhs) : _termList(rhs._termList), _var(rhs._var), _isComplete(rhs._isComplete), _isValid(rhs._isValid){};
    FlutedSequence(bool isValid) : _isValid(isValid){};

    // Destructor
    ~FlutedSequence() = default;

    // Operators

    FlutedSequence &operator=(const FlutedSequence &fl)
    {
      _termList = fl._termList;
      _var = fl._var;
      _isComplete = fl._isComplete;
      _isValid = fl._isValid;

      return *this;
    }
    FlutedSequence &operator=(FlutedSequence &&fl)
    {
      _termList = fl._termList;
      _var = fl._var;
      _isComplete = fl._isComplete;
      _isValid = fl._isValid;

      return *this;
    }

    // Exposed methods
    inline bool isFunctional()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _termList;
    }
    inline bool isComplete()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _isComplete;
    }
    inline void setIsComplete()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      _isComplete = true;
    }
    inline bool isVarSet()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _var.isSet();
    }
    inline const EVar &var() const
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      if (!_var.isSet() || _var.isConst()) {
        throw "Variable not set or has zero vars";
      }
      return _var;
    }

    inline void setVar(EVar var)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      _var = var;
    }

    inline void setNoVars()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      _var.setNoVars();
    }
    inline void addTerm(Term *term)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      _termList = List<Term *>::addLast(_termList, term);
    }
    inline bool isVarConst()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _var.isConst();
    }
    inline bool hasTermList()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _termList;
    }
    inline List<Term *> *termList()
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      return _termList;
    }
    inline void setTermList(List<Term *> *termList)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      _termList = termList;
    }
    inline bool isListMember(Term *term)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      List<Term *>::Iterator it(_termList);
      while (it.hasNext()) {
        if (it.next() == term) {
          return true;
        }
      }
      return false;
    }
    inline bool hasAsSubfix(List<Term *> *tl)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      List<Term *>::Iterator it1(_termList);
      bool foundFirst{false};
      while (it1.hasNext() && tl) {
        Term *currT = it1.next();
        if (currT == tl->head()) {
          foundFirst = true;
        }
        if (foundFirst) {
          if (currT != tl->head()) {
            return false;
          }
          tl = tl->tail();
        }
      }
      return true;
    }
    inline bool onePrefixOfOther(List<Term *> *tl)
    {
      if (!_isValid)
        throw "Invalid FlutedSequence";
      List<Term *>::Iterator it1(_termList);
      while (it1.hasNext() && tl) {
        if (it1.next() != tl->head()) {
          return false;
        }
        tl = tl->tail();
      }
      return true;
    }
    inline void setInvalid() { _isValid = false; }
    inline bool isValid() { return _isValid; }

  private:
    // Members
    List<Term *> *_termList{nullptr};
    EVar _var{};
    bool _isComplete{false};
    bool _isValid{true};
  };

  friend class Separator;

  // Core Methods
  bool isFluted(Clause *clause);
  bool isFluted(Literal *literal, FlutedSequence &flutedSequence);
  FlutedSequence isFluted(Term *literal, EVar v);
  bool isFL1Clause(Clause *clause);
  bool isFL2Clause(Clause *clause);
  bool isFL3Clause(Clause *clause);
  bool UpdateRightMostVars(EVar &rightMostVar1, EVar &rightMostVar2, unsigned int lastVar);
};
} // namespace FlutedFragment

#endif // __CLASSIFIER_H__