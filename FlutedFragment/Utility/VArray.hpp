#ifndef __VARRAY_H__
#define __VARRAY_H__

#include "Lib/Array.hpp"

namespace FlutedFragment {

using namespace Lib;

class VArray : public Array<unsigned> {
public:
  VArray(size_t initialCapacity) : Array<unsigned>(initialCapacity) {}

  inline void fillInterval(size_t start, size_t end)
  {
    for (size_t i = start; i < end; i++) {
      _array[i] = static_cast<unsigned>(0);
    }
  }

  inline void reset() { fillInterval(0, _capacity); }

  inline unsigned indexOf(unsigned el)
  {
    for (unsigned i = 0; i < _capacity; ++i) {
      if (_array[i] == el) {
        return i;
      }
    }
    return _capacity;
  }

  inline unsigned indexOf(unsigned el, unsigned start, unsigned end)
  {
    if (end > _capacity) {
      end = _capacity;
    }
    for (unsigned i = start; i < end; ++i) {
      if (_array[i] == el) {
        return i;
      }
    }
    return _capacity;
  }

  inline std::string toString()
  {
    std::string s{""};
    for (unsigned i = 0; i < size(); i++) {
      s += std::to_string((*this)[i]);
    }
    return s;
  }
};

} // namespace FlutedFragment

#endif // __VARRAY_H__