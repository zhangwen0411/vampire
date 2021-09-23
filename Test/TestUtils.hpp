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
 * @file TestUtils.hpp
 * Defines class TestUtils.
 */

#ifndef __TestUtils__
#define __TestUtils__

#include "Forwards.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"

#include "Api/FormulaBuilder.hpp"
#include "Api/Problem.hpp"
#include "Lib/Coproduct.hpp"
#include "Lib/Map.hpp"
#include "Kernel/Clause.hpp"

namespace Test {
class TestUtils {

public:
  /** 
   * Tests whether two terms are equal modulo associativity and commutativity.
   * Whether a method is assoc and commut is checked with `TestUtils::isAC(..)`
   *
   * !!! exponential runtime !!!
   */
  static bool eqModAC(Kernel::TermList lhs, Kernel::TermList rhs);

  /** 
   * Tests whether two clauses are equal. All permutations of the clauses are tested. Variable renamings are 
   * not taken into account (i.e.: { p(x) } is NOT equal to { p(y) } for this function).
   *
   * !!! exponential runtime !!!
   */
  static bool eqModAC(const Kernel::Clause* lhs, const Kernel::Clause* rhs);
  static bool eqModAC(Kernel::Literal* lhs, Kernel::Literal* rhs);

  // /** 
  //  * Tests whether two clauses are equal. All permutations of the clauses are tested. Variable renamings are 
  //  * taken into account (i.e.: { p(x) } IS equal to { p(y) } for this function).
  //  *
  //  * !!! exponential runtime !!!
  //  */
  // static bool eqModACVar(const Kernel::Clause* lhs, const Kernel::Clause* rhs);

  /**
   * The ... are len of integers, positive -- positive polarity, negative -- negative polarity.
   */
  static SAT::SATClause* buildSATClause(unsigned len,...);



private:

  struct RectMap
  {
    class Inner {
      unsigned cnt = 0;
      Map<unsigned, unsigned> _self;
    public:
      unsigned get(unsigned var) 
      { return _self.getOrInit(std::move(var), [&](){ return cnt++; }); }
    };
    Inner l;
    Inner r;
  };


  // static bool eqModACVar(const Kernel::Clause* lhs, const Kernel::Clause* rhs, RectMap& r);
  // static bool eqModACVar(Kernel::Literal* lhs, Kernel::Literal* rhs, RectMap& r);
  // static bool eqModACVar(Kernel::TermList lhs, Kernel::TermList rhs, RectMap& r);
  template<class Comparisons>
  static bool eqModAC_(Kernel::TermList lhs, Kernel::TermList rhs, Comparisons c);

  /**
   * Tests whether there is a permutation pi s.t. pi(lhs) == rhs, where elements are compared by
   * elemEq(l,r)
   * `List` must provide methods 
   *    - `elem_type operator[](unsigned)` 
   *    - `unsigned size()`
   * `Eq`   must provide methods
   *    - `bool operator(const elem_type&, const elem_type&)`
   */
  template<class List, class Eq> 
  static bool permEq(const List& lhs, const List& rhs, Eq elemEq);

  /** returns whether the function f is associative and commutative */
  static bool isAC(Kernel::Theory::Interpretation f);
  static bool isAC(Kernel::Term* f);
};

/** 
 * Newtype for pretty-printing objects. 
 *
 * Usage: 
 * std::cout << pretty(obj) << std::endl;
 */
template<class T>
class Pretty {
  const T& _self;
public:
  Pretty(const T& t) : _self(t) { }

  std::ostream& prettyPrint(std::ostream& out) const
  { return out << _self; }

  template<class U>
  friend Pretty<U> pretty(const U& t);
};

template<class U>
Pretty<U> pretty(const U& t) 
{ return Pretty<U>(t); }


template<class U>
std::ostream& operator<<(std::ostream& out, const Pretty<U>& self)
{  return self.prettyPrint(out); }


template<class... As>
class Pretty<Lib::Coproduct<As...>> 
{
  Lib::Coproduct<As...> const& _self;

public:
  Pretty(Lib::Coproduct<As...> const& self) : _self(self) { }

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self.apply([&](auto const& a) -> std::ostream& { return out << pretty(a); }); }
};


template<class A>
class Pretty<A*> {
  A* const& _self;

public:
  Pretty(A* const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self == nullptr ? out << "null" : out << pretty(*_self); }
};


template<class A>
class Pretty<Stack<A>> {
  Stack<A> const& _self;

public:
  Pretty(Stack<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  {
    auto iter = _self.iterFifo();
    out << "[ ";
    if (iter.hasNext()) {
      out << pretty(iter.next());
      while (iter.hasNext()) {
        out << ", " << pretty(iter.next());
      }
    }
    out << " ]";
    return out;
  }
};


template<class A>
class Pretty<Option<A>> {
  Option<A> const& _self;

public:
  Pretty(Option<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return _self.isSome() ? out << pretty(_self.unwrap()) : out << "none"; }
};

template<class A>
class Pretty<unique_ptr<A>> {
  unique_ptr<A> const& _self;

public:
  Pretty(unique_ptr<A> const& self) : _self(self) {}

  std::ostream& prettyPrint(std::ostream& out) const
  { return out << pretty(*_self); }
};


}

#endif // __TestUtils__
