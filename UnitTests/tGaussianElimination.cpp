/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/GaussianVariableElimination.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"

//TODO factor out
Clause& clause(std::initializer_list<reference_wrapper<Literal>> ls) { 
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 
  Clause& out = *new(ls.size()) Clause(ls.size(), testInf); 
  auto l = ls.begin(); 
  for (int i = 0; i < ls.size(); i++) { 
    out[i] = &l->get(); 
    l++; 
  }
  return out; 
}

bool exactlyEq(const Clause& lhs, const Clause& rhs, const Stack<unsigned>& perm) {
  for (int j = 0; j < perm.size(); j++) {
    if (!Indexing::TermSharing::equals(lhs[j], rhs[perm[j]])) {
      return false;
    }
  }
  return true;
}


bool permEq(const Clause& lhs, const Clause& rhs, Stack<unsigned>& perm, unsigned idx) {
  if (exactlyEq(lhs, rhs, perm)) {
    return true;
  }
  for (int i = idx; i < perm.size(); i++) {
    swap(perm[i], perm[idx]);

    
    if (permEq(lhs,rhs, perm, idx+1)) return true;

    swap(perm[i], perm[idx]);
  }

  return false;
}

//TODO factor out
bool operator==(const Clause& lhs, const Clause& rhs) {
  if (lhs.size() != rhs.size()) return false;

  Stack<unsigned> perm;
  for (int i = 0; i<lhs.size(); i++) {
    perm.push(i);
  }
  return permEq(lhs, rhs, perm, 0);

}
bool operator!=(const Clause& lhs, const Clause& rhs) {
  return !(lhs == rhs);
}


Clause* exhaustiveGve(Clause* in) {

  struct FakeOrdering : Kernel::Ordering {
    virtual Result compare(Literal*, Literal*) const override { return Kernel::Ordering::LESS; }
    virtual Result compare(TermList, TermList) const override {ASSERTION_VIOLATION}
    virtual Comparison compareFunctors(unsigned, unsigned) const override {ASSERTION_VIOLATION}
    virtual void show(ostream&) const override {ASSERTION_VIOLATION}
  };
  static FakeOrdering ord;
  static GaussianVariableElimination inf = GaussianVariableElimination();
  static InterpretedEvaluation ev = InterpretedEvaluation(false, ord);
  Clause* last = in;
  Clause* latest = in;
  do {
    last = latest;
    latest = ev.simplify(inf.simplify(last));
  } while (latest != last);
  return latest;
}


void test_eliminate_na(Clause& toSimplify) {
  auto res = exhaustiveGve(&toSimplify);
  if (res != &toSimplify ) {
    cout  << endl;
    cout << "[     case ]: " << toSimplify.toString() << endl;
    cout << "[       is ]: " << res->toString() << endl;
    cout << "[ expected ]: < nop >" << endl;
    exit(-1);
  }
}

void test_eliminate(Clause& toSimplify, const Clause& expected) {
  auto res = exhaustiveGve(&toSimplify);
  if (!res || *res != expected) {
    cout  << endl;
    cout << "[     case ]: " << toSimplify.toString() << endl;
    cout << "[       is ]: " << res->toString() << endl;
    cout << "[ expected ]: " << expected.toString() << endl;
    exit(-1);
  }
}

#define TEST_ELIMINATE(name, toSimplify, expected) \
  TEST_FUN(name) { \
    THEORY_SYNTAX_SUGAR(REAL) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
      _Pragma("GCC diagnostic pop") \
    test_eliminate((toSimplify),(expected)); \
  }

#define TEST_ELIMINATE_NA(name, toSimplify) \
  TEST_FUN(name) { \
    THEORY_SYNTAX_SUGAR(REAL) \
      _Pragma("GCC diagnostic push") \
      _Pragma("GCC diagnostic ignored \"-Wunused\"") \
        THEORY_SYNTAX_SUGAR_FUN(f, 1) \
      _Pragma("GCC diagnostic pop") \
    test_eliminate_na((toSimplify)); \
  }

TEST_ELIMINATE(test_1
    , clause({  neq(mul(3, x), 6), lt(x, y)  })
    , clause({  lt(2, y)  })
    )

TEST_ELIMINATE_NA(test_2
    , clause({ eq(mul(3, x), 6), lt(x, y) })
    )

TEST_ELIMINATE(test_3
    , clause({  neq(mul(3, x), 6), lt(x, x)  })
    , clause({  /* lt(2, 2) */  }) 
    )

TEST_ELIMINATE(test_uninterpreted
    , clause({  neq(mul(3, f(x)), y), lt(x, y)  })
    , clause({  lt(x, mul(3, f(x)))  })
    )

  // x!=4 \/ x+y != 5 \/ C[x]
  //         4+y != 5 \/ C[4]
  //                     C[4]
TEST_ELIMINATE(test_multiplesteps_1
    , clause({  neq(x, 4), neq(add(x,y), 5), lt(x, f(x))  })
    , clause({  lt(4, f(4))  })
    )

  // x!=4 \/ x+y != 5 \/ C[x,y]
  //         4+y != 5 \/ C[4,y]
  //                     C[4,1]
TEST_ELIMINATE(test_multiplesteps_2
    , clause({  neq(x, 4), neq(add(x,y), 5), lt(x, f(y))  })
    , clause({  lt(4, f(1))  })
    )

  // x  !=4 \/ x+y != 5 \/ C[x]
  // 5-y!=4             \/ C[5-y]
  //                    \/ C[5]


