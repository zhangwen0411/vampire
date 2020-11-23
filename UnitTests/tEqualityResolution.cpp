
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "Inferences/EqualityResolution.hpp"

using namespace Test;

/** 
 * NECESSARY: as for every test unit we need to specify a name, and initialize the unit 
 */
#define UNIT_ID EqualityResolution
UT_CREATE;

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<Inferences::EqualityResolution>)

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_SORT(s)                                                                                                \
  DECL_FUNC(f, {s}, s)                                                                                        \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \


/** Defines a test case. */
TEST_GENERATION(test_01,                                   // <- name
    Generation::TestCase()
      .input(     clause({  selected(x != f(a)), p(x)  })) // <- input clause
      .expected(exactly(                                   // <- a list of exactly which clauses are expected
            clause({  p(f(a))  })                          //    to be returned. Order matters!
      ))
      .premiseRedundant(false)                             // <- shall the premis be removed from the search 
                                                           //    space after the rule application ? 
                                                           //    (default value: false)
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .input(     clause({  x != f(a), selected(p(x))  }))
      .expected( exactly())
    )

TEST_GENERATION(test_03,
    Generation::TestCase()
      .input(     clause({  selected(x != f(a)), selected(p(x))  }))
      .expected( exactly( clause({  p(f(a))                              })))
    )

TEST_GENERATION(test_04,
    Generation::TestCase()
      .input(     clause({  selected(g(x) != f(a)), p(x)  }))
      .expected( exactly())
    )

TEST_GENERATION(test_05,
    Generation::TestCase()
      .input(     clause({  selected(f(g(x)) != f(y))  }))
      .expected( exactly( clause({})))
    )

TEST_GENERATION(test_06,
    Generation::TestCase()
      .input(     clause({  selected(f(g(x)) != f(x))  }))
      .expected( exactly())
    )
