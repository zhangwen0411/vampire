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
#include "Inferences/IRC/InequalityResolution.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/TermIndexTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using Test::TermIndexTest::termQueryResult;
using Test::TermIndexTest::subs;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define MY_SYNTAX_SUGAR                                                                                       \
  NUMBER_SUGAR(Rat)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Rat}, Rat)                                                                                    \
  DECL_CONST(a, Rat)                                                                                          \
  DECL_CONST(b, Rat)                                                                                          \
  DECL_CONST(c, Rat)                                                                                          \
  DECL_CONST(d, Rat)                                                                                          \

#define UWA_MODE Options::UnificationWithAbstraction::IRC1

InequalityResolutionIndex* inequalityResolutionIndex() 
{
  auto idx = new InequalityResolutionIndex( new TermSubstitutionTree(UWA_MODE, /* useC = */ true));
  idx->setShared(testIrcState(UWA_MODE));
  return idx;
}

TERM_INDEX_TEST_SET_DEFAULT(withConstraints, true);
TERM_INDEX_TEST_SET_DEFAULT(index, inequalityResolutionIndex());

TEST_TERM_INDEX(test01,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({  selected(2 * a + 3 * b > 0)  }),
      })
      .query ( a )
      .expected({
      })
    )

TEST_TERM_INDEX(test02,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected( 2 * a + 3 * b > 0 ) }),
      })
      .query ( b )
      .expected({
          termQueryResult()
            .term        ( b )
            .substitution({ })
            .constraints ({ })
      })
    )

TEST_TERM_INDEX(test03,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected( 2 * a + 3 * b > 0 ) }),
      })
      .query ( b )
      .expected({
          termQueryResult()
            .term        ( b )
            .substitution({ })
            .constraints ({ })
      })
    )

TEST_TERM_INDEX(test04,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected(     f(a) > 0 ) }),
                  clause({ selected( 2 * f(b) > 0 ) }),
      })
      .query ( b )
      .expected({ /* nothing */ })
    )

TEST_TERM_INDEX(test05,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected(     f(a) > 0 ) }),
                  clause({ selected( 2 * f(b) > 0 ) }),
      })
      .query ( f(x) )
      .expected({

          termQueryResult()
            .term        ( f(a) )
            .substitution({ subs(x, a) })
            .constraints ({ }),

          termQueryResult()
            .term        ( f(b) )
            .substitution({ subs(x, b) })
            .constraints ({ }),

      })
    )

TEST_TERM_INDEX(test06,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected( f(b + x + y) > 0 ) }),
      })
      .query (  f(a + z) )
      .expected({

          termQueryResult()
            .term        ( f(b + x + y) )
            .substitution({  })
            .constraints ({ a + z == b + x + y }),

      })
    )

TEST_TERM_INDEX(test07,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected( f(c + b + a) + f(c) > 0  ) }),
      })
      .query (  f(c) )
      .expected({

          // termQueryResult() -> not maximal
          //   .term        ( f(c) )
          //   .substitution({  })
          //   .constraints ({  }),

          termQueryResult()
            .term        ( f(c + b + a) )
            .substitution({   })
            .constraints ({ c == c + b + a }),

      })
    )

TEST_TERM_INDEX(test08,
    TermIndexTest::TestCase()
      .contents ({ 
                  clause({ selected( f(a + b) > 0  ) }),
      })
      .query (  f(c + d) )
      .expected({

          termQueryResult()
            .term        ( f(a + b) )
            .substitution({  })
            .constraints ({ a + b == c + d }),

      })
    )