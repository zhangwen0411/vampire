/**
 * @file vtest.cpp
 * Provides main function for the vtest executable which is used for unit testing.
 */

#include "Forwards.hpp"

#include "Api/ResourceLimits.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/List.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Test/UnitTesting.hpp"

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

using namespace Lib;
using namespace Kernel;
using namespace Test;

UnitList* globUnitList=0;
int globReturnValue = 1;

void explainException (Exception& exception)
{
  exception.cry(cout);
} // explainException

int main(int argc, char* argv [])
{
  CALL("main");

  srand(1); //this is for the reproducibility

  Api::ResourceLimits::disableLimits();
  System::setSignalHandlers();
   // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  try {

    if(argc==1) {
      UnitTesting::instance()->runAllTests(cout);
    }
    else if(argc==2) {
      if(!strcmp(argv[1],"-l")) {
	UnitTesting::instance()->printTestNames(cout);
      }
      else {
	if(!UnitTesting::instance()->runTest(argv[1],cout)) {
	  cout<<"Unknown test name: "<<argv[1]<<endl;
	  cout<<"Run \""<<argv[0]<<" -l\" for the list of available tests."<<endl;
	}
      }
    }
    else {
      cout<<"Invalid number of arguments ("<<(argc-1)<<")."<<endl;
      cout<<"Run \""<<argv[0]<<"\" to run all available tests."<<endl;
      cout<<"Run \""<<argv[0]<<" <test_id>\" to run a single test."<<endl;
      cout<<"Run \""<<argv[0]<<" -l\" for the list of available tests."<<endl;
    }


#if CHECK_LEAKS
    if (globUnitList) {
      MemoryLeak leak;
      leak.release(globUnitList);
    }
    delete env.signature;
    env.signature = 0;
#endif

    //if we got here, all went well and we can return 0
    globReturnValue = 0;
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
    env.statistics->print(cout);
  }
  catch (std::bad_alloc& _) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    cout << "Insufficient system memory" << '\n';
  }
//   delete env.allocator;

  return globReturnValue;
}
