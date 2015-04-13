
#include "Lib/Vstring.hpp"
#include "Shell/Options.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID optionConstraints
UT_CREATE;

using namespace Shell;

bool testGlobal(Options& o)
{
  try{
    return o.checkGlobalOptionConstraints();
  }
  catch(Lib::UserErrorException& e){
    e.cry(cout);
    return false;
  }
}

bool testOption(bool bad, vstring name,vstring value)
{
    //cout << (bad ? "Should be bad" : "Should be good") << endl;
    Options options;
    options.set(name,value);
    bool res = testGlobal(options);
    if(bad) res = !res;
    return res;
}
bool testOptionBad(vstring name, vstring value){ return testOption(true,name,value); }
bool testOptionGood(vstring name, vstring value){ return testOption(false,name,value); }


TEST_FUN(int_bounds)
{
  ASS(testOptionBad("naming","327681"));
  ASS(testOptionGood("naming","32767"));
  ASS(testOptionBad("lrs_first_time_check","200"));
  ASS(testOptionBad("lrs_first_time_check","-200"));
  ASS(testOptionGood("lrs_first_time_check","50"));
  ASS(testOptionBad("extensionality_max_length","1"));
}

TEST_FUN(choice_con)
{
  ASS(testOptionBad("equality_resolution_with_deletion","on"));
}

TEST_FUN(default_dependence)
{
  ASS(testOptionBad("saturation_algorithm","inst_gen"));
}

TEST_FUN(urr)
{
  // Unit resulting resolution has the dependence that it cannot be non-default
  // if the saturation algorithm is inst_gen AND inst_gen_with_resolution is off

  {
    Options o;
    o.set("unit_resulting_resolution","on");
    o.set("saturation_algorithm","inst_gen");
    o.set("splitting","off");
    o.set("inst_gen_with_resolution","off");
    ASS(!testGlobal(o));
  } 
}

TEST_FUN(nonlit)
{
  Options o;
  o.set("splitting","off");
  o.set("nonliterals_in_clause_weight","on");
  ASS(!testGlobal(o));
}
