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
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include <fstream>

#include "Forwards.hpp"

#include "Indexing/TermSharing.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"

#include "Shell/Options.hpp"
#include "Shell/Property.hpp"

#include "LPO.hpp"
#include "KBO.hpp"
#include "SKIKBO.hpp"
#include "KBOForEPR.hpp"
#include "Problem.hpp"
#include "Signature.hpp"

#include "Ordering.hpp"

#define NONINTERPRETED_PRECEDENCE_BOOST 0x1000

#define NONINTERPRETED_LEVEL_BOOST 0x1000
#define COLORED_LEVEL_BOOST 0x10000

using namespace Lib;
using namespace Kernel;

OrderingSP Ordering::s_globalOrdering;

Ordering::Ordering()
{
  CALL("Ordering::Ordering");

  createEqualityComparator();
  ASS(_eqCmp);
}

Ordering::~Ordering()
{
  CALL("Ordering::~Ordering");

  destroyEqualityComparator();
}


/**
 * If there is no global ordering yet, assign @c ordering to be
 * it and return true. Otherwise return false.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
bool Ordering::trySetGlobalOrdering(OrderingSP ordering)
{
  CALL("Ordering::trySetGlobalOrdering");

  if(s_globalOrdering) {
    return false;
  }
  s_globalOrdering = ordering;
  return true;
}

/**
 * If global ordering is set, return pointer to it, otherwise
 * return 0.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
Ordering* Ordering::tryGetGlobalOrdering()
{
  CALL("Ordering::tryGetGlobalOrdering");

  if(s_globalOrdering) {
    return s_globalOrdering.ptr();
  }
  else {
    return 0;
  }
}

/**
 * Creates the ordering
 *
 * Currently the ordering is created in @b SaturationAlgorithm::createFromOptions()
 */
Ordering* Ordering::create(Problem& prb, const Options& opt)
{
  CALL("Ordering::create");

  if(env.options->combinatorySup() || env.options->lambdaFreeHol()){
    return new SKIKBO(prb, opt, env.options->lambdaFreeHol());
  }

  Ordering* out;
  switch (env.options->termOrdering()) {
  case Options::TermOrdering::KBO:
    // KBOForEPR does not support 
    // - colors
    // - user specified symbol weights
    // TODO fix this! 
    if(prb.getProperty()->maxFunArity()==0 
        && !env.colorUsed
        && env.options->predicateWeights() == ""
        && env.options->functionWeights() == ""
        ) {
      out = new KBOForEPR(prb, opt);
    } else {
      out = new KBO(prb, opt);
    }
    break;
  case Options::TermOrdering::LPO:
    out = new LPO(prb, opt);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  if (opt.showSimplOrdering()) {
    env.beginOutput();
    out->show(env.out());
    env.endOutput();
  }
  return out;
}


Ordering::Result Ordering::fromComparison(Comparison c)
{
  CALL("Ordering::fromComparison");

  switch(c) {
  case Lib::GREATER:
    return GREATER;
  case Lib::EQUAL:
    return EQUAL;
  case Lib::LESS:
    return LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

Comparison Ordering::intoComparison(Ordering::Result r)
{
  CALL("Ordering::intoComparison");

  switch(r) {
  case Ordering::Result::GREATER: return Lib::GREATER;
  case Ordering::Result::EQUAL:   return Lib::EQUAL;
  case Ordering::Result::LESS:    return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

const char* Ordering::resultToString(Result r)
{
  CALL("Ordering::resultToString");

  switch(r) {
  case GREATER:
    return "GREATER";
  case GREATER_EQ:
    return "GREATER_EQ";
  case LESS:
    return "LESS";
  case LESS_EQ:
    return "LESS_EQ";
  case EQUAL:
    return "EQUAL";
  case INCOMPARABLE:
    return "INCOMPARABLE";
  default:
    ASSERTION_VIOLATION;
    return 0;
  }
}

/**
 * Remove non-maximal literals from the list @b lits. The order
 * of remaining literals stays unchanged.
 */
void Ordering::removeNonMaximal(LiteralList*& lits) const
{
  CALL("Ordering::removeNonMaximal");

  LiteralList** ptr1=&lits;
  while(*ptr1) {
    LiteralList** ptr2=&(*ptr1)->tailReference();
    while(*ptr2 && *ptr1) {
      Ordering::Result res=compare((*ptr1)->head(), (*ptr2)->head());

      if(res==Ordering::GREATER || res==Ordering::GREATER_EQ || res==Ordering::EQUAL) {
	LiteralList::pop(*ptr2);
	continue;
      } else if(res==Ordering::LESS || res==Ordering::LESS_EQ) {
	LiteralList::pop(*ptr1);
	goto topLevelContinue;
      }
      ptr2=&(*ptr2)->tailReference();
    }
    ptr1=&(*ptr1)->tailReference();
topLevelContinue: ;
  }

}

Ordering::Result Ordering::getEqualityArgumentOrder(Literal* eq) const
{
  CALL("Ordering::getEqualityArgumentOrder");
  ASS(eq->isEquality());

  if(tryGetGlobalOrdering()!=this) {
    return compare(*eq->nthArgument(0), *eq->nthArgument(1));
  }

  Result res;
  ArgumentOrderVals precomputed = static_cast<ArgumentOrderVals>(eq->getArgumentOrderValue());
  if(precomputed!=0) {
    res = static_cast<Result>(precomputed);
    ASS_EQ(res, compare(*eq->nthArgument(0), *eq->nthArgument(1)));
  }
  else {
    res = compare(*eq->nthArgument(0), *eq->nthArgument(1));
    eq->setArgumentOrderValue(res);
  }
  return res;
}

//////////////////////////////////////////////////
// PrecedenceOrdering class
//////////////////////////////////////////////////

Ordering::Result PrecedenceOrdering::compare(Literal* l1, Literal* l2) const
{
  CALL("PrecedenceOrdering::compare(Literal*...)");
  ASS(l1->shared());
  ASS(l2->shared());

  if (l1 == l2) {
    return EQUAL;
  }

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if( (l1->isNegative() ^ l2->isNegative()) && (p1==p2) &&
	  l1->weight()==l2->weight() && l1->vars()==l2->vars() &&  //this line is just optimization, so we don't check whether literals are opposite when they cannot be
	  l1==env.sharing->tryGetOpposite(l2)) {
    return l1->isNegative() ? LESS : GREATER;
  }

  if (p1 != p2) {
    Comparison levComp=Int::compare(predicateLevel(p1),predicateLevel(p2));
    if(levComp!=Lib::EQUAL) {
      return fromComparison(levComp);
    }
  }

  if(l1->isEquality()) {
    ASS(l2->isEquality());
    return compareEqualities(l1, l2);
  }
  ASS(!l1->isEquality());

  if(_reverseLCM && (l1->isNegative() || l2->isNegative()) ) {
    if(l1->isNegative() && l2->isNegative()) {
      return reverse(comparePredicates(l1, l2));
    }
    else {
      return l1->isNegative() ? LESS : GREATER;
    }
  }
  return comparePredicates(l1, l2);
} // PrecedenceOrdering::compare()

/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality). If a predicate is colored, its level is multiplied by
 * the COLORED_LEVEL_BOOST value.
 */
int PrecedenceOrdering::predicateLevel (unsigned pred) const
{
  int basic=pred >= _predicates ? 1 : _predicateLevels[pred];
  if(NONINTERPRETED_LEVEL_BOOST && !env.signature->getPredicate(pred)->interpreted() && pred != 0) {
    //ASS(!Signature::isEqualityPredicate(pred)); //equality is always interpreted
    //TODO remove the final condition once interpreted equality is reintroduced
    basic+=NONINTERPRETED_LEVEL_BOOST;
  }
  if(env.signature->predicateColored(pred)) {
    ASS_NEQ(pred,0); //equality should never be colored
    return COLORED_LEVEL_BOOST*basic;
  } else {
    return basic;
  }
} // PrecedenceOrdering::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 */
int PrecedenceOrdering::predicatePrecedence (unsigned pred) const
{
  int res=pred >= _predicates ? (int)pred : _predicatePrecedences[pred];
  if(NONINTERPRETED_PRECEDENCE_BOOST) {
    ASS_EQ(NONINTERPRETED_PRECEDENCE_BOOST & 1, 0); // an even number

    bool intp = env.signature->getPredicate(pred)->interpreted();
    res *= 2;
    return intp ? res+1 : res+NONINTERPRETED_PRECEDENCE_BOOST;
  }
  return res;
} // PrecedenceOrdering::predicatePrecedences

Comparison PrecedenceOrdering::compareFunctors(unsigned fun1, unsigned fun2) const
{
  CALL("PrecedenceOrdering::compareFunctors");

  if(fun1==fun2) {
    return Lib::EQUAL;
  }
  switch(compareFunctionPrecedences(fun1, fun2)) {
  case GREATER: return Lib::GREATER;
  case LESS: return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Compare precedences of two function symbols
 */ //TODO update for HOL>?
Ordering::Result PrecedenceOrdering::compareFunctionPrecedences(unsigned fun1, unsigned fun2) const
{
  CALL("PrecedenceOrdering::compareFunctionPrecedences");

  if (fun1 == fun2)
    return EQUAL;

  // $$false is the smallest
  if (env.signature->isFoolConstantSymbol(false,fun1)) {
    return LESS;
  }
  if (env.signature->isFoolConstantSymbol(false,fun2)) {
    return GREATER;
  }

  // $$true is the second smallest
  if (env.signature->isFoolConstantSymbol(true,fun1)) {
    return LESS;
  }

  if (env.signature->isFoolConstantSymbol(true,fun2)) {
    return GREATER;
  }

  Signature::Symbol* s1=env.signature->getFunction(fun1);
  Signature::Symbol* s2=env.signature->getFunction(fun2);
  // term algebra constructors are smaller than other symbols
  if(s1->termAlgebraCons() && !s2->termAlgebraCons()) {
    return LESS;
  }
  if(!s1->termAlgebraCons() && s2->termAlgebraCons()) {
    return GREATER;
  }
  // uninterpreted things are greater than interpreted things
  if(!s1->interpreted()) {
    if(s2->interpreted()) {
      return GREATER;
    }
    static bool reverse = env.options->introducedSymbolPrecedence() == Shell::Options::IntroducedSymbolPrecedence::BOTTOM;
    //two non-interpreted functions
    return fromComparison(Int::compare(
        fun1 >= _functions ? (int)(reverse ? -fun1 : fun1) : _functionPrecedences[fun1],
        fun2 >= _functions ? (int)(reverse ? -fun2 : fun2) : _functionPrecedences[fun2] ));
  }
  if(!s2->interpreted()) {
    return LESS;
  }
  if(s1->arity()) {
    if(!s2->arity()) {
      return GREATER;
    }
    //two interpreted functions
    return fromComparison(Int::compare(fun1, fun2));
  }
  if(s2->arity()) {
    return LESS;
  }
  //two interpreted constants

  if (!s1->numericConstant() || !s2->numericConstant()) {
    return fromComparison(Int::compare(fun1, fun2));
  }

  Comparison cmpRes;
  if(s1->integerConstant() && s2->integerConstant()) {
    cmpRes = IntegerConstantType::comparePrecedence(s1->integerValue(), s2->integerValue());
  }
  else if(s1->rationalConstant() && s2->rationalConstant()) {
    cmpRes = RationalConstantType::comparePrecedence(s1->rationalValue(), s2->rationalValue());
  }
  else if(s1->realConstant() && s2->realConstant()) {
    cmpRes = RealConstantType::comparePrecedence(s1->realValue(), s2->realValue());
  }
  else if(s1->integerConstant()) {
    ASS_REP(s2->rationalConstant() || s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->integerConstant()) {
    ASS_REP(s1->rationalConstant() || s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else if(s1->rationalConstant()) {
    ASS_REP(s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->rationalConstant()) {
    ASS_REP(s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else {
    ASSERTION_VIOLATION;
    cmpRes = Int::compare(fun1, fun2);
  }
  return fromComparison(cmpRes);
}

template<typename Comparator>
struct FnBoostWrapper
{
  FnBoostWrapper(Comparator comp) : _comp(comp) {}
  Comparator _comp;

  Comparison compare(unsigned f1, unsigned f2)
  {
    static Options::SymbolPrecedenceBoost boost = env.options->symbolPrecedenceBoost();
    Comparison res = EQUAL;
    bool u1 = env.signature->getFunction(f1)->inUnit(); 
    bool u2 = env.signature->getFunction(f2)->inUnit(); 
    bool g1 = env.signature->getFunction(f1)->inGoal();
    bool g2 = env.signature->getFunction(f2)->inGoal();
    switch(boost){
      case Options::SymbolPrecedenceBoost::NONE:
        break;
      case Options::SymbolPrecedenceBoost::GOAL:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::UNIT:
        if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::GOAL_UNIT:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        else if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
    }
    if(res==EQUAL){
      res = _comp.compare(f1,f2);
    }
    return res;
  }

};
template<typename Comparator>
struct PredBoostWrapper
{
  PredBoostWrapper(Comparator comp) : _comp(comp) {}
  Comparator _comp;

  Comparison compare(unsigned p1, unsigned p2)
  {
    static Options::SymbolPrecedenceBoost boost = env.options->symbolPrecedenceBoost();
    Comparison res = EQUAL;
    bool u1 = env.signature->getPredicate(p1)->inUnit();
    bool u2 = env.signature->getPredicate(p2)->inUnit();
    bool g1 = env.signature->getPredicate(p1)->inGoal();
    bool g2 = env.signature->getPredicate(p2)->inGoal();
    switch(boost){
      case Options::SymbolPrecedenceBoost::NONE:
        break;
      case Options::SymbolPrecedenceBoost::GOAL:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::UNIT:
        if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::GOAL_UNIT:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        else if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
    }
    if(res==EQUAL){
      res = _comp.compare(p1,p2);
    }
    return res;
  }
};

struct FnFreqComparator
{
  Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    Comparison res = Int::compare(c2,c1);
    if(res==EQUAL){
      res = Int::compare(f1,f2);
    }
    return res;
  }
};
struct PredFreqComparator
{
  Comparison compare(unsigned p1, unsigned p2)
  {
    unsigned c1 = env.signature->getPredicate(p1)->usageCnt();
    unsigned c2 = env.signature->getPredicate(p2)->usageCnt();
    Comparison res = Int::compare(c2,c1);
    if(res==EQUAL){
      res = Int::compare(p1,p2);
    }
    return res;
  }
};
struct FnRevFreqComparator
{
  Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    Comparison res = Int::compare(c1,c2);
    if(res==EQUAL){
      res = Int::compare(f1,f2);
    }
    return res;
  }
};
struct PredRevFreqComparator
{
  Comparison compare(unsigned p1, unsigned p2)
  {
    unsigned c1 = env.signature->getPredicate(p1)->usageCnt();
    unsigned c2 = env.signature->getPredicate(p2)->usageCnt();
    Comparison res = Int::compare(c1,c2);
    if(res==EQUAL){
      res = Int::compare(p1,p2);
    }
    return res;
  }
};

struct FnArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u1),
	    env.signature->functionArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u1),
	    env.signature->predicateArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

struct FnRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u2),
	    env.signature->functionArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u2),
	    env.signature->predicateArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

static void loadPermutationFromString(DArray<unsigned>& p, const vstring& str) {
  CALL("loadPermutationFromString");

  std::stringstream ss(str.c_str());
  unsigned i = 0;
  unsigned val;
  while (ss >> val)
  {
      if (i >= p.size()) {
        break;
      }

      if (val >= p.size()) {
        break;
      }

      p[i++] = val;

      if (ss.peek() == ',')
          ss.ignore();
  }
}

bool isPermutation(const DArray<int>& xs) {
  CALL("isPermutation");
  DArray<int> cnts(xs.size()); 
  cnts.init(xs.size(), 0);
  for (unsigned i = 0; i < xs.size(); i++) {
    cnts[xs[i]] += 1;
  }
  for (unsigned i = 0; i < xs.size(); i++) {
    if (cnts[xs[i]] != 1) {
      return false;
    }
  }
  return true;
}

/**
 * Create a PrecedenceOrdering object.
 */
PrecedenceOrdering::PrecedenceOrdering(const DArray<int>& funcPrec, const DArray<int>& predPrec, const DArray<int>& predLevels, bool reverseLCM)
  : _predicates(predPrec.size()),
    _functions(funcPrec.size()),
    _predicateLevels(predLevels),
    _predicatePrecedences(predPrec),
    _functionPrecedences(funcPrec),
    _reverseLCM(reverseLCM)
{
  CALL("PrecedenceOrdering::PrecedenceOrdering(const DArray<int>&, const DArray<int>&, const DArray<int>&, bool)");
  ASS_EQ(env.signature->predicates(), _predicates);
  ASS_EQ(env.signature->functions(), _functions);
  ASS(isPermutation(_functionPrecedences))
  ASS(isPermutation(_predicatePrecedences))
}

/**
 * Create a PrecedenceOrdering object.
 *
 * "Intermediate" constructor; this is needed so that we only call predPrecFromOpts once (and use it here twice).
 */
PrecedenceOrdering::PrecedenceOrdering(Problem& prb, const Options& opt, const DArray<int>& predPrec)
: PrecedenceOrdering(
    funcPrecFromOpts(prb,opt),
    predPrec,
    predLevelsFromOptsAndPrec(prb,opt,predPrec),
    opt.literalComparisonMode()==Shell::Options::LiteralComparisonMode::REVERSE
    )
{
  CALL("PrecedenceOrdering::PrecedenceOrdering((Problem&,const Options&,const DArray<int>&)");
}

/**
 * Create a PrecedenceOrdering object.
 */
PrecedenceOrdering::PrecedenceOrdering(Problem& prb, const Options& opt)
: PrecedenceOrdering(prb,opt,
    (
       // Make sure we (re-)compute usageCnt's for all the symbols;
       // in particular, the sP's (the Tseitin predicates) and sK's (the Skolem functions), which only exists since preprocessing.
       prb.getProperty(),
       predPrecFromOpts(prb, opt)))
{
  CALL("PrecedenceOrdering::PrecedenceOrdering(Problem&,const Options&)");
  ASS_G(_predicates, 0);
}

DArray<int> PrecedenceOrdering::funcPrecFromOpts(Problem& prb, const Options& opt) {
  unsigned nFunctions = env.signature->functions();
  DArray<unsigned> aux(nFunctions);

  if(nFunctions) {
    aux.initFromIterator(getRangeIterator(0u, nFunctions), nFunctions);

    if (!opt.functionPrecedence().empty()) {
      BYPASSING_ALLOCATOR;

      vstring precedence;
      ifstream precedence_file (opt.functionPrecedence().c_str());
      if (precedence_file.is_open() && getline(precedence_file, precedence)) {
        loadPermutationFromString(aux,precedence);
        precedence_file.close();
      }
    } else {
      switch(opt.symbolPrecedence()) {
      case Shell::Options::SymbolPrecedence::ARITY:
        aux.sort(FnBoostWrapper<FnArityComparator>(FnArityComparator()));
        break;
      case Shell::Options::SymbolPrecedence::REVERSE_ARITY:
        aux.sort(FnBoostWrapper<FnRevArityComparator>(FnRevArityComparator()));
        break;
      case Shell::Options::SymbolPrecedence::FREQUENCY:
      case Shell::Options::SymbolPrecedence::WEIGHTED_FREQUENCY:
        aux.sort(FnBoostWrapper<FnFreqComparator>(FnFreqComparator()));
        break;
      case Shell::Options::SymbolPrecedence::REVERSE_FREQUENCY:
      case Shell::Options::SymbolPrecedence::REVERSE_WEIGHTED_FREQUENCY:
        aux.sort(FnBoostWrapper<FnRevFreqComparator>(FnRevFreqComparator()));
        break;
      case Shell::Options::SymbolPrecedence::OCCURRENCE:
        break;
      case Shell::Options::SymbolPrecedence::SCRAMBLE:
        for(unsigned i=0;i<nFunctions;i++){
          unsigned j = Random::getInteger(nFunctions-i)+i;
          unsigned tmp = aux[j];
          aux[j]=aux[i];
          aux[i]=tmp;
        }
        break;
      }
    }

    
    /*cout << "Function precedences:" << endl;
    for(unsigned i=0;i<nFunctions;i++){
      cout << env.signature->functionName(aux[i]) << " ";
    }
    cout << endl;*/
    

    /*
    cout << "Function precedence: ";
    for(unsigned i=0;i<nFunctions;i++){
      cout << aux[i] << ",";
    }
    cout << endl;
    */

  }

  DArray<int>  functionPrecedences(nFunctions);
  for(unsigned i=0;i<nFunctions;i++) {
    functionPrecedences[aux[i]]=i;
  }
  return functionPrecedences;
}

DArray<int> PrecedenceOrdering::predPrecFromOpts(Problem& prb, const Options& opt) {
  unsigned nPredicates = env.signature->predicates();
  DArray<unsigned> aux(nPredicates);
  aux.initFromIterator(getRangeIterator(0u, nPredicates), nPredicates);

  if (!opt.predicatePrecedence().empty()) {
    BYPASSING_ALLOCATOR;

    vstring precedence;
    ifstream precedence_file (opt.predicatePrecedence().c_str());
    if (precedence_file.is_open() && getline(precedence_file, precedence)) {
      loadPermutationFromString(aux,precedence);
      precedence_file.close();
    }
  } else {
    switch(opt.symbolPrecedence()) {
    case Shell::Options::SymbolPrecedence::ARITY:
      aux.sort(PredBoostWrapper<PredArityComparator>(PredArityComparator()));
      break;
    case Shell::Options::SymbolPrecedence::REVERSE_ARITY:
      aux.sort(PredBoostWrapper<PredRevArityComparator>(PredRevArityComparator()));
      break;
    case Shell::Options::SymbolPrecedence::FREQUENCY:
    case Shell::Options::SymbolPrecedence::WEIGHTED_FREQUENCY:
      aux.sort(PredBoostWrapper<PredFreqComparator>(PredFreqComparator()));
      break;
    case Shell::Options::SymbolPrecedence::REVERSE_FREQUENCY:
    case Shell::Options::SymbolPrecedence::REVERSE_WEIGHTED_FREQUENCY:
     aux.sort(PredBoostWrapper<PredRevFreqComparator>(PredRevFreqComparator()));
     break;
    case Shell::Options::SymbolPrecedence::OCCURRENCE:
      break;
      case Shell::Options::SymbolPrecedence::SCRAMBLE:
        for(unsigned i=0;i<nPredicates;i++){
          unsigned j = Random::getInteger(nPredicates-i)+i;
          unsigned tmp = aux[j];
          aux[j]=aux[i];
          aux[i]=tmp;
        }
        break;
    }
  }
  /*
  cout << "Predicate precedences:" << endl;
  for(unsigned i=0;i<nPredicates;i++){
    cout << env.signature->predicateName(aux[i]) << " "; 
  }
  cout << endl;
  */
  /*
  cout << "Predicate precedence: ";
  for(unsigned i=0;i<nPredicates;i++){
    cout << aux[i] << ",";
  }
  cout << endl;
  */

  DArray<int> predicatePrecedences(nPredicates);
  for(unsigned i=0;i<nPredicates;i++) {
    predicatePrecedences[aux[i]]=i;
  }
  return predicatePrecedences;
}

DArray<int> PrecedenceOrdering::predLevelsFromOptsAndPrec(Problem& prb, const Options& opt, const DArray<int>& predicatePrecedences) {

  unsigned nPredicates = env.signature->predicates();
  DArray<int> predicateLevels(nPredicates);

  switch(opt.literalComparisonMode()) {
  case Shell::Options::LiteralComparisonMode::STANDARD:
    predicateLevels.init(nPredicates, 1);
    break;
  case Shell::Options::LiteralComparisonMode::PREDICATE:
  case Shell::Options::LiteralComparisonMode::REVERSE:
    for(unsigned i=1;i<nPredicates;i++) {
      predicateLevels[i]=predicatePrecedences[i]+1;
    }
    break;
  }
  //equality is on the lowest level
  predicateLevels[0]=0;

  if (env.predicateSineLevels) {
    // predicateSineLevels start from zero
    unsigned bound = env.maxSineLevel; // this is at least as large as the maximal value of a predicateSineLevel
    bool reverse = (opt.sineToPredLevels() == Options::PredicateSineLevels::ON); // the ON, i.e. reasonable, version wants low sine levels mapping to high predicateLevels

    for(unsigned i=1;i<nPredicates;i++) { // starting from 1, keeping predicateLevels[0]=0;
      unsigned level;
      if (!env.predicateSineLevels->find(i,level)) {
        level = bound;
      }
      predicateLevels[i] = reverse ? (bound - level + 1) : level;
      // cout << "setting predicate level of " << env.signature->predicateName(i) << " to " << predicateLevels[i] << endl;
    }
  }

  for(unsigned i=1;i<nPredicates;i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    //consequence-finding name predicates have the lowest level
    if(predSym->label()) {
      predicateLevels[i]=-1;
    }
    else if(predSym->equalityProxy()) {
      //equality proxy predicates have the highest level (lower than colored predicates)
      predicateLevels[i]=nPredicates+2;
    }

  }
  return predicateLevels;
}

void PrecedenceOrdering::show(ostream& out) const 
{
  CALL("PrecedenceOrdering::show(ostream& out)")
  {
    out << "% Function precedences, smallest symbols first (line format: `<name> <arity>`) " << std::endl;
    out << "% ===== begin of function precedences ===== " << std::endl;
    DArray<unsigned> functors;

    functors.initFromIterator(getRangeIterator(0u,env.signature->functions()),env.signature->functions());
    functors.sort(closureComparator([&](unsigned l, unsigned r){ return intoComparison(compareFunctionPrecedences(l,r)); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getFunction(i);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of function precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  {
    out << "% Predicate precedences, smallest symbols first (line format `<name> <arity>`) " << std::endl;
    out << "% ===== begin of predicate precedences ===== " << std::endl;

    DArray<unsigned> functors;
    functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
    functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(_predicatePrecedences[l], _predicatePrecedences[r]); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getPredicate(i);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of predicate precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  {
    out << "% Predicate levels (line format: `<name> <arity> <level>`)" << std::endl;
    out << "% ===== begin of predicate levels ===== " << std::endl;

    DArray<unsigned> functors;
    functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
    functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(_predicateLevels[l], _predicateLevels[r]); }));

    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getPredicate(i);
      out << "% " << sym->name() << " " << sym->arity() << " " << _predicateLevels[i] << std::endl;
    }

    out << "% ===== end of predicate precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  showConcrete(out);
}
