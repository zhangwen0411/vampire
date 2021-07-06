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
 * @file Signature.hpp
 * Defines class Signature for handling signatures
 *
 * @since 07/05/2007 Manchester, created anew instead of the old overcomplicated
 *        Signature
 */

#ifndef __Signature__
#define __Signature__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Stack.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Map.hpp"
#include "Lib/List.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/VString.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SmartPtr.hpp"

#include "Shell/InductionPreprocessor.hpp"
#include "Shell/TermAlgebra.hpp"
#include "Shell/Options.hpp"

#include "Sorts.hpp"
#include "Theory.hpp"


namespace Kernel {

using namespace std;
using namespace Lib;

/**
 * Class implementing signatures
 */
class Signature
{
 public:
  /** Function or predicate symbol */
  
  //Order is important
  //Narrow.cpp relies on it
  enum Combinator {
    S_COMB,
    B_COMB,
    C_COMB,
    I_COMB,
    K_COMB,
    NOT_COMB
  };
  
  enum Proxy {
    AND,
    OR,
    IMP,
    FORALL,
    EXISTS,
    IFF,
    XOR,
    NOT,
    PI,
    SIGMA,
    EQUALS,
    NOT_PROXY
  };  
  
  class Symbol {
  
  protected:
    /** print name */
    vstring _name;

    // both _arity and _typeArgsArity could be recovered from _type. Storing directly here as well for convenience

    /** arity */
    unsigned _arity;
    /** arity of type arguments */
    unsigned _typeArgsArity;

    /** Either a FunctionType of a PredicateType object */
    mutable OperatorType* _type;
    /** List of distinct groups the constant is a member of, all members of a distinct group should be distinct from each other */
    List<unsigned>* _distinctGroups;
    /** number of times it is used in the problem */
    unsigned _usageCount;
    /** number of units it is used in in the problem */
    unsigned _unitUsageCount;

    /** the object is of type InterpretedSymbol */
    unsigned _interpreted : 1;
    /** symbol that doesn't come from input problem, but was introduced by Vampire */
    unsigned _introduced : 1;
    /** protected symbols aren't subject to any kind of preprocessing elimination */
    unsigned _protected : 1;
    /** clauses with only skipped symbols will not be output as symbol eliminating */
    unsigned _skip : 1;
    /** marks propositional predicate symbols that are labels to 
        be used as names during consequence finding or function relationship finding */
    unsigned _label : 1;
    /** marks predicates that are equality proxy */
    unsigned _equalityProxy : 1;
    /** used in coloured proofs and interpolation */
    unsigned _color : 2;
    /** marks distinct string constants */
    unsigned _stringConstant : 1;
    /** marks numeric constants, they are only used in TPTP's fof declarations */
    unsigned _numericConstant : 1;
    /** predicate introduced for query answering */
    unsigned _answerPredicate : 1;
    /** marks numbers too large to represent natively */
    unsigned _overflownConstant : 1;
    /** marks term algebra constructors */
    unsigned _termAlgebraCons : 1;
    /** if used in the goal **/
    unsigned _inGoal : 1;
    /** if used in a unit **/
    unsigned _inUnit : 1;
    /** if induction skolem **/
    unsigned _inductionSkolem : 1;
    /** if skolem function in general **/
    unsigned _skolem : 1;
    /** if arrow constructor */
    unsigned _arrow : 1;
    /** if app function symbol */
    unsigned _app : 1;
    /** if tuple sort */
    unsigned _tuple : 1;
    /** if array sort */
    unsigned _array : 1;  
    /** if super sort */
    unsigned _superSort : 1;
    /** if Boolean sort */
    unsigned _boolSort : 1;
    /** if any non-Boolean default sort */
    unsigned _defaultSort : 1;
    /** if type constructor */
    unsigned _typeConstructor : 1;
    /** proxy type */
    Proxy _prox;
    /** combinator type */
    Combinator _comb;

  public:
    /** standard constructor */
    Symbol(const vstring& nm,unsigned arity, bool interpreted=false, bool stringConstant=false,bool numericConstant=false,bool overflownConstant=false, bool super = false);
    void destroyFnSymbol();
    void destroyPredSymbol();

    void addColor(Color color);
    /** mark symbol that doesn't come from input problem, but was introduced by Vampire */
    void markIntroduced() { _introduced=1; }
    /** remove the marking that the symbol was introduced, it has now been found in the input
        we should be careful that the previously introduced symbols are renamed elsewhere */
    void unmarkIntroduced(){ _introduced=0; }
    /** mark the symbol as protected so it is not being eliminated by preprocessing */
    void markProtected() { _protected=1; }
    /** mark the symbol as skip for the purpose of symbol elimination */
    void markSkip() { _skip=1; }
    /** mark the symbol as name for consequence finding */
    void markLabel() { ASS_EQ(arity(), 0); _label=1; markProtected(); }
    /** mark symbol to be an answer predicate */
    void markAnswerPredicate() { _answerPredicate=1; markProtected(); }
    /** mark predicate to be an equality proxy */
    void markEqualityProxy() { _equalityProxy=1; }
    /** mark constant as overflown */
    void markOverflownConstant() { _overflownConstant=1; }
    /** mark symbol as a term algebra constructor */
    void markTermAlgebraCons() { _termAlgebraCons=1; }

    /** return true iff symbol is marked as skip for the purpose of symbol elimination */
    bool skip() const { return _skip; }
    /** return true iff the symbol is marked as name predicate
        for consequence finding */
    bool label() const { return _label; }
    /** return the colour of the symbol */
    Color color() const { return static_cast<Color>(_color); }
    /** Return the arity of the symbol */
    inline unsigned arity() const { return _arity; }
    /** Return the type argument arity of the symbol. Only accurate once type has been set. */
    inline unsigned typeArgsArity() const { ASS_REP(_type, name()); return _typeArgsArity; }
    /** Return the name of the symbol */
    inline const vstring& name() const { return _name; }
    /** Return true iff the object is of type InterpretedSymbol */
    inline bool interpreted() const { return _interpreted; }
    /** Return true iff the symbol doesn't come from input problem but was introduced by Vampire */
    inline bool introduced() const { return _introduced; }
    /** Return true iff the symbol is must not be eliminated by proprocessing */
    inline bool protectedSymbol() const { return _protected; }
    /** Return true iff symbol is a distinct string constant */
    inline bool stringConstant() const { return _stringConstant; }
    /** Return true iff symbol is a numeric constant */
    inline bool numericConstant() const { return _numericConstant; }
    /** Return true iff symbol is an answer predicate */
    inline bool answerPredicate() const { return _answerPredicate; }
    /** Return true iff symbol is an equality proxy */
    inline bool equalityProxy() const { return _equalityProxy; }
    /** Return true iff symbol is an overflown constant */
    inline bool overflownConstant() const { return _overflownConstant; }
    /** Return true iff symbol is a term algebra constructor */
    inline bool termAlgebraCons() const { return _termAlgebraCons; }

    /** Increase the usage count of this symbol **/
    inline void incUsageCnt(){ _usageCount++; }
    /** Return the usage count of this symbol **/
    inline unsigned usageCnt() const { return _usageCount; }
    /** Reset usage count to zero, to start again! **/
    inline void resetUsageCnt(){ _usageCount=0; }

    inline void incUnitUsageCnt(){ _unitUsageCount++;}
    inline unsigned unitUsageCnt() const { return _unitUsageCount; }
    inline void resetUnitUsageCnt(){ _unitUsageCount=0;}

    inline void markInGoal(){ _inGoal=1; }
    inline bool inGoal(){ return _inGoal; }
    inline void markInUnit(){ _inUnit=1; }
    inline bool inUnit(){ return _inUnit; }

    inline void markSkolem(){ _skolem = 1;}
    inline bool skolem(){ return _skolem; }

    inline void markArrow(){ _arrow = 1; }
    inline bool arrow(){ return _arrow; }

    inline void markApp(){ _app = 1; }
    inline bool app(){ return _app; }

    inline void markTuple(){ _tuple = 1; }
    inline bool tupleSort(){ return _tuple; }

    inline void markArray(){ _array = 1; }
    inline bool arraySort(){ return _array; }

    inline void markBoolSort(){ _boolSort = 1; }
    inline const bool boolSort() const { return _boolSort; }

    inline void markDefaultSort(){ _defaultSort = 1; }    
    inline const bool defaultSort() const { return _defaultSort; }   

    inline void setProxy(Proxy prox){ _prox = prox; }
    inline Proxy proxy(){ return _prox; }

    inline void setComb(Combinator comb){ _comb = comb; }
    inline Combinator combinator(){ return _comb; }

    inline const bool super() const { return _superSort; }
    inline const bool typeCon() const { return _typeConstructor; } 

    inline void markInductionSkolem(){ _inductionSkolem=1; _skolem=1;}
    inline bool inductionSkolem(){ return _inductionSkolem;}
      
    /** Return true if symbol is an integer constant */
    inline bool integerConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Term::intSort(); }
    /** Return true if symbol is a rational constant */
    inline bool rationalConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Term::rationalSort(); }
    /** Return true if symbol is a real constant */
    inline bool realConstant() const
    { return interpreted() && arity()==0 && fnType()->result()==Term::realSort(); }

    /** return true if an interpreted number, note subtle but significant difference from numericConstant **/
    inline bool interpretedNumber() const
    { return integerConstant() || rationalConstant() || realConstant(); }

    /** Return value of an integer constant */
    inline IntegerConstantType integerValue() const
    { ASS(integerConstant()); return static_cast<const IntegerSymbol*>(this)->_intValue; }
    /** Return value of a rational constant */
    inline RationalConstantType rationalValue() const
    { ASS(rationalConstant()); return static_cast<const RationalSymbol*>(this)->_ratValue; }
    /** Return value of a real constant */
    inline RealConstantType realValue() const
    { ASS(realConstant()); return static_cast<const RealSymbol*>(this)->_realValue; }

    const List<unsigned>* distinctGroups() const { return _distinctGroups; }
    /** This takes the symbol number of this symbol as the symbol doesn't know it
        Note that this should only be called on a constant **/
    void addToDistinctGroup(unsigned group,unsigned this_number);
    friend ostream& operator<<(ostream& out, const Signature::Symbol& self){ return out << self.name(); };

    void setType(OperatorType* type);
    void forceType(OperatorType* type);
    OperatorType* fnType() const;
    OperatorType* predType() const;

    CLASS_NAME(Signature::Symbol);
    USE_ALLOCATOR(Symbol);
  }; // class Symbol

  class InterpretedSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    Interpretation _interp;

  public:

    InterpretedSymbol(const vstring& nm, Interpretation interp)
    : Symbol(nm, Theory::getArity(interp), true), _interp(interp)
    {
      CALL("InterpretedSymbol");
    }

    CLASS_NAME(Signature::InterpretedSymbol);
    USE_ALLOCATOR(InterpretedSymbol);

    /** Return the interpreted function that corresponds to this symbol */
    inline Interpretation getInterpretation() const { ASS_REP(interpreted(), _name); return _interp; }
  };

  class IntegerSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    IntegerConstantType _intValue;

  public:
    IntegerSymbol(const IntegerConstantType& val)
    : Symbol(val.toString(), 0, true), _intValue(val)
    {
      CALL("IntegerSymbol");

      setType(OperatorType::getConstantsType(Term::intSort()));
    }
    CLASS_NAME(Signature::IntegerSymbol);
    USE_ALLOCATOR(IntegerSymbol);
  };

  class RationalSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RationalConstantType _ratValue;

  public:
    RationalSymbol(const RationalConstantType& val)
    : Symbol(val.toString(), 0, true), _ratValue(val)
    {
      CALL("RationalSymbol");

      setType(OperatorType::getConstantsType(Term::rationalSort()));
    }
    CLASS_NAME(Signature::RationalSymbol);
    USE_ALLOCATOR(RationalSymbol);
  };

  class RealSymbol
  : public Symbol
  {
    friend class Signature;
    friend class Symbol;
  protected:
    RealConstantType _realValue;

  public:
    RealSymbol(const RealConstantType& val)
    : Symbol((env.options->proof() == Shell::Options::Proof::PROOFCHECK) ? "$to_real("+val.toString()+")" : val.toNiceString(), 0, true), _realValue(val)
    {
      CALL("RealSymbol");

      setType(OperatorType::getConstantsType(Term::realSort()));
    }
    CLASS_NAME(Signature::RealSymbol);
    USE_ALLOCATOR(RealSymbol);
  }; 

  //////////////////////////////////////
  // Uninterpreted symbol declarations
  //

  unsigned addPredicate(const vstring& name,unsigned arity,bool& added);
  unsigned addFunction(const vstring& name,unsigned arity,bool& added,bool overflowConstant = false);

  /**
   * If a predicate with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @param name name of the symbol
   * @param arity arity of the symbol
   * @since 07/05/2007 Manchester
   */
  unsigned addPredicate(const vstring& name,unsigned arity)
  {
    bool added;
    return addPredicate(name,arity,added);
  }
  /**
   * If a function with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * @since 28/12/2007 Manchester
   */
  unsigned addFunction(const vstring& name,unsigned arity)
  {
    bool added;
    return addFunction(name,arity,added);
  }
  /**
   * If a unique string constant with this name and arity exists, return its number.
   * Otherwise, add a new one and return its number.
   *
   * The added constant is of sort Sorts::SRT_DEFAULT.
   */
  unsigned addStringConstant(const vstring& name);
  unsigned addFreshFunction(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemFunction(unsigned arity,const char* suffix = 0);
  unsigned addFreshPredicate(unsigned arity, const char* prefix, const char* suffix = 0);
  unsigned addSkolemPredicate(unsigned arity,const char* suffix = 0);
  unsigned addNamePredicate(unsigned arity);
  unsigned addNameFunction(unsigned arity);
  void addEquality();
  unsigned getApp();
  unsigned getDiff();
  unsigned getChoice();

  // Interpreted symbol declarations
  unsigned addIntegerConstant(const vstring& number,bool defaultSort);
  unsigned addRationalConstant(const vstring& numerator, const vstring& denominator,bool defaultSort);
  unsigned addRealConstant(const vstring& number,bool defaultSort);

  unsigned addIntegerConstant(const IntegerConstantType& number);
  unsigned addRationalConstant(const RationalConstantType& number);
  unsigned addRealConstant(const RealConstantType& number);
 
  unsigned addInterpretedFunction(Interpretation itp, OperatorType* type, const vstring& name);
  unsigned addInterpretedFunction(Interpretation itp, const vstring& name)
  {
    CALL("Signature::addInterpretedFunction(Interpretation,const vstring&)");
    ASS(!Theory::isPolymorphic(itp));
    return addInterpretedFunction(itp,Theory::getNonpolymorphicOperatorType(itp),name);
  }

  unsigned addInterpretedPredicate(Interpretation itp, OperatorType* type, const vstring& name);
  unsigned addInterpretedPredicate(Interpretation itp, const vstring& name)
  {
    CALL("Signature::addInterpretedPredicate(Interpretation,const vstring&)");
    ASS(!Theory::isPolymorphic(itp));
    return addInterpretedPredicate(itp,Theory::getNonpolymorphicOperatorType(itp),name);
  }

  unsigned getInterpretingSymbol(Interpretation interp, OperatorType* type);
  unsigned getInterpretingSymbol(Interpretation interp)
  {
    CALL("Signature::getInterpretingSymbol(Interpretation)");
    ASS(!Theory::isPolymorphic(interp));
    return getInterpretingSymbol(interp,Theory::getNonpolymorphicOperatorType(interp));
  }

  /** Return true iff there is a symbol interpreted by Interpretation @b interp */
  bool haveInterpretingSymbol(Interpretation interp, OperatorType* type) const {
    CALL("Signature::haveInterpretingSymbol(Interpretation, OperatorType*)");
    return _iSymbols.find(std::make_pair(interp,type));
  }
  bool haveInterpretingSymbol(Interpretation interp)
  {
    CALL("Signature::haveInterpretingSymbol(Interpretation)");
    ASS(!Theory::isPolymorphic(interp));
    return haveInterpretingSymbol(interp,Theory::getNonpolymorphicOperatorType(interp));
  }

  /** return the name of a function with a given number */
  const vstring& functionName(int number);
  /** return the name of a predicate with a given number */
  const vstring& predicateName(int number)
  {
    return _preds[number]->name();
  }
  /** return the arity of a function with a given number */
  const unsigned functionArity(int number)
  {
    CALL("Signature::functionArity");
    return _funs[number]->arity();
  }
  /** return the arity of a predicate with a given number */
  const unsigned predicateArity(int number)
  {
    CALL("Signature::predicateArity");
    return _preds[number]->arity();
  }

  const bool predicateColored(int number)
  {
    return _preds[number]->color()!=COLOR_TRANSPARENT;
  }

  const bool functionColored(int number)
  {
    return _funs[number]->color()!=COLOR_TRANSPARENT;
  }

  /** return true iff predicate of given @b name and @b arity exists. */
  bool isPredicateName(vstring name, unsigned arity)
  {
    vstring symbolKey = key(name,arity);
    unsigned tmp;
    return _predNames.find(symbolKey,tmp);
  }

  void addChoiceOperator(unsigned fun){
    _choiceSymbols.insert(fun);
  }

  bool isChoiceOperator(unsigned fun){
    return _choiceSymbols.contains(fun);
  }

  DHSet<unsigned>* getChoiceOperators(){
    return &_choiceSymbols;
  }

  /** return the number of functions */
  unsigned functions() const { return _funs.length(); }
  /** return the number of predicates */
  unsigned predicates() const { return _preds.length(); }

  /** Return the function symbol by its number */
  inline Symbol* getFunction(unsigned n)
  {
    ASS_REP(n < _funs.length(),n);
    return _funs[n];
  } // getFunction
  /** Return the predicate symbol by its number */
  inline Symbol* getPredicate(unsigned n)
  {
    ASS(n < _preds.length());
    return _preds[n];
  } // getPredicate

  static inline bool isEqualityPredicate(unsigned p)
  {
    // we make sure equality is always 0
    return (p == 0); // see the ASSERT in Signature::Signature
  }

  Signature();
  ~Signature();

  CLASS_NAME(Signature);
  USE_ALLOCATOR(Signature);

  bool functionExists(const vstring& name,unsigned arity) const;
  bool predicateExists(const vstring& name,unsigned arity) const;

  bool isTypeConOrSup(unsigned fun) { 
    Symbol* sym =  getFunction(fun);
    return sym->typeCon() || sym->super(); 
  }

  bool tryGetFunctionNumber(const vstring& name, unsigned arity, unsigned& out) const;
  bool tryGetPredicateNumber(const vstring& name, unsigned arity, unsigned& out) const;
  unsigned getFunctionNumber(const vstring& name, unsigned arity) const;
  unsigned getPredicateNumber(const vstring& name, unsigned arity) const;

  typedef SmartPtr<Stack<unsigned>> DistinctGroupMembers;
  
  Unit* getDistinctGroupPremise(unsigned group);
  unsigned createDistinctGroup(Unit* premise = 0);
  void addToDistinctGroup(unsigned constantSymbol, unsigned groupId);
  bool hasDistinctGroups(){ return _distinctGroupsAddedTo; }
  void noDistinctGroupsLeft(){ _distinctGroupsAddedTo=false; }
  Stack<DistinctGroupMembers> &distinctGroupMembers(){ return _distinctGroupMembers; }

  bool hasTermAlgebras() { return !_termAlgebras.isEmpty(); }
      
  static vstring key(const vstring& name,int arity);

  /** the number of string constants */
  unsigned strings() const {return _strings;}
  /** the number of integer constants */
  unsigned integers() const {return _integers;}
  /** the number of rational constants */
  unsigned rationals() const {return _rationals;}
  /** the number of real constants */
  unsigned reals() const {return _reals;}

  static const unsigned STRING_DISTINCT_GROUP;

  unsigned getFoolConstantSymbol(bool isTrue){ 
    if(!_foolConstantsDefined){
      _foolFalse = addFunction("$$false",0); 
      getFunction(_foolFalse)->setType(OperatorType::getConstantsType(Term::boolSort()));
      _foolTrue = addFunction("$$true",0);
      getFunction(_foolTrue)->setType(OperatorType::getConstantsType(Term::boolSort()));
      _foolConstantsDefined=true;
    }
    return isTrue ? _foolTrue : _foolFalse;
  }
  bool isFoolConstantSymbol(bool isTrue, unsigned number){
    if(!_foolConstantsDefined) return false;
    return isTrue ? number==_foolTrue : number==_foolFalse;
  }

  unsigned getDefaultSort(){
    CALL("Signature::getDefaultSort");

    bool added = false;
    unsigned individualSort = addFunction("$i",0, added);
    if(added){
      getFunction(individualSort)->setType(OperatorType::getConstantsType(Term::superSort()));
      getFunction(individualSort)->markDefaultSort();    
    }
    return individualSort;
  }

  unsigned getBoolSort(){
    CALL("Signature::getBoolSort");

    bool added = false;
    unsigned boolSort = addFunction("$o",0, added);
    if(added){
      getFunction(boolSort)->setType(OperatorType::getConstantsType(Term::superSort()));
      getFunction(boolSort)->markBoolSort();
    }
    return boolSort;
  }

  unsigned getRealSort(){
    bool added = false;
    unsigned realSort = addFunction("$real",0, added);
    if(added){
      getFunction(realSort)->setType(OperatorType::getConstantsType(Term::superSort()));
      getFunction(realSort)->markDefaultSort();
    }
    return realSort;
  }

  unsigned getIntSort(){
    bool added = false;
    unsigned intSort = addFunction("$int",0, added);
    if(added){
      getFunction(intSort)->setType(OperatorType::getConstantsType(Term::superSort()));
      getFunction(intSort)->markDefaultSort();
    }
    return intSort;
  }  

  unsigned getRatSort(){
    bool added = false;
    unsigned ratSort = addFunction("$rat",0, added);
    if(added){
      getFunction(ratSort)->setType(OperatorType::getConstantsType(Term::superSort()));
      getFunction(ratSort)->markDefaultSort();    
    }
    return ratSort;    
  }

  unsigned getArrowConstructor(){
    bool added = false;
    unsigned arrow = addFunction(">",2, added);
    if(added){
      TermList ss = Term::superSort();
      Symbol* arr = getFunction(arrow);
      arr->setType(OperatorType::getFunctionType({ss, ss}, ss));
      arr->markArrow();
    }
    return arrow;    
  }

  unsigned getArrayConstructor(){
    bool added = false;
    unsigned array = addFunction("Array",2, added);
    if(added){
      TermList ss = Term::superSort();
      Symbol* arr = getFunction(array);
      arr->setType(OperatorType::getFunctionType({ss, ss}, ss));
      arr->markArray();
    }
    return array;    
  }

  unsigned getTupleConstructor(unsigned arity){
    bool added = false;
    //TODO make the name unique
    unsigned tuple = addFunction("Tuple", arity, added);
    if(added){
      TermList ss = Term::superSort();
      Symbol* tup = getFunction(tuple);
      tup->setType(OperatorType::getFunctionTypeUniformRange(arity, ss, ss));
      tup->markTuple();
    }
    return tuple;    
  }  

  unsigned getEqualityProxy(){
    bool added = false;
    unsigned eqProxy = addFunction("vEQ",1, added);
    if(added){
      TermList tv = TermList(0, false);
      TermList result = Term::arrowSort(tv, tv, Term::boolSort());
      Symbol * sym = getFunction(eqProxy);
      sym->setType(OperatorType::getConstantsType(result, 1));
      sym->setProxy(EQUALS);
    }
    return eqProxy;  
  }

  unsigned getBinaryProxy(vstring name){
    ASS(name == "vIMP" || name == "vAND" || name == "vOR" || name == "vIFF" || name == "vXOR");
    bool added = false;
    
    auto convert = [] (vstring name) { 
      if(name == "vIMP"){ return IMP; }
      else if(name == "vAND"){ return AND; }
      else if(name == "vOR"){ return OR; }
      else if(name == "vIFF"){ return IFF; }
      else{ return XOR; }
    };

    unsigned proxy = addFunction(name,0, added);
    if(added){
      TermList bs = Term::boolSort();
      TermList result = Term::arrowSort(bs, bs, bs);
      Symbol * sym = getFunction(proxy);
      sym->setType(OperatorType::getConstantsType(result));
      sym->setProxy(convert(name));
    }
    return proxy;  
  }

  unsigned getNotProxy(){
    bool added = false;
    unsigned notProxy = addFunction("vNOT",0, added);
    if(added){
      TermList bs = Term::boolSort();
      TermList result = Term::arrowSort(bs, bs);
      Symbol * sym = getFunction(notProxy);
      sym->setType(OperatorType::getConstantsType(result));
      sym->setProxy(NOT);
    }
    return notProxy;  
  } //TODO merge with above?


  unsigned getPiSigmaProxy(vstring name){
    bool added = false;
    unsigned proxy = addFunction(name,1, added);
    if(added){
      TermList tv = TermList(0, false);
      TermList result = Term::arrowSort(tv, Term::boolSort());
      result = Term::arrowSort(result, Term::boolSort());
      Symbol * sym = getFunction(proxy);
      sym->setType(OperatorType::getConstantsType(result, 1));
      sym->setProxy(name == "vPI" ? PI : SIGMA);
    }
    return proxy;  
  } //TODO merge with above?  

  //TODO make all these names protected

  unsigned getCombinator(Combinator c){
    bool added = false;
    unsigned comb;
    
    auto convert = [] (Combinator cb) { 
      switch(cb){
        case S_COMB:
          return "sCOMB";
        case C_COMB:
          return "cCOMB";
        case B_COMB:
          return "bCOMB";
        case K_COMB:
          return "kCOMB";
        default:
          return "iCOMB";
      }
    };
    
    vstring name = convert(c);
    if(c == S_COMB || c == B_COMB || c == C_COMB){
      comb = addFunction(name,3, added);
    } else if ( c == K_COMB) {
      comb = addFunction(name,2, added);      
    } else {
      comb = addFunction(name,1, added);
    }
    
    unsigned typeArgsArity = 3;
    TermList x0 = TermList(0, false);
    TermList x1 = TermList(1, false);
    TermList x2 = TermList(2, false);
    TermList t0 = Term::arrowSort(x1, x2);
    TermList t1 = Term::arrowSort(x0, t0);
    TermList t2 = Term::arrowSort(x0, x1);
    TermList t3 = Term::arrowSort(x0, x2);

    if(added){
      TermList sort; 
      if(c == S_COMB){
        sort = Term::arrowSort(t1, t2, t3);
      }else if(c == C_COMB){
        sort = Term::arrowSort(t1, x1, t3);
      }else if(c == B_COMB){
        sort = Term::arrowSort(t0, t2, t3);
      }else if(c == K_COMB){
        typeArgsArity = 2;
        sort = Term::arrowSort(x0, x1 , x0);
      }else if(c == I_COMB){
        typeArgsArity = 1;
        sort = Term::arrowSort(x0, x0);
      }    

      Symbol* sym = getFunction(comb);
      sym->setType(OperatorType::getConstantsType(sort, typeArgsArity));
      sym->setComb(c);
    } 
    return comb;
  }

  void incrementFormulaCount(Term* t);
  void decrementFormulaCount(Term* t);
  void formulaNamed(Term* t);
  unsigned formulaCount(Term* t);


  bool isTermAlgebraSort(TermList sort) { return _termAlgebras.find(sort); }
  Shell::TermAlgebra *getTermAlgebraOfSort(TermList sort) { return _termAlgebras.get(sort); }
  void addTermAlgebra(Shell::TermAlgebra *ta) { _termAlgebras.insert(ta->sort(), ta); }
  VirtualIterator<Shell::TermAlgebra*> termAlgebrasIterator() const { return _termAlgebras.range(); }
  Shell::TermAlgebraConstructor* getTermAlgebraConstructor(unsigned functor);

  Shell::FnDefHandler* getFnDefHandler() {
    if (!_fnDefHandler) {
      _fnDefHandler = new Shell::FnDefHandler();
    }
    return _fnDefHandler;
  }

  void recordDividesNvalue(TermList n){
    _dividesNvalues.push(n);
  }
  Stack<TermList>& getDividesNvalues(){ return _dividesNvalues; }

  static bool symbolNeedsQuoting(vstring name, bool interpreted, unsigned arity);

private:
  Stack<TermList> _dividesNvalues;
  DHMap<Term*, int> _formulaCounts;

  bool _foolConstantsDefined;
  unsigned _foolTrue;
  unsigned _foolFalse;

  static bool isProtectedName(vstring name);
  static bool charNeedsQuoting(char c, bool first);
  /** Stack of function symbols */
  Stack<Symbol*> _funs;
  /** Stack of predicate symbols */
  Stack<Symbol*> _preds;

  DHSet<unsigned> _choiceSymbols;
  /**
   * Map from vstring "name_arity" to their numbers
   *
   * String constants have key "value_c", integer constants "value_n",
   * rational "numerator_denominator_q" and real "value_r".
   */
  SymbolMap _funNames;
  /** Map from vstring "name_arity" to their numbers */
  SymbolMap _predNames;
  /** Map for the arity_check options: maps symbols to their arities */
  SymbolMap _arityCheck;
  /** Last number used for fresh functions and predicates */
  int _nextFreshSymbolNumber;

  /** Number of Skolem functions (this is just for LaTeX output) */
  unsigned _skolemFunctionCount;

  /** Map from symbol names to variable numbers*/
  SymbolMap _varNames;
  
  // Store the premise of a distinct group for proof printing, if 0 then group is input
  Stack<Unit*> _distinctGroupPremises;

  // We only store members up until a hard-coded limit i.e. the limit at which we will expand the group
  Stack<DistinctGroupMembers> _distinctGroupMembers;
  // Flag to indicate if any distinct groups have members
  bool _distinctGroupsAddedTo;

  /**
   * Map from MonomorphisedInterpretation values to function and predicate symbols representing them
   *
   * We mix here function and predicate symbols, but it is not a problem, as
   * the MonomorphisedInterpretation value already determines whether we deal with a function
   * or a predicate.
   */
  DHMap<Theory::MonomorphisedInterpretation, unsigned> _iSymbols;

  /** the number of string constants */
  unsigned _strings;
  /** the number of integer constants */
  unsigned _integers;
  /** the number of rational constants */
  unsigned _rationals;
  /** the number of real constants */
  unsigned _reals;

  /**
   * Map from sorts to the associated term algebra, if applicable for the sort
   */ 
  DHMap<TermList, Shell::TermAlgebra*> _termAlgebras;

  Shell::FnDefHandler* _fnDefHandler;

  //TODO Why are these here? They are not used anywhere. AYB
  //void defineOptionTermAlgebra(unsigned optionSort);
  //void defineEitherTermAlgebra(unsigned eitherSort);
}; // class Signature

}

#endif // __Signature__
