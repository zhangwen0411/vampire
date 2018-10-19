
/*
 * File Signature.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Signature.cpp
 * Implements class Signature for handling signatures
 */

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Shell/Options.hpp"
#include "Shell/DistinctGroupExpansion.hpp"

#include "Signature.hpp"

using namespace std;
using namespace Kernel;
using namespace Shell;

const unsigned Signature::STRING_DISTINCT_GROUP = 0;

/**
 * Standard constructor.
 * @since 03/05/2013 train London-Manchester, argument numericConstant added
 * @author Andrei Voronkov
 */
Signature::Symbol::Symbol(const vstring& nm,unsigned arity, bool interpreted, bool stringConstant,bool numericConstant, bool overflownConstant)
  : _name(nm),
    _arity(arity),
    _interpreted(interpreted ? 1 : 0),
    _introduced(0),
    _protected(0),
    _skip(0),
    _label(0),
    _equalityProxy(0),
    _color(COLOR_TRANSPARENT),
    _stringConstant(stringConstant ? 1: 0),
    _numericConstant(numericConstant ? 1: 0),
    _answerPredicate(0),
    _overflownConstant(overflownConstant ? 1 : 0),
    _termAlgebraCons(0),
    _type(0),
    _distinctGroups(0),
    _usageCount(0),
	  _isAPP(0),
    _isPlaceHolder(0),
    _dummyArg(0),
	  _HOLconst(NULL_CONSTANT)
{
  CALL("Signature::Symbol::Symbol");
  ASS(!stringConstant || arity==0);

  if (!stringConstant && !numericConstant && !overflownConstant && symbolNeedsQuoting(_name, interpreted,arity)) {
    _name="'"+_name+"'";
  }
  if (_interpreted || isProtectedName(nm)) {
    markProtected();
  }
} // Symbol::Symbol

/**
 * Deallocate function Symbol object
 */
void Signature::Symbol::destroyFnSymbol()
{
  CALL("Signature::Symbol::destroyFnSymbol");

  if (integerConstant()) {
    delete static_cast<IntegerSymbol*>(this);
  }
  else if (rationalConstant()) {
    delete static_cast<RationalSymbol*>(this);
  }
  else if (realConstant()) {
    delete static_cast<RealSymbol*>(this);
  }
  else if (interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
  }
  else {
    delete this;
  }
}

/**
 * Deallocate predicate Symbol object
 */
void Signature::Symbol::destroyPredSymbol()
{
  CALL("Signature::Symbol::destroyPredSymbol");

  if (interpreted()) {
    delete static_cast<InterpretedSymbol*>(this);
  }
  else {
    delete this;
  }
}

/**
 * Add constant symbol into a distinct group
 *
 * A constant can be added into one particular distinct group
 * at most once
 *
 * We also record the symbol in the group's members, under certain conditions
 */
void Signature::Symbol::addToDistinctGroup(unsigned group,unsigned this_number)
{
  CALL("Signature::Symbol::addToDistinctGroup");

  ASS_EQ(arity(), 0);
  ASS(!List<unsigned>::member(group, _distinctGroups))

  List<unsigned>::push(group, _distinctGroups);

  env.signature->_distinctGroupsAddedTo=true;

  Stack<unsigned>* members = env.signature->_distinctGroupMembers[group];
  if(members->size() <= DistinctGroupExpansion::EXPAND_UP_TO_SIZE || env.options->bfnt()
                       || env.options->saturationAlgorithm()==Options::SaturationAlgorithm::FINITE_MODEL_BUILDING){
    // we add one more than EXPAND_UP_TO_SIZE to signal to DistinctGroupExpansion::apply not to expand
    // ... instead DistinctEqualitySimplifier will take over
    members->push(this_number);
  }

} // addToDistinctGroup

/**
 * Set type of the symbol
 *
 * The type can be set only once for each symbol, and if the type
 * should be different from the default type, this function must be
 * called before any call to @c fnType() or @c predType().
 */
void Signature::Symbol::setType(OperatorType* type)
{
  CALL("Signature::Symbol::setType");
  ASS(!_type);

  _type = type;
}

/**
 * This force the type to change
 * This can be unsafe so should only be used when you know it is safe to
 * change the type i.e. nothing yet relies on the type of this symbol
 */
void Signature::Symbol::forceType(OperatorType* type)
{
  CALL("Signature::Symbol::forceType");
  if(_type){ delete _type; }
  _type = type;
}


/**
 * Return the type of a function symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
OperatorType* Signature::Symbol::fnType() const
{
  CALL("Signature::Symbol::fnType");

  if (!_type) {
    _type = OperatorType::getFunctionType(arity(), (unsigned*)0, Sorts::SRT_DEFAULT);
  }
  return _type;
}

/**
 * Return the type of a predicate symbol
 *
 * If the @c setType() function was not called before, the function
 * symbol is assigned a default type.
 */
OperatorType* Signature::Symbol::predType() const
{
  CALL("Signature::Symbol::predType");

  if (!_type) {
    _type = OperatorType::getPredicateType(arity(), (unsigned*)0);
  }
  return _type;
}


/**
 * Create a Signature.
 * @since 07/05/2007 Manchester
 * @since 04/05/2015 Gothenburg -- add true and false
 */
Signature::Signature ():
    _foolConstantsDefined(false), _foolTrue(0), _foolFalse(0),
    _funs(32),
    _preds(32),
    _nextFreshSymbolNumber(0),
    _skolemFunctionCount(0),
    _distinctGroupsAddedTo(false),
    _strings(0),
    _integers(0),
    _rationals(0),
    _reals(0),
    _termAlgebras()
{
  CALL("Signature::Signature");

  // initialize equality
  addInterpretedPredicate(Theory::EQUAL, OperatorType::getPredicateType(2), "=");
  ASS_EQ(predicateName(0), "="); //equality must have number 0
  getPredicate(0)->markSkip();

  unsigned aux;
  aux = createDistinctGroup();
  ASS_EQ(STRING_DISTINCT_GROUP, aux);
} // Signature::Signature

/**
 * Destroy a Signature.
 * @since 07/05/2007 Manchester
 */
Signature::~Signature ()
{
  for (int i = _funs.length()-1;i >= 0;i--) {
    _funs[i]->destroyFnSymbol();
  }
  for (int i = _preds.length()-1;i >= 0;i--) {
    _preds[i]->destroyPredSymbol();
  }
} // Signature::~Signature

/**
 * Add an integer constant to the signature. If defaultSort is true, treat it as
 * a term of the default sort, otherwise as an interepreted integer value.
 * @since 03/05/2013 train Manchester-London
 * @author Andrei Voronkov
 */
unsigned Signature::addIntegerConstant(const vstring& number,bool defaultSort)
{
  CALL("Signature::addIntegerConstant(vstring)");

  IntegerConstantType value(number);
  if (!defaultSort) {
    return addIntegerConstant(value);
  }

  // default sort should be used
  vstring name = value.toString();
  vstring symbolKey = name + "_n";
  unsigned result;
  if (_funNames.find(symbolKey,result)) {
    return result;
  }

  result = _funs.length();
  Symbol* sym = new Symbol(name,0,false,false,true);
  /*
  sym->addToDistinctGroup(INTEGER_DISTINCT_GROUP,result);
  if(defaultSort){ 
     sym->addToDistinctGroup(STRING_DISTINCT_GROUP,result); // numbers are disctinct from strings
  }
  */
  _funs.push(sym);
  _funNames.insert(symbolKey,result);
  return result;
} // Signature::addIntegerConstant

/**
 * Add an integer constant to the signature.
 * @todo something smarter, so that we don't need to convert all values to string
 */
unsigned Signature::addIntegerConstant(const IntegerConstantType& value)
{
  CALL("Signature::addIntegerConstant");

  vstring key = value.toString() + "_n";
  unsigned result;
  if (_funNames.find(key, result)) {
    return result;
  }
  _integers++;
  result = _funs.length();
  Symbol* sym = new IntegerSymbol(value);
  _funs.push(sym);
  _funNames.insert(key,result);
  /*
  sym->addToDistinctGroup(INTEGER_DISTINCT_GROUP,result);
  */
  return result;
} // addIntegerConstant

/**
 * Add a rational constant to the signature. If defaultSort is true, treat it as
 * a term of the default sort, otherwise as an interepreted rational value.
 * @since 03/05/2013 London
 * @author Andrei Voronkov
 */
unsigned Signature::addRationalConstant(const vstring& numerator, const vstring& denominator,bool defaultSort)
{
  CALL("Signature::addRationalConstant(vstring,vstring)");

  RationalConstantType value(numerator, denominator);
  if (!defaultSort) {
    return addRationalConstant(value);
  }

  vstring name = value.toString();
  vstring key = name + "_q";
  unsigned result;
  if (_funNames.find(key,result)) {
    return result;
  }
  result = _funs.length();
  Symbol* sym = new Symbol(name,0,false,false,true);
  /*
  if(defaultSort){ 
    sym->addToDistinctGroup(STRING_DISTINCT_GROUP,result); // numbers are distinct from strings
  }
  sym->addToDistinctGroup(RATIONAL_DISTINCT_GROUP,result);
  */
  _funs.push(sym);
  _funNames.insert(key,result);
  return result;
} // addRatonalConstant

unsigned Signature::addRationalConstant(const RationalConstantType& value)
{
  CALL("Signature::addRationalConstant");

  vstring key = value.toString() + "_q";
  unsigned result;
  if (_funNames.find(key, result)) {
    return result;
  }
  _rationals++;
  result = _funs.length();
  _funs.push(new RationalSymbol(value));
  _funNames.insert(key, result);
  return result;
} // Signature::addRationalConstant

/**
 * Add a real constant to the signature. If defaultSort is true, treat it as
 * a term of the default sort, otherwise as an interepreted real value.
 * @since 03/05/2013 London
 * @author Andrei Voronkov
 */
unsigned Signature::addRealConstant(const vstring& number,bool defaultSort)
{
  CALL("Signature::addRealConstant(vstring)");

  RealConstantType value(number);
  if (!defaultSort) {
    return addRealConstant(value);
  }
  vstring key = value.toString() + "_r";
  unsigned result;
  if (_funNames.find(key,result)) {
    return result;
  }
  result = _funs.length();
  Symbol* sym = new Symbol(value.toNiceString(),0,false,false,true);
  /*
  if(defaultSort){ 
    sym->addToDistinctGroup(STRING_DISTINCT_GROUP,result); // numbers are distinct from strings
  }
  sym->addToDistinctGroup(REAL_DISTINCT_GROUP,result);
  */
  _funs.push(sym);
  _funNames.insert(key,result);
  return result;
} // addRealConstant

unsigned Signature::addRealConstant(const RealConstantType& value)
{
  CALL("Signature::addRealConstant");

  vstring key = value.toString() + "_r";
  unsigned result;
  if (_funNames.find(key, result)) {
    return result;
  }
  _reals++;
  result = _funs.length();
  _funs.push(new RealSymbol(value));
  _funNames.insert(key, result);
  return result;
}

/**
 * Add interpreted function
 */
unsigned Signature::addInterpretedFunction(Interpretation interpretation, OperatorType* type, const vstring& name)
{
  CALL("Signature::addInterpretedFunction(Interpretation,OperatorType*,const vstring&)");
  ASS(Theory::isFunction(interpretation));

  Theory::MonomorphisedInterpretation mi = std::make_pair(interpretation,type);

  unsigned res;
  if (_iSymbols.find(mi,res)) { // already declared
    if (name!=functionName(res)) {
      USER_ERROR("Interpreted function '"+functionName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  vstring symbolKey = name+"_i"+Int::toString(interpretation)+(Theory::isPolymorphic(interpretation) ? type->toString() : "");
  ASS(!_funNames.find(symbolKey));

  unsigned fnNum = _funs.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _funs.push(sym);
  _funNames.insert(symbolKey, fnNum);
  ALWAYS(_iSymbols.insert(mi, fnNum));

  OperatorType* fnType = type;
  ASS(fnType->isFunctionType());
  sym->setType(fnType);
  return fnNum;
} // Signature::addInterpretedFunction

/**
 * Add interpreted predicate
 */
unsigned Signature::addInterpretedPredicate(Interpretation interpretation, OperatorType* type, const vstring& name)
{
  CALL("Signature::addInterpretedPredicate(Interpretation,OperatorType*,const vstring&)");
  ASS(!Theory::isFunction(interpretation));

  // cout << "addInterpretedPredicate " << (type ? type->toString() : "nullptr") << " " << name << endl;

  Theory::MonomorphisedInterpretation mi = std::make_pair(interpretation,type);

  unsigned res;
  if (_iSymbols.find(mi,res)) { // already declared
    if (name!=predicateName(res)) {
      USER_ERROR("Interpreted predicate '"+predicateName(res)+"' has the same interpretation as '"+name+"' should have");
    }
    return res;
  }

  vstring symbolKey = name+"_i"+Int::toString(interpretation)+(Theory::isPolymorphic(interpretation) ? type->toString() : "");

  // cout << "symbolKey " << symbolKey << endl;

  ASS(!_predNames.find(symbolKey));

  unsigned predNum = _preds.length();
  InterpretedSymbol* sym = new InterpretedSymbol(name, interpretation);
  _preds.push(sym);
  _predNames.insert(symbolKey,predNum);
  ALWAYS(_iSymbols.insert(mi, predNum));
  if (predNum!=0) {
    OperatorType* predType = type;
    ASS_REP(!predType->isFunctionType(), predType->toString());
    sym->setType(predType);
  }
  return predNum;
} // Signature::addInterpretedPredicate


/**
 * Return number of symbol that is interpreted by Interpretation @b interp.
 *
 * If no such symbol exists, it is created.
 */
unsigned Signature::getInterpretingSymbol(Interpretation interp, OperatorType* type)
{
  CALL("Signature::getInterpretingSymbol(Interpretation,OperatorType*)");
  
  Theory::MonomorphisedInterpretation mi = std::make_pair(interp,type);

  unsigned res;
  if (_iSymbols.find(mi, res)) {
    return res;
  }

  vstring name = theory->getInterpretationName(interp);
  unsigned arity = Theory::getArity(interp);
  
  if (Theory::isFunction(interp)) {
    if (functionExists(name, arity)) {
      int i=0;
      while(functionExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedFunction(interp, type, name);
  }
  else {
    if (predicateExists(name, arity)) {
      int i=0;
      while(predicateExists(name+Int::toString(i), arity)) {
        i++;
      }
      name=name+Int::toString(i);
    }
    addInterpretedPredicate(interp, type, name);
  }

  //we have now registered a new function, so it should be present in the map
  return _iSymbols.get(mi);
}

const vstring& Signature::functionName(int number)
{
  CALL("Signature::functionName");

  // it is safe to reuse "$true" and "$false" for constants
  // because the user cannot define constants with these names herself
  // and the formula, obtained by toString() with "$true" or "$false"
  // in term position would be syntactically valid in FOOL
  if (!env.options->showFOOL() && isFoolConstantSymbol(false,number)) {
    static vstring fols("$false");
    return fols;
  }
  if (!env.options->showFOOL() && isFoolConstantSymbol(true,number)) { 
    static vstring troo("$true");
    return troo;
  }
  return _funs[number]->name();
}

/**
 * Return true if specified function exists
 */
bool Signature::functionExists(const vstring& name,unsigned arity) const
{
  CALL("Signature::functionExists");

  return _funNames.find(key(name, arity));
}

/**
 * Return true if specified predicate exists
 */
bool Signature::predicateExists(const vstring& name,unsigned arity) const
{
  CALL("Signature::predicateExists");

  return _predNames.find(key(name, arity));
}

unsigned Signature::getFunctionNumber(const vstring& name, unsigned arity) const
{
  CALL("Signature::getFunctionNumber");

  ASS(_funNames.find(key(name, arity)));
  return _funNames.get(key(name, arity));
}

unsigned Signature::getPredicateNumber(const vstring& name, unsigned arity) const
{
  CALL("Signature::getPredicateNumber");

  ASS(_predNames.find(key(name, arity)));
  return _predNames.get(key(name, arity));
}

/**
 * If a function with this name and arity exists, return its number.
 * Otherwise, add a new one and return its number.
 *
 * @param name name of the symbol
 * @param arity arity of the symbol
 * @param added will be set to true if the function did not exist
 * @since 07/05/2007 Manchester
 */
unsigned Signature::addFunction (const vstring& name,
				 unsigned arity,
				 bool& added,
				 bool overflowConstant)
{
  CALL("Signature::addFunction");

  vstring symbolKey = key(name,arity);
  unsigned result;
  if (_funNames.find(symbolKey,result)) {
    added = false;
    getFunction(result)->unmarkIntroduced();
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((vstring)"Symbol " + name +
		 " is used both as a function of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity+1);
  }

  result = _funs.length();
  _funs.push(new Symbol(name, arity, false, false, false, overflowConstant));
  _funNames.insert(symbolKey, result);
  added = true;
  return result;
} // Signature::addFunction

/**
 * Add a string constant to the signature. This constant will automatically be
 * added to the distinct group STRING_DISTINCT_GROUP.
 * @author Andrei Voronkov
 */
unsigned Signature::addStringConstant(const vstring& name)
{
  CALL("Signature::addStringConstant");

  vstring symbolKey = name + "_c";
  unsigned result;
  if (_funNames.find(symbolKey,result)) {
    return result;
  }

  _strings++;
  vstring quotedName = "\"" + name + "\"";
  result = _funs.length();
  Symbol* sym = new Symbol(quotedName,0,false,true);
  sym->addToDistinctGroup(STRING_DISTINCT_GROUP,result);
  _funs.push(sym);
  _funNames.insert(symbolKey,result);
  return result;
} // addStringConstant

/**
 * If a predicate with this name and arity exists, return its number.
 * Otherwise, add a new one and return its number.
 *
 * @param name name of the symbol
 * @param arity arity of the symbol
 * @param added set to true if a new predicate has been added, and false
 *        otherwise
 * @since 07/05/2007 Manchester
 * @since 08/07/2007 Manchester, adds parameter added
 * @since 06/12/2009 Haifa, arity check added
 * @author Andrei Voronkov
 */
unsigned Signature::addPredicate (const vstring& name,
				  unsigned arity,
				  bool& added)
{
  CALL("Signature::addPredicate");

  vstring symbolKey = key(name,arity);
  unsigned result;
  if (_predNames.find(symbolKey,result)) {
    added = false;
    getPredicate(result)->unmarkIntroduced();
    return result;
  }
  if (env.options->arityCheck()) {
    unsigned prev;
    if (_arityCheck.find(name,prev)) {
      unsigned prevArity = prev/2;
      bool isFun = prev % 2;
      USER_ERROR((vstring)"Symbol " + name +
		 " is used both as a predicate of arity " + Int::toString(arity) +
		 " and a " + (isFun ? "function" : "predicate") +
		 " of arity " + Int::toString(prevArity));
    }
    _arityCheck.insert(name,2*arity);
  }

  result = _preds.length();
  _preds.push(new Symbol(name,arity));
  _predNames.insert(symbolKey,result);
  added = true;
  return result;
} // Signature::addPredicate

/**
 * Create a new name.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addNamePredicate(unsigned arity)
{
  CALL("Signature::addNamePredicate");
  return addFreshPredicate(arity,"sP");
} // addNamePredicate


/**
 * Create a new name.
 * @since 19/10/2018 Manchester
 */
unsigned Signature::addNameFunction(unsigned arity)
{
  CALL("Signature::addNameFunction");
  return addFreshFunction(arity,"sP");
} // addNameFunction

/**
 * Add fresh function of a given arity and with a given prefix. If suffix is non-zero,
 * the function name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new function will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshFunction(unsigned arity, const char* prefix, const char* suffix)
{
  CALL("Signature::addFreshFunction");

  vstring pref(prefix);
  vstring suf(suffix ? vstring("_")+suffix : "");
  bool added;
  unsigned result;
  //commented out because it could lead to introduction of function with the same name
  //that differ only in arity (which is OK with tptp, but iProver was complaining when
  //using Vampire as clausifier)
//  unsigned result = addFunction(pref+suf,arity,added);
//  if (!added) {
    do {
      result = addFunction(pref+Int::toString(_nextFreshSymbolNumber++)+suf,arity,added);
    }
    while (!added);
//  }
  Symbol* sym = getFunction(result);
  sym->markIntroduced();
  sym->markSkip();
  return result;
} // addFreshFunction

/**
 * Add fresh predicate of a given arity and with a given prefix. If suffix is non-zero,
 * the predicate name will be prefixI, where I is an integer, otherwise it will be
 * prefixI_suffix. The new predicate will be marked as skip for the purpose of equality
 * elimination.
 */
unsigned Signature::addFreshPredicate(unsigned arity, const char* prefix, const char* suffix)
{
  CALL("Signature::addFreshPredicate");

  vstring pref(prefix);
  vstring suf(suffix ? vstring("_")+suffix : "");
  bool added = false;
  unsigned result;
  //commented out because it could lead to introduction of function with the same name
  //that differ only in arity (which is OK with tptp, but iProver was complaining when
  //using Vampire as clausifier)
//  if (suffix) {
//    result = addPredicate(pref+suf,arity,added);
//  }
//  if (!added) {
    do {
      result = addPredicate(pref+Int::toString(_nextFreshSymbolNumber++)+suf,arity,added);
    }
    while (!added);
//  }
  Symbol* sym = getPredicate(result);
  sym->markIntroduced();
  sym->markSkip();
  return result;
} // addFreshPredicate

/**
 * Return a new Skolem function. If @b suffix is nonzero, include it
 * into the name of the Skolem function.
 * @since 01/07/2005 Manchester
 */
unsigned Signature::addSkolemFunction (unsigned arity, const char* suffix)
{
  CALL("Signature::addSkolemFunction");

  unsigned f = addFreshFunction(arity, "sK", suffix);

  // Register it as a LaTeX function
  theory->registerLaTeXFuncName(f,"\\sigma_{"+Int::toString(_skolemFunctionCount)+"}(a0)");
  _skolemFunctionCount++;

  return f;
} // addSkolemFunction

/**
 * Return a new Skolem predicate. If @b suffix is nonzero, include it
 * into the name of the Skolem function.
 * @since 15/02/2016 Gothenburg
 */
unsigned Signature::addSkolemPredicate(unsigned arity, const char* suffix)
{
  CALL("Signature::addSkolemPredicate");

  unsigned f = addFreshPredicate(arity, "sK", suffix);

  // Register it as a LaTeX function
  theory->registerLaTeXFuncName(f,"\\sigma_{"+Int::toString(_skolemFunctionCount)+"}(a0)");
  _skolemFunctionCount++;

  return f;
} // addSkolemPredicate

/**
 * Return the key "name_arity" used for hashing. This key is obtained by
 * concatenating the name, underscore character and the arity. The key is
 * created in such a way that it does not collide with special keys, such as
 * those for string constants.
 * @since 27/02/2006 Redmond
 * @author Andrei Voronkov
 */
vstring Signature::key(const vstring& name,int arity)
{
  return name + '_' + Int::toString(arity);
} // Signature::key


/** Add a color to the symbol for interpolation and symbol elimination purposes */
void Signature::Symbol::addColor(Color color)
{
  ASS_L(color,3);
  ASS_G(color,0);
  ASS(env.colorUsed);

  if (_color && color != static_cast<Color>(_color)) {
    USER_ERROR("A symbol cannot have two colors");
  }
  _color = color;
} // addColor

/**
 * Create a group of distinct elements. @c premise should contain
 * the unit that declared the distinct group, or zero if there isn't any.
 */
unsigned Signature::createDistinctGroup(Unit* premise)
{
  CALL("Signature::createDistinctGroup");

  unsigned res = _distinctGroupPremises.size();
  _distinctGroupPremises.push(premise);
  Stack<unsigned>* stack = new Stack<unsigned>;
  _distinctGroupMembers.push(stack);
  return res;
}

/**
 * Return premise of the distinct group, or 0 if the distinct group doesn't have any
 */
Unit* Signature::getDistinctGroupPremise(unsigned group)
{
  CALL("Signature::getDistinctGroupPremise");

  return _distinctGroupPremises[group];
}

/**
 * Add a constant into a group of distinct elements
 *
 * One constant can be added into one particular distinct group only once.
 */
void Signature::addToDistinctGroup(unsigned constantSymbol, unsigned groupId)
{
  CALL("Signature::addToDistinctGroup");

  Symbol* sym = getFunction(constantSymbol);
  sym->addToDistinctGroup(groupId,constantSymbol);
}

bool Signature::isProtectedName(vstring name)
{
  CALL("Signature::isProtectedName");

  if (name=="$distinct") {
    //TODO: remove this hack once we properly support the $distinct predicate
    return true;
  }

  vstring protectedPrefix = env.options->protectedPrefix();
  if (protectedPrefix.size()==0) {
    return false;
  }
  if (name.substr(0, protectedPrefix.size())==protectedPrefix) {
    return true;
  }
  return false;
}

/**
 * Return true if specified symbol should be quoted in the TPTP syntax.
 * This function does not apply to integer or string constants. It only
 * applies during parsing, it is not used when the symbol is printed:
 * when it is printed, its saved name will already be quoted.
 *
 * The function charNeedsQuoting determines characters whose presence in
 * the symbol name implies that they should be quoted. There are however
 * several exceptions to it:
 *
 * Equality is not quoted
 *
 * Numbers are not quoted. However names that just look like numbers
 * are quoted (the distinction is that these are not interpreted)
 *
 * $distinct predicate is not quoted
 *
 * $true and $false -- the names of FOOL term-level boolean constants are not quoted
 *
 * For interpreted symbols its legal to start with $
 *
 * It's legal for symbols to start with $$.
 *
 * @since 03/05/2013 train Manchester-London
 * @since 04/05/2015 Gothenburg -- do not quote FOOL true and false
 */
bool Signature::symbolNeedsQuoting(vstring name, bool interpreted, unsigned arity)
{
  CALL("Signature::symbolNeedsQuoting");
  ASS_G(name.length(),0);

  if (name=="=" || (interpreted && arity==0)) {
    return false;
  }

  const char* c = name.c_str();
  bool quote = false;
  bool first = true;
  if (*c=='$') {
    if (*(c+1)=='$') {
      c+=2; //skip the initial $$
      first = false;
    }
    else if (interpreted) {
      c++; //skip the initial $ for interpreted
      first = false;
    }
  }
  while(!quote && *c) {
    quote |= charNeedsQuoting(*c, first);
    first = false;
    c++;
  }
  if (!quote) { return false; }
  if (name=="$distinct") {
    //TODO: remove this once we properly support the $distinct predicate and quoting
    return false;
  }
  if (name.find("$array") == 0) {
    //TODO: a hacky solution not to quote array sorts
    return false;
  }
  if (name.find(">") >= 0) {
    //TODO: a hacky solution not to quote function sorts
    return false;
  }
  return true;
} // Signature::symbolNeedsQuoting

TermAlgebraConstructor* Signature::getTermAlgebraConstructor(unsigned functor)
{
  CALL("Signature::getTermAlgebraConstructor");

  if (getFunction(functor)->termAlgebraCons()) {
    TermAlgebra *ta = _termAlgebras.get(getFunction(functor)->fnType()->result());
    if (ta) {
      for (unsigned i = 0; i < ta->nConstructors(); i++) {
        TermAlgebraConstructor *c = ta->constructor(i);
        if (c->functor() == functor)
          return c;
      }
    }
  }

  return nullptr;
}

/**
 * Return true if the name containing che character must be quoted
 */
bool Signature::charNeedsQuoting(char c, bool first)
{
  switch (c) {
  case 'a':
  case 'b':
  case 'c':
  case 'd':
  case 'e':
  case 'f':
  case 'g':
  case 'h':
  case 'i':
  case 'j':
  case 'k':
  case 'l':
  case 'm':
  case 'n':
  case 'o':
  case 'p':
  case 'q':
  case 'r':
  case 's':
  case 't':
  case 'u':
  case 'v':
  case 'w':
  case 'x':
  case 'y':
  case 'z':
//  case '$':
    return false;
  case 'A':
  case 'B':
  case 'C':
  case 'D':
  case 'E':
  case 'F':
  case 'G':
  case 'H':
  case 'I':
  case 'J':
  case 'K':
  case 'L':
  case 'M':
  case 'N':
  case 'O':
  case 'P':
  case 'Q':
  case 'R':
  case 'S':
  case 'T':
  case 'U':
  case 'V':
  case 'W':
  case 'X':
  case 'Y':
  case 'Z':
  case '_':
  case '0':
  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    return first;
  default:
    return true;
  }
}
