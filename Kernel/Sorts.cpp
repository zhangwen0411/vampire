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
 * @file Sorts.cpp
 * Implements class Sorts for handling collections of sorts.
 */

#include "Sorts.hpp"

#include "Lib/Environment.hpp"
//#include "Kernel/Theory.hpp"
#include "Shell/Options.hpp"

#include "Term.hpp"
#include "Signature.hpp"

using namespace Kernel;

/**
 * Initialise sorts by adding the default sort
 * @since 04/05/2013 Manchester, updated with the new built-in sorts
 * @author Andrei Voronkov
 */
  
Sorts::Sorts()
{
  CALL("Sorts::Sorts");
  _arraySorts = new DHSet<TermList>();
 //_hasSort = false;
} // Sorts::Sorts

/**
 * Destroy the object and delete all sorts in it.
 * @author Andrei Voronkov
 */
Sorts::~Sorts()
{
  CALL("Sorts::~Sorts");
  delete _arraySorts;
  /*while(_sorts.isNonEmpty()) {
    delete _sorts.pop();
  }*/
} // Sorts::~Sorts


bool Sorts::addSort(TermList sort)
{ 
  CALL("Sorts::addSort");
 
  if(_termListsToUnsigned.find(sort)){
    return false;
  }
  
  _termListsToUnsigned.insert(sort, _sorts.size());
  _sorts.push(sort);
  return true;
}

unsigned Sorts::getSortNum(TermList sort)
{ 
  CALL("Sorts::getSortNum");

  ASS_REP(_termListsToUnsigned.find(sort), sort.toString())
  return _termListsToUnsigned.get(sort);
}

TermList Sorts::getSortTerm(unsigned sortNum)
{
  CALL("Sorts::getSortTerm");
  
  ASS(sortNum < _sorts.size())
  return _sorts[sortNum];
}

/**
 * Pre-initialise an OperatorKey.
 *
 * If @c sorts is is NULL, all arguments will be initalized by the default sort,
 * otherwise, by sorts from the array @c sorts
 * @author Andrei Voronkov
 */
OperatorType::OperatorKey* OperatorType::setupKey(unsigned arity, const TermList* sorts)
{
  CALL("OperatorType::setupKey(unsigned,const unsigned*)");

  OperatorKey* key = OperatorKey::allocate(arity+1);

  if (!sorts) {
    // initialise all argument types to the default type
    for (unsigned i=0; i < arity; i++) {
      (*key)[i] = Term::defaultSort();
    }
  } else {
    // initialise all the argument types to those taken from sorts
    for (unsigned i = 0; i < arity; i++) {
      (*key)[i] = sorts[i];
    }
  }
  return key;
}

/**
 * Pre-initialise an OperatorKey from an initializer list of sorts.
 */
OperatorType::OperatorKey* OperatorType::setupKey(std::initializer_list<TermList> sorts)
{
  CALL("OperatorType::setupKey(std::initializer_list<unsigned>)");

  OperatorKey* key = OperatorKey::allocate(sorts.size()+1);

  // initialise all the argument types to those taken from sorts
  unsigned i = 0;
  for (auto sort : sorts) {
    (*key)[i++] = sort;
  }

  return key;
}

/**
 * Pre-initialise an OperatorKey from using a uniform range.
 */
OperatorType::OperatorKey* OperatorType::setupKeyUniformRange(unsigned arity, TermList argsSort)
{
  CALL("OperatorType::setupKeyUniformRange");

  OperatorKey* key = OperatorKey::allocate(arity+1);

  for (unsigned i=0; i < arity; i++) {
    (*key)[i] = argsSort;
  }

  return key;
}

OperatorType::OperatorTypes& OperatorType::operatorTypes() {
  struct DeletingOperatorTypes : public OperatorType::OperatorTypes {
    ~DeletingOperatorTypes() {
      deleteAll();
    }
  };

  static DeletingOperatorTypes _operatorTypes;
  return _operatorTypes;
}

/**
 * Check if OperatorType corresponding to the given key
 * already exists. If so return it, if not create new,
 * store it for future retrieval and return it.
 *
 * Release key if not needed.
 */
OperatorType* OperatorType::getTypeFromKey(OperatorType::OperatorKey* key, unsigned taArity)
{
  CALL("OperatorType::getTypeFromKey");

  /*
  cout << "getTypeFromKey(" << key->length() << "): ";
  for (unsigned i = 0; i < key->length(); i++) {
    cout << (((*key)[i] == PREDICATE_FLAG) ? "FFFF" : env.sorts->sortName((*key)[i])) << ",";
  }
  */

  OperatorType* resultType = new OperatorType(key, taArity);

  if (operatorTypes().find(resultType, resultType)) {
    key->deallocate();

    //cout << " Found " + resultType->toString() << endl;
    
    return resultType;
  }

  operatorTypes().insert(resultType);

  //cout << " Created new " + resultType->toString() << endl;

  return resultType;
}

/**
 * Return the string representation of arguments of a non-atomic
 * functional or a predicate sort in the form (t1 * ... * tn)
 * @since 04/05/2013 bug fix (comma was used instead of *)
 * @author Andrei Voronkov
 */
vstring OperatorType::argsToString() const
{
  CALL("OperatorType::argsToString");

  vstring res = "(";
  unsigned ar = arity();
  ASS(ar);
  for (unsigned i = _typeArgsArity; i < ar; i++) {
    res += arg(i).toString();
    if (i != ar-1) {
      res += " * ";
    }
  }
  res += ')';
  return res;
} // OperatorType::argsToString()

/**
 * Return the TPTP string representation of the OpertorType.
 */
vstring OperatorType::toString() const
{
  CALL("OperatorType::toString");

  vstring res;
  bool bracket = false;
  if(_typeArgsArity){
    res = "!>[";
    for(unsigned i = 0; i < _typeArgsArity; i++){
      if(i != 0){ res += ", "; }
      res+=  quantifiedVar(i).toString() + ": $tType"; 
    }
    res += "]:";
    bracket = true;
  }

  return res + (bracket ? "(" : "") +  (arity() - typeArgsArity() ? argsToString() + " > " : "") +
      (isPredicateType() ? "$o" : result().toString()) + (bracket ? ")" : "");
}

/**
 * True if all arguments of this type have sort @c str
 * and so is the result sort if we are talking about a function type.
 * @author Andrei Voronkov
 */
bool OperatorType::isSingleSortType(TermList srt) const
{
  CALL("OperatorType::isSingleSortType");

  unsigned len = arity();
  for (unsigned i = 0; i <len; i++) {
    if (arg(i) != srt) { //term comparison with != should be OK on the basis that both are shared terms
      return false;
    }
  }

  if (isFunctionType() && result() != srt) { 
    return false;
  }

  return true;
} // isSingleSortType
