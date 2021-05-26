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
 * @file SortHelper.hpp
 * Defines class SortHelper.
 */

#ifndef __SortHelper__
#define __SortHelper__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Sorts.hpp"

namespace Kernel {

class SortHelper {
private:
  enum CollectWhat {
    COLLECT_TERM,
    COLLECT_TERMLIST,
    COLLECT_SPECIALTERM,
    COLLECT_FORMULA
  };

  struct CollectTask {
    CollectWhat fncTag;
    union {
      Term* t; // shared by TERM and SPECIALTERM
      Formula* f;
    };
    TermList ts; // outside of union, because it has a non-trivial constructor
    TermList contextSort; // only used by TERMLIST and SPECIALTERM
  };

  static void collectVariableSortsIter(CollectTask task, DHMap<unsigned,TermList>& map);
public:
  static TermList getResultSort(const Term* t);
  static TermList getResultSortMono(const Term* t);
  static TermList getResultSort(TermList t, DHMap<unsigned,TermList>& varSorts);
  static TermList getArgSort(Term* t, unsigned argIndex);

  static bool tryGetResultSort(const Term* t, TermList& result);
  static bool tryGetResultSort(const TermList t, TermList& result);
  static bool getResultSortOrMasterVariable(const Term* t, TermList& resultSort, TermList& resultVar);
  static bool getResultSortOrMasterVariable(const TermList t, TermList& resultSort, TermList& resultVar);

  static TermList getEqualityArgumentSort(const Literal* lit);

  static bool tryGetVariableSort(unsigned var, Formula* f, TermList& res);
  static TermList getVariableSort(TermList var, Term* t);
  static TermList getTermSort(TermList trm, Literal* lit);

  static void collectVariableSorts(Unit* u, DHMap<unsigned,TermList>& map);
  static void collectVariableSorts(Term* t, DHMap<unsigned,TermList>& map);
  static void collectVariableSorts(TermList ts, TermList contextSort, DHMap<unsigned,TermList>& map);
  // static void collectVariableSortsSpecialTerm(Term* t, TermList contextSort, DHMap<unsigned,TermList>& map);
  static void collectVariableSorts(Formula* f, DHMap<unsigned,TermList>& map);

  static bool areSortsValid(Clause* cl);
  static bool areImmediateSortsValidPoly(Term* t); 
  static bool areImmediateSortsValidMono(Term* t);
  // static bool isStructuredSort(unsigned s);
  static bool isTupleSort(TermList sort);
  static bool isArraySort(TermList sort);
  static bool isBoolSort(TermList sort);
  static TermList getIndexSort(TermList arraySort);
  static TermList getInnerSort(TermList arraySort);
  static bool isNotDefaultSort(unsigned s);
  static bool isInterpretedNonDefault(unsigned s);
  static bool isInterpretedNonBool(unsigned s);
  /** convenience function see Sorts::getSortNum(...) */
  static unsigned sortNum(TermList sort);
  /** convenience function see Sorts::getSortId(...) */
  static TermList sortTerm(unsigned sortNum);

  static void normaliseArgSorts(VList* qVars, TermStack& argSorts);
  static void normaliseSort(VList* qVars, TermList& sort);
  static void normaliseArgSorts(TermStack& qVars, TermStack& argSorts);
  static void normaliseSort(TermStack qVars, TermList& sort);    

  static OperatorType* getType(Term* t);

  static void getTypeSub(const Term* t, Substitution& subst);

  static bool areSortsValid(Term* t, DHMap<unsigned,TermList>& varSorts);
private:
  // It is important this function is private, because it only works in cooperation with tryGetVariableSort(unsigned var, Formula* f, unsigned& res);
  static bool tryGetVariableSort(TermList var, Term* t, TermList& result);
};

}

#endif // __SortHelper__
