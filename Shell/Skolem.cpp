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
 * @file Skolem.cpp
 * Implementing Skolemisation.
 * @since 05/01/2003 Manchester
 * @since 08/07/2007 flight Manchester-Cork, changed to new datastructures
 */

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Lib/SharedSet.hpp"

#include "Shell/Statistics.hpp"
#include "Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "Rectify.hpp"
// #include "Refutation.hpp"
#include "Skolem.hpp"
#include "VarManager.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Skolemise the unit.
 *
 * @warning the unit must contain a closed formula in NNF
 * @since 05/01/2004 Manchester
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 31/01/2004 Manchester. Rectify inference has been added
 * (otherwise proof-checking had been very difficult).
 */
FormulaUnit* Skolem::skolemise (FormulaUnit* unit, bool appify)
{
  CALL("Skolem::skolemise(Unit*)");
  ASS(! unit->isClause());

  unit = Rectify::rectify(unit);
  //cout << "skolemising " + unit->toString() << endl; 

 Formula* f = unit->formula();
  switch (f->connective()) {
  case FALSE:
  case TRUE:
    return unit;
  default:
    break;
  }

  static Skolem skol;
  return skol.skolemiseImpl(unit, appify);
} // Skolem::skolemise

FormulaUnit* Skolem::skolemiseImpl (FormulaUnit* unit, bool appify)
{
  CALL("Skolem::skolemiseImpl(FormulaUnit*)");

  ASS(_introducedSkolemFuns.isEmpty());
  
  _appify = appify;
  _beingSkolemised=unit;
  _skolimizingDefinitions = UnitList::empty();
  _varOccs.reset();
  _varSorts.reset();
  _subst.reset();
  _varDeps.reset();
  _blockLookup.reset();

  Formula* f = unit->formula();
  preskolemise(f);
  ASS_EQ(_varOccs.size(),0);

  Formula* g = skolemise(f);
  
  _beingSkolemised = 0;

  if (f == g) { // not changed
    return unit;
  }

  UnitList* premiseList = new UnitList(unit,_skolimizingDefinitions); // making sure unit is the last inserted, i.e. first in the list

  FormulaUnit* res = new FormulaUnit(g,FormulaTransformationMany(InferenceRule::SKOLEMIZE,premiseList));

  ASS(_introducedSkolemFuns.isNonEmpty());
  while(_introducedSkolemFuns.isNonEmpty()) {
    unsigned fn = _introducedSkolemFuns.pop();
    InferenceStore::instance()->recordIntroducedSymbol(res,true,fn);
    if(unit->derivedFromGoal()){
      env.signature->getFunction(fn)->markInGoal();
    }
  }

  return res;
}

unsigned Skolem::addSkolemFunction(unsigned arity, TermList* domainSorts,
    TermList rangeSort, unsigned var, unsigned taArity)
{
  CALL("Skolem::addSkolemFunction(unsigned,unsigned*,unsigned,unsigned)");

  if(VarManager::varNamePreserving()) {
    vstring varName=VarManager::getVarName(var);
    return addSkolemFunction(arity, taArity, domainSorts, rangeSort, varName.c_str());
  }
  else {
    return addSkolemFunction(arity, taArity, domainSorts, rangeSort);
  }
}

unsigned Skolem::addSkolemFunction(unsigned arity, unsigned taArity, TermList* domainSorts,
    TermList rangeSort, const char* suffix)
{
  CALL("Skolem::addSkolemFunction(unsigned,TermList*,TermList,const char*)");
  //ASS(arity==0 || domainSorts!=0);

  unsigned fun = env.signature->addSkolemFunction(arity, suffix);
  Signature::Symbol* fnSym = env.signature->getFunction(fun);
  OperatorType* ot = OperatorType::getFunctionType(arity - taArity, domainSorts, rangeSort, taArity);
  fnSym->setType(ot);
  return fun;
}

unsigned Skolem::addSkolemPredicate(unsigned arity, TermList* domainSorts, unsigned var, unsigned taArity)
{
  CALL("Skolem::addSkolemPredicate(unsigned,unsigned*,unsigned,unsigned)");

  if(VarManager::varNamePreserving()) {
    vstring varName=VarManager::getVarName(var);
    return addSkolemPredicate(arity, taArity, domainSorts, varName.c_str());
  }
  else {
    return addSkolemPredicate(arity, taArity, domainSorts);
  }
}

unsigned Skolem::addSkolemPredicate(unsigned arity, unsigned taArity, TermList* domainSorts, const char* suffix)
{
  CALL("Skolem::addSkolemPredicate(unsigned,unsigned*,unsigned,const char*)");
  //ASS(arity==0 || domainSorts!=0);

  unsigned pred = env.signature->addSkolemPredicate(arity, suffix);
  Signature::Symbol* pSym = env.signature->getPredicate(pred);
  OperatorType* ot = OperatorType::getPredicateType(arity - taArity, domainSorts, taArity);
  pSym->setType(ot);
  return pred;
}

void Skolem::ensureHavingVarSorts()
{
  CALL("Skolem::ensureHavingVarSorts");

  if (_varSorts.size() == 0) {
    Formula* f = _beingSkolemised->formula();
    SortHelper::collectVariableSorts(f, _varSorts);
  }
}

/**
 * Traverse the given formula and prepare skolemising
 * substitution based actual on occurrences
 * of universal variables in the sub-formulas below
 * existential quantifiers.
 */
void Skolem::preskolemise (Formula* f)
{
  CALL("Skolem::preskolemise (Formula*)");

  switch (f->connective()) {
  case LITERAL:
    {
      const Literal* l = f->literal();

      VariableIterator it(l);
      while (it.hasNext()) {
        TermList v = it.next();
        ASS(v.isVar());
        VarOccInfo varOccInfo;
        ALWAYS(_varOccs.find(v.var(),varOccInfo));

        if (BoolList::isNonEmpty(varOccInfo.occurs_below)) { // below a quantifier ...
          varOccInfo.occurs_below->headRef() = true;         // ... occurs in this literal
        }
      }
      return;
    }

  case AND:
  case OR:
    {
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        preskolemise(it.next());
      }
      return;
    }

  case FORALL:
    {
      VList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        ALWAYS(_varOccs.insert(vs.next(),{false/*univeral*/,nullptr})); // ALWAYS, because we are rectified
      }
      preskolemise(f->qarg());
      vs.reset(f->vars());
      while (vs.hasNext()) {
        _varOccs.remove(vs.next());
      }
      return;
    }

  case EXISTS:
    {
      { // reset the "occurs" flag for all the variables we are in scope of
        VarOccInfos::Iterator vit(_varOccs);
        while (vit.hasNext()) {
          unsigned dummy;
          VarOccInfo& varOccInfo = vit.nextRef(dummy);
          BoolList::push(false,varOccInfo.occurs_below);
        }
      }

      // add our own variables (for which we are not interested in occurrences)
      VList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        unsigned var = vs.next();
        ALWAYS(_varOccs.insert(var,{true/*existential*/,nullptr})); // ALWAYS, because we are rectified
        ALWAYS(_blockLookup.insert(var,f));
      }

      preskolemise(f->qarg());

      // take ours out again
      vs.reset(f->vars());
      while (vs.hasNext()) {
        _varOccs.remove(vs.next());
      }

      static Stack<unsigned> univ_dep_stack;
      static Stack<unsigned> exists_deps_stack;
      ASS(univ_dep_stack.isEmpty());
      ASS(exists_deps_stack.isEmpty());

      // collect results from subformulas
      VarOccInfos::Iterator vit(_varOccs);
      while(vit.hasNext()) {
        unsigned var;
        VarOccInfo& varOccInfo = vit.nextRef(var);
        ASS(BoolList::isNonEmpty(varOccInfo.occurs_below));
        if (!BoolList::pop(varOccInfo.occurs_below)) { // the var didn't really occur in the subformula
          continue;
        }
        if (BoolList::isNonEmpty(varOccInfo.occurs_below)) { // pass the fact that it did occur above
          varOccInfo.occurs_below->headRef() = true;
        }

        if (varOccInfo.existential) {
          exists_deps_stack.push(var);
        } else {
          univ_dep_stack.push(var);
        }
      }

      Stack<unsigned>::Iterator udIt(univ_dep_stack);
      VarSet* univ_dep_set = VarSet::getFromIterator(udIt);
      univ_dep_stack.reset();

      Stack<unsigned>::Iterator edIt(exists_deps_stack);
      VarSet* exists_dep_set = VarSet::getFromIterator(edIt);
      exists_deps_stack.reset();

      _varDeps.insert(f,{univ_dep_set,exists_dep_set});

      return;
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

  case TRUE:
  case FALSE:
    return;

  default:
    ASSERTION_VIOLATION_REP(f->connective());
  }
}

/**
 * Skolemise a subformula = drop existential quantifiers,
 * and apply already prepared substitution in literals.
 *
 * @param f the subformula
 *
 * @since 28/06/2002 Manchester
 * @since 04/09/2002 Bolzano, changed
 * @since 05/09/2002 Trento, changed
 * @since 19/01/2002 Manchester, information about 
 *        positions and inferences added.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 31/01/2004 Manchester, simplified to work with rectified formulas
 * @since 11/12/2004 Manchester, true and false added
 * @since 12/12/2004 Manchester, optimised by quantifying only over
 *    variables actually occurring in the formula.
 * @since 28/12/2007 Manchester, changed to new datastructures
 * @since 14/11/2015 Manchester, changed to really optimise by quantifying only over
 *    variables actually occurring in the formula (done in cooperation with preskolimise)
 */
Formula* Skolem::skolemise (Formula* f)
{
  CALL("Skolem::skolemise (Formula*)");

  switch (f->connective()) {
  case LITERAL: 
    {
      Literal* l = f->literal();
      Literal* ll = l->apply(_subst);
      if (l == ll) {
        return f;
      }
      return new AtomicFormula(ll);
    }

  case AND:
  case OR: 
    {
      FormulaList* fs = skolemise(f->args());
      if (fs == f->args()) {
        return f;
      }
      return new JunctionFormula(f->connective(),fs);
    }

  case FORALL: 
    {
      Formula* g = skolemise(f->qarg());
      if (g == f->qarg()) {
        return f;
      }
      return new QuantifiedFormula(f->connective(),f->vars(),f->sorts(),g);
    }

  case EXISTS: 
    {
      // create the skolems for the existentials here
      // and bind them in _subst
      unsigned arity = 0;
      ensureHavingVarSorts();
      static TermStack allVars;
      static TermStack typeVars;
      static TermStack termVars;
      static TermStack termVarSorts;
      termVarSorts.reset();
      termVars.reset();
      allVars.reset();
      typeVars.reset();

      // for proof recording purposes, see below
      VList* varArgs = VList::empty();
      //We use a FIFO structure since in the polymorphic case
      //a variable list must be of the form [typevars, termvars]
      VList::FIFO vArgs(varArgs);
      Formula* before = SubstHelper::apply(f, _subst);

      static DHSet<vstring> cache;
      FormulaUnit *copy = new FormulaUnit(before, Inference(FromInput(UnitInputType::AXIOM)));
      FormulaUnit *rectified = Rectify::rectify(copy);
      Formula *normalised = rectified->formula();
      if(!cache.insert(normalised->toString()))
        std::cout
          << "DUPE SKOLEM in " << env.options->problemName()
          << ": " << normalised->toString()
          << std::endl;


      ExVarDepInfo& depInfo = _varDeps.get(f);

      VarSet* dep = depInfo.univ;

      VarSet::Iterator veIt(*depInfo.exist);
      while(veIt.hasNext()) {
        unsigned evar = veIt.next();
        Formula* block = _blockLookup.get(evar);
        VarSet* their_dep = _varDeps.get(block).univ;
        dep = dep->getUnion(their_dep);
      }

      /*
      if (depInfo.univ != dep) {
        // PANIC !!!
      }
      */

      // store updated, for the existentials below us to lookup as well
      depInfo.univ = dep;

      VarSet::Iterator vuIt(*dep);
      while(vuIt.hasNext()) {
        unsigned uvar = vuIt.next();
        TermList sort = _varSorts.get(uvar, Term::defaultSort());
        if(sort == Term::superSort()){
          //This a type variable
          TermList var = TermList(uvar, false);
          allVars.push(var);
          typeVars.push(var);
          vArgs.pushFront(uvar);
        } else {
          //This is a term variable
          if(sort.isVar() || !sort.term()->shared() || !sort.term()->ground()){
            //the sort may include existential type variables that have been skolemised 
            //above
            sort = SubstHelper::apply(sort, _subst);
          }
          termVarSorts.push(sort);
          termVars.push(TermList(uvar, false));
          vArgs.pushBack(uvar);
        }
        arity++;
      }

      for(unsigned i = 0; i < termVars.size() && !_appify; i++){
        allVars.push(termVars[i]);
      }
      SortHelper::normaliseArgSorts(typeVars, termVarSorts);

      VList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        unsigned v = vs.next();
        TermList rangeSort=_varSorts.get(v, Term::defaultSort());
        if(rangeSort.isVar() || !rangeSort.term()->shared() || 
           !rangeSort.term()->ground()){
          //the range sort may include existential type variables that have been skolemised 
          //above
          rangeSort = SubstHelper::apply(rangeSort, _subst);
        }

        SortHelper::normaliseSort(typeVars, rangeSort);
        Term* skolemTerm;

        if(!_appify){
          //Not the higher-order case. Create the term
          //sk(typevars, termvars).
          unsigned fun = addSkolemFunction(arity, termVarSorts.begin(), rangeSort, v, typeVars.size());
          _introducedSkolemFuns.push(fun);
          skolemTerm = Term::create(fun, arity, allVars.begin());
        } else {
          //The higher-order case. Create the term
          //sk(typevars) @ termvar_1 @ termvar_2 @ ... @ termvar_n
          TermList skSymSort = Term::arrowSort(termVarSorts, rangeSort);
          unsigned fun = addSkolemFunction(typeVars.size(), 0, skSymSort, v, typeVars.size());
          _introducedSkolemFuns.push(fun);
          TermList head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
          skolemTerm = ApplicativeHelper::createAppTerm(skSymSort, head, termVars).term();
        }

        env.statistics->skolemFunctions++;

        _subst.bind(v,skolemTerm);

        if (env.options->showSkolemisations()) {
          env.beginOutput();
          env.out() << "Skolemising: "<<skolemTerm->toString()<<" for X"<< v
            <<" in "<<f->toString()<<" in formula "<<_beingSkolemised->toString() << endl;
          env.endOutput();
        }

        if (env.options->showNonconstantSkolemFunctionTrace() && arity!=0) {
          env.beginOutput();
          ostream& out = env.out();
            out <<"Nonconstant skolem function introduced: "
            <<skolemTerm->toString()<<" for X"<<v<<" in "<<f->toString()
            <<" in formula "<<_beingSkolemised->toString()<<endl;

          /*
          Refutation ref(_beingSkolemised, true);
          ref.output(out);
          */
          env.endOutput();
        }
      }

      {
        Formula* after = SubstHelper::apply(f->qarg(), _subst);
        Formula* def = new BinaryFormula(IMP, before, after);

        if (arity > 0) {
          def = new QuantifiedFormula(FORALL,varArgs,nullptr,def);
        }

        Unit* defUnit = new FormulaUnit(def,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::CHOICE_AXIOM));
        UnitList::push(defUnit,_skolimizingDefinitions);
      }

      // drop the existential one:
      return skolemise(f->qarg());
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

  case TRUE:
  case FALSE:
    return f;

  default:
    ASSERTION_VIOLATION;
  }
} // Skolem::skolemise


/**
 * Skolemise a list of formulas in NFF.
 *
 * @since 28/06/2002 Manchester
 * @since 04/09/2002 Bolzano, changed
 * @since 19/01/2002 Manchester, information about 
 *        positions and inferences added.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 12/12/2004 Manchester, optimised by quantifying only over
 *    variables actually occurring in the formula.
 */
FormulaList* Skolem::skolemise (FormulaList* fs)
{
  CALL("Skolem:skolemise(FormulaList*)");

  ASS(FormulaList::isNonEmpty(fs));

  Stack<FormulaList*> args;

  while (FormulaList::isNonEmpty(fs)) {
    args.push(fs);
    fs = fs->tail();
  }

  FormulaList* res = args.top()->tail();
  ASS(FormulaList::isEmpty(res));

  while (args.isNonEmpty()) {
    fs = args.pop();
    Formula* g = fs->head();
    FormulaList* gs = fs->tail();
    Formula* h = skolemise(g);
    FormulaList* hs = res; // = skolemise(gs);

    if (gs == hs && g == h) {
      res = fs;
    } else {
      res = new FormulaList(h,hs);
    }
  }

  return res;
} // Skolem::skolemise


