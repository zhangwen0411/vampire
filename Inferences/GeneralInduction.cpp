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
 * @file GeneralInduction.cpp
 * Implements class GeneralInduction.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "Lib/Array.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/Splitter.hpp"

#include "Shell/InductionSchemeGenerator.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/InductionHelper.hpp"

#include "GeneralInduction.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Lib;
using namespace Shell;

TermList TermOccurrenceReplacement::transformSubterm(TermList trm)
{
  if (trm.isVar()) {
    return trm;
  }
  auto rIt = _r.find(trm.term());
  if (rIt != _r.end()) {
    auto oIt = _o._m.find(make_pair(_lit, trm.term()));
    ASS(oIt != _o._m.end());
    // if current bit is one, replace
    if (oIt->second.pop_last()) {
      return TermList(rIt->second, false);
    }
  }
  return trm;
}

TermList TermMapReplacement::transformSubterm(TermList trm)
{
  if (trm.isVar()) {
    return trm;
  }
  auto t = trm.term();
  auto rIt = _r.find(t);
  if (rIt != _r.end()) {
    // if term needs to be replaced, get its sort and map it
    // to the next replacement term within that sort
    TermList srt = env.signature->getFunction(t->functor())->fnType()->result();
    auto oIt = _ord.find(t);
    if (oIt == _ord.end()) {
      oIt = _ord.insert(make_pair(t, _curr.at(srt)++)).first;
    }
    return TermList(_m.get(srt)[oIt->second]);
  }
  return trm;
}

ClauseIterator GeneralInduction::generateClauses(Clause* premise)
{
  CALL("GeneralInduction::generateClauses");

  InductionClauseIterator res;
  if (InductionHelper::isInductionClause(premise)) {
    for (unsigned i = 0; i < premise->length(); i++) {
      process(res, premise, (*premise)[i]);
    }
  }

  return pvi(res);
}

inline bool skolem(Term* t) {
  return env.signature->getFunction(t->functor())->skolem();
}

void GeneralInduction::process(InductionClauseIterator& res, Clause* premise, Literal* literal)
{
  CALL("GeneralInduction::process");

  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << *literal << " in " << *premise << endl;
    env.endOutput();
  }

  auto pairs = selectMainSidePairs(literal, premise);

  for (auto& gen : _gen) {
    for (const auto& kv : pairs) {
      const auto& main = kv.first;
      const auto& sides = kv.second;
      static vvector<pair<InductionScheme, OccurrenceMap>> schOccMap;
      schOccMap.clear();
      gen->generate(main, sides, schOccMap);

      vvector<pair<Literal*, vset<Literal*>>> schLits;
      for (const auto& kv : schOccMap) {
        // Retain side literals for further processing if:
        // (1) they contain some induction term from the current scheme
        // (2) they have either induction depth 0 or they contain some complex induction term
        //     (this has been partly checked in selectMainSidePairs but there we did not know
        //      yet whether there is a complex induction term)
        vset<pair<Literal*, Clause*>> sidesFiltered;
        for (const auto& s : sides) {
          for (const auto& kv2 : kv.first.inductionTerms()) {
            if (s.first->containsSubterm(TermList(kv2.first)) && (!skolem(kv2.first) || !s.second->inference().inductionDepth())) {
              sidesFiltered.insert(s);
              break;
            }
          }
        }
        // Check whether we done this induction before. Since there can
        // be other induction schemes and literals that produce the same,
        // we add the new ones at the end
        schLits.emplace_back(nullptr, vset<Literal*>());
        if (alreadyDone(literal, sidesFiltered, kv.first, schLits.back())) {
          continue;
        }
        static const bool generalize = env.options->inductionGen();
        ScopedPtr<IteratorCore<OccurrenceMap>> g;
        if (generalize) {
          static const bool heuristic = env.options->inductionGenHeur();
          g = new GeneralizationIterator(kv.second, heuristic, gen->setsFixOccurrences());
        } else {
          g = new NoGeneralizationIterator(kv.second);
        }
        while (g->hasNext()) {
          auto eg = g->next();
          // create the generalized literals by replacing the current
          // set of occurrences of induction terms by the variables
          TermOccurrenceReplacement tr(kv.first.inductionTerms(), eg, main.literal);
          auto mainLitGen = tr.transformLit();
          ASS_NEQ(mainLitGen, main.literal); // main literal should be inducted on
          vvector<pair<Literal*, SLQueryResult>> sidesGeneralized;
          for (const auto& kv2 : sidesFiltered) {
            TermOccurrenceReplacement tr(kv.first.inductionTerms(), eg, kv2.first);
            auto sideLitGen = tr.transformLit();
            if (sideLitGen != kv2.first) { // side literals may be discarded if they contain no induction term occurrence
              sidesGeneralized.push_back(make_pair(sideLitGen, SLQueryResult(kv2.first, kv2.second)));
            }
          }
          generateClauses(kv.first, mainLitGen, main, sidesGeneralized, res._clauses);
        }
      }
      for (const auto& schLit : schLits) {
        // if the pattern is already contained but we have a superset of its
        // side literals, we add the superset to cover as many as possible
        if (!_done.insert(schLit.first, schLit.second)) {
          auto curr = _done.get(schLit.first);
          if (includes(schLit.second.begin(), schLit.second.end(), curr.begin(), curr.end())) {
            _done.set(schLit.first, schLit.second);
          }
          // TODO(mhajdu): there can be cases where the current set of side literals
          // is not a superset of the already inducted on ones, in this case the new
          // ones are not added
        }
      }
    }
  }
}

void GeneralInduction::attach(SaturationAlgorithm* salg)
{
  CALL("GeneralInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _splitter=_salg->getSplitter();
  _index = static_cast<TermIndex *>(
      _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE));
}

void GeneralInduction::detach()
{
  CALL("GeneralInduction::detach");

  _index = 0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _splitter=0;
  GeneratingInferenceEngine::detach();
}

Formula* createImplication(Substitution subst, Literal* mainLit, const vvector<pair<Literal*, SLQueryResult>>& sideLitQrPairs, Literal*& mainLitS) {
  FormulaList* ll = FormulaList::empty();
  for (const auto& kv : sideLitQrPairs) {
    FormulaList::push(new AtomicFormula(SubstHelper::apply<Substitution>(kv.first, subst)), ll);
  }
  Formula* left = 0;
  if (FormulaList::isNonEmpty(ll)) {
    left = JunctionFormula::generalJunction(Connective::AND, ll);
  }
  mainLitS = Literal::complementaryLiteral(SubstHelper::apply<Substitution>(mainLit, subst));
  Formula* right = new AtomicFormula(mainLitS);
  return left ? new BinaryFormula(Connective::IMP, left, right) : right;
}

InductionScheme::Case renameCase(const InductionScheme::Case& c, const vmap<Term*, unsigned>& inductionTerms, unsigned& var) {
  Renaming r(var);
  TermList t;
  Substitution step;
  vvector<Substitution> recCalls;
  for (const auto& kv : inductionTerms) {
    if (c._step.findBinding(kv.second, t)) {
      r.normalizeVariables(t);
      step.bind(kv.second, r.apply(t));
    }
  }
  for (const auto& recCall : c._recursiveCalls) {
    recCalls.emplace_back();
    for (const auto& kv : inductionTerms) {
      if (recCall.findBinding(kv.second, t)) {
        r.normalizeVariables(t);
        recCalls.back().bind(kv.second, r.apply(t));
      }
    }
  }
  var = r.nextVar();
  return InductionScheme::Case(std::move(recCalls), std::move(step));
}

void GeneralInduction::generateClauses(
  const Shell::InductionScheme& scheme,
  Literal* mainLit, const SLQueryResult& mainQuery,
  const vvector<pair<Literal*, SLQueryResult>>& sideLitQrPairs,
  ClauseStack& clauses)
{
  CALL("GeneralInduction::generateClauses");

  static const bool indhrw = env.options->inductionHypRewriting();

  if (env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] generating from scheme " << scheme
              << " with generalized literals " << *mainLit << ", ";
    for (const auto& kv : sideLitQrPairs) {
      env.out() << *kv.first << ", ";
    }
    env.out() << endl;
    env.endOutput();
  }

  vset<unsigned> hypVars;
  FormulaList* cases = FormulaList::empty();
  Literal* mainLitS;
  unsigned var = 0;
  for (const auto& kv : scheme.inductionTerms()) {
    var = max(var, kv.second);
  }
  var++;

  TermList t;
  for (const auto& c : scheme.cases()) {
    auto rn = renameCase(c, scheme.inductionTerms(), var);
    FormulaList* ll = FormulaList::empty();
    VList* vars = VList::empty();
    for (auto& r : rn._recursiveCalls) {
      FormulaList::push(createImplication(r, mainLit, sideLitQrPairs, mainLitS), ll);
      if (indhrw && mainLit->isEquality()) {
        VList::Iterator vit(mainLitS->freeVariables());
        while (vit.hasNext()) {
          hypVars.insert(vit.next());
        }
      }
      for (const auto& kv : scheme.inductionTerms()) {
        if (r.findBinding(kv.second, t)) {
          VList::Iterator vit(t.freeVariables());
          while (vit.hasNext()) {
            auto v = vit.next();
            if (!VList::member(v, vars)) {
              VList::push(v, vars);
            }
          }
        }
      }
    }
    auto right = createImplication(rn._step, mainLit, sideLitQrPairs, mainLitS);
    Formula* left = 0;
    if (FormulaList::isNonEmpty(ll)) {
      left = JunctionFormula::generalJunction(Connective::AND, ll);
    }
    auto f = left ? new BinaryFormula(Connective::IMP, left, right) : right;
    for (const auto& kv : scheme.inductionTerms()) {
      if (rn._step.findBinding(kv.second, t)) {
        VList::Iterator vit(t.freeVariables());
        while (vit.hasNext()) {
          auto v = vit.next();
          if (!VList::member(v, vars)) {
            VList::push(v, vars);
          }
        }
      }
    }
    FormulaList::push(VList::isEmpty(vars) ? f : new QuantifiedFormula(Connective::FORALL, vars, 0, f), cases);
  }

  ASS(FormulaList::isNonEmpty(cases));
  Substitution empty;
  VList* vars = VList::empty();
  RobSubstitution subst;
  for (const auto& kv : scheme.inductionTerms()) {
    VList::push(kv.second, vars);
    ALWAYS(subst.match(TermList(kv.second, false), 0, TermList(kv.first), 1));
  }
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
    JunctionFormula::generalJunction(Connective::AND, cases),
    new QuantifiedFormula(Connective::FORALL, vars, 0,
      createImplication(empty, mainLit, sideLitQrPairs, mainLitS)));
  // cout << *hypothesis << endl;

  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
  Inference inf2 = NonspecificInference0(UnitInputType::AXIOM,_rule);
  unsigned maxDepth = mainQuery.clause->inference().inductionDepth();
  for (const auto& kv : sideLitQrPairs) {
    maxDepth = max(maxDepth, kv.second.clause->inference().inductionDepth());
  }
  inf2.setInductionDepth(maxDepth+1);
  auto fu = new FormulaUnit(hypothesis,inf2);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);
  auto skFunToVarMap = cnf.getSkFunToVarMap();
  DHMap<unsigned,unsigned>::Iterator it(skFunToVarMap);
  DHMap<unsigned,unsigned> rvs;
  if (indhrw && mainLit->isEquality()) {
    while (it.hasNext()) {
      unsigned f, v;
      it.next(f, v);
      ALWAYS(rvs.insert(v, f));
    }
  }

  auto resSubst = ResultSubstitution::fromSubstitution(&subst, 0, 1);
  auto skMain = InductionHelper::collectSkolems(mainQuery.literal, mainQuery.clause);
  for (unsigned i = 0; i < mainQuery.clause->length(); i++) {
    auto lit = (*mainQuery.clause)[i];
    if (lit != mainQuery.literal) {
      auto skLit = InductionHelper::collectSkolems(lit, mainQuery.clause);
      for (const auto& fn : skLit) {
        skMain.erase(fn);
      }
    }
  }

  // Resolve all induction clauses with the main and side literals
  ClauseStack::Iterator cit(hyp_clauses);
  while(cit.hasNext()){
    Clause* c = cit.next();
    for (const auto& v : hypVars) {
      c->inference().addToInductionInfo(rvs.get(v));
    }
    auto qr = mainQuery;
    qr.substitution = resSubst;
    c = BinaryResolution::generateClause(c, Literal::complementaryLiteral(mainLit), qr, *env.options);
    ASS(c);
    if (_splitter && !sideLitQrPairs.empty()) {
      _splitter->onNewClause(c);
    }
    unsigned i = 0;
    for (const auto& kv : sideLitQrPairs) {
      auto conclusion = subst.apply(kv.first, 0);
      auto qr = kv.second;
      qr.substitution = resSubst;
      c = BinaryResolution::generateClause(c, Literal::complementaryLiteral(conclusion), qr, *env.options);
      ASS(c);
      if (_splitter && ++i < sideLitQrPairs.size()) {
        _splitter->onNewClause(c);
      }
    }
    for (const auto& fn : skMain) {
      c->inference().removeFromInductionInfo(fn);
    }
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl;
      env.endOutput();
    }
    clauses.push(c);
  }
  env.statistics->induction++;
}

void reserveBlanksForScheme(const InductionScheme& sch, DHMap<TermList, vvector<Term*>>& blanks)
{
  vmap<TermList, unsigned> srts;
  // count sorts in induction terms
  for (const auto& kv : sch.inductionTerms()) {
    TermList srt = env.signature->getFunction(kv.first->functor())->fnType()->result();
    auto res = srts.insert(make_pair(srt,1));
    if (!res.second) {
      res.first->second++;
    }
  }
  // introduce as many blanks for each sort as needed
  for (const auto kv : srts) {
    if (!blanks.find(kv.first)) {
      blanks.insert(kv.first, vvector<Term*>());
    }
    auto& v = blanks.get(kv.first);
    v.reserve(kv.second);
    while (v.size() < kv.second) {
      unsigned fresh = env.signature->addFreshFunction(0, "blank");
      env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(kv.first));
      v.push_back(Term::createConstant(fresh));
    }
  }
}

bool GeneralInduction::alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
  const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res)
{
  CALL("GeneralInduction::alreadyDone");

  // Instead of relying on the order within the induction term set, we map induction terms
  // to blanks based on their first occurrences within the literal to avoid creating different
  // blanks for the same literal pattern. E.g. if we have a saved pattern leq(blank0,blank1)
  // and a new literal leq(sk1,sk0) should be inducted upon with induction terms { sk0, sk1 },
  // instead of using the order within the set to get the different leq(blank1,blank0) essentially
  // for the same pattern, since sk1 is the first within the literal, we map this to
  // leq(blank0,blank1) and we detect that it was already inducted upon in this form

  // introduce the blanks
  static DHMap<TermList, vvector<Term*>> blanks;
  reserveBlanksForScheme(sch, blanks);

  // place the blanks in main literal
  TermMapReplacement cr(blanks, sch.inductionTerms());
  res.first = cr.transform(mainLit);

  // place the blanks in sides (using the now fixed order from main literal)
  for (const auto& kv : sides) {
    res.second.insert(cr.transform(kv.first));
  }
  // TODO(mhajdu): the reason we check this is to avoid
  // "induction loops" when we induct on the step immediately
  // after creating it. This means we usually want to exclude
  // schemes with complex terms, but this is an ugly workaround
  for (const auto& kv : sch.inductionTerms()) {
    if (skolem(kv.first)) {
      return false;
    }
  }
  // check already existing pattern for main literal
  if (!_done.find(res.first)) {
    return false;
  }
  auto s = _done.get(res.first);
  // check if the sides for the new pattern are included in the existing one
  if (includes(s.begin(), s.end(), res.second.begin(), res.second.end())) {
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "[Induction] already inducted on " << *mainLit << " in " << *res.first << " form" << endl;
      env.endOutput();
    }
    return true;
  }
  return false;
}

inline bool sideLitCondition(Literal* main, Clause* mainCl, Literal* side, Clause* sideCl) {
  auto mainSk = InductionHelper::collectSkolems(main, mainCl);
  auto sideSk = InductionHelper::collectSkolems(side, sideCl);
  return side->ground() && main != side && mainCl != sideCl &&
    // either they are both induction depth 0 (not yet inducted on)
    ((!mainCl->inference().inductionDepth() && !sideCl->inference().inductionDepth()) ||
    // or they are hypothesis and conclusion from the same step and predicates
    (InductionHelper::isInductionLiteral(side, sideCl) &&
      InductionHelper::isInductionLiteral(main, mainCl) &&
      includes(mainSk.begin(), mainSk.end(), sideSk.begin(), sideSk.end()) && !side->isEquality() && !main->isEquality()));
}

vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> GeneralInduction::selectMainSidePairs(Literal* literal, Clause* premise)
{
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> res;
  static const bool indmc = env.options->inductionMultiClause();

  // TODO(mhajdu): is there a way to duplicate these iterators?
  TermQueryResultIterator itSides = TermQueryResultIterator::getEmpty();
  TermQueryResultIterator itMains = TermQueryResultIterator::getEmpty();
  if (indmc) {
    SubtermIterator stit(literal);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (st.isTerm() && skolem(st.term())) {
        itSides = pvi(getConcatenatedIterator(itSides, _index->getGeneralizations(st)));
        itMains = pvi(getConcatenatedIterator(itMains, _index->getGeneralizations(st)));
      }
    }
  }

  // pair current literal as main literal with possible side literals
  // this results in any number of side literals
  if (InductionHelper::isInductionLiteral(literal))
  {
    res.emplace_back(SLQueryResult(literal, premise), vset<pair<Literal*,Clause*>>());
    while (itSides.hasNext()) {
      auto qr = itSides.next();
      if (InductionHelper::isInductionClause(qr.clause) && sideLitCondition(literal, premise, qr.literal, qr.clause)) {
        res.back().second.emplace(qr.literal, qr.clause);
      }
    }
  }
  // pair current literal as side literal with possible main literals
  // this results in only one side literal (the current)
  while (itMains.hasNext()) {
    auto qr = itMains.next();
    if (InductionHelper::isInductionClause(qr.clause) &&
        InductionHelper::isInductionLiteral(qr.literal) &&
        sideLitCondition(qr.literal, qr.clause, literal, premise)) {
      res.emplace_back(SLQueryResult(qr.literal, qr.clause), vset<pair<Literal*,Clause*>>());
      res.back().second.emplace(literal, premise);
    }
  }
  return res;
}

}