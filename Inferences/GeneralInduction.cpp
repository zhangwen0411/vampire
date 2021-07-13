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
        // (1) they contain some induction term
        // (2) they have either induction depth 0 or they contain some complex induction term
        vset<pair<Literal*, Clause*>> sidesFiltered;
        for (const auto& s : sides) {
          for (const auto& kv2 : kv.first.inductionTerms()) {
            if (s.first->containsSubterm(TermList(kv2.first)) && (!skolem(kv2.first) || !s.second->inference().inductionDepth())) {
              sidesFiltered.insert(s);
              break;
            }
          }
        }
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
          TermOccurrenceReplacement tr(kv.first.inductionTerms(), eg, main.literal);
          auto mainLitGen = tr.transformLit();
          ASS_NEQ(mainLitGen, main.literal);
          vvector<pair<Literal*, SLQueryResult>> sidesGeneralized;
          for (const auto& kv2 : sidesFiltered) {
            TermOccurrenceReplacement tr(kv.first.inductionTerms(), eg, kv2.first);
            auto sideLitGen = tr.transformLit();
            if (sideLitGen != kv2.first) {
              sidesGeneralized.push_back(make_pair(sideLitGen, SLQueryResult(kv2.first, kv2.second)));
            }
          }
          generateClauses(kv.first, mainLitGen, main, sidesGeneralized, res._clauses);
        }
      }
      for (const auto& schLit : schLits) {
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

void GeneralInduction::generateClauses(
  const Shell::InductionScheme& scheme,
  Literal* mainLit, const SLQueryResult& mainQuery,
  const vvector<pair<Literal*, SLQueryResult>>& sideLitQrPairs,
  ClauseStack& clauses)
{
  CALL("GeneralInduction::generateClauses");

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

  vvector<LiteralStack> lits(1);
  vmap<Literal*, vset<unsigned>> litToSkolemsMap;

  for (const auto& c : scheme.cases()) {
    vvector<LiteralStack> newLits;

    vset<unsigned> skIntroduced;
    auto sk = skolemizeCase(c, scheme.inductionTerms(), skIntroduced);
    auto newMainLit = SubstHelper::apply<Substitution>(mainLit, sk._step);
    for (auto st : lits) {
      st.push(newMainLit);
      newLits.push_back(st);
    }

    for (const auto& kv : sideLitQrPairs) {
      for (auto st : lits) {
        st.push(SubstHelper::apply<Substitution>(kv.first, sk._step));
        newLits.push_back(st);
      }
    }

    for (auto& r : sk._recursiveCalls) {
      auto newHypLit = Literal::complementaryLiteral(
        SubstHelper::apply<Substitution>(mainLit, r));
      for (auto st : lits) {
        st.push(newHypLit);
        for (const auto& kv : sideLitQrPairs) {
          st.push(Literal::complementaryLiteral(
            SubstHelper::apply<Substitution>(kv.first, r)));
        }
        newLits.push_back(st);
      }
      if (env.options->inductionHypRewriting() && mainLit->isEquality()) {
        litToSkolemsMap.insert(make_pair(newHypLit, vset<unsigned>()));
        litToSkolemsMap.insert(make_pair(newMainLit, vset<unsigned>()));
        for (const auto& fn : skIntroduced) {
          TermList t(Term::create(fn, 0, nullptr));
          if (newHypLit->containsSubterm(t)) {
            litToSkolemsMap.at(newHypLit).insert(fn);
            litToSkolemsMap.at(newMainLit).insert(fn);
          }
        }
      }
    }
    lits = newLits;
  }

  for (auto& st : lits) {
    st.push(Literal::complementaryLiteral(mainLit));
    for (const auto& kv : sideLitQrPairs) {
      st.push(Literal::complementaryLiteral(kv.first));
    }
  }

  ClauseStack temp;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,_rule);
  unsigned maxDepth = mainQuery.clause->inference().inductionDepth();
  for (const auto& kv : sideLitQrPairs) {
    maxDepth = max(maxDepth, kv.second.clause->inference().inductionDepth());
  }
  inf.setInductionDepth(maxDepth+1);
  for (const auto& st : lits) {
    temp.push(Clause::fromStack(st, inf));
  }
  for (const auto& kv : litToSkolemsMap) {
    for (auto& c : temp) {
      if (c->contains(kv.first)) {
        for (const auto& e : kv.second) {
          c->inference().addToInductionInfo(e);
        }
      }
    }
  }

  ClauseStack::Iterator cit(temp);
  RobSubstitution subst;
  if (!subst.match(TermList(mainLit), 0, TermList(mainQuery.literal), 1)) {
    ASS(mainLit->isEquality());
    // direct match did not succeed, so we match one literal with the other reversed
    ALWAYS(subst.match(*mainLit->nthArgument(0), 0, *mainQuery.literal->nthArgument(1), 1)
      && subst.match(*mainLit->nthArgument(1), 0, *mainQuery.literal->nthArgument(0), 1));
  }
  for (const auto& kv : sideLitQrPairs) {
    auto conclusion = kv.first;
    auto qr = kv.second;
    if (!subst.match(TermList(conclusion), 0, TermList(qr.literal), 1)) {
      ASS_REP(conclusion->isEquality() && qr.literal->isEquality(), conclusion->toString() + qr.literal->toString());
      // direct match did not succeed, so we match one literal with the other reversed
      ALWAYS(subst.match(*conclusion->nthArgument(0), 0, *qr.literal->nthArgument(1), 1)
        && subst.match(*conclusion->nthArgument(1), 0, *qr.literal->nthArgument(0), 1));
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
  while(cit.hasNext()){
    Clause* c = cit.next();
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

TermList mapVarsToSkolems(Substitution& subst, TermList t, TermList sort, vset<unsigned>& introducedSkolems) {
  DHMap<unsigned,TermList> varSorts;
  SortHelper::collectVariableSorts(t, sort, varSorts);

  auto it = varSorts.items();
  while (it.hasNext()) {
    auto v = it.next();
    TermList temp;
    if (!subst.findBinding(v.first, temp)) {
      auto fn = Skolem::addSkolemFunction(0, 0, nullptr, v.second);
      subst.bind(v.first, Term::create(fn, 0, nullptr));
      introducedSkolems.insert(fn);
    }
  }
  return SubstHelper::apply<Substitution>(t, subst);
}

InductionScheme::Case GeneralInduction::skolemizeCase(const InductionScheme::Case& c, const vmap<Term*, unsigned>& inductionTerms, vset<unsigned>& introducedSkolems)
{
  Substitution subst, step;
  TermList t;
  for (const auto& kv : inductionTerms) {
    if (c._step.findBinding(kv.second, t)) {
      auto sort = SortHelper::getResultSort(kv.first);
      step.bind(kv.second, mapVarsToSkolems(subst, t, sort, introducedSkolems));
    }
  }
  vvector<Substitution> recursiveCalls;
  for (const auto& recCall : c._recursiveCalls) {
    recursiveCalls.emplace_back();
    for (const auto& kv : inductionTerms) {
      if (recCall.findBinding(kv.second, t)) {
        auto sort = SortHelper::getResultSort(kv.first);
        recursiveCalls.back().bind(kv.second, mapVarsToSkolems(subst, t, sort, introducedSkolems));
      }
    }
  }
  return InductionScheme::Case(std::move(recursiveCalls), std::move(step));
}

void reserveBlanksForScheme(const InductionScheme& sch, DHMap<TermList, vvector<Term*>>& blanks)
{
  vmap<TermList, unsigned> srts;
  for (const auto& kv : sch.inductionTerms()) {
    TermList srt = env.signature->getFunction(kv.first->functor())->fnType()->result();
    auto res = srts.insert(make_pair(srt,1));
    if (!res.second) {
      res.first->second++;
    }
  }
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

  static DHMap<TermList, vvector<Term*>> blanks;
  reserveBlanksForScheme(sch, blanks);

  TermReplacement cr(blanks, sch.inductionTerms());
  res.first = cr.transform(mainLit);

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
  if (!_done.find(res.first)) {
    return false;
  }
  auto s = _done.get(res.first);
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
    ((!mainCl->inference().inductionDepth() && !sideCl->inference().inductionDepth()) ||
    (InductionHelper::isInductionLiteral(side, sideCl) &&
      InductionHelper::isInductionLiteral(main, mainCl) &&
      includes(mainSk.begin(), mainSk.end(), sideSk.begin(), sideSk.end()) && !main->isEquality()));
}

vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> GeneralInduction::selectMainSidePairs(Literal* literal, Clause* premise)
{
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> res;
  static const bool indmc = env.options->inductionMultiClause();

  TermQueryResultIterator it = TermQueryResultIterator::getEmpty();
  if (indmc) {
    SubtermIterator stit(literal);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (st.isTerm() && skolem(st.term())) {
        it = pvi(getConcatenatedIterator(it, _index->getGeneralizations(st)));
      }
    }
  }

  if (InductionHelper::isInductionLiteral(literal))
  {
    res.emplace_back(SLQueryResult(literal, premise), vset<pair<Literal*,Clause*>>());
    while (it.hasNext()) {
      auto qr = it.next();
      if (InductionHelper::isInductionClause(qr.clause) && sideLitCondition(literal, premise, qr.literal, qr.clause)) {
        res.back().second.emplace(qr.literal, qr.clause);
      }
    }
  } else {
    while (it.hasNext()) {
      auto qr = it.next();
      if (InductionHelper::isInductionClause(qr.clause) &&
          InductionHelper::isInductionLiteral(qr.literal) &&
          sideLitCondition(qr.literal, qr.clause, literal, premise)) {
        res.emplace_back(SLQueryResult(qr.literal, qr.clause), vset<pair<Literal*,Clause*>>());
        res.back().second.emplace(literal, premise);
      }
    }
  }
  return res;
}

}