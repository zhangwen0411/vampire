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
 * @file Induction.cpp
 * Implements class Induction.
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

#include "GeneralInduction.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Lib;
using namespace Shell;

ClauseIterator GeneralInduction::generateClauses(Clause* premise)
{
  CALL("GeneralInduction::generateClauses");

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal = (kind == Options::InductionChoice::GOAL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static unsigned maxD = env.options->maxInductionDepth();
  static bool unitOnly = env.options->inductionUnitOnly();

  // auto res = ClauseIterator::getEmpty();
  InductionClauseIterator res;
  if((!unitOnly || premise->length()==1) && 
     (all || ( (goal || goal_plus) && premise->derivedFromGoal())) &&
     (maxD == 0 || premise->inference().inductionDepth() < maxD)
    )
  {
    for(unsigned i=0;i<premise->length();i++){
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

  for (const auto& kv : pairs) {
    const auto& main = kv.first;
    const auto& sides = kv.second;
    static vvector<pair<InductionScheme, OccurrenceMap>> schOccMap;
    schOccMap.clear();
    RecursionInductionSchemeGenerator gen;
    gen.generate(main, sides, schOccMap);
    vvector<pair<Literal*, vset<Literal*>>> schLits;
    for (const auto& kv : schOccMap) {
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
      static const bool heuristic = env.options->inductionGenHeur();
      GeneralizationIterator g(kv.second, heuristic);
      while (g.hasNext()) {
        auto eg = g.next();
        TermOccurrenceReplacement tr(kv.first.inductionTerms(), eg, main.literal);
        auto mainLitGen = tr.transformLit();
        ASS(mainLitGen != main.literal);
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
      _done.insert(schLit.first, schLit.second);
    }
  }
}

void GeneralInduction::attach(SaturationAlgorithm* salg)
{
  CALL("GeneralInduction::attach");

  GeneratingInferenceEngine::attach(salg);
  _splitter=_salg->getSplitter();
  _index = static_cast<DemodulationSubtermIndex *>(
      _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE));
}

void GeneralInduction::detach()
{
  CALL("GeneralInduction::detach");

  _index = 0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
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

  if(env.options->showInduction()){
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
  vmap<Literal*, Literal*> hypToConcMap;

  for (const auto& c : scheme.cases()) {
    vvector<LiteralStack> newLits;

    auto sk = skolemizeCase(c, scheme.inductionTerms());
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
      if (env.options->inductionHypRewriting()) {
        hypToConcMap.insert(make_pair(newHypLit, newMainLit));
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
  for (const auto& kv : hypToConcMap) {
    auto h = Hash::hash(kv);
    for (auto& c : temp) {
      if (c->contains(kv.first)) {
        c->markInductionLiteral(h, kv.first);
      }
      if (c->contains(kv.second)) {
        c->markInductionLiteral(h, kv.second);
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
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << c->toString() << endl;
      env.endOutput();
    }
    clauses.push(c);
  }
  env.statistics->induction++;
}

TermList mapVarsToSkolems(Substitution& subst, TermList t, TermList sort) {
  DHMap<unsigned,TermList> varSorts;
  SortHelper::collectVariableSorts(t, sort, varSorts);

  auto it = varSorts.items();
  while (it.hasNext()) {
    auto v = it.next();
    TermList temp;
    if (!subst.findBinding(v.first, temp)) {
      subst.bind(v.first, Term::create(
        Skolem::addSkolemFunction(0, 0, nullptr, v.second), 0, nullptr));
    }
  }
  return SubstHelper::apply<Substitution>(t, subst);
}

InductionScheme::Case GeneralInduction::skolemizeCase(const InductionScheme::Case& c, const vmap<Term*, unsigned>& inductionTerms)
{
  Substitution subst, step;
  TermList t;
  for (const auto& kv : inductionTerms) {
    if (c._step.findBinding(kv.second, t)) {
      auto sort = SortHelper::getResultSort(kv.first);
      step.bind(kv.second, mapVarsToSkolems(subst, t, sort));
    }
  }
  vvector<Substitution> recursiveCalls;
  for (const auto& recCall : c._recursiveCalls) {
    recursiveCalls.emplace_back();
    for (const auto& kv : inductionTerms) {
      if (recCall.findBinding(kv.second, t)) {
        auto sort = SortHelper::getResultSort(kv.first);
        recursiveCalls.back().bind(kv.second, mapVarsToSkolems(subst, t, sort));
      }
    }
  }
  return InductionScheme::Case(std::move(recursiveCalls), std::move(step));
}

vmap<TermList, TermList> createBlanksForScheme(const InductionScheme& sch, DHMap<pair<TermList, unsigned>, TermList>& blanks)
{
  vmap<TermList, unsigned> srts;
  vmap<TermList, TermList> replacements;
  for (const auto& kv : sch.inductionTerms()) {
    TermList srt = env.signature->getFunction(kv.first->functor())->fnType()->result();
    auto it = srts.find(srt);
    if (it == srts.end()) {
      it = srts.insert(make_pair(srt,0)).first;
    } else {
      it->second++;
    }
    const auto p = make_pair(srt, it->second);
    if (!blanks.find(p)) {
      unsigned fresh = env.signature->addFreshFunction(0,"blank",to_string(it->second).c_str());
      env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
      TermList blank = TermList(Term::createConstant(fresh));
      blanks.insert(p,blank);
    }
    replacements.insert(make_pair(kv.first, blanks.get(p)));
  }
  return replacements;
}

bool GeneralInduction::alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
  const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res)
{
  CALL("GeneralInduction::alreadyDone");

  static DHMap<pair<TermList, unsigned>, TermList> blanks;
  auto replacements = createBlanksForScheme(sch, blanks);

  TermReplacement cr(replacements);
  res.first = cr.transform(mainLit);

  for (const auto& kv : sides) {
    res.second.insert(cr.transform(kv.first));
  }
  // TODO(mhajdu): the reason we check this is to avoid
  // "induction loops" when we induct on the step immediately
  // after creating it. This means we usually want to exclude
  // schemes with complex terms, but this is an ugly workaround
  bool containsComplex = true;
  for (const auto& kv : sch.inductionTerms()) {
    if (skolem(kv.first)) {
      containsComplex = false;
      break;
    }
  }
  if (!_done.find(res.first) || !containsComplex) {
    return false;
  }
  auto s = _done.get(res.first);
  if (includes(s.begin(), s.end(), res.second.begin(), res.second.end())) {
    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] already inducted on " << *mainLit << " in " << *res.first << " form" << endl;
      env.endOutput();
    }
    return true;
  }
  return false;
}

inline bool mainLitCondition(Literal* literal) {
  static bool negOnly = env.options->inductionNegOnly();
  return (!negOnly || literal->isNegative() || 
      (theory->isInterpretedPredicate(literal) && theory->isInequality(theory->interpretPredicate(literal)))
    ) && literal->ground();
}

inline bool sideLitCondition(Literal* main, Clause* mainCl, Literal* side, Clause* sideCl) {
  vset<unsigned> sig, sigOther;
  return side->ground() &&
    env.options->inductionMultiClause() &&
    main != side &&
    mainCl != sideCl &&
    ((!mainCl->inference().inductionDepth() && !sideCl->inference().inductionDepth()) ||
    (sideCl->isInductionLiteral(side, sigOther) &&
      mainCl->isInductionLiteral(main, sig) &&
      includes(sig.begin(), sig.end(), sigOther.begin(), sigOther.end()) && !main->isEquality()));
}

vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> GeneralInduction::selectMainSidePairs(Literal* literal, Clause* premise)
{
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> res;

  TermQueryResultIterator it = TermQueryResultIterator::getEmpty();
  SubtermIterator stit(literal);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (st.isTerm() && skolem(st.term())) {
      it = pvi(getConcatenatedIterator(it, _index->getGeneralizations(st)));
    }
  }

  if (mainLitCondition(literal))
  {
    res.emplace_back(SLQueryResult(literal, premise), vset<pair<Literal*,Clause*>>());
    while (it.hasNext()) {
      auto qr = it.next();
      if (qr.clause->store() == Clause::ACTIVE && sideLitCondition(literal, premise, qr.literal, qr.clause)) {
        res.back().second.emplace(qr.literal, qr.clause);
      }
    }
  } else {
    while (it.hasNext()) {
      auto qr = it.next();
      if (qr.clause->store() == Clause::ACTIVE && mainLitCondition(qr.literal) && sideLitCondition(qr.literal, qr.clause, literal, premise)) {
        res.emplace_back(SLQueryResult(qr.literal, qr.clause), vset<pair<Literal*,Clause*>>());
        res.back().second.emplace(literal, premise);
      }
    }
  }
  return res;
}

}