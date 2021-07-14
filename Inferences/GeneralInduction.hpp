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
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __GeneralInduction__
#define __GeneralInduction__

#include <cmath>
#include <bitset>

#include "Forwards.hpp"

#include "Indexing/TermIndex.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/InductionSchemeGenerator.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

class NoGeneralizationIterator
  : public IteratorCore<OccurrenceMap>
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  NoGeneralizationIterator(const OccurrenceMap& occ)
    : _occ(occ), _hasNext(true) {}

  inline bool hasNext() override
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next() override
  {
    CALL("NoGeneralizationIterator::next()");
    ASS(_hasNext);

    auto it = _occ.begin();
    while (it != _occ.end()) {
      it->second.set_bits();
      it++;
    }
    _hasNext = false;
    return _occ;
  }

  inline vstring toString()
  {
    vstringstream str;
    for (const auto& kv : _occ) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString() << " ";
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
};

class GeneralizationIterator
  : public IteratorCore<OccurrenceMap>
{
public:
  DECL_ELEMENT_TYPE(OccurrenceMap);

  GeneralizationIterator(const OccurrenceMap& occ, bool heuristic, bool hasFixOccurrences)
    : _occ(occ), _hasNext(true), _heuristic(heuristic), _hasFixOccurrences(hasFixOccurrences)
  {
    if (!_hasFixOccurrences) {
      // eliminate all 0s
      for (auto& o : _occ) {
        if (!o.second.num_set_bits()) {
          ALWAYS(o.second.next());
        }
      }
    }
  }

  inline bool hasNext() override
  {
    return _hasNext;
  }

  inline OWN_ELEMENT_TYPE next() override
  {
    CALL("GeneralizationIterator::next()");
    ASS(_hasNext);

    auto temp = _occ;
    auto it = _occ.begin();
    while (it != _occ.end()) {
      if (it->second.next()) {
        // heuristic gives only active occurrences
        // then and all occurrences, so we set all bits
        // immediately after returning only the actives
        if (_heuristic) {
          it->second.set_bits();
        }
        break;
      }
      it->second.reset_bits();
      if (!_hasFixOccurrences) {
        // eliminate all 0s as in ctor
        if (!it->second.num_set_bits()) {
          ALWAYS(it->second.next());
        }
      }
      it++;
    }
    if (it == _occ.end()) {
      _hasNext = false;
    }
    return temp;
  }

  inline vstring toString()
  {
    vstringstream str;
    for (const auto& kv : _occ) {
      str << *kv.first.first << ", " << kv.first.second
          << ": " << kv.second.toString() << " ";
    }
    return str.str();
  }

private:
  OccurrenceMap _occ;
  bool _hasNext;
  bool _heuristic;
  bool _hasFixOccurrences;
};

class GeneralInduction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(GeneralInduction);
  USE_ALLOCATOR(GeneralInduction);

  GeneralInduction(const vvector<InductionSchemeGenerator*> gen, InferenceRule rule)
    : _gen(gen),
      _splitter(0),
      _rule(rule) {}

  ~GeneralInduction() {
    for (auto& gen : _gen) {
      delete gen;
    }
  }

  ClauseIterator generateClauses(Clause* premise) override;
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  class InductionClauseIterator
    : public ClauseIterator
  {
  public:
    InductionClauseIterator() = default;
    DECL_ELEMENT_TYPE(Clause*);

    inline bool hasNext() { return _clauses.isNonEmpty(); }
    inline OWN_ELEMENT_TYPE next() { 
      return _clauses.pop();
    }

    Stack<Clause*> _clauses;
  };

  void process(InductionClauseIterator& it, Clause* premise, Literal* literal);
  void generateClauses(
    const Shell::InductionScheme& scheme,
    Literal* mainLit, const SLQueryResult& mainQuery,
    const vvector<pair<Literal*,SLQueryResult>>& sideLitQrPairs,
    ClauseStack& clauses);
  InductionScheme::Case skolemizeCase(
    const InductionScheme::Case& c,
    const vmap<Term*, unsigned>& inductionTerms,
    vset<unsigned>& introducedSkolems);
  bool alreadyDone(Literal* mainLit, const vset<pair<Literal*,Clause*>>& sides,
    const InductionScheme& sch, pair<Literal*,vset<Literal*>>& res);
  vvector<pair<SLQueryResult, vset<pair<Literal*,Clause*>>>> selectMainSidePairs(Literal* literal, Clause* premise);
  Literal* replaceLit(unsigned& var, const vmap<TermList,TermList>& r, const OccurrenceMap& occurrences, Literal* lit,
    const vset<pair<Literal*,Clause*>>& sideLits, const vvector<LiteralStack>& lits, vvector<LiteralStack>& newLits, bool hypothesis = false);

  vvector<InductionSchemeGenerator*> _gen;
  Splitter* _splitter;
  InferenceRule _rule;
  DHMap<Literal*, vset<Literal*>> _done;
  TermIndex* _index;
};

}

#endif /*__GeneralInduction__*/
