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
 * @file FnDefRewriting.cpp
 * Implements class FnDefRewriting.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"

#include "InductionHypothesisRewriting.hpp"
#include "InductionHelper.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;

ClauseIterator InductionHypothesisRewriting::generateClauses(Clause *premise)
{
  CALL("InductionHypothesisRewriting::generateClauses");
  ClauseIterator res = ClauseIterator::getEmpty();
  for (unsigned i = 0; i < premise->length(); i++) {
    res = pvi(getConcatenatedIterator(res, generateClauses((*premise)[i], premise)));
  }
  return res;
}

ClauseIterator InductionHypothesisRewriting::generateClauses(Literal* lit, Clause *premise)
{
  ClauseIterator res = ClauseIterator::getEmpty();
  if (!lit->isEquality()) {
    return res;
  }
  if (InductionHelper::isInductionLiteral(lit, premise)) {
    auto sk = InductionHelper::collectSkolems(lit, premise);
    TermIterator lhsi = EqHelper::getEqualityArgumentIterator(lit);
    while (lhsi.hasNext()) {
      TermList litarg = lhsi.next();
      if (lit->isNegative()) {
        NonVariableIterator sti(litarg.term(), true);
        while (sti.hasNext()) {
          auto t = sti.next();
          auto ts = _lhsIndex->getUnifications(t);
          while (ts.hasNext()) {
            auto qr = ts.next();
            if (!InductionHelper::isInductionLiteral(qr.literal, qr.clause)) {
              continue;
            }

            auto skOther = InductionHelper::collectSkolems(qr.literal, qr.clause);
            if (!includes(sk.begin(), sk.end(), skOther.begin(), skOther.end())) {
              continue;
            }
            res = pvi(getConcatenatedIterator(res,
              perform(skOther, premise, lit, litarg, t, qr.clause, qr.literal, qr.term, qr.substitution, true)));
          }
        }
      } else {
        auto ts = _stIndex->getUnifications(litarg);
        while (ts.hasNext()) {
          auto qr = ts.next();
          if (!InductionHelper::isInductionLiteral(qr.literal, qr.clause)) {
            continue;
          }

          auto skOther = InductionHelper::collectSkolems(qr.literal, qr.clause);
          if (!includes(skOther.begin(), skOther.end(), sk.begin(), sk.end())) {
            continue;
          }
          for (unsigned k = 0; k <= 1; k++) {
            auto side = *qr.literal->nthArgument(k);
            if (!side.containsSubterm(qr.term)) {
              continue;
            }
            res = pvi(getConcatenatedIterator(res,
              perform(sk, qr.clause, qr.literal, side, qr.term, premise, lit, litarg, qr.substitution, false)));
          }
        }
      }
    }
  }
  return res;
}

ClauseIterator InductionHypothesisRewriting::perform(const vset<unsigned>& sig,
    Clause *rwClause, Literal *rwLit, TermList rwSide, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionHypothesisRewriting::perform");
  // the rwClause may not be active as
  // it is from a demodulation index
  // if (rwClause->store() != Clause::ACTIVE) {
  //   return 0;
  // }
  ASS(eqClause->store() == Clause::ACTIVE);
  ClauseIterator res = ClauseIterator::getEmpty();

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return res;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList otherSide = EqHelper::getOtherEqualitySide(rwLit, rwSide);
  Ordering& ordering = _salg->getOrdering();
  // check that we are rewriting either against the order or the smaller side
  if (!Ordering::isGorGEorE(ordering.compare(tgtTerm,eqLHS))
    && !Ordering::isGorGEorE(ordering.compare(otherSide,rwSide))) {
    return res;
  }

  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);
  TermList rwSideS = subst->apply(rwSide, !eqIsResult);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);
  TermList rwSideSR(EqHelper::replace(rwSideS.term(), rwTermS, tgtTermS));
  if (rwSide == rwTerm) {
    rwSideSR = tgtTermS;
  }
  Stack<TermList> args;
  args.push(rwSideSR);
  args.push(EqHelper::getOtherEqualitySide(rwLitS, rwSideS));
  Literal *tgtLitS = Literal::create(rwLitS, args.begin());

  // cout << "HYP: " << *eqLit << endl
  //      << "SRC: " << eqLHS << endl
  //      << "TGT: " << tgtTerm << endl
  //      << "RWSIDE: " << rwSideS << endl
  //      << "TGTLIT: " << *tgtLitS << endl;

  if (EqHelper::isEqTautology(tgtLitS)) {
    return res;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::IH_REWRITING, rwClause, eqClause));
  Clause *newCl = new (newLength) Clause(newLength, inf);

  // static bool doSimS = env.options->simulatenousSuperposition();
  (*newCl)[0] = tgtLitS;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      // if (doSimS) {
      //   curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      // }
      curr = subst->apply(curr, !eqIsResult);

      if (EqHelper::isEqTautology(curr)) {
        newCl->destroy();
        return res;
      }

      (*newCl)[next++] = curr;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter = subst->apply(curr, eqIsResult);
        if (EqHelper::isEqTautology(currAfter)) {
          newCl->destroy();
          return res;
        }

        (*newCl)[next++] = currAfter;
      }
    }
  }

  newCl->setStore(Clause::ACTIVE);
  if (_splitter) {
    _splitter->onNewClause(newCl);
  }
  auto temp = _dupLitRemoval->simplify(newCl);
  if (temp != newCl) {
    if (_splitter) {
      _splitter->onNewClause(newCl);
    }
    newCl->setStore(Clause::NONE);
    newCl = temp;
    newCl->setStore(Clause::ACTIVE);
  }
  for (const auto& fn : sig) {
    newCl->inference().removeFromInductionInfo(fn);
  }
  res = pvi(getConcatenatedIterator(generateClauses(tgtLitS, newCl), _induction->generateClauses(newCl)));
  newCl->setStore(Clause::NONE);

  return res;
}
