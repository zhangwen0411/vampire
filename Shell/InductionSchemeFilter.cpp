/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionSchemeFilter.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

// bool checkContainsRecCall(const vmap<TermList, TermList>& recCall1, const vmap<TermList, TermList>& recCall2, const vmap<TermList, TermList>& step)
// {
//   for (auto kv : step) {
//     auto it1 = recCall1.find(kv.first);
//     auto it2 = recCall2.find(kv.first);
//     if (it1 != recCall1.end() && it2 != recCall2.end()) {
//       // the second is strengthened or the first is not strengthened and they are not the same
//       if (it1->second != it2->second && (!kv.second.containsSubterm(it2->second) || kv.second.containsSubterm(it1->second))) {
//         return false;
//       }
//     } else if (it2 != recCall2.end() || it1 != recCall1.end()) {
//       // the second cannot be strengthened
//       return false;
//     }
//   }
//   return true;
// }

bool beforeMergeCheck(const InductionScheme& sch1, const InductionScheme& sch2) {
  // If one of the induction terms from sch2 contains
  // one from sch1, it means that those subterms are also
  // in active positions and we lose some structure
  // of sch1 if we discard it because of subsumption
  for (const auto& kv1 : sch1.inductionTerms()) {
    auto t1 = kv1.first;
    for (const auto& kv2 : sch2.inductionTerms()) {
      auto t2 = kv2.first;
      if (t1 != t2 && (t2->containsSubterm(TermList(t1)) || t1->containsSubterm(TermList(t2)))) {
        return false;
      }
    }
  }
  return true;
}

// bool createMergedCase(const InductionScheme::Case& case1, const InductionScheme::Case& case2,
//   const vset<TermList>& combinedInductionTerms, InductionScheme::Case& res)
// {
//   Substitution step;
//   RobSubstitution subst;
//   auto repr1 = InductionScheme::createRepresentingTerm(combinedInductionTerms, case1._step);
//   auto repr2 = InductionScheme::createRepresentingTerm(combinedInductionTerms, case2._step);
//   if (!subst.unify(repr1, 0, repr2, 1)) {
//     return false;
//   }
//   auto repr = subst.apply(repr1, 0);
//   Term::Iterator it(repr.term());
//   for (const auto& indTerm : combinedInductionTerms) {
//     step.insert(make_pair(indTerm, it.next()));
//   }
//   vvector<vmap<TermList, TermList>> recCalls;
//   auto recCallFn = [&combinedInductionTerms, &recCalls, &subst](const InductionScheme::Case& c, unsigned bank) {
//     for (const auto& recCall : c._recursiveCalls) {
//       auto reprrc = InductionScheme::createRepresentingTerm(combinedInductionTerms, recCall);
//       reprrc = subst.apply(reprrc, bank);
//       recCalls.emplace_back();
//       Term::Iterator it(reprrc.term());
//       for (const auto& indTerm : combinedInductionTerms) {
//         recCalls.back().insert(make_pair(indTerm, it.next()));
//       }
//     }
//   };
//   recCallFn(case1, 0);
//   recCallFn(case2, 1);
//   for (unsigned i = 0; i < recCalls.size(); i++) {
//     for (unsigned j = i+1; j < recCalls.size();) {
//       if (checkContainsRecCall(recCalls[j], recCalls[i], step)) {
//         recCalls[j] = recCalls.back();
//         recCalls.pop_back();
//       } else {
//         j++;
//       }
//     }
//   }

//   res = InductionScheme::Case(std::move(recCalls), std::move(step));
//   return true;
// }

// bool InductionSchemeFilter::mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res) {
//   // copy original schemes in case we fail and we modified them
//   return false;
//   InductionScheme sch1copy = sch1;
//   InductionScheme sch2copy = sch2;
//   // if (!sch1copy.checkWellFoundedness() || !sch2copy.checkWellFoundedness()) {
//   //   return false;
//   // }

//   vset<TermList> indTerms = sch1.inductionTerms();
//   if (!includes(indTerms.begin(), indTerms.end(),
//       sch2.inductionTerms().begin(), sch2.inductionTerms().end()) &&
//       !includes(sch2.inductionTerms().begin(), sch2.inductionTerms().end(),
//       indTerms.begin(), indTerms.end())) {
//     return false;
//   }
//   indTerms.insert(sch2.inductionTerms().begin(), sch2.inductionTerms().end());

//   for (const auto& case1 : sch1copy.cases()) {
//     for (const auto& case2 : sch2copy.cases()) {
//       InductionScheme::Case c;
//       if (createMergedCase(case1, case2, indTerms, c, var)) {
//         res.addCase(std::move(c));
//       }
//     }
//   }

//   if (!res.finalize()) {
//     if (env.options->showInduction()) {
//       env.beginOutput();
//       env.out() << "[Induction] induction scheme is not well-founded: " << endl
//         << res << endl << "combined from schemes: " << endl
//         << "1: " << sch1 << endl << "2: " << sch2 << endl;
//       env.endOutput();
//     }
//     return false;
//   }
//   if(env.options->showInduction()){
//     env.beginOutput();
//     env.out() << "[Induction] induction scheme " << sch1
//               << " and induction scheme " << sch2
//               << " are merged into:" << endl << res << endl;
//     env.endOutput();
//   }

//   return true;
// }

void InductionSchemeFilter::filter(vvector<InductionScheme>& schemes, const OccurrenceMap& actOccMaps)
{
  CALL("InductionSchemeFilter::filter");

  static const bool filterC = env.options->inductionOnComplexTermsHeuristic();
  if (filterC) {
    filterComplex(schemes, actOccMaps);
  }

  for (unsigned i = 0; i < schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < schemes.size();) {

      if (!beforeMergeCheck(schemes[i], schemes[j])) {
        j++;
        continue;
      }

      // InductionScheme merged;
      if (checkContainment(schemes[j], schemes[i])) {
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
      }
      else if (checkContainment(schemes[i], schemes[j])) {
        subsumed = true;
        break;
      // }
      // else if (mergeSchemes(schemes[j], schemes[i], merged)) {
      //   schemes[j] = std::move(schemes.back());
      //   schemes.pop_back();
      //   schemes[i] = merged;
      //   break;
      } else {
        j++;
      }
    }
    if (subsumed) {
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

void InductionSchemeFilter::filterComplex(vvector<InductionScheme>& schemes, const OccurrenceMap& occMap)
{
  for (unsigned i = 0; i < schemes.size();) {
    bool filter = false;
    for (const auto& kv : schemes[i].inductionTerms()) {
      if (env.signature->getFunction(kv.first->functor())->skolem()) {
        continue;
      }
      unsigned occ = 0;
      for (const auto& kv2 : occMap) {
        if (kv2.first.second == kv.first) {
          occ += kv2.second.num_bits();
        }
      }
      if (occ == 1) {
        filter = true;
        break;
      }
    }
    if (filter) {
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "scheme inducting on complex terms filtered out " << schemes[i] << endl;
        env.endOutput();
      }
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

/**
 * Checks whether all cases of sch1 are contained by some case of sch2
 */
bool InductionSchemeFilter::checkContainment(const InductionScheme& sch1, const InductionScheme& sch2)
{
  CALL("InductionSchemeFilter::checkContainment");

  if (sch1.inductionTerms() != sch2.inductionTerms()) {
    return false;
  }

  for (const auto& case1 : sch1.cases()) {
    if (case1._recursiveCalls.empty()) {
      continue;
    }
    bool foundStep = false;
    for (const auto& case2 : sch2.cases()) {
      if (case2._recursiveCalls.empty()) {
        continue;
      }

      if (case2.contains(case1, sch1.inductionTerms(), sch2.inductionTerms())) {
        foundStep = true;
        break;
      }
    }
    if (!foundStep) {
      return false;
    }
  }
  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] induction scheme " << sch1
              << " is subsumed by " << sch2 << endl;
    env.endOutput();
  }
  return true;
}

} // Shell
