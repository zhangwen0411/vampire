/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "FunctionDefinitionDiscovery.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "InductionPreprocessor.hpp"

using namespace Kernel;

namespace Shell {

bool isConstructorTerm(TermList t)
{
  CALL("isConstructorTerm");

  // vars are allowed even if they are
  // not of a term algebra sort
  if (t.isVar()) {
    return true;
  }

  auto term = t.term();
  if (!env.signature->isTermAlgebraSort(SortHelper::getResultSort(term))
    || !isTermAlgebraCons(t)) {
    return false;
  }

  Term::Iterator it(term);
  while (it.hasNext()) {
    auto arg = it.next();
    if (!isConstructorTerm(arg)) {
      return false;
    }
  }
  return true;
}

bool isHeader(TermList t)
{
  CALL("isHeader");

  if (t.isVar() || isTermAlgebraCons(t)) {
    return false;
  }

  Term::Iterator it(t.term());
  while (it.hasNext()) {
    auto arg = it.next();
    if (!isConstructorTerm(arg)) {
      return false;
    }
  }
  return true;
}

void FunctionDefinitionDiscovery::addBestConfiguration()
{
  CALL("FunctionDefinitionDiscovery::addBestConfiguration");

  auto n = foundFunctionDefinitions.size();
  vvector<vset<unsigned>> nonWellFounded(n);
  vvector<vset<unsigned>> nonWellDefined(n);
  vvector<vmap<unsigned, vvector<vvector<TermList>>>> missingCases(n);
  unsigned i = 0;
  auto fnDefHandler = env.signature->getFnDefHandler();
  for (auto& fndefs : foundFunctionDefinitions) {
    for (auto& kv : fndefs) {
      if (fnDefHandler->hasInductionTemplate(kv.first, true /* trueFun */)) {
        continue;
      }
      if (!kv.second.first.checkWellFoundedness())
      {
        nonWellFounded[i].insert(kv.first);
      }
      ALWAYS(missingCases[i].insert(make_pair(kv.first, vvector<vvector<TermList>>())).second);
      if (!kv.second.first.checkWellDefinedness(missingCases[i].at(kv.first)))
      {
        nonWellDefined[i].insert(kv.first);
      }
    }
    i++;
  }
  // calculate score: non well-founded templates count more
  unsigned best = nonWellFounded[0].size() * 5 + nonWellDefined[0].size();
  unsigned best_i = 0;
  for (unsigned i = 1; i < n; i++) {
    auto curr = nonWellFounded[i].size() * 5 + nonWellDefined[i].size();
    if (curr < best) {
      best = curr;
      best_i = i;
    }
  }
  auto& fndefs = foundFunctionDefinitions[best_i];
  if (best > 0) {
    env.beginOutput();
    env.out() << "% Warning: all function orientations contain non well-founded"
      " or non well-defined sets, best score " << best << " with "
      << nonWellFounded[best_i].size() << " non well-founded and "
      << nonWellDefined[best_i].size() << " non well-defined " << endl;
    env.endOutput();
  }
  for (auto& kv : fndefs) {
    if (kv.second.first.checkUsefulness()) {
      if (nonWellDefined[best_i].count(kv.first)
        && missingCases[best_i].at(kv.first).size() > 0)
      {
        kv.second.first.addMissingCases(missingCases[best_i].at(kv.first));
      }
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] function definition has been discovered: "
                  << env.signature->functionName(kv.first) << endl;
        if (!nonWellFounded[best_i].count(kv.first)) {
          env.out() << " with induction template: " << kv.second.first << endl;
        }
        env.endOutput();
      }
      if (!nonWellFounded[best_i].count(kv.first)) {
        for (auto& t : kv.second.second) {
          fnDefHandler->handleClause(get<0>(t), get<1>(t), get<2>(t)); 
        }
      } else {
        env.beginOutput();
        env.out() << "% Warning: non-well-founded template is discarded: " << kv.second.first << endl;
        env.endOutput();
      }
    }
  }
  for (auto& kv : foundPredicateDefinitions) {
    if (env.signature->getFnDefHandler()->hasInductionTemplate(kv.first, false /* trueFun */)) {
      continue;
    }
    if (kv.second.first.checkUsefulness()) {
      vvector<vvector<TermList>> missingCases;
      if (!kv.second.first.checkWellDefinedness(missingCases)
          && missingCases.size() > 0)
      {
        kv.second.first.addMissingCases(missingCases);
      }
      if (kv.second.first.checkWellFoundedness()) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] predicate definition has been discovered: "
                    << env.signature->predicateName(kv.first)
                    << ", with induction template: " << kv.second.first << endl;
          env.endOutput();
        }
        for (auto& t : kv.second.second) {
          fnDefHandler->handleClause(t.first, t.second, false /* reversed */); 
        }
      }
    }
  }
}

void FunctionDefinitionDiscovery::findPossibleDefinitions(Clause* cl)
{
  CALL("FunctionDefinitionDiscovery::findPossibleRecursiveDefinitions");

  for(unsigned i = 0; i < cl->length(); i++) {
    Literal* lit = (*cl)[i];
    if (lit->isEquality()) {
      auto lhs = *lit->nthArgument(0);
      auto rhs = *lit->nthArgument(1);
      auto processFn = [](TermList header, TermList body, InductionTemplate& templ) {
        if (!isHeader(header)) {
          return false;
        }
        auto fn = header.term()->functor();
        vvector<TermList> recursiveCalls;
        InductionPreprocessor::processCase(fn, body, recursiveCalls);
        templ.addBranch(std::move(recursiveCalls), std::move(header));
        // we have to check that the found relations
        // are decreasing, e.g. f(c(x),c(y))=f(x,y)
        // is checked both ways but only one is decreasing
        return templ.checkWellFoundedness();
      };
      InductionTemplate tlhs;
      auto succlhs = processFn(lhs, rhs, tlhs) && lhs.containsAllVariablesOf(rhs);
      InductionTemplate trhs;
      auto succrhs = processFn(rhs, lhs, trhs) && rhs.containsAllVariablesOf(lhs);

      auto temp = foundFunctionDefinitions;
      if (succlhs || succrhs) {
        foundFunctionDefinitions.clear();
      }
      auto insertFn = [this, temp, i, cl](TermList lhs, TermList rhs, InductionTemplate templ, bool reversed) {
        for (auto fndefs : temp) {
          auto it = fndefs.find(lhs.term()->functor());
          if (it == fndefs.end()) {
            it = fndefs.insert(make_pair(lhs.term()->functor(),
              make_pair(templ, vvector<tuple<Clause*,unsigned,bool>>()))).first;
          } else {
            for (const auto& b : templ.branches()) {
              vvector<TermList> recursiveCalls = b._recursiveCalls;
              TermList header = b._header;
              it->second.first.addBranch(std::move(recursiveCalls), std::move(header));
            }
          }
          it->second.second.push_back(make_tuple(cl, i, reversed));
          foundFunctionDefinitions.push_back(fndefs);
        }
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] Equality " << lhs << "=" << rhs << " is probably a function definition axiom" << endl;
          env.endOutput();
        }
      };
      if (succlhs)
      {
        insertFn(lhs, rhs, tlhs, false);
      }
      if (succrhs)
      {
        insertFn(rhs, lhs, trhs, true);
      }
    } else {
      if (isHeader(TermList(lit))) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] Literal " << *lit << " is probably a predicate definition axiom" << endl;
          env.endOutput();
        }
        auto pred = lit->functor();
        vvector<TermList> recCalls;
        for(unsigned j = 0; j < cl->length(); j++) {
          Literal* curr = (*cl)[i];
          if (lit != curr) {
            if (!curr->isEquality() && curr->functor() == pred) {
              recCalls.push_back(TermList(curr));
            }
          }
        }
        auto it = foundPredicateDefinitions.find(pred);
        if (it == foundPredicateDefinitions.end()) {
          it = foundPredicateDefinitions.emplace(pred, make_pair(InductionTemplate(), vvector<pair<Clause*,unsigned>>())).first;
        }
        it->second.first.addBranch(std::move(recCalls), TermList(lit));
        it->second.second.push_back(make_pair(cl, i));
      }
    }
  }
}

} // Shell
