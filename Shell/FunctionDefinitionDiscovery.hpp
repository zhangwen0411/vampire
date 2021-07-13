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
 * @file FunctionDefinitionDiscovery.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __FunctionDefinitionDiscovery__
#define __FunctionDefinitionDiscovery__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Kernel/Problem.hpp"
#include "Lib/STL.hpp"

#include "InductionPreprocessor.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

class FunctionDefinitionDiscovery {
public:
  FunctionDefinitionDiscovery() : foundFunctionDefinitions(1) {}

  void preprocess(const Problem& prb) {
    UnitList::Iterator it(prb.units());
    while (it.hasNext()) {
      auto unit = it.next();
      if (!unit->isClause()){
        continue;
      }

      findPossibleDefinitions(unit->asClause());
    }
    addBestConfiguration();
  }
  void findPossibleDefinitions(Clause* cl);
  void addBestConfiguration();

private:
  vvector<vmap<unsigned, pair<InductionTemplate, vvector<tuple<Clause*,unsigned,bool>>>>> foundFunctionDefinitions;
  vmap<unsigned, pair<InductionTemplate, vvector<pair<Clause*,unsigned>>>> foundPredicateDefinitions;
};

} // Shell

#endif
