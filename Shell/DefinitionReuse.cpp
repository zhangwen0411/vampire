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
 * @file DefinitionReuse.cpp
 * Defines definition-reuse policies, configured by an option
 */

#include "DefinitionReuse.hpp"
#include "Kernel/Formula.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include <iostream>

namespace Shell {

static DefinitionReusePolicy *make_policy()
{
  switch (env.options->definitionReusePolicy()) {
    case Options::DefinitionReusePolicy::NONE:
      return new NoDefinitionReuse();
    case Options::DefinitionReusePolicy::EXACT:
      return new ExactDefinitionReuse();
  }
}

DefinitionReusePolicy *DefinitionReusePolicy::instance()
{
  static DefinitionReusePolicy *instance = make_policy();
  return instance;
}

Term *ExactDefinitionReuse::get(Formula *f)
{
  return _map.get(f->toString(), nullptr);
}

void ExactDefinitionReuse::reuse(Formula *f, Term *d)
{
  _map.insert(f->toString(), d);
}

}; // namespace Shell