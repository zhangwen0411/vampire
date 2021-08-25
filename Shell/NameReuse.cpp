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
 * @file NameReuse.cpp
 * Defines definition-reuse policies, configured by an option
 */

#include "NameReuse.hpp"
#include "Kernel/Formula.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include <iostream>

namespace Shell {

static NameReuse *make_policy(Options::NameReuse option)
{
  switch (option) {
    case Options::NameReuse::NONE:
      return new NoNameReuse();
    case Options::NameReuse::EXACT:
      return new ExactNameReuse();
  }
}

NameReuse *NameReuse::skolemInstance()
{
  static NameReuse *instance = make_policy(env.options->skolemReuse());
  return instance;
}

Term *ExactNameReuse::get(Formula *f)
{
  return _map.get(f->toString(), nullptr);
}

void ExactNameReuse::reuse(Formula *f, Term *d)
{
  _map.insert(f->toString(), d);
}

}; // namespace Shell