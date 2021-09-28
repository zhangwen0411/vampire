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
#include "Kernel/FormulaUnit.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Shell/Rectify.hpp"
#include <iostream>

namespace Shell {

static NameReuse *make_policy(Options::NameReuse option)
{
  CALL("NameReuse::make_policy");
  switch (option) {
    case Options::NameReuse::NONE:
      return new NoNameReuse();
    case Options::NameReuse::EXACT:
      return new ExactNameReuse();
  }
}

NameReuse *NameReuse::skolemInstance()
{
  CALL("NameReuse::skolemInstance");
  static NameReuse *instance = make_policy(env.options->skolemReuse());
  return instance;
}

Formula *ExactNameReuse::normalise(Formula *f)
{
  CALL("ExactNameReuse::normalise");
  FormulaUnit *copy =
      new FormulaUnit(f, Inference(FromInput(UnitInputType::AXIOM)));
  FormulaUnit *rectified = Rectify::rectify(copy);
  return rectified->formula();
}

Term *ExactNameReuse::get(Formula *normalised)
{
  CALL("ExactNameReuse::get");
  return _map.get(normalised->toString(), nullptr);
}

void ExactNameReuse::put(Formula *normalised, Term *d)
{
  CALL("ExactNameReuse::put");
  _map.insert(normalised->toString(), d);
}

}; // namespace Shell