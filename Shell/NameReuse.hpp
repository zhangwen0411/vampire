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

#ifndef __NameReuse__
#define __NameReuse__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Abstract base class: reuse "definition" terms used in place of formulae
 * Use for Skolemisation, naming, possibly others.
 */
class NameReuse {
public:
  // singleton: look at env.options and return a suitable policy for...
  // skolems
  static NameReuse *skolemInstance();

  // normalise `f` in some way to use as a key: saves recomputing it later
  virtual Formula *normalise(Formula *f) = 0;

  // try and reuse a definition for `normalised`: nullptr if not seen before
  virtual Term *get(Formula *normalised) = 0;

  // remember that we've used a definition term `d` for `normalised`
  virtual void put(Formula *normalised, Term *d) = 0;

  // do we use formulae at all? - only false for NoNameReuse
  virtual bool requiresFormula() { return true; };
};

/**
 * do not attempt to reuse definitions
 */
class NoNameReuse : public NameReuse {
public:
  CLASS_NAME(NoNameReuse)
  USE_ALLOCATOR(NoNameReuse)
  inline Formula *normalise(Formula *f) override { return nullptr; }
  inline Term *get(Formula *normalised) override { return nullptr; }
  inline void put(Formula *normalised, Term *d) override {}
  inline bool requiresFormula() override { return false; }
};

/**
 * reuse definitions if they match exactly
 */
class ExactNameReuse : public NameReuse {
public:
  CLASS_NAME(ExactNameReuse)
  USE_ALLOCATOR(ExactNameReuse)
  Formula *normalise(Formula *f) override;
  Term *get(Formula *f) override;
  void put(Formula *f, Term *d) override;

private:
  DHMap<vstring, Term *> _map;
};

} // namespace Shell

#endif