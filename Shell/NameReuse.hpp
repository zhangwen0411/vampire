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

  // try and reuse a definition for `f`: nullptr if not seen before or reuse failed
  virtual Term *get(Formula *f) = 0;

  // remember that we've used a definition term `d` for `f`
  virtual void reuse(Formula *f, Term *d) = 0;

  // do we use formulae at all? - only false for NoNameReuse
  virtual bool requiresFormula() { return true; };

  // do formulae need rectifying to be re-used?
  virtual bool requiresRectification() = 0;
};

/**
 * do not attempt to reuse definitions
 */
class NoNameReuse : public NameReuse {
public:
  CLASS_NAME(NoNameReuse)
  USE_ALLOCATOR(NoNameReuse)
  inline Term *get(Formula *f) override { return nullptr; }
  inline void reuse(Formula *f, Term *d) override {}
  inline bool requiresFormula() override { return false; }
  inline bool requiresRectification() override { return false; }
};

/**
 * reuse definitions if they match exactly
 */
class ExactNameReuse : public NameReuse {
public:
  CLASS_NAME(ExactNameReuse)
  USE_ALLOCATOR(ExactNameReuse)
  Term *get(Formula *f) override;
  void reuse(Formula *f, Term *d) override;
  inline bool requiresRectification() override { return true; }

private:
  DHMap<vstring, Term *> _map;
};

} // namespace Shell

#endif