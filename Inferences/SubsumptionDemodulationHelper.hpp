#ifndef SUBSUMPTIONDEMODULATIONHELPER_HPP
#define SUBSUMPTIONDEMODULATIONHELPER_HPP

#include "Indexing/LiteralMiniIndex.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"


namespace Inferences {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;



/**
 * A binder that consists of two maps: a base and an overlay.
 * Lookup first checks the base map, then the overlay map.
 * New bindings are added to the overlay map.
 *
 * In FSD, the base bindings are extracted from the MLMatcher and correspond to the subsumption part,
 * while the overlay bindings are from the demodulation part (i.e., from
 * matching the lhs of the demodulation equality to the candidate term that
 * might be simplified).
 *
 * This class implements the Binder interface as described in Kernel/Matcher.hpp,
 * and the Applicator interface as described in Kernel/SubstHelper.hpp.
 */
class OverlayBinder
{
  public:
    using Var = unsigned int;
    using BindingsMap = v_unordered_map<Var, TermList>;

    OverlayBinder()
      : m_base(16)
      , m_overlay(16)
    { }

    /// Initializes the base bindings with the given argument
    explicit
    OverlayBinder(BindingsMap&& initialBindings)
      : m_base(std::move(initialBindings))
      , m_overlay(16)
    { }

    bool bind(Var var, TermList term)
    {
      // If the variable is already bound, it must be bound to the same term.
      auto base_it = m_base.find(var);
      if (base_it != m_base.end()) {
        return base_it->second == term;
      }
      else {
        auto res = m_overlay.insert({var, term});
        auto it = res.first;
        bool inserted = res.second;
        return inserted || (it->second == term);
      }
    }

    bool isBound(Var var) const
    {
      return m_base.find(var) != m_base.end()
        || m_overlay.find(var) != m_overlay.end();
    }

    void specVar(Var var, TermList term) const
    {
      ASSERTION_VIOLATION;
    }

    /// Clear all bindings
    void clear()
    {
      m_base.clear();
      m_overlay.clear();
    }

    /// Direct access to base bindings.
    /// The returned map may only be modified if the overlay map is empty!
    /// (this function is unfortunately necessary to be able to extract the base bindings from the MLMatcher without dynamic memory allocation)
    BindingsMap& base()
    {
      ASS(m_overlay.empty());
      return m_base;
    }

    /// Resets to base bindings
    void reset()
    {
      m_overlay.clear();
    }

    bool tryGetBinding(Var var, TermList& result) const
    {
      auto b_it = m_base.find(var);
      if (b_it != m_base.end()) {
        // var has base binding
        result = b_it->second;
        return true;
      } else {
        auto o_it = m_overlay.find(var);
        if (o_it != m_overlay.end()) {
          // var has overlay binding
          result = o_it->second;
          return true;
        } else {
          // var is unbound
          return false;
        }
      }
    }

    /// Makes objects of this class work as applicator for substitution
    /// (as defined in Kernel/SubstHelper.hpp)
    TermList apply(Var var) const
    {
      TermList result;
      if (tryGetBinding(var, result)) {
        return result;
      } else {
        // We should never access unbound variables
        // (NOTE: we should not return the variable itself here, as this creates a risk of mixing variables coming from different clauses)
        ASSERTION_VIOLATION;
      }
    }

    TermList applyTo(TermList t, bool noSharing = false) const
    {
      return SubstHelper::apply(t, *this, noSharing);
    }

    Literal* applyTo(Literal* l) const
    {
      return SubstHelper::apply(l, *this);
    }

    /// Like applyTo, but all unbound variables are shifted by unboundVarOffset
    TermList applyWithUnboundVariableOffsetTo(TermList t, Var unboundVarOffset, bool noSharing = false) const
    {
      UnboundVariableOffsetApplicator applicator(*this, unboundVarOffset);
      return SubstHelper::apply(t, applicator, noSharing);
    }

  public:
    class UnboundVariableOffsetApplicator
    {
      public:
        UnboundVariableOffsetApplicator(OverlayBinder const& binder, Var unboundVarOffset)
          : binder(binder), unboundVarOffset(unboundVarOffset)
        { }

        /// Does the same as OverlayBinder::apply, except for the case where the variable is not bound
        TermList apply(Var var) const
        {
          TermList result;
          if (binder.tryGetBinding(var, result)) {
            return result;
          } else {
            // No bindings? return the variable shifted by offset
            return TermList(var + unboundVarOffset, false);
          }
        }

      private:
        OverlayBinder const& binder;
        Var unboundVarOffset;
    };

  private:
    BindingsMap m_base;
    BindingsMap m_overlay;

    friend std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder);
};  // class OverlayBinder

std::ostream& operator<<(std::ostream& o, OverlayBinder const& binder);


/**
 * Stores an instance of the multi-literal matching problem.
 * Allows us to re-use the alts from subsumption for subsumption resolution.
 */
class ClauseMatches
{
  public:
    ClauseMatches(Clause* base, LiteralMiniIndex const& ixAlts);

    ~ClauseMatches();

    // Disallow copy
    ClauseMatches(ClauseMatches const&) = delete;
    ClauseMatches& operator=(ClauseMatches const&) = delete;

    // Default move is fine
    ClauseMatches(ClauseMatches&&) = default;
    ClauseMatches& operator=(ClauseMatches&&) = default;

    Clause* base() const { return m_base; }
    LiteralList const* const* alts() const { return m_alts.data(); }

    unsigned baseLitsWithoutAlts() const { return m_baseLitsWithoutAlts; }

    bool isSubsumptionPossible() const
    {
      // For subsumption, every base literal must have at least one alternative
      return m_baseLitsWithoutAlts == 0;
    }

    bool isSubsumptionDemodulationPossible() const
    {
      ASS_GE(m_baseLitsWithoutAlts, m_basePosEqsWithoutAlts);
      // Demodulation needs at least one positive equality
      if (m_basePosEqs == 0) {
        return false;
      }
      // If there are base literals without any suitable alternatives:
      // 1. If there is only one literal without alternative and it is a positive equality,
      //    then it might still be possible to get an FSD inference by choosing this literal
      //    as equality for demodulation.
      // 2. If there is a literal without alternative but it is not a positive equality,
      //    then it is impossible to get an FSD inference.
      // 3. If there are two literals without alternatives, then it is impossible as well.
      return m_baseLitsWithoutAlts == 0  // every base literal has alternatives
        || (m_baseLitsWithoutAlts == 1 && m_basePosEqsWithoutAlts == 1);  // case 1 in comment above
    }

  private:
    Clause* m_base;
    v_vector<LiteralList*> m_alts;
    unsigned m_basePosEqs;
    unsigned m_baseLitsWithoutAlts;
    unsigned m_basePosEqsWithoutAlts;
};  // class ClauseMatches


class SDHelper
{
  public:
    static bool checkForSubsumptionResolution(Clause* cl, ClauseMatches const& cm, Literal* resLit);
    static Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* resLit, Clause* mcl);

#if VDEBUG
    /// Returns true iff clause with literal lits1 is smaller than clause with literals lits2
    /// in the multiset extension of the given ordering.
    static bool clauseIsSmaller(Literal* const lits1[], unsigned n1, Literal* const lits2[], unsigned n2, Ordering const& ordering);
#endif
};


/**
 * Returns true iff termθ contains all variables that otherθ contains (possibly more).
 *
 * The substitution θ is given as an applicator, cf. class SubstHelper.
 * An applicator is an object with a method of the following signature:
 *    TermList apply(unsigned int var);
 */
template <typename Applicator>
bool termContainsAllVariablesOfOtherUnderSubst(TermList term, TermList other, Applicator const& applicator)
{
  CALL("termContainsAllVariablesOfOtherUnderSubst");

  static v_unordered_set<unsigned int> vars(16);
  vars.clear();

  static VariableIterator vit;
  static VariableIterator vit2;

  // collect term's vars after substitution
  vit.reset(term);
  while (vit.hasNext()) {
    TermList t = applicator.apply(vit.next().var());
    vit2.reset(t);
    while (vit2.hasNext()) {
      vars.insert(vit2.next().var());
    }
  }

  // check that all vars of other after substition have been collected
  vit.reset(other);
  while (vit.hasNext()) {
    TermList t = applicator.apply(vit.next().var());
    vit2.reset(t);
    while (vit2.hasNext()) {
      if (vars.find(vit2.next().var()) == vars.end()) {
#if VDEBUG
        {
          TermList termS = SubstHelper::apply(term, applicator, /* no sharing = */ true);
          TermList otherS = SubstHelper::apply(other, applicator, /* no sharing = */ true);
          ASS(!termS.containsAllVariablesOf(otherS));
          if (termS.isTerm()) { termS.term()->destroyNonShared(); }
          if (otherS.isTerm()) { otherS.term()->destroyNonShared(); }
        }
#endif
        return false;
      }
    }
  }

#if VDEBUG
  {
      TermList termS = SubstHelper::apply(term, applicator, /* no sharing = */ true);
      TermList otherS = SubstHelper::apply(other, applicator, /* no sharing = */ true);
      ASS(termS.containsAllVariablesOf(otherS));
      if (termS.isTerm()) { termS.term()->destroyNonShared(); }
      if (otherS.isTerm()) { otherS.term()->destroyNonShared(); }
  }
#endif
  return true;
}


};

#endif /* !SUBSUMPTIONDEMODULATIONHELPER_HPP */
