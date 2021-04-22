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
 * @file InequalityResolution.hpp
 * Defines class InequalityResolution
 *
 */

#ifndef __InequalityResolution__
#define __InequalityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/InequalityNormalizer.hpp"

namespace Indexing {


class InequalityResolutionIndex
: public TermIndex
{
public:
  CLASS_NAME(InequalityResolutionIndex);
  USE_ALLOCATOR(InequalityResolutionIndex);

  InequalityResolutionIndex(TermIndexingStructure* is, Ordering& ord, InequalityNormalizer norm)
    : TermIndex(is)
    , _ord(&ord)
    , _normalizer(std::move(norm)) {}

  InequalityNormalizer const& normalizer() const { return _normalizer; }
  Ordering* ord() const { return _ord; }
protected:
  void handleClause(Clause* c, bool adding);
private:
  template<class NumTraits> bool handleLiteral(Literal* lit, Clause* c, bool adding);

  Ordering* _ord;
  InequalityNormalizer _normalizer;
};
}


namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InequalityNormalization
: public ImmediateSimplificationEngine 
{
  InequalityNormalizer _normalizer;
public: 
  InequalityNormalization(Ordering& ord);
  CLASS_NAME(InequalityNormalization);
  USE_ALLOCATOR(InequalityNormalization);

  virtual Clause* simplify(Clause* cl) final override;
};

class InequalityResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InequalityResolution);
  USE_ALLOCATOR(InequalityResolution);

  InequalityResolution() 
    : _index(0)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

  /* 
   * maps (num1, num2) -> (k1, k2) 
   * s.t.  num1 * k1 = - num2 * k2
   */
  // TODO move this somewhere else
  template<class Numeral>
  static pair<Numeral,Numeral> computeFactors(Numeral num1, Numeral num2)
  { 
    ASS(num1 != Numeral(0))
    ASS(num2 != Numeral(0))
    // num1 * k1 = - num2 * k2
    // let k1 = 1
    // ==> num1 = - num2 * k2 ==> k2 = - num1 / num2
    return std::make_pair(Numeral(1), -(num1 / num2));
  }

  /* 
   * maps (num1, num2) -> (k1, k2) 
   * s.t.  num1 * k1 = - num2 * k2
   */
  static pair<IntegerConstantType,IntegerConstantType> computeFactors(IntegerConstantType num1, IntegerConstantType num2)
  { 
    ASS(num1 != IntegerConstantType(0))
    ASS(num2 != IntegerConstantType(0))
    // num1 * k1 = - num2 * k2
    // let k1 =   num2 / gcd(num1, num2)
    //     k2 = - num1 / gcd(num1, num2)
    // num1 * num2 / gcd(num1, num2) = - num2 * (- num1 / gcd(num1, num2))
    auto gcd = IntegerConstantType::gcd(num1, num2);
    ASS(gcd.divides(num1));
    ASS(gcd.divides(num2));
    return num1.isNegative() ? std::make_pair( num2.quotientE(gcd), -num1.quotientE(gcd))
                             : std::make_pair(-num2.quotientE(gcd),  num1.quotientE(gcd));
  }


  

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

  template<class NumTraits> static Stack<Monom<NumTraits>> maxTerms(InequalityLiteral<NumTraits> const& lit, Ordering* ord);
private:

  template<class NumTraits> ClauseIterator generateClauses(Clause* clause, Literal* lit) const;

  InequalityNormalizer const& normalizer() const { return _index->normalizer(); }
  Ordering* ord() const { return _index->ord(); }
  InequalityResolutionIndex* _index;
};

};

#endif /*__InequalityResolution__*/
