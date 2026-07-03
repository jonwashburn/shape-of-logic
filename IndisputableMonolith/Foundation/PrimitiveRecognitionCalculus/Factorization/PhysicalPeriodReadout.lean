/-
  PrimitiveRecognitionCalculus/Factorization/PhysicalPeriodReadout.lean

  Door B interface only. This file states what a physical or quantum-like
  period readout must certify before it can be used for factorization. It does
  not posit that such a readout exists.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.RecognitionLowerBound

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A certified period readout for a base `a` modulo `N`. -/
structure CertifiedPeriodReadout (N : DistinctionNat) (hN : N ≠ zero)
    (a : DistinctionNat) : Type where
  exponent : DistinctionNat
  witness : PeriodWitness N hN a exponent

/-- A certified factor readout is stronger than a period readout: it exposes a
proper divisor certified by the period data. This is the minimal Lean-facing
interface a physical period-finder must satisfy. -/
structure CertifiedFactorReadout (N : DistinctionNat) (hN : N ≠ zero)
    (a : DistinctionNat) : Type where
  exponent : DistinctionNat
  factor_witness : ProperDivisorFromPeriod N hN a exponent

theorem certifiedFactorReadout_to_nontrivialFactorization
    {N a : DistinctionNat} {hN : N ≠ zero}
    (r : CertifiedFactorReadout N hN a) :
    nontrivialFactorization N := by
  exact period_divisor_to_nontrivialFactorization r.factor_witness

/-- The interface separates period certification from a factorization theorem.
The device, algorithm, or physical substrate must supply the certificate. -/
structure PhysicalPeriodReadoutCertificate : Prop where
  certified_factor_readout_extracts_factorization :
    ∀ {N a : DistinctionNat} {hN : N ≠ zero},
      CertifiedFactorReadout N hN a → nontrivialFactorization N

theorem physical_period_readout_certificate :
    PhysicalPeriodReadoutCertificate where
  certified_factor_readout_extracts_factorization := by
    intro N a hN r
    exact certifiedFactorReadout_to_nontrivialFactorization r

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
