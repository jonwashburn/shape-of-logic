import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Verification
namespace UnitNormalizationZero

open IndisputableMonolith.Cost.FunctionalEquation
open Real

/-!
# Unit Normalization → Zero at Origin Certificate

This certificate packages the proof that if F(1) = 0, then G_F(0) = 0.

## Key Result

If F : ℝ → ℝ satisfies F(1) = 0, then G_F(0) = F(exp(0)) = F(1) = 0.

## Why this matters for the certificate chain

This result connects unit normalization in the multiplicative domain to the
log-coordinate representation:

1. **Multiplicative domain**: F(1) = 0 means the cost at "unity" is zero
   - No cost when there's no deviation from the reference point

2. **Log-coordinates**: G_F(0) = 0 means the log-coordinate cost at t = 0 is zero
   - The origin of log-coordinates (t = 0 ↔ x = exp(0) = 1) has zero cost

3. **Initial condition for ODE**: Combined with H = G + 1, this gives H(0) = 1,
   which is the initial condition for the ODE uniqueness theorem

This is a simple but crucial link in the chain:
  F(1) = 0 → G_F(0) = 0 → H(0) = 1 → ODE initial conditions

## Mathematical Content

The proof is immediate from the definitions:
  G_F(0) = F(exp(0)) = F(1) = 0
-/

structure UnitNormalizationZeroCert where
  deriving Repr

/-- Verification predicate: unit normalization F(1) = 0 implies G_F(0) = 0.

This certifies that the log-coordinate representation respects unit normalization. -/
@[simp] def UnitNormalizationZeroCert.verified (_c : UnitNormalizationZeroCert) : Prop :=
  ∀ (F : ℝ → ℝ), F 1 = 0 → G F 0 = 0

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem UnitNormalizationZeroCert.verified_any (c : UnitNormalizationZeroCert) :
    UnitNormalizationZeroCert.verified c := by
  intro F hUnit
  exact G_zero_of_unit F hUnit

end UnitNormalizationZero
end Verification
end IndisputableMonolith
