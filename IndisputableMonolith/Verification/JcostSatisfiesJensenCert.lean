import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace Verification
namespace JcostSatisfiesJensen

open IndisputableMonolith.Cost

/-!
# Jcost Satisfies JensenSketch Certificate

This certificate closes the T5 uniqueness loop by proving that **Jcost itself**
satisfies the `JensenSketch` interface requirements.

## Why this matters

The T5 uniqueness theorem (`T5UniqueCert`) states:
> Any function F satisfying `JensenSketch` equals `Jcost` on (0, ∞).

But this is conditional on F satisfying `JensenSketch`. This certificate proves:
> `Jcost` satisfies all `JensenSketch` requirements.

Together, these establish:
1. If F satisfies JensenSketch, then F = Jcost (T5 uniqueness)
2. Jcost satisfies JensenSketch requirements (this certificate)
3. Therefore, Jcost is THE unique cost function satisfying these axioms

## JensenSketch Requirements

The `JensenSketch` class requires:
1. **Symmetry**: F(x) = F(1/x) for x > 0
2. **Unit normalization**: F(1) = 0
3. **Axis upper bound**: F(exp t) ≤ J(exp t) for all t
4. **Axis lower bound**: J(exp t) ≤ F(exp t) for all t

For Jcost, requirements 3-4 are trivially satisfied (equality holds by `rfl`),
and 1-2 are proven from the explicit formula J(x) = (x + x⁻¹)/2 - 1.

## Proof

The proof is definitional: Jcost's symmetry and unit normalization are
algebraically verified, and the axis bounds are reflexive equalities.
-/

structure JcostSatisfiesJensenCert where
  deriving Repr

/-- Verification predicate: Jcost satisfies all JensenSketch requirements.

This certifies all four JensenSketch requirements for Jcost:
1. Jcost(x) = Jcost(1/x) for x > 0 (symmetry)
2. Jcost(1) = 0 (unit normalization)
3. Jcost(exp t) ≤ Jcost(exp t) for all t (axis upper - trivial)
4. Jcost(exp t) ≤ Jcost(exp t) for all t (axis lower - trivial)
-/
@[simp] def JcostSatisfiesJensenCert.verified (_c : JcostSatisfiesJensenCert) : Prop :=
  -- Jcost satisfies all JensenSketch requirements
  (∀ x : ℝ, 0 < x → Jcost x = Jcost x⁻¹) ∧
  (Jcost 1 = 0) ∧
  (∀ t : ℝ, Jcost (Real.exp t) ≤ Jcost (Real.exp t)) ∧
  (∀ t : ℝ, Jcost (Real.exp t) ≤ Jcost (Real.exp t))

/-- Top-level theorem: the certificate verifies.

This proves Jcost satisfies JensenSketch requirements, closing the T5 uniqueness loop. -/
@[simp] theorem JcostSatisfiesJensenCert.verified_any (c : JcostSatisfiesJensenCert) :
    JcostSatisfiesJensenCert.verified c := by
  refine ⟨?symm, ?unit, ?upper, ?lower⟩
  · -- Symmetry: Jcost(x) = Jcost(1/x)
    intro x hx
    exact Jcost_symm hx
  · -- Unit normalization: Jcost(1) = 0
    exact Jcost_unit0
  · -- Axis upper bound (trivial equality)
    intro t
    exact le_refl _
  · -- Axis lower bound (trivial equality)
    intro t
    exact le_refl _

/-- The Jcost instance can be explicitly constructed from the verified properties. -/
def jcost_jensen_sketch : JensenSketch Jcost :=
  { symmetric := fun hx => Jcost_symm hx
  , unit0 := Jcost_unit0
  , axis_upper := fun _ => le_refl _
  , axis_lower := fun _ => le_refl _ }

end JcostSatisfiesJensen
end Verification
end IndisputableMonolith
