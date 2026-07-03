import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation

/-!
# Direct RCL theorem for operative positive-ratio comparison

This module gives the paper-facing "operative comparison" wrapper around the
already-formalised translation theorem.  It isolates the finite pairwise
polynomial closure hypothesis as the precise regularity condition needed to
force the Recognition Composition Law family, and it also proves the strict
bi-affine counted-once subcase directly.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open Real
open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-- An operative positive-ratio comparison is a continuous, nontrivial
comparison operator satisfying identity, symmetric single-valued comparison,
and scale invariance on positive arguments. -/
structure OperativePositiveRatioComparison (C : ComparisonOperator) : Prop where
  identity : Identity C
  non_contradiction : NonContradiction C
  continuous : ExcludedMiddle C
  scale_invariant : ScaleInvariant C
  non_trivial : NonTrivial C

/-- Finite pairwise polynomial closure is the polynomial route-independence
condition from the Level-1 logic-as-functional-equation module. -/
def FinitePairwisePolynomialClosure (C : ComparisonOperator) : Prop :=
  RouteIndependence C

/-- Scale invariance descends a two-argument comparison to a cost on the
positive ratio of the arguments. -/
theorem operative_descends_to_ratio
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C) :
    ∀ x y : ℝ, 0 < x → 0 < y → C x y = derivedCost C (x / y) := by
  intro x y hx hy
  unfold derivedCost
  have hy_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy
  have hscale := hOp.scale_invariant x y y⁻¹ hx hy hy_inv_pos
  have hleft : y⁻¹ * x = x / y := by
    rw [div_eq_mul_inv, mul_comm]
  have hright : y⁻¹ * y = 1 := by
    exact inv_mul_cancel₀ (ne_of_gt hy)
  calc
    C x y = C (y⁻¹ * x) (y⁻¹ * y) := hscale.symm
    _ = C (x / y) 1 := by rw [hleft, hright]

/-- Operative comparisons have reciprocal-symmetric derived costs. -/
theorem operative_derived_cost_symmetric
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C) :
    IsSymmetric (derivedCost C) :=
  non_contradiction_and_scale_imply_reciprocal C
    hOp.non_contradiction hOp.scale_invariant

/-- Package an operative comparison plus finite pairwise closure as the
`SatisfiesLawsOfLogic` structure used by the Level-1 theorem. -/
theorem operative_to_laws_of_logic
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (hFinite : FinitePairwisePolynomialClosure C) :
    SatisfiesLawsOfLogic C where
  identity := hOp.identity
  non_contradiction := hOp.non_contradiction
  excluded_middle := hOp.continuous
  scale_invariant := hOp.scale_invariant
  route_independence := hFinite
  non_trivial := hOp.non_trivial

/-- **RCL as the finite pairwise polynomial algebra of positive-ratio comparison.**

Any operative positive-ratio comparison with finite pairwise polynomial
closure has a derived cost satisfying the Recognition Composition Law family.
This theorem uses the existing d'Alembert inevitability theorem, since its
hypothesis is the broader polynomial-degree-two closure condition.
-/
theorem rcl_polynomial_closure_theorem
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (hFinite : FinitePairwisePolynomialClosure C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2 * u + 2 * v + c * u * v) := by
  exact RCL_is_unique_functional_form_of_logic C
    (operative_to_laws_of_logic C hOp hFinite)

/-- **Direct counted-once algebra.**

If the combiner is already known to be bi-affine,
`P u v = a + b*u + c*v + d*u*v`, then identity, non-triviality and
composition with the identity force `a = 0`, `b = 2`, and `c = 2`.
This is the self-contained algebraic proof used for the counted-once
subcase, independent of the d'Alembert inevitability theorem. -/
theorem rcl_direct_theorem
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (P : ℝ → ℝ → ℝ)
    (a b c d : ℝ)
    (hP : ∀ u v, P u v = a + b * u + c * v + d * u * v)
    (hSym : ∀ u v, P u v = P v u)
    (hCons : HasMultiplicativeConsistency (derivedCost C) P) :
    ∃ c0 : ℝ, ∀ u v, P u v = 2 * u + 2 * v + c0 * u * v := by
  have hF1 : derivedCost C 1 = 0 := by
    simpa [derivedCost] using hOp.identity 1 zero_lt_one
  rcases hOp.non_trivial with ⟨x0, hx0_pos, hx0_ne⟩
  let t := derivedCost C x0
  have ht_ne : t ≠ 0 := hx0_ne

  have hCons11 := hCons 1 1 zero_lt_one zero_lt_one
  have hC11 : C 1 1 = 0 := hOp.identity 1 zero_lt_one
  have ha_zero : a = 0 := by
    have hp00 : P 0 0 = a := by
      simpa using hP 0 0
    have hzero : P 0 0 = 0 := by
      have htmp : 0 = P 0 0 := by
        simpa [derivedCost, hC11] using hCons11
      exact htmp.symm
    exact hp00 ▸ hzero

  have hCons_x1 := hCons x0 1 hx0_pos zero_lt_one
  have hb_two : b = 2 := by
    have hmain : t + t = a + b * t := by
      simpa [derivedCost, t, hC11, hP] using hCons_x1
    have hprod : (2 - b) * t = 0 := by
      nlinarith [hmain, ha_zero]
    have hfactor : 2 - b = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_right ht_ne
    linarith

  have hc_two : c = 2 := by
    have hsym_t0 : P 0 t = P t 0 := hSym 0 t
    have hleft : P 0 t = c * t := by
      simpa [ha_zero] using hP 0 t
    have hright : P t 0 = b * t := by
      simpa [ha_zero] using hP t 0
    have hct : c * t = b * t := by
      simpa [hleft, hright] using hsym_t0
    have hct' : c * t = 2 * t := by
      simpa [hb_two] using hct
    have hprod : (c - 2) * t = 0 := by
      nlinarith
    have hfactor : c - 2 = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_right ht_ne
    linarith

  refine ⟨d, ?_⟩
  intro u v
  calc
    P u v = a + b * u + c * v + d * u * v := hP u v
    _ = 2 * u + 2 * v + d * u * v := by
      rw [ha_zero, hb_two, hc_two]
      ring

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
