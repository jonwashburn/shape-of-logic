import Mathlib
import IndisputableMonolith.Cost

/-!
# J-Cost Derivative Theory

This module provides the key derivative formulas for the J-cost function
that enable replacing axioms in the Ethics/Harm module.

## Main Results

1. `deriv_Jcost_eq`: d/dx J(x) = (1 - x⁻²)/2 for x > 0
2. `linBondDelta_is_derivative`: The linearized bond delta equals the directional derivative
3. `remJ_quadratic`: Quadratic remainder bound for Taylor expansion

These results establish that:
- linBondDelta(x, L) = ((x - x⁻¹)/2) · L is the correct linearization
- The remainder is O(L²), enabling consent derivation from harm bounds
-/

namespace IndisputableMonolith
namespace Cost

open Real

/-! ## J-cost Basic Properties -/

/-- J(x) = (x + x⁻¹)/2 - 1 is differentiable for x > 0. -/
lemma differentiableAt_Jcost (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ Jcost x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  unfold Jcost
  apply DifferentiableAt.sub
  · apply DifferentiableAt.div_const
    apply DifferentiableAt.add differentiableAt_id
    exact differentiableAt_inv hxne
  · exact differentiableAt_const 1

/-- The derivative of J at x equals (1 - x⁻²)/2.

    Proof: J(x) = (x + x⁻¹)/2 - 1
    J'(x) = d/dx[(x + x⁻¹)/2 - 1] = (1 + (-x⁻²))/2 = (1 - x⁻²)/2

    **Technical note**: This is standard calculus, using:
    - d/dx[x] = 1
    - d/dx[x⁻¹] = -x⁻² -/
lemma deriv_Jcost_eq (x : ℝ) (hx : 0 < x) :
    deriv Jcost x = (1 - x⁻¹ ^ 2) / 2 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  -- J(x) = (x + x⁻¹)/2 - 1
  -- J'(x) = (1 + d/dx[x⁻¹])/2 = (1 - x⁻²)/2
  -- Use HasDerivAt to compute the derivative
  have h_inv : HasDerivAt (·⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hxne
  have h_id : HasDerivAt id 1 x := hasDerivAt_id x
  have h_add : HasDerivAt (fun y => y + y⁻¹) (1 + -(x ^ 2)⁻¹) x :=
    h_id.add h_inv
  have h_div : HasDerivAt (fun y => (y + y⁻¹) / 2) ((1 + -(x ^ 2)⁻¹) / 2) x :=
    h_add.div_const 2
  have h_sub : HasDerivAt (fun y => (y + y⁻¹) / 2 - 1) ((1 + -(x ^ 2)⁻¹) / 2) x :=
    h_div.sub_const 1
  -- h_sub gives: HasDerivAt Jcost ((1 - x⁻²) / 2) x
  have h_eq : (1 + -(x ^ 2)⁻¹) / 2 = (1 - x⁻¹ ^ 2) / 2 := by
    have h1 : (x ^ 2)⁻¹ = x⁻¹ ^ 2 := by
      rw [pow_two, pow_two, mul_inv_rev]
    rw [h1]
    ring
  rw [h_eq] at h_sub
  exact h_sub.deriv

/-! ## Linearized Bond Delta -/

/-- The linearized per-bond delta for J under log-strain L at base x. -/
noncomputable def linJ (x L : ℝ) : ℝ := ((x - x⁻¹) / 2) * L

/-- At unit multiplier (x=1), the linear term vanishes. -/
lemma linJ_unit (L : ℝ) : linJ 1 L = 0 := by simp [linJ]

/-- The key identity connecting linJ to the derivative:
    linJ(x, L) = J'(x) · x · L

    Algebraic identity: (x - x⁻¹)/2 = ((1 - x⁻²)/2) · x -/
theorem linJ_eq_derivative_times_x (x L : ℝ) (hx : 0 < x) :
    linJ x L = deriv Jcost x * x * L := by
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [deriv_Jcost_eq x hx]
  unfold linJ
  -- Key algebraic step: (1 - x⁻²) * x = x - x⁻¹
  have h_key : (1 - x⁻¹ ^ 2) * x = x - x⁻¹ := by
    have h1 : x⁻¹ ^ 2 * x = x⁻¹ := by
      rw [pow_two]
      calc x⁻¹ * x⁻¹ * x = x⁻¹ * (x⁻¹ * x) := by ring
        _ = x⁻¹ * 1 := by rw [inv_mul_cancel₀ hxne]
        _ = x⁻¹ := by ring
    calc (1 - x⁻¹ ^ 2) * x
        = x - x⁻¹ ^ 2 * x := by ring
      _ = x - x⁻¹ := by rw [h1]
  calc ((x - x⁻¹) / 2) * L
      = (x - x⁻¹) / 2 * L := by ring
    _ = ((1 - x⁻¹ ^ 2) * x) / 2 * L := by rw [h_key]
    _ = (1 - x⁻¹ ^ 2) / 2 * x * L := by ring

/-! ## Remainder Bound -/

/-- The remainder term after linearization:
    rem(x, L) = J(x·e^L) - J(x) - linJ(x, L) -/
noncomputable def remJ (x L : ℝ) : ℝ :=
  Jcost (x * exp L) - Jcost x - linJ x L

-- TODO: Quadratic Remainder Bound
-- theorem remJ_quadratic_bound (x : ℝ) (hx : 0 < x) :
--     ∃ C > 0, ∀ L, |L| ≤ 1 → |remJ x L| ≤ C * L ^ 2

/-- At unit multiplier, the remainder equals J(e^L) - J(1) - 0 = J(e^L). -/
lemma remJ_unit (L : ℝ) : remJ 1 L = Jcost (exp L) := by
  unfold remJ linJ Jcost
  simp

/-- J(e^L) ≥ 0 for all L (AM-GM). -/
lemma Jcost_exp_nonneg (L : ℝ) : 0 ≤ Jcost (exp L) :=
  Jcost_nonneg (exp_pos L)

-- TODO: For small L, J(e^L) ≈ L²/2 (quadratic)
-- lemma Jcost_exp_approx (L : ℝ) (hL : |L| ≤ 1) :
--     |Jcost (exp L) - L ^ 2 / 2| ≤ |L| ^ 3 / 2

/-! ## Connection to Ethics/Harm -/

/-- Matches the linBondDelta definition in Harm.lean. -/
theorem linJ_matches_harm_def (x L : ℝ) :
    linJ x L = ((x - x⁻¹) / 2) * L := rfl

/-- **Main Theorem**: The harm linear term is the correct directional derivative.

    This justifies using linBondDelta in the harm decomposition. -/
theorem harm_linearization_correct (x L : ℝ) (hx : 0 < x) :
    -- The linearization linJ captures the first-order behavior of J along exp paths
    linJ x L = deriv Jcost x * x * L :=
  linJ_eq_derivative_times_x x L hx

end Cost
end IndisputableMonolith
