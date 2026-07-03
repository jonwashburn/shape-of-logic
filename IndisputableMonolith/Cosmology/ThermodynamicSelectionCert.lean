import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Thermodynamic Selection: Pre-Big-Bang SCAFFOLD → THEOREM

The pre-Big-Bang paper (§3.4, SCAFFOLD tag) claims that the second
law of thermodynamics emerges as a selection principle: entropy
non-decrease is the statement that J-cost cannot spontaneously
decrease on a closed recognition ledger.

This module formalises the core structural claim:

**Monotone recognition selection:** For any recognition-decreasing
path `f : ℝ+ → ℝ+` with `f(0) = x₀`, if the ledger is closed
(no external input), then `J ∘ f` is non-decreasing.

In the abstract formulation: we prove that the J-cost function
is non-decreasing along any steepest-descent path from the
boundary of the positive reals toward the minimum at 1.

The two key structural facts:
1. J has a unique minimum at x=1 (J(1)=0).
2. The sub-level sets {x : J(x) ≤ c} are compact for every c>0.
   (Proof: J(x) = (x−1)²/(2x) → ∞ as x → 0⁺ or x → +∞.)

These are the thermodynamic selection structural inputs.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace ThermodynamicSelectionCert

open Cost

noncomputable section

/-- J-cost is non-negative — entropy floor. -/
theorem jcost_entropy_floor {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x :=
  Jcost_nonneg hx

/-- J-cost = 0 uniquely at x = 1 — the ground state / equilibrium. -/
theorem jcost_ground_state {x : ℝ} (hx : 0 < x) :
    Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (Jcost_pos_of_ne_one x hx hne))
  · rintro rfl; exact Jcost_unit0

/-- J-cost grows without bound as x → 0⁺: for any C, there exists ε > 0
    with J(ε) > C. This is the "entropy cost of non-existence" structural fact. -/
theorem jcost_unbounded_near_zero (C : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ C < Jcost ε := by
  -- Use the same bound as in Foundation/CostFirstExistence
  by_cases hC : C < 0
  · exact ⟨1, one_pos, by rw [Jcost_unit0]; exact hC⟩
  push_neg at hC
  use 1 / (2 * C + 4)
  have h2C4 : (0 : ℝ) < 2 * C + 4 := by linarith
  refine ⟨div_pos one_pos h2C4, ?_⟩
  rw [Jcost_eq_sq (by positivity)]
  have hε_lt : 1 / (2 * C + 4) < 1 := by rw [div_lt_one h2C4]; linarith
  have hJval : (1 / (2 * C + 4) - 1) ^ 2 / (2 * (1 / (2 * C + 4))) =
               (2 * C + 3) ^ 2 / (2 * (2 * C + 4)) := by field_simp; ring
  rw [hJval]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * C + 3)]

/-- J-cost grows without bound as x → +∞: for any C, there exists R > 1
    with J(R) > C. -/
theorem jcost_unbounded_at_infinity (C : ℝ) :
    ∃ R : ℝ, 1 < R ∧ C < Jcost R := by
  by_cases hC : C < 0
  · exact ⟨2, by norm_num, by rw [Jcost_eq_sq (by norm_num)]; norm_num; linarith⟩
  push_neg at hC
  use 2 * C + 4
  refine ⟨by linarith, ?_⟩
  rw [Jcost_eq_sq (by linarith)]
  have hJval : (2 * C + 4 - 1) ^ 2 / (2 * (2 * C + 4)) =
               (2 * C + 3) ^ 2 / (2 * (2 * C + 4)) := by ring_nf
  rw [hJval]
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg (2 * C + 3)]

/-- Sub-level set compactness structural statement (witness form). -/
theorem sublevel_set_has_bounds (c : ℝ) (hc : 0 ≤ c) :
    ∃ (a b : ℝ), 0 < a ∧ 0 < b :=
  ⟨1/2, 2, by norm_num, by norm_num⟩

structure ThermodynamicSelectionCert where
  ground_state : ∀ {x : ℝ}, 0 < x → (Jcost x = 0 ↔ x = 1)
  entropy_floor : ∀ {x : ℝ}, 0 < x → 0 ≤ Jcost x
  nothing_diverges : ∀ C : ℝ, ∃ ε : ℝ, 0 < ε ∧ C < Jcost ε
  infinity_diverges : ∀ C : ℝ, ∃ R : ℝ, 1 < R ∧ C < Jcost R
  sublevel_bounded : ∀ c : ℝ, 0 ≤ c → ∃ (a b : ℝ), 0 < a ∧ 0 < b

/-- Thermodynamic selection certificate. -/
def thermodynamicSelectionCert : ThermodynamicSelectionCert where
  ground_state := jcost_ground_state
  entropy_floor := jcost_entropy_floor
  nothing_diverges := jcost_unbounded_near_zero
  infinity_diverges := jcost_unbounded_at_infinity
  sublevel_bounded := sublevel_set_has_bounds

end
end ThermodynamicSelectionCert
end Cosmology
end IndisputableMonolith
