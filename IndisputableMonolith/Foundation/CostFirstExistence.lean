import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Cost-First Existence: Pre-Big-Bang Selection Principle

The pre-Big-Bang paper argues that existence is not posited but selected:
stable configurations are those with minimum recognition cost. This module
formalises the core structural claim:

**Cost-first selection principle:** A pattern `x > 0` "exists" in the
recognition sense iff `J(x) = 0`, i.e., iff `x = 1` (the cost minimum).
All other positive values carry strictly positive J-cost and are
transiently unstable under R̂ evolution.

This gives a clean RS definition of existence:
  RSExists(x) ↔ J(x) = 0 ↔ x = 1  (for x : ℝ, x > 0)

The origin of law from cost-minimisation:
- Laws are the unique J-minimising configurations of the recognition lattice.
- Physics emerges from the constraint "the universe minimises J".
- The pre-Big-Bang "era" is the pre-geometric cost landscape.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CostFirstExistence

open Cost

noncomputable section

/-- Recognition existence: `x` exists iff J(x) = 0. -/
def RSExists (x : ℝ) : Prop := Jcost x = 0

/-- RSExists iff x = 1 (the unique J-cost minimiser). -/
theorem rsExists_iff_one {x : ℝ} (hx : 0 < x) :
    RSExists x ↔ x = 1 := by
  unfold RSExists
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (Jcost_pos_of_ne_one x hx hne))
  · rintro rfl
    exact Jcost_unit0

/-- Non-existence costs more than zero. -/
theorem non_existence_has_positive_cost {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    0 < Jcost x :=
  Jcost_pos_of_ne_one x hx hne

/-- The unique "nothing" reference: cost is unbounded on (0,∞). -/
theorem divergence_at_zero_direction :
    ¬ ∃ (C : ℝ), ∀ (ε : ℝ), 0 < ε → Jcost ε ≤ C := by
  intro ⟨C, hC⟩
  -- Pick ε = 1/(2*(|C|+2)); then J(ε) > |C|+1 > C
  -- Actual proof: pick ε = 1/4, then J(1/4) = (1/4-1)²/(2·1/4) = (9/16)/(1/2) = 9/8
  -- That only bounds J away from C when C < 9/8.
  -- For large C, pick ε = 1/(C+2):
  -- J(1/(C+2)) = (1/(C+2)-1)²/(2/(C+2)) = (C+1)²/(C+2)²·(C+2)/2 = (C+1)²/(2(C+2))
  -- For C ≥ 0: (C+1)²/(2(C+2)) > C ↔ (C+1)² > 2C(C+2) = 2C²+4C ↔ C²+2C+1 > 2C²+4C ↔ 0 > C²+2C-1
  -- This fails for C ≥ 1. Need a better choice. Use ε = 1/(2C+4):
  -- J(1/(2C+4)) = (1/(2C+4)-1)²/(2/(2C+4)) = ((2C+3)/(2C+4))²·(2C+4)/2 = (2C+3)²/(2(2C+4))
  -- Compare with C: (2C+3)²/(2(2C+4)) > C ↔ (2C+3)² > 2C(2C+4) = 4C²+8C
  -- = 4C²+12C+9 > 4C²+8C ↔ 4C+9 > 0, which holds for C > -9/4.
  -- For C ≤ -3, J(ε) ≥ 0 > C since C < 0. Done by cases.
  -- Use J(1) = 0 to handle C < 0, and a direct computation for C ≥ 0
  by_cases hC_neg : C < 0
  · linarith [hC 1 one_pos, Jcost_unit0]
  push_neg at hC_neg  -- C ≥ 0
  -- J(1/(2C+4)) = (2C+3)²/(2(2C+4)) > C for C ≥ 0
  have h2C4 : (0 : ℝ) < 2 * C + 4 := by linarith
  have hε := hC (1 / (2 * C + 4)) (div_pos one_pos h2C4)
  have hJval : Jcost (1 / (2 * C + 4)) = (2 * C + 3) ^ 2 / (2 * (2 * C + 4)) := by
    rw [Jcost_eq_sq (by positivity)]
    field_simp
    ring
  rw [hJval] at hε
  have hnum : 0 ≤ (2 * C + 3) ^ 2 := sq_nonneg _
  -- (2C+3)²/(2(2C+4)) ≤ C ↔ (2C+3)² ≤ 2C(2C+4) = 4C²+8C
  -- But (2C+3)² = 4C²+12C+9 > 4C²+8C = 2C(2C+4) for C ≥ 0 (since 4C+9 > 0)
  have hrewrite : (2 * C + 3) ^ 2 / (2 * (2 * C + 4)) ≤ C ↔
      (2 * C + 3) ^ 2 ≤ C * (2 * (2 * C + 4)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * C + 4))]
  rw [hrewrite] at hε
  nlinarith [sq_nonneg (2 * C + 3)]

structure CostFirstExistenceCert where
  rsExists_iff : ∀ {x : ℝ}, 0 < x → (RSExists x ↔ x = 1)
  non_existence_costly :
    ∀ {x : ℝ}, 0 < x → x ≠ 1 → 0 < Jcost x
  nothing_diverges :
    ¬ ∃ (C : ℝ), ∀ (ε : ℝ), 0 < ε → Jcost ε ≤ C

/-- Cost-first existence certificate. -/
def costFirstExistenceCert : CostFirstExistenceCert where
  rsExists_iff := @rsExists_iff_one
  non_existence_costly := @non_existence_has_positive_cost
  nothing_diverges := divergence_at_zero_direction

end
end CostFirstExistence
end Foundation
end IndisputableMonolith
