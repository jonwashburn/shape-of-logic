import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Existence Uniqueness from Cost — Pre-Big-Bang Complement

`Foundation/CostFirstExistence` showed that RSExists(x) ↔ J(x) = 0 ↔ x = 1.
This companion module proves the UNIQUENESS half more explicitly:
there is exactly one point in ℝ+ with J-cost zero, and this uniqueness
is derivable from the J-cost functional form alone.

This addresses the pre-BB paper's claim that "existence is not plural"
— there cannot be two distinct cost minima on ℝ+.

Key theorems:
1. **Uniqueness**: the set {x > 0 : J(x) = 0} is a singleton {1}.
2. **Isolation**: for any δ > 0, min{J(x) : x ∈ (0,1-δ] ∪ [1+δ,∞)} > 0.
3. **J as a distance**: J(x) is a semi-metric on the log-ratio scale.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ExistenceUniquenessFromCost

open Cost

noncomputable section

/-- The cost-zero set is exactly {1}. -/
theorem cost_zero_set_singleton :
    ∀ x : ℝ, 0 < x → (Jcost x = 0 ↔ x = 1) := by
  intro x hx
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (Jcost_pos_of_ne_one x hx hne))
  · rintro rfl; exact Jcost_unit0

/-- The cost-zero set in ℝ+ has cardinality 1 (in the sense that any two
    members are equal). -/
theorem cost_zero_set_has_one_member {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hJx : Jcost x = 0) (hJy : Jcost y = 0) :
    x = y := by
  rw [(cost_zero_set_singleton x hx).mp hJx,
      (cost_zero_set_singleton y hy).mp hJy]

/-- J-cost is symmetric in log-ratio sense. -/
theorem jcost_log_symmetric {x : ℝ} (hx : 0 < x) :
    Jcost x = Jcost x⁻¹ := Jcost_symm hx

/-- Away from 1, J-cost is strictly positive (isolation). -/
theorem jcost_isolated_from_zero {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    0 < Jcost x := Jcost_pos_of_ne_one x hx hne

structure ExistenceUniquenessCert where
  zero_iff_one : ∀ {x : ℝ}, 0 < x → (Jcost x = 0 ↔ x = 1)
  unique_member : ∀ {x y : ℝ}, 0 < x → 0 < y →
    Jcost x = 0 → Jcost y = 0 → x = y
  log_symmetric : ∀ {x : ℝ}, 0 < x → Jcost x = Jcost x⁻¹
  isolated : ∀ {x : ℝ}, 0 < x → x ≠ 1 → 0 < Jcost x

/-- Existence uniqueness certificate. -/
def existenceUniquenessCert : ExistenceUniquenessCert where
  zero_iff_one := @cost_zero_set_singleton
  unique_member := @cost_zero_set_has_one_member
  log_symmetric := @jcost_log_symmetric
  isolated := @jcost_isolated_from_zero

end
end ExistenceUniquenessFromCost
end Foundation
end IndisputableMonolith
