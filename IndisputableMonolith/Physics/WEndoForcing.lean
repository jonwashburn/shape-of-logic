import Mathlib
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# W_endo Forcing: W = E_pass + F = 17 if and only if D = 3

The endogenous wallpaper count W_endo(D) = passive_field_edges(D) + cube_faces(D)
equals 17 if and only if D = 3. This is the paper's Tr7 argument.

## The Proof

W_endo(D) = (D · 2^(D-1) - 1) + 2D = D · 2^(D-1) + 2D - 1

- D = 1: W_endo = 1·1 + 2 - 1 = 2 ≠ 17
- D = 2: W_endo = 2·2 + 4 - 1 = 7 ≠ 17
- D = 3: W_endo = 3·4 + 6 - 1 = 17 ✓
- D ≥ 4: W_endo ≥ 4·8 + 8 - 1 = 39 > 17

This is pure arithmetic, fully decidable by case analysis.
-/

namespace IndisputableMonolith
namespace Physics
namespace WEndoForcing

open Constants.AlphaDerivation

/-- The endogenous wallpaper count: E_passive + F for a D-cube. -/
def W_endo (d : ℕ) : ℕ := passive_field_edges d + cube_faces d

/-- At D = 3: W_endo = 11 + 6 = 17. -/
theorem W_endo_at_3 : W_endo 3 = 17 := by native_decide

/-- W_endo(3) matches the wallpaper groups constant. -/
theorem W_endo_eq_wallpaper : W_endo 3 = wallpaper_groups := by native_decide

/-- W_endo(1) = 2 ≠ 17. -/
theorem W_endo_at_1 : W_endo 1 = 2 := by native_decide

/-- W_endo(2) = 7 ≠ 17. -/
theorem W_endo_at_2 : W_endo 2 = 7 := by native_decide

/-- For D = 4: W_endo = 39. -/
theorem W_endo_at_4 : W_endo 4 = 39 := by native_decide

/-- For D = 5: W_endo = 89. -/
theorem W_endo_at_5 : W_endo 5 = 89 := by native_decide

/-- For D ≥ 4, W_endo(D) > 17. Proved by showing W_endo(4) = 39 > 17
    and W_endo is increasing (since D·2^(D-1) dominates). -/
theorem W_endo_gt_17_of_ge_4 (d : ℕ) (hd : 4 ≤ d) : 17 < W_endo d := by
  have h4 : W_endo 4 = 39 := W_endo_at_4
  suffices W_endo 4 ≤ W_endo d by linarith
  unfold W_endo passive_field_edges cube_edges active_edges_per_tick cube_faces
  have hpow : 2 ^ 3 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : 4 * 2 ^ 3 ≤ d * 2 ^ (d - 1) := by
    calc 4 * 2 ^ 3 ≤ d * 2 ^ 3 := by nlinarith
      _ ≤ d * 2 ^ (d - 1) := Nat.mul_le_mul_left d hpow
  omega

/-- **THE KEY THEOREM**: W_endo(D) = 17 if and only if D = 3.
    This is the paper's Tr7 — dimension selection via the cube sum. -/
theorem W_endo_eq_17_iff (d : ℕ) (hd : 1 ≤ d) : W_endo d = 17 ↔ d = 3 := by
  constructor
  · intro h
    match d, hd with
    | 1, _ => simp [W_endo_at_1] at h
    | 2, _ => simp [W_endo_at_2] at h
    | 3, _ => rfl
    | 4, _ => simp [W_endo_at_4] at h
    | d + 5, _ =>
      have : 4 ≤ d + 5 := by omega
      have := W_endo_gt_17_of_ge_4 (d + 5) this
      omega
  · intro h; subst h; exact W_endo_at_3

/-- Uniqueness: D = 3 is the unique positive dimension with W_endo = 17. -/
theorem dimension_unique_from_W_endo :
    ∃! d : ℕ, 1 ≤ d ∧ W_endo d = 17 := by
  use 3
  constructor
  · exact ⟨by norm_num, W_endo_at_3⟩
  · intro d ⟨hd, hw⟩
    exact (W_endo_eq_17_iff d hd).mp hw

/-- The decomposition: W = E_pass + F at D = 3. -/
theorem W_decomposition :
    W_endo 3 = passive_field_edges 3 + cube_faces 3 := rfl

/-- Verify the components. -/
theorem components_at_D3 :
    passive_field_edges 3 = 11 ∧ cube_faces 3 = 6 := by
  constructor <;> native_decide

end WEndoForcing
end Physics
end IndisputableMonolith
