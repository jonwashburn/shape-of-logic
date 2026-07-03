import Mathlib
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# Wallpaper Endogenous Bridge (Pass 2)

This module provides an explicit bridge from cube combinatorics to the
crystallographic constant `W = 17`.

## Goal

The current framework imports `wallpaper_groups = 17` as a classical mathematical
fact (Fedorov 1891). This file does **not** re-prove wallpaper classification,
but it formalizes an endogenous RS candidate:

`W_endogenous(D) := E_passive(D) + F(D)`.

For `D = 3`, this gives:
- `E_passive = 11`,
- `F = 6`,
- `W_endogenous = 17`.

So the counting-layer identity `11 + 6 = 17` is now explicit and machine-checked,
and at `D = 3` it matches the imported `wallpaper_groups`.

This is a bridge step toward full endogeneity of `W`.
-/

namespace IndisputableMonolith
namespace Verification
namespace WallpaperEndogenousBridge

open Constants.AlphaDerivation

/-- Endogenous candidate for the `W`-count from RS cube combinatorics. -/
def W_endogenous (d : ℕ) : ℕ :=
  passive_field_edges d + cube_faces d

/-- Expanded closed form:
`W_endogenous(d) = d * 2^(d-1) - 1 + 2d`. -/
theorem W_endogenous_formula (d : ℕ) :
    W_endogenous d = (cube_edges d - active_edges_per_tick) + cube_faces d := by
  rfl

/-- At `D=3`, the endogenous candidate is exactly 17. -/
theorem W_endogenous_at_D3 : W_endogenous D = 17 := by
  native_decide

/-- At `D=3`, the endogenous candidate matches the imported wallpaper constant. -/
theorem W_endogenous_matches_wallpaper_groups :
    W_endogenous D = wallpaper_groups := by
  native_decide

/-- Component decomposition at `D=3`: `11 + 6 = 17`. -/
theorem decomposition_at_D3 :
    passive_field_edges D = 11 ∧ cube_faces D = 6 ∧ W_endogenous D = 17 := by
  native_decide

/-- Finite computational scan: up to dimension 64, only `D=3` gives 17. -/
def unique17ScanUpTo64 : Bool :=
  (List.range 65).all (fun d => decide (W_endogenous d = 17 ↔ d = 3))

theorem unique17ScanUpTo64_true : unique17ScanUpTo64 = true := by
  native_decide

/-- Endogenous candidate at `D=3` as a named constant. -/
def W_from_cube : ℕ := W_endogenous D

theorem W_from_cube_eq_17 : W_from_cube = 17 := by
  simpa [W_from_cube] using W_endogenous_at_D3

theorem W_from_cube_eq_wallpaper_groups : W_from_cube = wallpaper_groups := by
  simpa [W_from_cube] using W_endogenous_matches_wallpaper_groups

/-- Generator-level slot closure at `D=3`:
the wallpaper slot is exactly the endogenous cube formula `E_passive + F`. -/
theorem wallpaper_slot_iff_endogenous_formula (w : ℕ) :
    (w = wallpaper_groups) ↔ (w = passive_field_edges D + cube_faces D) := by
  constructor
  · intro hw
    calc
      w = wallpaper_groups := hw
      _ = W_from_cube := W_from_cube_eq_wallpaper_groups.symm
      _ = passive_field_edges D + cube_faces D := by
            simp [W_from_cube, W_endogenous]
  · intro hw
    calc
      w = passive_field_edges D + cube_faces D := hw
      _ = W_from_cube := by
            simp [W_from_cube, W_endogenous]
      _ = wallpaper_groups := W_from_cube_eq_wallpaper_groups

/-- Uniqueness form: any `w` satisfying the endogenous wallpaper formula
at `D=3` is forced to the imported wallpaper constant. -/
theorem wallpaper_slot_unique_from_endogenous_formula (w : ℕ)
    (hw : w = passive_field_edges D + cube_faces D) :
    w = wallpaper_groups := by
  exact (wallpaper_slot_iff_endogenous_formula w).2 hw

/-- Endogenous closure package for the counting-layer wallpaper slot:
    the cube-derived value is exactly 17 and matches the imported constant. -/
theorem endogenous_wallpaper_bridge_complete :
    W_from_cube = 17 ∧
    W_from_cube = wallpaper_groups ∧
    (∀ w : ℕ, (w = wallpaper_groups) ↔ (w = passive_field_edges D + cube_faces D)) := by
  refine ⟨W_from_cube_eq_17, W_from_cube_eq_wallpaper_groups, ?_⟩
  intro w
  exact wallpaper_slot_iff_endogenous_formula w

end WallpaperEndogenousBridge
end Verification
end IndisputableMonolith
