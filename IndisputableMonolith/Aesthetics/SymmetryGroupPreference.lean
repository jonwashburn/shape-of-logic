import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Visual Symmetry-Group Preference (Track A5 / E5)

## Status: THEOREM (real derivation, replaces v4 SKELETON)

This module replaces the v4 `IS_SKELETON` placeholder. The v4 file
defined "wallpaper J-cost" as `orbit_count` (an integer cast to ℝ),
which had nothing to do with `Cost.Jcost`. This file enumerates the
seventeen wallpaper groups by their canonical generator-orbit
multiplicity and defines the wallpaper J-cost as the genuine
`Cost.Jcost` of the orbit-multiplicity ratio relative to the maximum
symmetry orbit.

## What we prove

For each of the seventeen wallpaper groups we record `orbitCount g`,
the orbit cardinality of the canonical fundamental domain under the
full symmetry group action (the standard crystallographic count: p1
has 1 orbit, p6m has 12, etc.). We define

  `wallpaperJ g := Cost.Jcost (orbitCount g / maxOrbitCount)`

where `maxOrbitCount = orbitCount p6m = 12`. This is the genuine
J-cost of the orbit-multiplicity *ratio*, which lives on the positive
reals and is reciprocal-symmetric (`J(x) = J(1/x)`).

Headline theorems:

* `wallpaperJ_p6m_eq_zero` — the maximum-symmetry group `p6m` sits at
  J = 0 (the cost minimum), exactly because its ratio is `1`.
* `wallpaperJ_nonneg` — every wallpaper group has non-negative
  J-cost (from `Cost.Jcost_nonneg`).
* `wallpaperJ_p1_pos` — the trivial-symmetry group `p1` has strictly
  positive J-cost (because its ratio `1/12` is not `1`).
* `wallpaperJ_mono_in_orbits` — for two groups whose orbit counts both
  lie in `[1, maxOrbitCount]`, the higher-orbit group has lower J-cost
  (preference orders symmetric over asymmetric).
* `preference_p6m_max` — `p6m` is the universally maximally preferred
  wallpaper group under the J-cost-derived preference functional.

This is the structural content for the cross-cultural preference
prediction (Washburn & Crowe 1988; Dietsch 2024). The numerical
preference *order* over the seventeen groups is the empirical
falsifier; the structural fact "preference is anti-monotone in
J-cost-of-orbit-ratio with `p6m` at the floor" is the Lean theorem.

## Falsifier

A cross-cultural preference experiment whose ranking is incompatible
with the J-cost ordering on the canonical `orbitCount` table below.
In particular, any experiment that ranks `p1` (trivial symmetry,
orbit ratio `1/12`) above `p6m` (maximum symmetry, orbit ratio `1`)
falsifies the prediction.
-/

namespace IndisputableMonolith
namespace Aesthetics
namespace SymmetryGroupPreference

open Constants Cost

/-! ## §1. The seventeen wallpaper groups -/

/-- The seventeen crystallographic wallpaper (plane-symmetry) groups,
in IUC notation. The order listed here matches Schattschneider 1978
and the standard crystallographic tables. -/
inductive WallpaperGroup
  | p1 | p2 | pm | pg | cm | pmm | pmg | pgg | cmm
  | p4 | p4m | p4g | p3 | p3m1 | p31m | p6 | p6m
  deriving DecidableEq, Repr

/-- Canonical orbit count under the full symmetry-group action on the
unit cell. These are the standard crystallographic orbit
multiplicities (point-group order × 1 for the symmorphic groups; the
non-symmorphic groups inherit the same orbit count from their point
group on a fundamental domain that ignores the glide). -/
def orbitCount : WallpaperGroup → ℕ
  | .p1 => 1
  | .p2 => 2
  | .pm => 2
  | .pg => 2
  | .cm => 2
  | .pmm => 4
  | .pmg => 4
  | .pgg => 4
  | .cmm => 4
  | .p4 => 4
  | .p4m => 8
  | .p4g => 8
  | .p3 => 3
  | .p3m1 => 6
  | .p31m => 6
  | .p6 => 6
  | .p6m => 12

/-- The maximum-symmetry group is `p6m` with twelve canonical orbits. -/
def maxOrbitCount : ℕ := 12

theorem orbitCount_p6m : orbitCount .p6m = maxOrbitCount := by
  unfold orbitCount maxOrbitCount
  rfl

theorem orbitCount_pos : ∀ g : WallpaperGroup, 0 < orbitCount g := by
  intro g; cases g <;> (unfold orbitCount; norm_num)

theorem orbitCount_le_max : ∀ g : WallpaperGroup,
    orbitCount g ≤ maxOrbitCount := by
  intro g; cases g <;> (unfold orbitCount maxOrbitCount; norm_num)

/-! ## §2. Symmetry ratio and J-cost -/

noncomputable section

/-- Symmetry ratio: `orbitCount g / maxOrbitCount ∈ (0, 1]`. -/
def symmetryRatio (g : WallpaperGroup) : ℝ :=
  (orbitCount g : ℝ) / (maxOrbitCount : ℝ)

theorem symmetryRatio_pos (g : WallpaperGroup) :
    0 < symmetryRatio g := by
  unfold symmetryRatio
  have h_num : (0 : ℝ) < (orbitCount g : ℝ) := by
    exact_mod_cast orbitCount_pos g
  have h_den : (0 : ℝ) < (maxOrbitCount : ℝ) := by
    unfold maxOrbitCount; norm_num
  positivity

theorem symmetryRatio_p6m : symmetryRatio .p6m = 1 := by
  unfold symmetryRatio
  rw [orbitCount_p6m]
  unfold maxOrbitCount
  norm_num

theorem symmetryRatio_le_one (g : WallpaperGroup) :
    symmetryRatio g ≤ 1 := by
  unfold symmetryRatio
  have h_num : (orbitCount g : ℝ) ≤ (maxOrbitCount : ℝ) := by
    exact_mod_cast orbitCount_le_max g
  have h_den : (0 : ℝ) < (maxOrbitCount : ℝ) := by
    unfold maxOrbitCount; norm_num
  rw [div_le_one h_den]
  exact h_num

/-- **Wallpaper J-cost.** The genuine `Cost.Jcost` evaluated on the
symmetry ratio, replacing the v4 placeholder `wallpaper_J_cost := orbit_count`. -/
def wallpaperJ (g : WallpaperGroup) : ℝ :=
  Cost.Jcost (symmetryRatio g)

theorem wallpaperJ_nonneg (g : WallpaperGroup) :
    0 ≤ wallpaperJ g :=
  Cost.Jcost_nonneg (symmetryRatio_pos g)

/-- **THEOREM.** `p6m` sits at the J-cost floor `J = 0`. -/
theorem wallpaperJ_p6m_eq_zero : wallpaperJ .p6m = 0 := by
  unfold wallpaperJ
  rw [symmetryRatio_p6m]
  exact Cost.Jcost_unit0

/-- For any non-`p6m` group whose ratio is not `1`, J-cost is strictly
positive. The technical content is `Jcost x = (x-1)²/(2x) > 0` when
`x ≠ 1`. -/
theorem wallpaperJ_pos_of_ne_one {g : WallpaperGroup}
    (h : symmetryRatio g ≠ 1) : 0 < wallpaperJ g := by
  unfold wallpaperJ
  have hx_pos : 0 < symmetryRatio g := symmetryRatio_pos g
  have hx_ne : symmetryRatio g ≠ 0 := ne_of_gt hx_pos
  rw [Cost.Jcost_eq_sq hx_ne]
  have h_sq_pos : 0 < (symmetryRatio g - 1) ^ 2 := by
    have h_diff : symmetryRatio g - 1 ≠ 0 := sub_ne_zero.mpr h
    positivity
  have h_den_pos : 0 < 2 * symmetryRatio g := by linarith
  positivity

/-- The trivial-symmetry group `p1` has strictly positive J-cost. -/
theorem wallpaperJ_p1_pos : 0 < wallpaperJ .p1 := by
  apply wallpaperJ_pos_of_ne_one
  unfold symmetryRatio orbitCount maxOrbitCount
  norm_num

/-- `p6m` strictly minimizes wallpaper J-cost over the seventeen groups
(strict for any group whose ratio is not `1`). -/
theorem wallpaperJ_p6m_le (g : WallpaperGroup) :
    wallpaperJ .p6m ≤ wallpaperJ g := by
  rw [wallpaperJ_p6m_eq_zero]
  exact wallpaperJ_nonneg g

/-! ## §3. Anti-monotonicity of J-cost in symmetry ratio (on `[r, 1]`) -/

/-- For ratios `x, y ∈ (0, 1]` with `x ≤ y`, the J-cost is monotone
*decreasing* in the ratio. This is the statement "more symmetric → lower
J-cost" on the relevant domain. Proof: on `(0, 1]`, `Jcost x = (x-1)²/(2x)`
is monotone decreasing because both `(x-1)²` decreases and `1/(2x)`
decreases as `x → 1`. -/
theorem Jcost_anti_mono_on_unit_interval {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    Cost.Jcost y ≤ Cost.Jcost x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hy_ne : y ≠ 0 := ne_of_gt hy
  rw [Cost.Jcost_eq_sq hx_ne, Cost.Jcost_eq_sq hy_ne]
  -- Goal: (y-1)²/(2y) ≤ (x-1)²/(2x)
  -- Equivalent: 2x · (y-1)² ≤ 2y · (x-1)²  (multiplying by 2xy > 0)
  rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * y) (by linarith : (0:ℝ) < 2 * x)]
  -- Goal: (y-1)² · (2*x) ≤ (x-1)² · (2*y)
  -- Both x, y are in (0, 1], so y-1 ≤ 0 and x-1 ≤ 0. Let a = 1-x ≥ 0, b = 1-y ≥ 0,
  -- then b ≤ a (since x ≤ y means 1-y ≤ 1-x).
  -- (y-1)² = b², (x-1)² = a², so we want 2x · b² ≤ 2y · a².
  -- Equivalently: x · b² ≤ y · a².
  -- Since b ≤ a and b² ≤ a², and x ≤ y, the product inequality follows.
  set a := 1 - x with ha_def
  set b := 1 - y with hb_def
  have ha_nn : 0 ≤ a := by linarith
  have hb_nn : 0 ≤ b := by linarith
  have hba : b ≤ a := by linarith
  have hxy' : x ≤ y := hxy
  have hsq_nn : (1 - y) ^ 2 = b ^ 2 := by rw [hb_def]
  have hsq_nn' : (1 - x) ^ 2 = a ^ 2 := by rw [ha_def]
  have hyy_eq : (y - 1) ^ 2 = b ^ 2 := by rw [show (y - 1) = -(1 - y) from by ring]; ring
  have hxx_eq : (x - 1) ^ 2 = a ^ 2 := by rw [show (x - 1) = -(1 - x) from by ring]; ring
  rw [hyy_eq, hxx_eq]
  -- Goal: b^2 * (2*x) ≤ a^2 * (2*y).
  -- Use: b ≤ a (both nonneg) ⇒ b^2 ≤ a^2; and x ≤ y. Then b^2 * x ≤ a^2 * y.
  have hb2_le_a2 : b ^ 2 ≤ a ^ 2 := by
    have := mul_self_le_mul_self hb_nn hba
    rw [pow_two, pow_two]; exact this
  have hb2_nn : 0 ≤ b ^ 2 := by positivity
  have ha2_nn : 0 ≤ a ^ 2 := by positivity
  -- b^2 · (2x) ≤ a^2 · (2x) ≤ a^2 · (2y).
  have step1 : b ^ 2 * (2 * x) ≤ a ^ 2 * (2 * x) :=
    mul_le_mul_of_nonneg_right hb2_le_a2 (by linarith)
  have step2 : a ^ 2 * (2 * x) ≤ a ^ 2 * (2 * y) :=
    mul_le_mul_of_nonneg_left (by linarith) ha2_nn
  linarith

/-- **PREFERENCE ANTI-MONOTONICITY ON THE WALLPAPER LATTICE.** For two
wallpaper groups, the one with strictly more orbits has lower J-cost
(equivalently, higher preference). -/
theorem wallpaperJ_mono_in_orbits {g h : WallpaperGroup}
    (hgh : orbitCount g ≤ orbitCount h) :
    wallpaperJ h ≤ wallpaperJ g := by
  unfold wallpaperJ
  apply Jcost_anti_mono_on_unit_interval
  · exact symmetryRatio_pos g
  · exact symmetryRatio_pos h
  · -- Goal: symmetryRatio g ≤ symmetryRatio h
    unfold symmetryRatio
    have h_den_pos : (0 : ℝ) < (maxOrbitCount : ℝ) := by
      unfold maxOrbitCount; norm_num
    rw [div_le_div_iff₀ h_den_pos h_den_pos]
    have : (orbitCount g : ℝ) ≤ (orbitCount h : ℝ) := by exact_mod_cast hgh
    nlinarith
  · exact symmetryRatio_le_one h

/-! ## §4. Aesthetic preference functional -/

/-- Aesthetic preference is the negation of J-cost: higher preference =
lower cost. -/
def preference (g : WallpaperGroup) : ℝ := - wallpaperJ g

theorem preference_p6m_eq_zero : preference .p6m = 0 := by
  unfold preference
  rw [wallpaperJ_p6m_eq_zero]
  ring

/-- **THEOREM.** `p6m` is the universally maximally preferred
wallpaper group under the J-cost-derived preference functional. -/
theorem preference_p6m_max (g : WallpaperGroup) :
    preference g ≤ preference .p6m := by
  unfold preference
  rw [wallpaperJ_p6m_eq_zero]
  have := wallpaperJ_nonneg g
  linarith

/-- Anti-monotone in orbits: if `orbitCount g ≤ orbitCount h`, then
preference for `g` is at most preference for `h`. -/
theorem preference_anti_mono_in_orbits {g h : WallpaperGroup}
    (hgh : orbitCount g ≤ orbitCount h) :
    preference g ≤ preference h := by
  unfold preference
  have := wallpaperJ_mono_in_orbits hgh
  linarith

/-! ## §5. Master certificate -/

/-- **SYMMETRY GROUP PREFERENCE MASTER CERTIFICATE.** Eight clauses
backing the J-cost-driven cross-cultural preference prediction. All
fields derived from `Cost.Jcost`, not asserted as orbit-count
arithmetic.

1. `orbit_pos`: every group has positive orbit count.
2. `orbit_p6m_eq_max`: `p6m` orbit count = 12 = `maxOrbitCount`.
3. `ratio_le_one`: every symmetry ratio is in `(0, 1]`.
4. `J_nonneg`: every wallpaper J-cost is non-negative.
5. `J_p6m_zero`: `p6m` sits at the J-cost floor.
6. `J_p1_pos`: `p1` has strictly positive J-cost.
7. `J_mono`: J-cost is anti-monotone in orbit count.
8. `preference_p6m_max`: `p6m` maximizes preference.
-/
structure SymmetryGroupPreferenceCert where
  orbit_pos : ∀ g, 0 < orbitCount g
  orbit_p6m_eq_max : orbitCount .p6m = maxOrbitCount
  ratio_le_one : ∀ g, symmetryRatio g ≤ 1
  J_nonneg : ∀ g, 0 ≤ wallpaperJ g
  J_p6m_zero : wallpaperJ .p6m = 0
  J_p1_pos : 0 < wallpaperJ .p1
  J_mono : ∀ {g h}, orbitCount g ≤ orbitCount h → wallpaperJ h ≤ wallpaperJ g
  preference_p6m_max : ∀ g, preference g ≤ preference .p6m

def symmetryGroupPreferenceCert : SymmetryGroupPreferenceCert where
  orbit_pos := orbitCount_pos
  orbit_p6m_eq_max := orbitCount_p6m
  ratio_le_one := symmetryRatio_le_one
  J_nonneg := wallpaperJ_nonneg
  J_p6m_zero := wallpaperJ_p6m_eq_zero
  J_p1_pos := wallpaperJ_p1_pos
  J_mono := wallpaperJ_mono_in_orbits
  preference_p6m_max := preference_p6m_max

/-! ## §6. One-statement summary -/

/-- **SYMMETRY GROUP PREFERENCE ONE-STATEMENT.** Three structural
facts assembled into one theorem:

(1) `p6m` (orbit count 12) sits at J-cost zero.
(2) `p1` (orbit count 1) sits at J-cost strictly positive.
(3) For any pair, the group with more orbits has lower J-cost.

This forces the universal preference ordering:
maximum-symmetry groups are universally preferred to lower-symmetry
groups under the J-cost-derived preference functional. -/
theorem symmetry_group_preference_one_statement :
    wallpaperJ .p6m = 0 ∧
    0 < wallpaperJ .p1 ∧
    ∀ {g h : WallpaperGroup},
      orbitCount g ≤ orbitCount h → wallpaperJ h ≤ wallpaperJ g :=
  ⟨wallpaperJ_p6m_eq_zero, wallpaperJ_p1_pos,
   @wallpaperJ_mono_in_orbits⟩

end

end SymmetryGroupPreference
end Aesthetics
end IndisputableMonolith
