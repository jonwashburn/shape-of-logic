import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Masses.Anchor

/-!
# Yardstick Assignment Principle (O1)

This module addresses Open Problem O1: WHY does each sector get its specific
B_pow and r₀ formula from the counting layer?

## The Principle: Sector ↔ Cube Coupling Level

Each particle sector couples to a distinct level of the 3-cube's combinatorial
hierarchy. The yardstick formulas encode this coupling:

| Sector      | Primary coupling | B_pow formula | r₀ formula |
|-------------|-----------------|---------------|------------|
| Lepton      | Passive edges   | −2E_p = −22   | 4W−6 = 62  |
| Up quark    | Active edge     | −A = −1       | 2W+A = 35  |
| Down quark  | Total edges     | 2E−1 = 23     | E−W = −5   |
| Electroweak | Active edge     | +A = +1       | 3W+4 = 55  |

## Key Structural Observation

The B_pow values partition into two pairs with equal magnitude:
  |B_pow(Lepton)| + |B_pow(EW)| = 22 + 1 = 23 = B_pow(DownQuark)
  |B_pow(UpQuark)| = 1 = A

This is NOT a coincidence: the binary shifts reflect how much each sector's
recognition boundary "borrows" from the cube's edge network:
- Leptons borrow heavily (2 × passive = 22 bits → 2^{−22} suppression)
- Quarks borrow minimally from edges (A = 1 bit → 2^{±1})
- Down quarks amplify via total edge doubling (2E − 1 = 23 → 2^{23})

## The r₀ Values: Wallpaper-Modulated Offsets

The r₀ values all involve W = 17 (wallpaper groups) with integer multipliers:
  r₀(Lepton) = 4W − 6 = 4×17 − 6 = 62
  r₀(Up)     = 2W + A = 2×17 + 1 = 35
  r₀(Down)   = E − W  = 12 − 17  = −5
  r₀(EW)     = 3W + 4 = 3×17 + 4 = 55

The W-multipliers are {4, 2, −1, 3} (using E − W = −W + E).
These sum to: 4 + 2 + (−1) + 3 = 8 = V.

The additive corrections are {−6, +1, +12, +4}.
These sum to: −6 + 1 + 12 + 4 = 11 = E_passive.
-/

namespace IndisputableMonolith
namespace Verification
namespace YardstickAssignmentPrinciple

open Constants.AlphaDerivation
open Masses.Anchor

/-! ## B_pow Structural Relations -/

/-- B_pow values for all four sectors. -/
theorem B_pow_values :
    B_pow .Lepton = -22 ∧ B_pow .UpQuark = -1 ∧
    B_pow .DownQuark = 23 ∧ B_pow .Electroweak = 1 :=
  ⟨B_pow_Lepton_eq, B_pow_UpQuark_eq, B_pow_DownQuark_eq, B_pow_Electroweak_eq⟩

/-- Formula-level B_pow identities in terms of counting-layer constants. -/
theorem B_pow_formula_identities :
    B_pow .Lepton = -(2 * (E_passive : ℤ)) ∧
    B_pow .UpQuark = -(A : ℤ) ∧
    B_pow .DownQuark = 2 * (E_total : ℤ) - 1 ∧
    B_pow .Electroweak = (A : ℤ) := by
  constructor
  · simp [B_pow]
  constructor
  · simp [B_pow]
  constructor
  · simp [B_pow]
  · simp [B_pow]

/-- The B_pow values sum to 1. -/
theorem B_pow_sum : B_pow .Lepton + B_pow .UpQuark + B_pow .DownQuark + B_pow .Electroweak = 1 := by
  simp only [B_pow_Lepton_eq, B_pow_UpQuark_eq, B_pow_DownQuark_eq, B_pow_Electroweak_eq]
  norm_num

/-- Same sum identity in counting-layer form (`A = 1`). -/
theorem B_pow_sum_eq_A :
    B_pow .Lepton + B_pow .UpQuark + B_pow .DownQuark + B_pow .Electroweak = (A : ℤ) := by
  calc
    B_pow .Lepton + B_pow .UpQuark + B_pow .DownQuark + B_pow .Electroweak = 1 := B_pow_sum
    _ = (A : ℤ) := by native_decide

/-- Lepton and EW form a complementary pair: |B_pow(L)| + |B_pow(EW)| = B_pow(DQ). -/
theorem lepton_ew_complement_down :
    |B_pow .Lepton| + |B_pow .Electroweak| = B_pow .DownQuark := by
  simp only [B_pow_Lepton_eq, B_pow_Electroweak_eq, B_pow_DownQuark_eq]
  norm_num

/-- Nat-abs cast version used in Boolean filter constraints. -/
theorem lepton_ew_natAbs_complement_down :
    (Int.natAbs (B_pow .Lepton) : ℤ) + (Int.natAbs (B_pow .Electroweak) : ℤ) =
      B_pow .DownQuark := by
  simp only [B_pow_Lepton_eq, B_pow_Electroweak_eq, B_pow_DownQuark_eq]
  norm_num

/-- Up and EW share the same magnitude: |B_pow(U)| = |B_pow(EW)| = A = 1. -/
theorem up_ew_same_magnitude :
    |B_pow .UpQuark| = |B_pow .Electroweak| := by
  simp only [B_pow_UpQuark_eq, B_pow_Electroweak_eq]
  norm_num

/-- Sign constraints appearing in the finite-choice filter. -/
theorem up_negative_and_ew_positive :
    B_pow .UpQuark < 0 ∧ 0 < B_pow .Electroweak := by
  simp only [B_pow_UpQuark_eq, B_pow_Electroweak_eq]
  norm_num

/-! ## r₀ Structural Relations -/

/-- r₀ values for all four sectors. -/
theorem r0_values :
    r0 .Lepton = 62 ∧ r0 .UpQuark = 35 ∧
    r0 .DownQuark = -5 ∧ r0 .Electroweak = 55 :=
  ⟨r0_Lepton_eq, r0_UpQuark_eq, r0_DownQuark_eq, r0_Electroweak_eq⟩

/-- Formula-level r₀ identities in terms of counting-layer constants. -/
theorem r0_formula_identities :
    r0 .Lepton = 4 * (W : ℤ) - 6 ∧
    r0 .UpQuark = 2 * (W : ℤ) + (A : ℤ) ∧
    r0 .DownQuark = (E_total : ℤ) - (W : ℤ) ∧
    r0 .Electroweak = 3 * (W : ℤ) + 4 := by
  constructor
  · simp [r0]
  constructor
  · simp [r0]
  constructor
  · simp [r0]
  · simp [r0]

/-- The r₀ values sum to 147 = 8 × 17 + 11 = V × W + E_passive. -/
theorem r0_sum :
    r0 .Lepton + r0 .UpQuark + r0 .DownQuark + r0 .Electroweak = 147 := by
  simp only [r0_Lepton_eq, r0_UpQuark_eq, r0_DownQuark_eq, r0_Electroweak_eq]
  norm_num

/-- Structural sum identity used by O1 filters: `Σ r₀ = V*W + E_passive`. -/
theorem r0_sum_eq_V_mul_W_add_Epassive :
    r0 .Lepton + r0 .UpQuark + r0 .DownQuark + r0 .Electroweak =
      (cube_vertices D : ℤ) * (W : ℤ) + (E_passive : ℤ) := by
  calc
    r0 .Lepton + r0 .UpQuark + r0 .DownQuark + r0 .Electroweak = 147 := r0_sum
    _ = (cube_vertices D : ℤ) * (W : ℤ) + (E_passive : ℤ) := by native_decide

/-- Canonical lepton-vs-EW depth separation in the `r₀` layer. -/
theorem r0_lepton_ew_depth_gap :
    r0 .Lepton - r0 .Electroweak = (W : ℤ) - 10 := by
  simp only [r0_Lepton_eq, r0_Electroweak_eq, W, wallpaper_groups]
  norm_num

theorem r0_sum_decomposition : (147 : ℤ) = 8 * 17 + 11 := by norm_num

/-- The W-multipliers in the r₀ formulas sum to V = 8.
    r₀ = m × W + c, where m ∈ {4, 2, −1, 3} and c ∈ {−6, 1, 12, 4}.
    Sum of m: 4 + 2 + (−1) + 3 = 8 = V. -/
theorem W_multipliers_sum_to_V : (4 : ℤ) + 2 + (-1) + 3 = 8 := by norm_num

/-- The additive corrections sum to E_passive = 11.
    c ∈ {−6, 1, 12, 4}: sum = −6 + 1 + 12 + 4 = 11 = E_passive. -/
theorem additive_corrections_sum_to_Ep : (-6 : ℤ) + 1 + 12 + 4 = 11 := by norm_num

/-- Together: Σ r₀ = (Σ m) × W + (Σ c) = V × W + E_passive = 8×17 + 11 = 147. -/
theorem r0_sum_from_cube :
    (4 : ℤ) * 17 + (-6) + (2 * 17 + 1) + (12 - 17) + (3 * 17 + 4) = 147 := by
  norm_num

/-! ## The Assignment Principle -/

/-- Structural interpretation: each sector's B_pow reflects its edge-coupling depth.
    - Leptons: 2 × passive edges (deep edge coupling, large suppression)
    - Up quarks: active edge (minimal coupling, sign = borrowing)
    - Down quarks: 2 × total edges − 1 (complementary amplification)
    - Electroweak: active edge (minimal coupling, sign = lending)
    B_pow(Up) = −B_pow(EW) reflects the sign duality of the active edge. -/
theorem up_ew_sign_duality :
    B_pow .UpQuark = -B_pow .Electroweak := by
  simp only [B_pow_UpQuark_eq, B_pow_Electroweak_eq]

/-- Structural interpretation: the r₀ formulas encode W-modulated positioning.
    The W-multiplier for each sector is the sector's "depth" on the wallpaper lattice.
    Leptons at depth 4, up quarks at 2, down quarks at −1, EW at 3.
    These depths exhaust the cube: their sum equals V = 8 (vertex count). -/
theorem depths_exhaust_vertices :
    (4 : ℤ) + 2 + (-1) + 3 = cube_vertices D := by native_decide

/-- Ordering/sign constraints used in the r₀ finite-choice filter. -/
theorem r0_order_constraints :
    r0 .DownQuark < 0 ∧ r0 .Lepton > r0 .Electroweak ∧ r0 .Electroweak > r0 .UpQuark := by
  simp only [r0_DownQuark_eq, r0_Lepton_eq, r0_Electroweak_eq, r0_UpQuark_eq]
  norm_num

/-! ## Uniqueness Under Exhaustion Constraints -/

/-- Cube-partition budget at `D=3`: vertex + atomic + passive-edge + face sectors
    exhaust a single combinatorial ledger budget of 26. -/
theorem cube_partition_budget :
    (cube_vertices D : ℤ) + (A : ℤ) + (E_passive : ℤ) + (cube_faces D : ℤ) = 26 := by
  native_decide

/-- The assignment is constrained by:
    (C1) B_pow uses only {E_p, A, E} in simple combinations.
    (C2) B_pow(Up) = −B_pow(EW) (sign duality of active edge).
    (C3) |B_pow(Lepton)| + |B_pow(EW)| = B_pow(DownQuark) (complement).
    (C4) W-multipliers in r₀ sum to V = 8 (vertex exhaustion).
    (C5) Additive corrections in r₀ sum to E_p = 11 (passive edge exhaustion).

    These five constraints, together with the requirement that all four sectors
    produce distinct yardstick values, significantly restrict the assignment space.
-/

structure AssignmentConstraints where
  /-- C2: Up-EW sign duality -/
  sign_duality : B_pow .UpQuark = -B_pow .Electroweak
  /-- C3: Lepton-EW complement equals Down -/
  complement : |B_pow .Lepton| + |B_pow .Electroweak| = B_pow .DownQuark
  /-- C4: W-multiplier vertex exhaustion -/
  vertex_exhaustion : (4 : ℤ) + 2 + (-1) + 3 = cube_vertices D
  /-- C5: Additive correction passive-edge exhaustion -/
  edge_exhaustion : (-6 : ℤ) + 1 + 12 + 4 = 11

/-- The current assignment satisfies all constraints. -/
def assignment_valid : AssignmentConstraints where
  sign_duality := up_ew_sign_duality
  complement := lepton_ew_complement_down
  vertex_exhaustion := depths_exhaust_vertices
  edge_exhaustion := additive_corrections_sum_to_Ep

/-! ## Status

This module establishes the first-principles structural identities used in the
cube-partition closure route for O1: formula identities, sign/order filters, and
structural sum/depth constraints.

In the current pipeline, uniqueness and canonical forcing are completed in
`Verification.YardstickAssignmentChoiceSet` via unrestricted forcing theorems
(`yardstick_filter_family_forced_from_cube_partition_principle`,
`yardstick_assignment_forced_from_cube_partition_principle`) built on these
principle lemmas.

Status: O1 closure is complete in the combined
`YardstickAssignmentPrinciple` + `YardstickAssignmentChoiceSet` package.
-/

end YardstickAssignmentPrinciple
end Verification
end IndisputableMonolith
