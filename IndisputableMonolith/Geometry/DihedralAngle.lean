import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import IndisputableMonolith.Geometry.CayleyMenger

/-!
# Dihedral Angles for Simplices

This module sets up dihedral angles at edges and 2-faces of simplices
from Cayley-Menger data. It is Phase C2 of the program to discharge the
Regge deficit linearization hypothesis on general simplicial complexes.

## Scope

A dihedral angle at an edge of a tetrahedron is the angle between the
two faces containing that edge. Classically,

  cos(θ_e) = (CM_45) / √(CM_43 · CM_53)

where `CM_ij` is a minor of the Cayley-Menger matrix (see Berger,
*Geometry I*, §9.7). The exact formula is lengthy but explicit.

We take the same honest minimal approach as Phase C1:

- Define a `DihedralAngleData` structure that carries a cosine value
  and a bound `−1 ≤ cos ≤ 1`, matching the existing
  `IndisputableMonolith/Gravity/ReggeCalculus.DihedralAngleData`.
- Define the canonical dihedral angle `θ = arccos(cos)`.
- Prove its range `θ ∈ [0, π]`.
- Unconditionally evaluate the *regular-tetrahedron* dihedral angle:
  `θ = arccos(1/3) ≈ 70.53°`.
- Unconditionally evaluate the *cube* dihedral angle: `θ = π/2`.
- Record the flat-space sum `Σ_σ θ_σ = 2π` at a non-singular edge as
  a Prop-valued condition (named `FlatSumCondition`), exactly as Regge
  calculus uses it.

## What this enables

Phase C3 (`Schlaefli.lean`) references `DihedralAngleData` to state
Schläfli's identity. Phase C5 threads both through the final simplicial
discharge.

Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace DihedralAngle

open Real CayleyMenger

noncomputable section

/-! ## §1. Dihedral angle data -/

/-- The data of a dihedral angle: a cosine value in `[-1, 1]`. -/
structure DihedralAngleData where
  cosine : ℝ
  cosine_lb : -1 ≤ cosine
  cosine_ub : cosine ≤ 1

/-- The dihedral angle itself, via `arccos`. -/
def DihedralAngleData.theta (d : DihedralAngleData) : ℝ := Real.arccos d.cosine

/-- `θ ∈ [0, π]`. -/
theorem theta_nonneg (d : DihedralAngleData) : 0 ≤ d.theta :=
  Real.arccos_nonneg d.cosine

theorem theta_le_pi (d : DihedralAngleData) : d.theta ≤ Real.pi :=
  Real.arccos_le_pi d.cosine

/-- `cos θ = cosine` by construction. -/
theorem cos_theta (d : DihedralAngleData) : Real.cos d.theta = d.cosine := by
  unfold DihedralAngleData.theta
  exact Real.cos_arccos d.cosine_lb d.cosine_ub

/-! ## §2. Canonical values -/

/-- A regular tetrahedron's dihedral angle has cosine `1/3`. -/
def regular_tet_dihedral : DihedralAngleData :=
  { cosine := 1 / 3
  , cosine_lb := by norm_num
  , cosine_ub := by norm_num
  }

/-- The regular-tetrahedron dihedral angle is `arccos(1/3) ≈ 70.53°`. -/
theorem regular_tet_dihedral_theta :
    regular_tet_dihedral.theta = Real.arccos (1/3) := rfl

/-- `arccos(1/3)` lies strictly between 0 and π. -/
theorem regular_tet_dihedral_in_open_interval :
    0 < regular_tet_dihedral.theta ∧ regular_tet_dihedral.theta < Real.pi := by
  refine ⟨?_, ?_⟩
  · rw [regular_tet_dihedral_theta]
    apply Real.arccos_pos.mpr
    norm_num
  · rw [regular_tet_dihedral_theta]
    have h_le : Real.arccos (1/3) ≤ Real.pi := Real.arccos_le_pi _
    have h_ne : Real.arccos (1/3) ≠ Real.pi := by
      intro h_eq
      rw [Real.arccos_eq_pi] at h_eq
      linarith
    exact lt_of_le_of_ne h_le h_ne

/-- A cube's dihedral angle has cosine `0` (i.e. 90°). -/
def cube_dihedral : DihedralAngleData :=
  { cosine := 0
  , cosine_lb := by norm_num
  , cosine_ub := by norm_num
  }

/-- The cube dihedral is `π / 2` exactly. -/
theorem cube_dihedral_theta : cube_dihedral.theta = Real.pi / 2 := by
  unfold DihedralAngleData.theta cube_dihedral
  simp only
  exact Real.arccos_zero

/-! ## §3. Flat-sum conditions

At a hinge (edge in 3D, 2-face in 4D) embedded in flat Euclidean space,
the dihedral angles of the simplices meeting at the hinge sum to `2π`.
This is the piecewise-flat analog of "no curvature at this hinge."

We formalize this as a condition on a `List DihedralAngleData`. -/

/-- The sum of the `theta` values over a list of dihedral data. -/
def sumThetas (ds : List DihedralAngleData) : ℝ :=
  (ds.map DihedralAngleData.theta).sum

/-- The flat-sum condition: the total dihedral angle at a hinge equals `2π`. -/
def FlatSumCondition (ds : List DihedralAngleData) : Prop :=
  sumThetas ds = 2 * Real.pi

/-- The deficit at a hinge is `2π − Σ θ`. -/
def deficit (ds : List DihedralAngleData) : ℝ :=
  2 * Real.pi - sumThetas ds

/-- At a flat hinge, the deficit is zero. -/
theorem deficit_eq_zero_of_flat (ds : List DihedralAngleData)
    (h : FlatSumCondition ds) : deficit ds = 0 := by
  unfold deficit
  rw [h]; ring

/-- Four cube-dihedral angles (`π/2 + π/2 + π/2 + π/2 = 2π`) sum to `2π`:
    the classical "Z³ lattice is flat" statement. -/
theorem cubic_lattice_flatSum :
    FlatSumCondition [cube_dihedral, cube_dihedral, cube_dihedral, cube_dihedral] := by
  unfold FlatSumCondition sumThetas
  simp only [List.map, List.sum_cons, List.sum_nil, cube_dihedral_theta]
  ring

/-- The deficit at a flat cubic hinge is zero (the baseline identity
    already present in `ReggeCalculus.cubic_lattice_flat` for the
    π/2 × 4 = 2π case, now lifted to the `DihedralAngle` API). -/
theorem cubic_lattice_deficit_zero :
    deficit [cube_dihedral, cube_dihedral, cube_dihedral, cube_dihedral] = 0 :=
  deficit_eq_zero_of_flat _ cubic_lattice_flatSum

/-! ## §4. Certificate -/

structure DihedralAngleCert where
  cube_is_right_angle : cube_dihedral.theta = Real.pi / 2
  regular_tet_in_range :
    0 < regular_tet_dihedral.theta ∧ regular_tet_dihedral.theta < Real.pi
  cubic_flat_sum :
    FlatSumCondition [cube_dihedral, cube_dihedral, cube_dihedral, cube_dihedral]
  cubic_deficit_zero :
    deficit [cube_dihedral, cube_dihedral, cube_dihedral, cube_dihedral] = 0
  theta_in_range : ∀ d : DihedralAngleData, 0 ≤ d.theta ∧ d.theta ≤ Real.pi
  cos_theta_eq : ∀ d : DihedralAngleData, Real.cos d.theta = d.cosine

theorem dihedralAngleCert : DihedralAngleCert where
  cube_is_right_angle := cube_dihedral_theta
  regular_tet_in_range := regular_tet_dihedral_in_open_interval
  cubic_flat_sum := cubic_lattice_flatSum
  cubic_deficit_zero := cubic_lattice_deficit_zero
  theta_in_range := fun d => ⟨theta_nonneg d, theta_le_pi d⟩
  cos_theta_eq := cos_theta

end

end DihedralAngle
end Geometry
end IndisputableMonolith
