import Mathlib
import IndisputableMonolith.Masses.GenerationTorsionBridge

/-!
# Excitation Ordering from CW-Filtration of Q₃

This module derives the edge-before-face excitation ordering for fermion
generation torsion from the CW-complex structure of the D=3 cube, combined
with J-cost monotonicity on φ-power ratios.

## The Argument

The 3-cube Q₃ has a natural CW-filtration by subcell dimension:
- 0-skeleton: 8 vertices (CW-dim 0)
- 1-skeleton: 12 edges, 11 passive (CW-dim 1)
- 2-skeleton: 6 faces (CW-dim 2)

When generation excitations couple to subcells in order of CW dimension,
the cumulative torsion schedule {0, 11, 17} emerges:
- Gen 1 (ground): couples to 0-skeleton only → τ = 0
- Gen 2 (first excitation): adds 1-cells → τ = passive_field_edges = 11
- Gen 3 (second excitation): adds 2-cells → τ = 11 + cube_faces = 17

The J-cost monotonicity on φ-power ratios then guarantees strict cost ordering:
  J(φ⁰) = 0 < J(φ¹¹) < J(φ¹⁷)

## What This Proves

IF excitations couple to Q₃ subcells in order of CW dimension, THEN:
1. The first nontrivial excitation is edge-supported (dim 1)
2. The next independent excitation is face-supported (dim 2)
3. The resulting torsion schedule equals the canonical one
4. J-cost respects this ordering strictly

The CW-dimensional ordering (dim 1 < dim 2) is a geometric fact about the
cube. It provides the structural reason why edges come before faces, which
is otherwise an unexplained feature of `CubeAdmissibleTorsion`.

## Remaining Premise

The statement "excitations couple in order of CW dimension" is the filtration
principle. It replaces the mode labels (ground/edge/face) in
`CubeAdmissibleTorsion` with a single geometric principle, but it is still
a structural premise about the coupling mechanism rather than a consequence
of the RCL alone.
-/

namespace IndisputableMonolith
namespace Masses
namespace ExcitationOrdering

open IndisputableMonolith.Constants
open IndisputableMonolith.Constants.AlphaDerivation
open IndisputableMonolith.Cost
open IndisputableMonolith.Masses.GenerationTorsionBridge
open IndisputableMonolith.RecogSpec

/-! ## Part 1: CW-Complex Structure of Q_D -/

/-- Subcell types of the D-dimensional hypercube Q_D, restricted to the
    dimensions relevant for fermion generation coupling (0, 1, 2). -/
inductive CubeCell (d : ℕ) where
  | vertex : CubeCell d
  | edge   : CubeCell d
  | face   : CubeCell d
  deriving DecidableEq

/-- The CW dimension of a subcell type. -/
def CubeCell.cwDim {d : ℕ} : CubeCell d → ℕ
  | .vertex => 0
  | .edge   => 1
  | .face   => 2

/-- Total subcell count of each type in Q_d. -/
def subcellCount (d : ℕ) : CubeCell d → ℕ
  | .vertex => cube_vertices d
  | .edge   => cube_edges d
  | .face   => cube_faces d

@[simp] theorem subcellCount_vertex : subcellCount D .vertex = 8 := by native_decide
@[simp] theorem subcellCount_edge   : subcellCount D .edge   = 12 := by native_decide
@[simp] theorem subcellCount_face   : subcellCount D .face   = 6 := by native_decide

/-- CW-dimensional ordering: edges are strictly lower-dimensional than faces. -/
theorem edge_dim_lt_face_dim :
    CubeCell.cwDim (.edge : CubeCell D) < CubeCell.cwDim (.face : CubeCell D) := by
  decide

/-- Vertices are strictly lower-dimensional than edges. -/
theorem vertex_dim_lt_edge_dim :
    CubeCell.cwDim (.vertex : CubeCell D) < CubeCell.cwDim (.edge : CubeCell D) := by
  decide

/-! ## Part 2: Passive Coupling Per CW Level -/

/-- The number of subcells available for passive coupling at each CW level.
    Vertices do not contribute (ground state couples trivially).
    Edges contribute `cube_edges - 1` (one edge is the active transition).
    All faces participate. -/
def passiveCoupling (d : ℕ) : CubeCell d → ℕ
  | .vertex => 0
  | .edge   => passive_field_edges d
  | .face   => cube_faces d

@[simp] theorem passiveCoupling_vertex : passiveCoupling D .vertex = 0 := rfl
@[simp] theorem passiveCoupling_edge   : passiveCoupling D .edge   = 11 := by native_decide
@[simp] theorem passiveCoupling_face   : passiveCoupling D .face   = 6 := by native_decide

theorem passiveCoupling_edge_pos : 0 < passiveCoupling D .edge := by native_decide
theorem passiveCoupling_face_pos : 0 < passiveCoupling D .face := by native_decide

/-! ## Part 3: CW-Cumulative Torsion -/

/-- Torsion schedule derived from cumulative CW-filtration.

    Generation g couples to all subcells of CW dimension ≤ (g - 1):
    - Gen 1 (ground): dim ≤ -1 → nothing → τ = 0
    - Gen 2: dim ≤ 0 already covered, new: dim 1 → adds edge coupling
    - Gen 3: dim ≤ 1 already covered, new: dim 2 → adds face coupling -/
def cwCumulativeTorsion (d : ℕ) : Generation → ℤ
  | .first  => 0
  | .second => (passiveCoupling d .edge : ℤ)
  | .third  => (passiveCoupling d .edge + passiveCoupling d .face : ℤ)

@[simp] theorem cwTorsion_first  : cwCumulativeTorsion D .first  = 0 := rfl
@[simp] theorem cwTorsion_second : cwCumulativeTorsion D .second = 11 := by native_decide
@[simp] theorem cwTorsion_third  : cwCumulativeTorsion D .third  = 17 := by native_decide

/-- CW-cumulative torsion at D=3 equals the canonical `generationTorsion`. -/
theorem cwTorsion_eq_generationTorsion :
    cwCumulativeTorsion D = generationTorsion := by
  funext g
  cases g with
  | first => rfl
  | second =>
    simp [cwCumulativeTorsion, generationTorsion, passiveCoupling,
          passive_field_edges, cube_edges, active_edges_per_tick, D]
  | third =>
    simp [cwCumulativeTorsion, generationTorsion, passiveCoupling,
          passive_field_edges, cube_edges, active_edges_per_tick, cube_faces, D]

/-- The first excitation increment equals the passive edge count. -/
theorem first_increment_is_passive_edges :
    cwCumulativeTorsion D .second - cwCumulativeTorsion D .first =
      (passive_field_edges D : ℤ) := by
  simp [cwCumulativeTorsion, passiveCoupling]

/-- The second excitation increment equals the face count. -/
theorem second_increment_is_faces :
    cwCumulativeTorsion D .third - cwCumulativeTorsion D .second =
      (cube_faces D : ℤ) := by
  simp [cwCumulativeTorsion, passiveCoupling,
        passive_field_edges, cube_edges, active_edges_per_tick, cube_faces, D]

/-- The CW-cumulative torsion is cube-admissible. -/
theorem cwTorsion_cubeAdmissible :
    CubeAdmissibleTorsion D (cwCumulativeTorsion D) := by
  rw [cwTorsion_eq_generationTorsion]
  exact generationTorsion_admissible

/-! ## Part 4: J-Cost Monotonicity on [1, ∞) -/

/-- J-cost is strictly increasing on [1, ∞).

    Proof: write `J(x) = (x + 1/x)/2 - 1` and show `x + 1/x` is strictly
    increasing for `x ≥ 1` via the identity
      `(y + 1/y) - (x + 1/x) = (y - x)(xy - 1)/(xy)`,
    which is positive when `1 ≤ x < y`. -/
theorem Jcost_strict_mono_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx1 : 1 ≤ x) (hxy : x < y) :
    Jcost x < Jcost y := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [Jcost]
  suffices h : x + x⁻¹ < y + y⁻¹ by linarith
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hxy1 : 0 < x * y - 1 := by nlinarith
  have key : y + y⁻¹ - (x + x⁻¹) = (y - x) * (x * y - 1) / (x * y) := by
    field_simp
    ring
  linarith [div_pos (mul_pos hyx hxy1) hxy_pos]

/-! ## Part 5: Excitation Cost and Ordering -/

/-- Excitation cost: the J-cost of the φ-power ratio at integer torsion τ. -/
noncomputable def excitationCost (τ : ℤ) : ℝ := Jcost (phi ^ τ)

/-- Ground state (τ = 0) has zero excitation cost. -/
theorem excitationCost_ground : excitationCost 0 = 0 := by
  simp [excitationCost, Jcost_unit0]

/-- Any nonzero torsion has positive excitation cost. -/
theorem excitationCost_pos_of_ne_zero (τ : ℤ) (hτ : τ ≠ 0) :
    0 < excitationCost τ := by
  apply Jcost_pos_of_ne_one
  · exact zpow_pos phi_pos τ
  · exact fun h => hτ ((phi_zpow_eq_one_iff τ).mp h)

/-- Excitation cost is strictly monotone for non-negative torsion:
    0 ≤ τ₁ < τ₂ implies J(φ^τ₁) < J(φ^τ₂). -/
theorem excitationCost_strictMono {τ₁ τ₂ : ℤ} (h1 : 0 ≤ τ₁) (h2 : τ₁ < τ₂) :
    excitationCost τ₁ < excitationCost τ₂ := by
  apply Jcost_strict_mono_pos (zpow_pos phi_pos τ₁) (zpow_pos phi_pos τ₂)
  · rcases eq_or_lt_of_le h1 with rfl | hpos
    · simp
    · exact le_of_lt (one_lt_zpow₀ one_lt_phi hpos)
  · exact zpow_lt_zpow_right₀ one_lt_phi h2

/-- The three generation torsion values have strictly ordered J-costs. -/
theorem excitation_cost_ordering :
    excitationCost 0 = 0 ∧
    0 < excitationCost 11 ∧
    excitationCost 11 < excitationCost 17 :=
  ⟨excitationCost_ground,
   excitationCost_pos_of_ne_zero 11 (by omega),
   excitationCost_strictMono (by omega) (by omega)⟩

/-! ## Part 6: The Excitation Ordering Theorem -/

/-- **The Excitation Ordering Theorem for Q₃.**

    Among neutral-to-excited admissible ledger transitions on Q₃:

    1. **Edge-before-face (dimensional)**: The first nontrivial excitation is
       edge-supported (CW dimension 1), and the next independent excitation
       is face-supported (CW dimension 2).

    2. **Cost ordering**: J-cost respects the CW filtration strictly —
       ground costs zero, edge excitation costs less than face+edge.

    3. **Increment provenance**: The first increment equals the passive edge
       count and the second equals the face count of Q₃.

    4. **Canonical forcing**: The CW-cumulative schedule matches `generationTorsion`.

    This derives the `E_passive` / `cube_faces` increments from the CW
    structure of Q₃ combined with J-cost monotonicity, rather than taking
    them as unexplained mode labels. -/
structure ExcitationOrderingTheorem : Prop where
  edge_lower_dim_than_face :
    CubeCell.cwDim (.edge : CubeCell D) < CubeCell.cwDim (.face : CubeCell D)
  cw_torsion_is_canonical :
    cwCumulativeTorsion D = generationTorsion
  ground_zero_cost :
    excitationCost (cwCumulativeTorsion D .first) = 0
  edge_cheaper_than_face_edge :
    excitationCost (cwCumulativeTorsion D .second) <
      excitationCost (cwCumulativeTorsion D .third)
  first_increment_is_edges :
    cwCumulativeTorsion D .second - cwCumulativeTorsion D .first =
      (passive_field_edges D : ℤ)
  second_increment_is_faces :
    cwCumulativeTorsion D .third - cwCumulativeTorsion D .second =
      (cube_faces D : ℤ)

/-- The excitation ordering theorem holds for Q₃. -/
theorem excitation_ordering_holds : ExcitationOrderingTheorem where
  edge_lower_dim_than_face := edge_dim_lt_face_dim
  cw_torsion_is_canonical := cwTorsion_eq_generationTorsion
  ground_zero_cost := by simp [cwCumulativeTorsion, excitationCost, Jcost_unit0]
  edge_cheaper_than_face_edge := by
    show excitationCost (cwCumulativeTorsion D .second) <
      excitationCost (cwCumulativeTorsion D .third)
    simp only [cwTorsion_second, cwTorsion_third]
    exact excitationCost_strictMono (by omega) (by omega)
  first_increment_is_edges := first_increment_is_passive_edges
  second_increment_is_faces := second_increment_is_faces

/-! ## Part 7: Variational Selection — Edge Is Minimal Nontrivial Excitation -/

/-- Among all subcell types with nonzero passive coupling, edges have the
    smallest CW dimension. The variational principle (selecting cheapest
    excitation) therefore selects edge modes first. -/
theorem edge_is_minimal_nontrivial_excitation :
    ∀ (cell : CubeCell D),
    0 < passiveCoupling D cell →
    CubeCell.cwDim (.edge : CubeCell D) ≤ CubeCell.cwDim cell := by
  intro cell hpos
  cases cell with
  | vertex => simp [passiveCoupling] at hpos
  | edge => exact le_refl _
  | face => exact Nat.le_of_lt edge_dim_lt_face_dim

/-- The CW-ordering is *dimensional*, not numerical: face coupling (6) is
    numerically smaller than edge coupling (11), but edges come first because
    dim(edge) = 1 < dim(face) = 2.

    This makes explicit that generation ordering cannot be explained by
    "smallest torsion increment first" — it requires the geometric notion
    of subcell dimension. -/
theorem ordering_is_dimensional_not_numerical :
    (cube_faces D : ℤ) < (passive_field_edges D : ℤ) ∧
    CubeCell.cwDim (.edge : CubeCell D) < CubeCell.cwDim (.face : CubeCell D) := by
  constructor
  · simp [cube_faces, passive_field_edges, cube_edges, active_edges_per_tick, D]
  · exact edge_dim_lt_face_dim

/-! ## Part 8: Connection to Existing Filtration -/

/-- The CW torsion satisfies the incremental cube filtration. -/
theorem cwTorsion_incremental :
    IncrementalCubeTorsion D (cwCumulativeTorsion D) := by
  rw [cwTorsion_eq_generationTorsion]
  exact generationTorsion_incremental

/-- The CW torsion satisfies the full cube-generation filtration package. -/
theorem cwTorsion_has_filtration :
    CubeGenerationFiltration (cwCumulativeTorsion D) := by
  rw [cwTorsion_eq_generationTorsion]
  exact generationTorsion_has_cube_filtration

/-- From `ExcitationOrderingTheorem` we recover `CubeGenerationFiltration`. -/
theorem excitation_ordering_implies_filtration
    (h : ExcitationOrderingTheorem) :
    CubeGenerationFiltration generationTorsion := by
  rw [← h.cw_torsion_is_canonical]
  exact cwTorsion_has_filtration

/-! ## Part 9: Excitation Ordering Certificate -/

/-- Full certificate summarizing the CW-filtration route to generation torsion.

    **Proved**:
    - CW-dimensional ordering: dim(edge) < dim(face)
    - CW-cumulative torsion matches canonical schedule
    - J-cost strict ordering: ground < edge < face+edge
    - First increment = passive edges of Q₃
    - Second increment = faces of Q₃
    - Edge modes are the minimal nontrivial excitation (by CW dimension)
    - Ordering is dimensional (not numerical): 6 < 11 but edges come first
    - CW route recovers the full CubeGenerationFiltration package

    **Structural premise**: Excitations couple in order of CW dimension.
    This is a geometric principle about the cube rather than a mode label,
    but it is not yet derived from the cost functional. -/
theorem excitation_ordering_certificate :
    ExcitationOrderingTheorem ∧
    CubeGenerationFiltration generationTorsion ∧
    (∀ (cell : CubeCell D), 0 < passiveCoupling D cell →
      CubeCell.cwDim (.edge : CubeCell D) ≤ CubeCell.cwDim cell) ∧
    ((cube_faces D : ℤ) < (passive_field_edges D : ℤ)) :=
  ⟨excitation_ordering_holds,
   excitation_ordering_implies_filtration excitation_ordering_holds,
   edge_is_minimal_nontrivial_excitation,
   ordering_is_dimensional_not_numerical.1⟩

end ExcitationOrdering
end Masses
end IndisputableMonolith
