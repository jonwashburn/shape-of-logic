import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Masses.BaselineDerivation
import IndisputableMonolith.Foundation.GroundStateDynamics
import IndisputableMonolith.Foundation.ParticleGenerations
import IndisputableMonolith.Foundation.WindingCharges
import IndisputableMonolith.RecogSpec.RSLedger

/-!
# Generation Torsion Bridge — Geometric Source of Truth

This module provides the single authoritative derivation of charged-generation
torsion {0, 11, 17} from Q₃ cube geometry, and proves it matches every
other representation in the codebase.

## Derivation Chain

The torsion schedule is defined entirely from D=3 cube combinatorics:
- Gen 1 (ground): τ₁ = 0 (no geometric coupling)
- Gen 2 (edge-dressed): τ₂ = E_passive(D) = cube_edges(D) − 1 = 11
- Gen 3 (face+edge-dressed): τ₃ = W_endo(D) = E_passive(D) + cube_faces(D) = 17

The endogenous third-generation value `W_endo(3) = 11 + 6 = 17` numerically
coincides with the crystallographic wallpaper-group count (Fedorov, 1891).
That coincidence is proved by `BaselineDerivation.W_endo_at_D3` but is NOT
the primary source of the integer here; the primary route is
`E_passive + F`, which is forced by cube arithmetic alone.

## What This Module Certifies

1. **No raw numerals**: `cubeGeometricTorsion` contains zero literal integers.
2. **Agreement with Anchor.Integers.tau**: pointwise equality.
3. **Agreement with RecogSpec.generationTorsion**: pointwise equality.
4. **Forcing predicate**: an explicit structural predicate `CubeAdmissibleTorsion`
   whose unique solution is the canonical schedule.

## Remaining Premise

The predicate `CubeAdmissibleTorsion` encodes the physical assignment rule
(ground / passive-edge / face+edge modes). This rule is a structural
premise about how fermion generations couple to cube features, NOT a
consequence of the cost functional alone. Until that coupling is derived
from the RCL, this module upgrades the gap from "hardcoded numerals" to
"explicit structural premise with a uniqueness proof."

See `ExcitationOrdering.lean` for a stronger route: the CW-filtration of
Q₃ derives the edge-before-face ordering from subcell dimension and proves
J-cost strict ordering on φ-power ratios.
-/

namespace IndisputableMonolith
namespace Masses
namespace GenerationTorsionBridge

open IndisputableMonolith.Constants.AlphaDerivation
open IndisputableMonolith.Masses.BaselineDerivation
open IndisputableMonolith.Foundation
open IndisputableMonolith.Foundation.VariationalDynamics
open IndisputableMonolith.RecogSpec

/-! ## Part 1: The Geometric Torsion Schedule -/

/-- Charged-generation torsion defined from Q₃ cube geometry alone.
    No raw numerals; every branch is a cube-combinatorial function of D. -/
def cubeGeometricTorsion : Generation → ℤ
  | .first  => 0
  | .second => (passive_field_edges D : ℤ)
  | .third  => (W_endo D : ℤ)

@[simp] lemma cubeGeoTorsion_first : cubeGeometricTorsion .first = 0 := rfl

@[simp] lemma cubeGeoTorsion_second : cubeGeometricTorsion .second = (passive_field_edges D : ℤ) := rfl

@[simp] lemma cubeGeoTorsion_third : cubeGeometricTorsion .third = (W_endo D : ℤ) := rfl

/-- Numeric verification: the geometric schedule evaluates to {0, 11, 17}. -/
theorem cubeGeoTorsion_values :
    cubeGeometricTorsion .first = 0 ∧
    cubeGeometricTorsion .second = 11 ∧
    cubeGeometricTorsion .third = 17 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [cubeGeometricTorsion, passive_field_edges, cube_edges, active_edges_per_tick, D]
  · simp [cubeGeometricTorsion, W_endo, passive_field_edges, cube_edges,
          active_edges_per_tick, cube_faces, D]

/-! ## Part 2: Agreement with RecogSpec.generationTorsion -/

/-- The geometric schedule equals the RecogSpec definition pointwise. -/
theorem cubeGeoTorsion_eq_generationTorsion :
    cubeGeometricTorsion = generationTorsion := by
  funext g
  cases g with
  | first => rfl
  | second =>
    simp [cubeGeometricTorsion, generationTorsion,
          passive_field_edges, cube_edges, active_edges_per_tick, D]
  | third =>
    simp [cubeGeometricTorsion, generationTorsion,
          W_endo, passive_field_edges, cube_edges, active_edges_per_tick, cube_faces, D]

/-- Pointwise: second generation. -/
theorem cubeGeoTorsion_second_eq :
    cubeGeometricTorsion .second = generationTorsion .second := by
  simp [cubeGeometricTorsion, generationTorsion,
        passive_field_edges, cube_edges, active_edges_per_tick, D]

/-- Pointwise: third generation. -/
theorem cubeGeoTorsion_third_eq :
    cubeGeometricTorsion .third = generationTorsion .third := by
  simp [cubeGeometricTorsion, generationTorsion,
        W_endo, passive_field_edges, cube_edges, active_edges_per_tick, cube_faces, D]

/-! ## Part 3: Agreement with Masses.Integers.tau -/

/-- The geometric schedule matches `Integers.tau` at generation index 0. -/
theorem cubeGeoTorsion_matches_tau_0 :
    cubeGeometricTorsion .first = Integers.tau 0 := by
  simp [cubeGeometricTorsion, Integers.tau]

/-- The geometric schedule matches `Integers.tau` at generation index 1. -/
theorem cubeGeoTorsion_matches_tau_1 :
    cubeGeometricTorsion .second = Integers.tau 1 := by
  simp [cubeGeometricTorsion, Integers.tau, Anchor.E_passive]

/-- The geometric schedule matches `Integers.tau` at generation index 2. -/
theorem cubeGeoTorsion_matches_tau_2 :
    cubeGeometricTorsion .third = Integers.tau 2 := by
  simp [cubeGeometricTorsion, Integers.tau, Anchor.W, W_endo,
        passive_field_edges, cube_edges, active_edges_per_tick,
        cube_faces, D, wallpaper_groups]

/-! ## Part 4: Structural Provenance -/

/-- The second-generation torsion is the passive edge count of Q₃. -/
theorem second_gen_is_passive_edges :
    cubeGeometricTorsion .second = ↑(cube_edges D - active_edges_per_tick) := by
  simp [cubeGeometricTorsion, passive_field_edges]

/-- The third-generation torsion is E_passive + F (endogenous wallpaper route). -/
theorem third_gen_is_Epass_plus_F :
    cubeGeometricTorsion .third = ↑(passive_field_edges D + cube_faces D) := by
  simp [cubeGeometricTorsion, W_endo]

/-- The endogenous wallpaper count coincides with the crystallographic constant. -/
theorem endogenous_matches_crystallographic :
    (W_endo D : ℤ) = (wallpaper_groups : ℤ) := by
  have := W_endo_at_D3
  exact_mod_cast this

/-- The torsion step from gen 2 to gen 3 equals the face count of Q₃. -/
theorem gen3_minus_gen2_is_faces :
    cubeGeometricTorsion .third - cubeGeometricTorsion .second =
      (cube_faces D : ℤ) := by
  simp [cubeGeometricTorsion, W_endo]

/-! ## Part 5: Cube-Admissible Torsion — Forcing Predicate -/

/-- A torsion schedule is cube-admissible if it assigns:
    - Ground mode (gen 1): zero coupling → τ = 0
    - Edge mode (gen 2): passive-edge coupling → τ = E_passive
    - Face+edge mode (gen 3): passive-edge + face coupling → τ = E_passive + F

    This is a STRUCTURAL PREMISE about how fermion generations couple to
    cube features. It is explicitly stated rather than buried in comments. -/
structure CubeAdmissibleTorsion (d : ℕ) (τ : Generation → ℤ) : Prop where
  ground_is_zero : τ .first = 0
  edge_mode : τ .second = (passive_field_edges d : ℤ)
  face_edge_mode : τ .third = (passive_field_edges d + cube_faces d : ℤ)

/-- The geometric torsion schedule is cube-admissible at D=3. -/
theorem cubeGeoTorsion_admissible : CubeAdmissibleTorsion D cubeGeometricTorsion where
  ground_is_zero := rfl
  edge_mode := rfl
  face_edge_mode := by simp [cubeGeometricTorsion, W_endo]

/-- `generationTorsion` is cube-admissible at D=3. -/
theorem generationTorsion_admissible : CubeAdmissibleTorsion D generationTorsion := by
  rw [← cubeGeoTorsion_eq_generationTorsion]
  exact cubeGeoTorsion_admissible

/-- Any cube-admissible schedule at dimension d equals the geometric schedule at d. -/
theorem cubeAdmissible_unique (d : ℕ) (τ : Generation → ℤ)
    (h : CubeAdmissibleTorsion d τ) :
    τ = fun g => match g with
      | .first  => 0
      | .second => (passive_field_edges d : ℤ)
      | .third  => (passive_field_edges d + cube_faces d : ℤ) := by
  funext g
  cases g with
  | first => exact h.ground_is_zero
  | second => exact h.edge_mode
  | third => exact h.face_edge_mode

/-- At D=3, any cube-admissible schedule equals the canonical `generationTorsion`. -/
theorem cubeAdmissible_forces_canonical (τ : Generation → ℤ)
    (h : CubeAdmissibleTorsion D τ) :
    τ = generationTorsion := by
  rw [← cubeGeoTorsion_eq_generationTorsion]
  funext g
  cases g with
  | first => exact h.ground_is_zero
  | second => exact h.edge_mode
  | third =>
    simp only [cubeGeometricTorsion, W_endo]
    exact h.face_edge_mode

/-- Torsion ordering follows from cube arithmetic (no native_decide needed). -/
theorem cubeAdmissible_ordered (d : ℕ) (τ : Generation → ℤ) (hd : 2 ≤ d)
    (h : CubeAdmissibleTorsion d τ) :
    τ .first < τ .second ∧ τ .second < τ .third := by
  constructor
  · rw [h.ground_is_zero, h.edge_mode]
    have := (generation_ordering_general d hd).1
    exact_mod_cast this
  · rw [h.edge_mode, h.face_edge_mode]
    have : 0 < cube_faces d := by unfold cube_faces; omega
    linarith [show (0 : ℤ) < (cube_faces d : ℤ) from by exact_mod_cast this]

/-! ## Part 6: Ground State from Variational Dynamics -/

/-- The one-channel configuration whose ratio is `φ^n`. -/
noncomputable def phiRatioConfig (n : ℤ) : InitialCondition.Configuration 1 :=
  GroundStateDynamics.ratioConfig (IndisputableMonolith.Constants.phi ^ n)
    (zpow_pos IndisputableMonolith.Constants.phi_pos n)

/-- If a φ-power ratio equals 1, its exponent is zero. -/
theorem phi_zpow_eq_one_iff (n : ℤ) :
    IndisputableMonolith.Constants.phi ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · exact hn
    · rcases lt_or_gt_of_ne hn with hneg | hpos
      · have hlt : (1 : ℝ) < IndisputableMonolith.Constants.phi ^ (-n) := by
          exact one_lt_zpow₀ IndisputableMonolith.Constants.one_lt_phi (by omega)
        have hone : IndisputableMonolith.Constants.phi ^ (-n) = 1 := by
          calc
            IndisputableMonolith.Constants.phi ^ (-n)
                = 1 * IndisputableMonolith.Constants.phi ^ (-n) := by ring
            _ = IndisputableMonolith.Constants.phi ^ n * IndisputableMonolith.Constants.phi ^ (-n) := by
                  rw [h]
            _ = IndisputableMonolith.Constants.phi ^ (n + (-n)) := by
                  rw [zpow_add₀ IndisputableMonolith.Constants.phi_ne_zero]
            _ = 1 := by simp
        have hcontra : False := by
          rw [hone] at hlt
          exact (not_lt_of_ge (show (1 : ℝ) ≤ 1 by rfl)) hlt
        exact False.elim hcontra
      · have hlt : (1 : ℝ) < IndisputableMonolith.Constants.phi ^ n := by
          exact one_lt_zpow₀ IndisputableMonolith.Constants.one_lt_phi hpos
        have hcontra : False := by
          rw [h] at hlt
          exact (not_lt_of_ge (show (1 : ℝ) ≤ 1 by rfl)) hlt
        exact False.elim hcontra
  · intro hn
    simp [hn]

/-- A torsion schedule is ground-state compatible if its first generation,
when realized as a one-channel φ-power ratio, is a neutral equilibrium of
the variational dynamics. -/
def GroundStateCompatibleTorsion (τ : Generation → ℤ) : Prop :=
  IsEquilibrium (phiRatioConfig (τ .first)) ∧
    log_charge (phiRatioConfig (τ .first)) = 0

/-- Variational stability in the neutral sector forces the ground exponent to zero. -/
theorem groundStateCompatible_forces_ground_zero (τ : Generation → ℤ)
    (h : GroundStateCompatibleTorsion τ) :
    τ .first = 0 := by
  rcases h with ⟨hEq, hCharge⟩
  have hRatio :
      IndisputableMonolith.Constants.phi ^ (τ .first) = 1 :=
    GroundStateDynamics.stable_zero_charge_ratio_eq_one
      (IndisputableMonolith.Constants.phi ^ (τ .first))
      (zpow_pos IndisputableMonolith.Constants.phi_pos _)
      hEq hCharge
  exact (phi_zpow_eq_one_iff (τ .first)).mp hRatio

/-! ## Part 7: Incremental Filtration and Slot Count -/

/-- Increment-only version of cube admissibility.

This removes the mode labels and keeps only the cumulative step data:
- ground state sits at zero torsion;
- the first jump adds the passive-edge count;
- the second jump adds the face count.

This is a more algebraic statement of the same structural premise. -/
structure IncrementalCubeTorsion (d : ℕ) (τ : Generation → ℤ) : Prop where
  ground_is_zero : τ .first = 0
  edge_increment :
    τ .second - τ .first = (passive_field_edges d : ℤ)
  face_increment :
    τ .third - τ .second = (cube_faces d : ℤ)

/-- Cube admissibility is equivalent to the incremental two-step filtration. -/
theorem cubeAdmissible_iff_incremental (d : ℕ) (τ : Generation → ℤ) :
    CubeAdmissibleTorsion d τ ↔ IncrementalCubeTorsion d τ := by
  constructor
  · intro h
    refine ⟨h.ground_is_zero, ?_, ?_⟩
    · rw [h.ground_is_zero, h.edge_mode]
      ring
    · rw [h.edge_mode, h.face_edge_mode]
      ring
  · intro h
    refine ⟨h.ground_is_zero, ?_, ?_⟩
    · simpa [h.ground_is_zero] using h.edge_increment
    · have hSecond : τ .second = (passive_field_edges d : ℤ) := by
        simpa [h.ground_is_zero] using h.edge_increment
      calc
        τ .third = (τ .third - τ .second) + τ .second := by ring
        _ = (cube_faces d : ℤ) + (passive_field_edges d : ℤ) := by
          rw [h.face_increment, hSecond]
        _ = (passive_field_edges d + cube_faces d : ℤ) := by ring

/-- The canonical geometric torsion schedule also satisfies the incremental view. -/
theorem cubeGeoTorsion_incremental : IncrementalCubeTorsion D cubeGeometricTorsion := by
  exact (cubeAdmissible_iff_incremental D cubeGeometricTorsion).mp cubeGeoTorsion_admissible

/-- `generationTorsion` satisfies the incremental cube filtration. -/
theorem generationTorsion_incremental : IncrementalCubeTorsion D generationTorsion := by
  exact (cubeAdmissible_iff_incremental D generationTorsion).mp generationTorsion_admissible

/-- The incremental cube filtration is enough to force canonical torsion. -/
theorem incremental_forces_canonical (τ : Generation → ℤ)
    (h : IncrementalCubeTorsion D τ) :
    τ = generationTorsion := by
  exact cubeAdmissible_forces_canonical τ
    ((cubeAdmissible_iff_incremental D τ).mpr h)

/-- Number of generation slots inherited from the D=3 cube face-pair count. -/
def generationSlotCount : ℕ := ParticleGenerations.face_pairs D

/-- The cube contributes exactly three generation slots. -/
theorem generationSlotCount_eq_three : generationSlotCount = 3 := by
  simpa [generationSlotCount, D] using ParticleGenerations.face_pairs_at_D3

/-- The generation slot count equals the number of independent Q₃ loops. -/
theorem generationSlotCount_eq_loopCount :
    generationSlotCount = WindingCharges.independent_loop_count 3 := by
  unfold generationSlotCount
  simpa [D] using WindingCharges.loops_eq_face_pairs_D3.symm

/-- Pack the current strongest structural explanation of charged-generation torsion.

At the present theorem surface, this is the sharpest honest statement:
- the cube contributes exactly three generation slots;
- those slots coincide with the three independent Q₃ loops / face-pairs;
- torsion accumulates by an edge increment followed by a face increment.

What still remains open is deriving this filtration from the cost functional
rather than taking it as a geometric premise. -/
structure CubeGenerationFiltration (τ : Generation → ℤ) : Prop where
  slot_count : generationSlotCount = 3
  loop_facepair_unification :
    generationSlotCount = WindingCharges.independent_loop_count 3
  torsion_steps : IncrementalCubeTorsion D τ

/-- The canonical schedule has the full cube-generation filtration package. -/
theorem generationTorsion_has_cube_filtration :
    CubeGenerationFiltration generationTorsion where
  slot_count := generationSlotCount_eq_three
  loop_facepair_unification := generationSlotCount_eq_loopCount
  torsion_steps := generationTorsion_incremental

/-- Any torsion schedule with the cube-generation filtration is canonical. -/
theorem cubeFiltration_forces_canonical (τ : Generation → ℤ)
    (h : CubeGenerationFiltration τ) :
    τ = generationTorsion :=
  incremental_forces_canonical τ h.torsion_steps

/-! ## Part 8: Minimal Loop Excitation Between Generations -/

/-- Cumulative count of independent Q₃ loop-layers excited by each generation. -/
def canonicalLoopExcitation : Generation → ℕ
  | .first => 0
  | .second => 1
  | .third => 2

/-- Minimal excitation profile: each later generation activates exactly one
new independent loop layer, and the third generation exhausts the available
three-loop budget of Q₃. -/
structure MinimalLoopExcitation (ℓ : Generation → ℕ) : Prop where
  ground_level : ℓ .first = 0
  second_adds_one : ℓ .second = ℓ .first + 1
  third_adds_one : ℓ .third = ℓ .second + 1
  exhausts_cube_loops : ℓ .third + 1 = WindingCharges.independent_loop_count 3

/-- The canonical loop excitation profile satisfies the minimal-step theorem. -/
theorem canonicalLoopExcitation_minimal :
    MinimalLoopExcitation canonicalLoopExcitation where
  ground_level := rfl
  second_adds_one := rfl
  third_adds_one := rfl
  exhausts_cube_loops := by
    simp [canonicalLoopExcitation, WindingCharges.three_independent_loops_D3]

/-- Minimal one-new-loop-per-generation-step excitation is unique. -/
theorem minimalLoopExcitation_unique (ℓ : Generation → ℕ)
    (h : MinimalLoopExcitation ℓ) :
    ℓ = canonicalLoopExcitation := by
  funext g
  cases g with
  | first =>
      exact h.ground_level
  | second =>
      calc
        ℓ .second = ℓ .first + 1 := h.second_adds_one
        _ = 0 + 1 := by rw [h.ground_level]
        _ = canonicalLoopExcitation .second := by simp [canonicalLoopExcitation]
  | third =>
      calc
        ℓ .third = ℓ .second + 1 := h.third_adds_one
        _ = (ℓ .first + 1) + 1 := by rw [h.second_adds_one]
        _ = (0 + 1) + 1 := by rw [h.ground_level]
        _ = canonicalLoopExcitation .third := by simp [canonicalLoopExcitation]

/-- There is exactly one minimal loop-excitation profile on the three generations. -/
theorem one_new_independent_loop_per_generation_step :
    ∃! ℓ : Generation → ℕ, MinimalLoopExcitation ℓ := by
  refine ⟨canonicalLoopExcitation, canonicalLoopExcitation_minimal, ?_⟩
  intro ℓ hℓ
  exact minimalLoopExcitation_unique ℓ hℓ

/-- The minimal loop-excitation profile matches the generation slot count. -/
theorem minimalLoopExcitation_matches_generation_slots (ℓ : Generation → ℕ)
    (h : MinimalLoopExcitation ℓ) :
    ℓ .third + 1 = generationSlotCount := by
  rw [h.exhausts_cube_loops, generationSlotCount_eq_loopCount.symm]

/-! ## Part 9: Direct RSLedger Integration -/

/-- An RSLedger whose torsion is cube-admissible at D=3 has canonical torsion.
    This replaces the bare hypothesis `L.torsion = generationTorsion` with
    a structural premise. -/
theorem rsLedger_torsion_from_cube (L : RSLedger)
    (h : CubeAdmissibleTorsion D L.torsion) :
    L.torsion = generationTorsion :=
  cubeAdmissible_forces_canonical L.torsion h

end GenerationTorsionBridge
end Masses
end IndisputableMonolith
