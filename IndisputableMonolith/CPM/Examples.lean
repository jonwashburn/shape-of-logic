import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

/-!
# CPM Examples and Unit Tests

This module provides sample instantiations of the abstract CPM model,
demonstrating usage of the core theorems and validating the infrastructure.

## Contents

1. Trivial model (all functionals zero) — baseline sanity check
2. Subspace model (K_net = C_proj = 1) — tests the subspace shortcut
3. RS cone model — tests the canonical RS constants
4. Custom model — demonstrates typical domain instantiation pattern

All examples include explicit verification that the core theorems apply.
-/

namespace IndisputableMonolith
namespace CPM
namespace Examples

open LawOfExistence

/-! ## Example 1: Trivial Model -/

/-- Trivial model: all functionals return zero.
This validates that the CPM inequalities hold vacuously. -/
def trivialModel : Model Unit := {
  C := {
    Knet := 1,
    Cproj := 1,
    Ceng := 1,
    Cdisp := 1,
    Knet_nonneg := by norm_num,
    Cproj_nonneg := by norm_num,
    Ceng_nonneg := by norm_num,
    Cdisp_nonneg := by norm_num
  },
  defectMass := fun _ => 0,
  orthoMass := fun _ => 0,
  energyGap := fun _ => 0,
  tests := fun _ => 0,
  projection_defect := by intro _; norm_num,
  energy_control := by intro _; norm_num,
  dispersion := by intro _; norm_num
}

/-- Verify coercivity theorem applies to trivial model. -/
example : trivialModel.defectMass () ≤
    (trivialModel.C.Knet * trivialModel.C.Cproj * trivialModel.C.Ceng) *
    trivialModel.energyGap () :=
  trivialModel.defect_le_constants_mul_energyGap ()

/-- Verify aggregation theorem applies to trivial model. -/
example : trivialModel.defectMass () ≤
    (trivialModel.C.Knet * trivialModel.C.Cproj * trivialModel.C.Cdisp) *
    trivialModel.tests () :=
  trivialModel.defect_le_constants_mul_tests ()

/-! ## Example 2: Subspace Model -/

/-- Subspace model: K_net = C_proj = 1, functionals satisfy equality.
This tests the subspace shortcut lemmas. -/
def subspaceModel : Model Unit := {
  C := {
    Knet := 1,
    Cproj := 1,
    Ceng := 2,
    Cdisp := 1,
    Knet_nonneg := by norm_num,
    Cproj_nonneg := by norm_num,
    Ceng_nonneg := by norm_num,
    Cdisp_nonneg := by norm_num
  },
  defectMass := fun _ => 1,
  orthoMass := fun _ => 1,
  energyGap := fun _ => 1,
  tests := fun _ => 2,
  projection_defect := by intro _; norm_num,
  energy_control := by intro _; norm_num,
  dispersion := by intro _; norm_num
}

/-- Verify subspace shortcut: D ≤ orthoMass when K_net = C_proj = 1. -/
example : subspaceModel.defectMass () ≤ subspaceModel.orthoMass () :=
  Model.defect_le_ortho_of_Knet_one_Cproj_one subspaceModel rfl rfl ()

/-- Verify subspace equality when orthoMass = defectMass. -/
example : subspaceModel.defectMass () = subspaceModel.orthoMass () :=
  Model.defect_eq_ortho_of_subspace_case subspaceModel rfl rfl (fun _ => rfl) ()

/-! ## Example 3: RS Cone Constants Model -/

/-- Model using the canonical RS cone constants. -/
def rsConeModel : Model Unit := {
  C := RS.coneConstants,
  defectMass := fun _ => 1,
  orthoMass := fun _ => 1,
  energyGap := fun _ => 2,
  tests := fun _ => 1,
  projection_defect := by
    intro _
    simp only [RS.cone_Knet_eq_one, RS.cone_Cproj_eq_two]
    norm_num,
  energy_control := by
    intro _
    simp only [RS.cone_Ceng_eq_one]
    norm_num,
  dispersion := by
    intro _
    simp only [RS.cone_Cdisp_eq_one]
    norm_num
}

/-- Verify the RS model has positive constants. -/
lemma rsConeModel_pos :
    0 < rsConeModel.C.Knet ∧ 0 < rsConeModel.C.Cproj ∧ 0 < rsConeModel.C.Ceng := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [rsConeModel, RS.coneConstants]

/-- Verify coercivity with explicit c_min for RS model. -/
example : rsConeModel.energyGap () ≥ cmin rsConeModel.C * rsConeModel.defectMass () :=
  Model.energyGap_ge_cmin_mul_defect rsConeModel rsConeModel_pos ()

/-- The RS cone coercivity constant is 1/2. -/
lemma rs_cone_cmin_value : cmin RS.coneConstants = 1 / 2 := by
  simp only [cmin, RS.cone_Knet_eq_one, RS.cone_Cproj_eq_two, RS.cone_Ceng_eq_one]
  norm_num

/-! ## Example 4: Eight-Tick Net Constants Model -/

/-- Model using the eight-tick aligned constants (K_net = (9/7)², C_proj = 2).
This matches the constants derived in the LaTeX support document. -/
noncomputable def eightTickModel : Model Unit := {
  C := {
    Knet := (9/7)^2,
    Cproj := 2,
    Ceng := 1,
    Cdisp := 1,
    Knet_nonneg := by norm_num,
    Cproj_nonneg := by norm_num,
    Ceng_nonneg := by norm_num,
    Cdisp_nonneg := by norm_num
  },
  defectMass := fun _ => 1,
  orthoMass := fun _ => 1,
  energyGap := fun _ => 4,
  tests := fun _ => 1,
  projection_defect := by
    intro _
    -- Need: 1 ≤ (9/7)^2 * 2 * 1
    have h : (1 : ℝ) ≤ (9/7)^2 * 2 := by norm_num
    linarith,
  energy_control := by intro _; norm_num,
  dispersion := by intro _; norm_num
}

/-- The eight-tick coercivity constant is 49/162. -/
lemma eight_tick_cmin_value : cmin eightTickModel.C = 49 / 162 := by
  simp only [cmin, eightTickModel]
  norm_num

/-- Verify positivity of eight-tick constants. -/
lemma eightTickModel_pos :
    0 < eightTickModel.C.Knet ∧ 0 < eightTickModel.C.Cproj ∧ 0 < eightTickModel.C.Ceng := by
  simp only [eightTickModel]
  norm_num

/-- Verify coercivity applies to eight-tick model. -/
example : eightTickModel.energyGap () ≥ cmin eightTickModel.C * eightTickModel.defectMass () :=
  Model.energyGap_ge_cmin_mul_defect eightTickModel eightTickModel_pos ()

/-! ## Demonstration: cpmsimp tactic -/

/-- Demonstration that `cpmsimp` normalizes products correctly. -/
example (a b c d : ℝ) : a * b * c * d = a * (b * c) * d := by cpmsimp

example (a b c : ℝ) : a * b * c = b * a * c := by cpmsimp

end Examples
end CPM
end IndisputableMonolith
