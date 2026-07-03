import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

namespace IndisputableMonolith
namespace URCGenerators

open IndisputableMonolith.CPM.LawOfExistence

/-!
# CPM Method Certificate (Standalone)

This certificate intentionally avoids any domain/problem-specific material.
It certifies:

- the generic CPM A/B/C consequences are available for any CPM `Model`, and
- the CPM assumptions are consistent (witnessed by a concrete toy model).

This file is part of the CPM-standalone layer.
-/

/-- Standalone certificate for the CPM method. -/
structure CPMMethodCert where
  deriving Repr

/-- A small toy CPM model witnessing consistency of the assumptions.

All functionals are constant 1, and the inequalities hold numerically with
`Knet = 1`, `Cproj = 2`, `Ceng = 1`, `Cdisp = 1`.

This is not intended to model physics; it is only a nontrivial consistency witness.
-/
noncomputable def toyModel : Model Unit where
  C := {
    Knet := 1,
    Cproj := 2,
    Ceng := 1,
    Cdisp := 1,
    Knet_nonneg := by norm_num,
    Cproj_nonneg := by norm_num,
    Ceng_nonneg := by norm_num,
    Cdisp_nonneg := by norm_num
  }
  defectMass := fun _ => 1
  orthoMass  := fun _ => 1
  energyGap  := fun _ => 1
  tests      := fun _ => 1
  projection_defect := by
    intro _
    norm_num
  energy_control := by
    intro _
    norm_num
  dispersion := by
    intro _
    norm_num

lemma toyModel_defect_pos : toyModel.defectMass () > 0 := by
  simp [toyModel]

lemma toyModel_energy_pos : toyModel.energyGap () > 0 := by
  simp [toyModel]

lemma toyModel_cmin_pos : 0 < cmin toyModel.C := by
  have hpos : 0 < toyModel.C.Knet ∧ 0 < toyModel.C.Cproj ∧ 0 < toyModel.C.Ceng := by
    simp [toyModel]
  simpa using (IndisputableMonolith.CPM.LawOfExistence.cmin_pos (C:=toyModel.C) hpos)

/-- Verification predicate for the standalone CPM method certificate.

It asserts the generic A/B/C consequences (for any CPM model) and includes a
concrete toy model witness to avoid vacuity.
-/
@[simp] def CPMMethodCert.verified (_c : CPMMethodCert) : Prop :=
  (∀ {β : Type} (M : Model β) (a : β),
      M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Ceng) * M.energyGap a)
  ∧
  (∀ {β : Type} (M : Model β)
      (_hpos : 0 < M.C.Knet ∧ 0 < M.C.Cproj ∧ 0 < M.C.Ceng) (a : β),
      M.energyGap a ≥ cmin M.C * M.defectMass a)
  ∧
  (∀ {β : Type} (M : Model β) (a : β),
      M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a)
  ∧
  (∃ toy : Model Unit,
      toy.defectMass () > 0 ∧ toy.energyGap () > 0 ∧ 0 < cmin toy.C)

/-- The standalone CPM method certificate verifies. -/
@[simp] theorem CPMMethodCert.verified_any (c : CPMMethodCert) :
    CPMMethodCert.verified c := by
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro β M a
    exact IndisputableMonolith.CPM.LawOfExistence.Model.defect_le_constants_mul_energyGap (M:=M) a
  · intro β M hpos a
    exact IndisputableMonolith.CPM.LawOfExistence.Model.energyGap_ge_cmin_mul_defect (M:=M) hpos a
  · intro β M a
    exact IndisputableMonolith.CPM.LawOfExistence.Model.defect_le_constants_mul_tests (M:=M) a
  · refine ⟨toyModel, toyModel_defect_pos, toyModel_energy_pos, toyModel_cmin_pos⟩

end URCGenerators
end IndisputableMonolith
