import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

/-!
# CPM Bridge: Hodge Instantiation (Abstract Scaffold)

This module provides an abstract, assumption-driven instantiation of the
CPM (Law of Existence) model for a Hodge-style setting. It avoids heavy
geometric analysis by factoring the concrete estimates into a bundled
assumptions structure. When the domain-specific inequalities are proven
elsewhere, this builder yields a `CPM.LawOfExistence.Model` and immediate
CPM consequences (A/B/C-style theorems) with explicit constants.

Constants are wired to the RS cone-projection route by default:
  - K_net = 1 (intrinsic cone projection)
  - C_proj = 2 (Hermitian rank-one, J''(1)=1 normalization)
while `C_eng` and `C_disp` are supplied by the user of the builder.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge
namespace Domain
namespace Hodge

open IndisputableMonolith.CPM.LawOfExistence

/-- Abstract assumptions encoding the domain-specific pieces needed to
build a CPM model for a Hodge-type problem. -/
structure Assumptions (β : Type) where
  /- Aggregated functionals -/
  defectMass : β → ℝ
  orthoMass  : β → ℝ
  energyGap  : β → ℝ
  tests      : β → ℝ
  /- Energy/dispersion constants -/
  Ceng  : ℝ
  Cdisp : ℝ
  hCeng_pos  : 0 < Ceng
  hCdisp_pos : 0 < Cdisp
  /- Projection-defect (cone) with RS constants (K_net=1, C_proj=2) -/
  projection_defect : ∀ a : β, defectMass a ≤ (1 : ℝ) * (2 : ℝ) * orthoMass a
  /- Energy control -/
  energy_control    : ∀ a : β, orthoMass a ≤ Ceng * energyGap a
  /- Dispersion/interface -/
  dispersion        : ∀ a : β, orthoMass a ≤ Cdisp * tests a

namespace Assumptions

variable {β : Type}

/-- Build a CPM model from the abstract assumptions. -/
def model (A : Assumptions β) : Model β where
  C := {
    Knet  := 1,
    Cproj := 2,
    Ceng  := A.Ceng,
    Cdisp := A.Cdisp,
    Knet_nonneg := by norm_num,
    Cproj_nonneg := by norm_num,
    Ceng_nonneg := le_of_lt A.hCeng_pos,
    Cdisp_nonneg := le_of_lt A.hCdisp_pos
  }
  defectMass := A.defectMass
  orthoMass  := A.orthoMass
  energyGap  := A.energyGap
  tests      := A.tests
  projection_defect := by
    intro a; simpa [one_mul] using A.projection_defect a
  energy_control    := A.energy_control
  dispersion        := A.dispersion

/-- Coercivity consequence: `E-E0 ≥ c_min · D` with `c_min = 1/(1·2·C_eng)`. -/
theorem coercivity (A : Assumptions β) (a : β) :
  (model A).energyGap a ≥ cmin (model A).C * (model A).defectMass a := by
  have hpos : 0 < (model A).C.Knet ∧ 0 < (model A).C.Cproj ∧ 0 < (model A).C.Ceng := by
    simp only [model]
    exact And.intro (by norm_num) (And.intro (by norm_num) A.hCeng_pos)
  exact Model.energyGap_ge_cmin_mul_defect (M:=model A) hpos a

/-- Aggregation consequence: `D ≤ (1·2·C_disp) · tests`. -/
theorem aggregation (A : Assumptions β) (a : β) :
  (model A).defectMass a
    ≤ ((model A).C.Knet * (model A).C.Cproj * (model A).C.Cdisp) * (model A).tests a := by
  simpa using Model.defect_le_constants_mul_tests (M:=model A) a

/-- Positivity of `c_min`. -/
theorem cmin_pos (A : Assumptions β) : 0 < cmin (model A).C := by
  have : 0 < (model A).C.Knet ∧ 0 < (model A).C.Cproj ∧ 0 < (model A).C.Ceng := by
    simp only [model]
    exact And.intro (by norm_num) (And.intro (by norm_num) A.hCeng_pos)
  simpa using IndisputableMonolith.CPM.LawOfExistence.cmin_pos (C:=(model A).C) this

end Assumptions

end Hodge
end Domain
end CPMBridge
end Verification
end IndisputableMonolith
