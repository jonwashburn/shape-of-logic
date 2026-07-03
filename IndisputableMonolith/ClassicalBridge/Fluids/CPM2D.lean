import Mathlib
import IndisputableMonolith.CPM.LawOfExistence
import IndisputableMonolith.ClassicalBridge.Fluids.CPM
import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D

namespace IndisputableMonolith.ClassicalBridge.Fluids

/-!
# CPM2D (Milestone M4)

This file instantiates the **CPM core** (`IndisputableMonolith.CPM.LawOfExistence`) for the
finite-dimensional 2D Galerkin model (`Galerkin2D`).

Important: the nontrivial analytic inequalities needed for a real fluids proof are **not**
proved here.  Instead, we package them explicitly in a `...Hypothesis` structure, so downstream
theorems can state exactly what they depend on **without** using `axiom` or `sorry`.
-/

open IndisputableMonolith.CPM.LawOfExistence
-- `GalerkinState` lives directly in `IndisputableMonolith.ClassicalBridge.Fluids`
-- (the module is `...Fluids.Galerkin2D`, but there is no nested `namespace ...Galerkin2D`).

namespace CPM2D

/-- The discrete 2D Galerkin state type at truncation level `N`. -/
abbrev State (N : ℕ) : Type := GalerkinState N

/-- The four CPM functionals required by `CPM.LawOfExistence.Model`. -/
structure Functionals (N : ℕ) where
  defectMass : State N → ℝ
  orthoMass  : State N → ℝ
  energyGap  : State N → ℝ
  tests      : State N → ℝ

/-- Hypothesis bundle: a CPM instance for `GalerkinState N`.

This is *exactly* the data needed to build a `CPM.LawOfExistence.Model`.
-/
structure Hypothesis (N : ℕ) where
  C : Constants
  F : Functionals N
  /- Projection-Defect (A): D ≤ K_net · C_proj · ||proj_{S⊥}||² -/
  projection_defect : ∀ a : State N, F.defectMass a ≤ C.Knet * C.Cproj * F.orthoMass a
  /- Energy control (B): ||proj_{S⊥}||² ≤ C_eng · (E−E₀) -/
  energy_control    : ∀ a : State N, F.orthoMass a ≤ C.Ceng * F.energyGap a
  /- Dispersion/interface (C): ||proj_{S⊥}||² ≤ C_disp · sup tests -/
  dispersion        : ∀ a : State N, F.orthoMass a ≤ C.Cdisp * F.tests a

/-- Build a CPM `Model` from the hypothesis bundle. -/
noncomputable def model {N : ℕ} (H : Hypothesis N) : Model (State N) :=
  { C := H.C
    defectMass := H.F.defectMass
    orthoMass  := H.F.orthoMass
    energyGap  := H.F.energyGap
    tests      := H.F.tests
    projection_defect := H.projection_defect
    energy_control    := H.energy_control
    dispersion        := H.dispersion }

/-- Pack the `Model` into the bridge-local `CPMBridge` structure (for traceability notes). -/
noncomputable def bridge {N : ℕ} (H : Hypothesis N) : ClassicalBridge.Fluids.CPMBridge (State N) :=
  { model := model H
    defectMeaning := "Galerkin2D defectMass: discrete distance to structured (e.g. divergence-free / low-cost) subspace."
    energyMeaning := "Galerkin2D energyGap: discrete kinetic energy gap above the structured baseline."
    testsMeaning  := "Galerkin2D tests: supremum of local dispersion / window tests on the discrete state." }

/-!
## A fully proved (but minimal) concrete instantiation

To reduce the hypothesis layer, we provide an explicit choice of CPM constants and functionals
for which the A/B/C inequalities are **provable by reflexivity**.

This is not yet the physically meaningful CPM for fluids; it is a useful “base instance” that
lets downstream modules stop carrying `Hypothesis` when they only need a concrete CPM model.
-/

/-- A convenient all-ones constant bundle. -/
noncomputable def constantsOne : Constants :=
  { Knet := 1
    Cproj := 1
    Ceng := 1
    Cdisp := 1
    Knet_nonneg := by norm_num
    Cproj_nonneg := by norm_num
    Ceng_nonneg := by norm_num
    Cdisp_nonneg := by norm_num }

/-- Concrete functionals: everything is measured by `‖u‖^2` (a nonnegative scalar). -/
noncomputable def functionalsNormSq (N : ℕ) : Functionals N :=
  { defectMass := fun u => ‖u‖ ^ 2
    orthoMass  := fun u => ‖u‖ ^ 2
    energyGap  := fun u => ‖u‖ ^ 2
    tests      := fun u => ‖u‖ ^ 2 }

/-- A no-assumption CPM hypothesis instance using `constantsOne` and `functionalsNormSq`. -/
noncomputable def hypothesisNormSq (N : ℕ) : Hypothesis N :=
  { C := constantsOne
    F := functionalsNormSq N
    projection_defect := by
      intro a
      simp [constantsOne, functionalsNormSq]
    energy_control := by
      intro a
      simp [constantsOne, functionalsNormSq]
    dispersion := by
      intro a
      simp [constantsOne, functionalsNormSq] }

/-- The corresponding concrete CPM bridge instance (still minimal/placeholder). -/
noncomputable def bridgeNormSq (N : ℕ) : ClassicalBridge.Fluids.CPMBridge (State N) :=
  bridge (hypothesisNormSq N)

end CPM2D

end IndisputableMonolith.ClassicalBridge.Fluids
