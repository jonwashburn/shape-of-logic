import IndisputableMonolith.Mathematics.HodgeDeltaBridge.FullTargetEquationSelector

/-!
# δ-Hodge Bridge: full-target equation realization target

`GlobalFullTargetEquationSelector` is the current sufficient criterion, but as
a construction target it is still one level too packaged.  This file exposes the
actual object that must be built for each rational Hodge class: a finite
homogeneous equation-cut certificate whose display is that class, relative to a
cycle-class map into the already supplied full Hodge target.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- A finite homogeneous equation-cut certificate realizing one class in a full
Hodge target. -/
structure FullTargetEquationRealization
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (F : FullTargetCycleClassMap H)
    (α : H.hodgeClass) where
  certificate : EquationFiniteCertificate X p
  displays :
    CertificateDisplaysClass
      F.cl
      certificate.toFiniteCertificate
      (H.toRationalHodgeClass α)

/-- A realization family for one supplied full target: choose the fixed
cycle-class map into that target, then realize every target class by finite
homogeneous equations. -/
structure FullTargetEquationRealizationFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  map : FullTargetCycleClassMap H
  realize : ∀ α : H.hodgeClass, FullTargetEquationRealization map α

/-- A realization family packages into the selector criterion. -/
def selectorOfRealizationFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (R : FullTargetEquationRealizationFamily H) :
    FullTargetEquationSelector H where
  map := R.map
  select := fun α => (R.realize α).certificate
  displays := fun α => (R.realize α).displays

/-- Global realization data: the exact algebraic geometry work remaining. -/
structure GlobalFullTargetEquationRealizationFamily where
  realization :
    ∀ (X : SmoothProjectiveComplexVariety.{u})
      (p : ℕ)
      (H : FullRationalHodgeTarget X p),
      FullTargetEquationRealizationFamily H

/-- Global realization data yields the global selector criterion. -/
def globalSelectorOfRealizationFamily
    (G : GlobalFullTargetEquationRealizationFamily.{u}) :
    GlobalFullTargetEquationSelector.{u} where
  selector := fun X p H => selectorOfRealizationFamily (G.realization X p H)

/-- The strongest current construction target: build global full-target
equation realizations, and the strengthened Hodge target follows. -/
theorem full_target_hodge_from_global_realization_family
    (G : GlobalFullTargetEquationRealizationFamily.{u}) :
    hodge_conjecture_unconditional_full_target.{u} :=
  full_target_hodge_from_global_equation_selector
    (globalSelectorOfRealizationFamily G)

/-- Nonempty global realization data is sufficient for the strengthened final
target. -/
theorem global_full_target_realization_family_is_sufficient :
    Nonempty (GlobalFullTargetEquationRealizationFamily.{u}) →
      hodge_conjecture_unconditional_full_target.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact full_target_hodge_from_global_realization_family G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

