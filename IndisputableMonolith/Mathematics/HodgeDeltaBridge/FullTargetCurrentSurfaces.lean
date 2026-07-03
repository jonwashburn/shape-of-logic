import IndisputableMonolith.Mathematics.HodgeDeltaBridge.FullTargetCurrentExtraction

/-!
# δ-Hodge Bridge: split full-target current surfaces

The previous layer bundled two different mathematical jobs:

1. represent each full-target rational Hodge class by a closed integral
   `(p,p)` current while keeping one fixed full-target cycle-class map;
2. convert each such current into finite homogeneous equation-cut data whose
   certificate display is the supplied class.

This file separates those jobs.  The split is useful because the first belongs
to the analytic/current side of the Hodge program, while the second belongs to
Harvey-Shiffman/Chow/GAGA/equation extraction.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement
open HodgeChainsAndCurrents
open HodgeKingChowBridge

universe u

/-- Surface A, one class: a closed integral `(p,p)` current representing a class
in the supplied full Hodge target, relative to a fixed target map. -/
structure FullTargetCurrentRepresentation
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (_F : FullTargetCycleClassMap H)
    (α : H.hodgeClass) where
  currentSpace : CurrentSpaceData X
  current : ClosedIntegralPPCurrent p currentSpace
  represents_class :
    hodgeClassFromClosedIntegralPPCurrent current = H.toRationalHodgeClass α

/-- Surface B, one class: finite equation-cut Chow extraction from a current
representation. -/
structure CurrentToEquationChowExtraction
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    {F : FullTargetCycleClassMap H}
    {α : H.hodgeClass}
    (R : FullTargetCurrentRepresentation F α) where
  analyticCycle : AnalyticCycleFromCurrent p R.currentSpace R.current
  support : FiniteEquationExtractionSupport X p
  support_matches_current : Prop
  support_matches_current_holds : support_matches_current
  displays :
    CertificateDisplaysClass
      F.cl
      support.toEquationFiniteCertificate.toFiniteCertificate
      (H.toRationalHodgeClass α)

/-- Split surface package for one supplied full target. -/
structure FullTargetCurrentSurfacePackage
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  map : FullTargetCycleClassMap H
  represent : ∀ α : H.hodgeClass, FullTargetCurrentRepresentation map α
  chowExtract :
    ∀ α : H.hodgeClass, CurrentToEquationChowExtraction (represent α)

/-- The split surface package assembles into the previous bundled
current-equation extraction family. -/
def currentExtractionFamilyOfSurfacePackage
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (P : FullTargetCurrentSurfacePackage H) :
    FullTargetCurrentEquationExtractionFamily H where
  map := P.map
  extract := fun α =>
    let R := P.represent α
    let C := P.chowExtract α
    { currentSpace := R.currentSpace
      current := R.current
      represents_class := R.represents_class
      analyticCycle := C.analyticCycle
      support := C.support
      support_matches_current := C.support_matches_current
      support_matches_current_holds := C.support_matches_current_holds
      displays := C.displays }

/-- Global split surface package. -/
structure GlobalFullTargetCurrentSurfacePackage where
  surface :
    ∀ (X : SmoothProjectiveComplexVariety.{u})
      (p : ℕ)
      (H : FullRationalHodgeTarget X p),
      FullTargetCurrentSurfacePackage H

/-- Global split surfaces assemble into global current-equation extraction. -/
def globalCurrentExtractionOfSurfacePackage
    (G : GlobalFullTargetCurrentSurfacePackage.{u}) :
    GlobalFullTargetCurrentEquationExtractionFamily.{u} where
  extraction := fun X p H =>
    currentExtractionFamilyOfSurfacePackage (G.surface X p H)

/-- The split full-target current surfaces are sufficient for the strengthened
Hodge target. -/
theorem full_target_hodge_from_global_current_surfaces
    (G : GlobalFullTargetCurrentSurfacePackage.{u}) :
    hodge_conjecture_unconditional_full_target.{u} :=
  full_target_hodge_from_global_current_equation_extraction
    (globalCurrentExtractionOfSurfacePackage G)

/-- Nonempty split full-target current surface data is sufficient for final
full-target Hodge closure. -/
theorem global_full_target_current_surfaces_are_sufficient :
    Nonempty (GlobalFullTargetCurrentSurfacePackage.{u}) →
      hodge_conjecture_unconditional_full_target.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact full_target_hodge_from_global_current_surfaces G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

