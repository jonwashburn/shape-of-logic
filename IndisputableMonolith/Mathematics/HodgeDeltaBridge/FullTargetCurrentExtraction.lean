import IndisputableMonolith.Mathematics.HodgeDeltaBridge.EquationExtraction
import IndisputableMonolith.Mathematics.HodgeKingChowBridge

/-!
# δ-Hodge Bridge: full-target current-to-equation extraction

The older referee-grade Hodge stack routes each rational Hodge class through a
closed integral `(p,p)` current, then through the Harvey-Shiffman/Chow surface.
That is not enough for the strengthened full-target statement unless the
cycle-class map is fixed for the supplied full target before individual classes
are selected.

This file isolates the honest bridge surface:

* choose one `FullTargetCycleClassMap H`;
* for every class in `H`, provide a closed integral `(p,p)` current representing
  that class;
* extract finite homogeneous equation-cut support whose display hits that class
  under the fixed map.

The file does not assert that such data exists.  It proves that if this
current-to-equation extraction data is supplied, then it packages into the
finite equation extraction criterion from the previous layer.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement
open HodgeChainsAndCurrents
open HodgeKingChowBridge

universe u

/-- Current-backed equation extraction for one class in a supplied full target,
relative to a fixed full-target cycle-class map. -/
structure FullTargetCurrentEquationExtraction
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (F : FullTargetCycleClassMap H)
    (α : H.hodgeClass) where
  currentSpace : CurrentSpaceData X
  current : ClosedIntegralPPCurrent p currentSpace
  represents_class :
    hodgeClassFromClosedIntegralPPCurrent current = H.toRationalHodgeClass α
  analyticCycle : AnalyticCycleFromCurrent p currentSpace current
  support : FiniteEquationExtractionSupport X p
  support_matches_current : Prop
  support_matches_current_holds : support_matches_current
  displays :
    CertificateDisplaysClass
      F.cl
      support.toEquationFiniteCertificate.toFiniteCertificate
      (H.toRationalHodgeClass α)

namespace FullTargetCurrentEquationExtraction

/-- Forget the current/analytic provenance and keep the finite equation
extraction needed by the δ-Hodge bridge. -/
def toEquationExtraction
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    {F : FullTargetCycleClassMap H}
    {α : H.hodgeClass}
    (E : FullTargetCurrentEquationExtraction F α) :
    FullTargetEquationExtraction F α where
  support := E.support
  displays := E.displays

end FullTargetCurrentEquationExtraction

/-- Family version for one supplied full target.  The fixed map belongs to the
target, while currents and equation extractions may vary by class. -/
structure FullTargetCurrentEquationExtractionFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  map : FullTargetCycleClassMap H
  extract :
    ∀ α : H.hodgeClass, FullTargetCurrentEquationExtraction map α

/-- Current-equation extraction gives the finite equation extraction family. -/
def equationExtractionFamilyOfCurrentExtractionFamily
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {H : FullRationalHodgeTarget X p}
    (E : FullTargetCurrentEquationExtractionFamily H) :
    FullTargetEquationExtractionFamily H where
  map := E.map
  extract := fun α => (E.extract α).toEquationExtraction

/-- Global current-to-equation extraction surface. -/
structure GlobalFullTargetCurrentEquationExtractionFamily where
  extraction :
    ∀ (X : SmoothProjectiveComplexVariety.{u})
      (p : ℕ)
      (H : FullRationalHodgeTarget X p),
      FullTargetCurrentEquationExtractionFamily H

/-- Global current-to-equation extraction yields the finite equation extraction
criterion. -/
def globalEquationExtractionOfCurrentExtraction
    (G : GlobalFullTargetCurrentEquationExtractionFamily.{u}) :
    GlobalFullTargetEquationExtractionFamily.{u} where
  extraction := fun X p H =>
    equationExtractionFamilyOfCurrentExtractionFamily (G.extraction X p H)

/-- The current-to-equation extraction surface is sufficient for the strengthened
full-target Hodge statement. -/
theorem full_target_hodge_from_global_current_equation_extraction
    (G : GlobalFullTargetCurrentEquationExtractionFamily.{u}) :
    hodge_conjecture_unconditional_full_target.{u} :=
  full_target_hodge_from_global_equation_extraction
    (globalEquationExtractionOfCurrentExtraction G)

/-- Nonempty global current-to-equation extraction data is sufficient for final
full-target Hodge closure. -/
theorem global_full_target_current_equation_extraction_is_sufficient :
    Nonempty (GlobalFullTargetCurrentEquationExtractionFamily.{u}) →
      hodge_conjecture_unconditional_full_target.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact full_target_hodge_from_global_current_equation_extraction G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

