import IndisputableMonolith.Mathematics.HodgeDeltaBridge.RefereeGradeClosure

/-!
# δ-Hodge Bridge: certificate selectors and universality criterion

This module turns `DeltaHodgeUniversality` into an explicit construction target.
For each fixed `(X,p,cl)`, a `FiniteCertificateSelector` chooses a finite
algebraic distinction certificate for every compatible rational Hodge class and
proves that the certificate displays that class.

This is still the hard theorem.  The improvement is that the remaining work is
now a concrete selector construction, not an abstract density phrase.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- A selector that assigns finite algebraic distinction certificates to every
compatible rational Hodge class for one fixed canonical cycle-class map. -/
structure FiniteCertificateSelector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) where
  select :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      FiniteAlgebraicDistinctionCertificate X p
  displays :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (hcompat : α.cohomologyClass = cl.targetCohomology),
      CertificateDisplaysClass cl (select α hcompat) α

/-- A finite-certificate selector yields conservative Hodge completion. -/
theorem conservative_completion_of_selector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    (S : FiniteCertificateSelector cl) :
    ConservativeHodgeCompletion cl := by
  intro α hcompat
  exact ⟨S.select α hcompat, S.displays α hcompat⟩

/-- Selector form of the fixed-map Hodge theorem. -/
theorem hodge_for_fixed_map_from_selector
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (S : FiniteCertificateSelector cl) :
    ∀ (α : RationalHodgeClass.{u, u} X p)
      (_hcompat : α.cohomologyClass = cl.targetCohomology),
      ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) := by
  intro α hcompat
  exact hodge_class_has_algebraic_cycle_of_conservative_completion
    cl (conservative_completion_of_selector S) α hcompat

/-- Global selector data for the δ-Hodge bridge: every `(X,p)` has a fixed
canonical cycle-class map and a finite-certificate selector for it. -/
structure GlobalFiniteCertificateSelector where
  cl :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      CanonicalCycleClassMap.{u} X p
  selector :
    ∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
      FiniteCertificateSelector (cl X p)

/-- Global selector data implies `DeltaHodgeUniversality`. -/
theorem delta_hodge_universality_of_global_selector
    (G : GlobalFiniteCertificateSelector.{u}) :
    DeltaHodgeUniversality.{u} := by
  intro X p
  exact ⟨G.cl X p, conservative_completion_of_selector (G.selector X p)⟩

/-- A global finite-certificate selector proves the referee-grade Hodge statement.
This is the sharpened next target: construct `GlobalFiniteCertificateSelector`
from actual algebraic geometry, not from a display stub. -/
theorem hodge_conjecture_from_global_finite_certificate_selector
    (G : GlobalFiniteCertificateSelector.{u}) :
    hodge_conjecture_unconditional_referee_grade.{u} :=
  referee_grade_hodge_reduced_to_delta_universality
    (delta_hodge_universality_of_global_selector G)

/-- The selector criterion is equivalent to the chosen constructive form of the
remaining target: one global selector is enough for final closure. -/
theorem global_selector_is_sufficient_for_final_goal :
    (Nonempty (GlobalFiniteCertificateSelector.{u})) →
      hodge_conjecture_unconditional_referee_grade.{u} := by
  intro h
  rcases h with ⟨G⟩
  exact hodge_conjecture_from_global_finite_certificate_selector G

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

