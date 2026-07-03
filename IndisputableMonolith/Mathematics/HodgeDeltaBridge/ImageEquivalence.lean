import IndisputableMonolith.Mathematics.HodgeDeltaBridge.ConservativeCompletion

/-!
# δ-Hodge Bridge: image equivalence

This module proves the usable δ-Hodge statement:

* admissible rational Hodge classes are exactly certificate-display classes;
* admissible rational Hodge classes have algebraic cycle representatives;
* a conservative Hodge completion upgrades compatibility to admissibility.

This is the point where the bridge becomes useful without pretending the
classical universality theorem has already been proved.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- The image of the finite-certificate display map for a fixed cycle-class map. -/
def CertificateDisplayImage
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) : Prop :=
  ∃ C : FiniteAlgebraicDistinctionCertificate X p, CertificateDisplaysClass cl C α

/-- The central image equivalence: δ-admissibility is exactly membership in the
finite certificate display image. -/
theorem admissible_iff_in_certificate_display_image
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) :
    AdmissibleRationalHodgeClass cl α ↔ CertificateDisplayImage cl α :=
  Iff.rfl

/-- Every δ-admissible rational Hodge class has an algebraic cycle
representative under the fixed canonical cycle-class map. -/
theorem hodge_class_has_algebraic_cycle_of_admissible
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p)
    (hα : AdmissibleRationalHodgeClass cl α) :
    ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) := by
  rcases hα with ⟨C, hC⟩
  exact certificate_display_has_cycle cl α C hC

/-- Under a conservative Hodge completion, every compatible rational Hodge class
has an algebraic cycle representative. -/
theorem hodge_class_has_algebraic_cycle_of_conservative_completion
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (hC : ConservativeHodgeCompletion cl)
    (α : RationalHodgeClass.{u, u} X p)
    (hcompat : α.cohomologyClass = cl.targetCohomology) :
    ∃ Z : AlgebraicCycle.{u, u} X p, Nonempty (CycleClassEquals cl Z α) :=
  hodge_class_has_algebraic_cycle_of_admissible cl α (hC α hcompat)

/-- Image equivalence plus non-admissibility gives the finite obstruction form:
if a compatible display class has no finite certificate, it is not admitted by
the δ-Hodge completion. -/
theorem no_certificate_is_completion_artifact
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p)
    (hno : ¬ CertificateDisplayImage cl α) :
    HodgeCompletionArtifact cl α := by
  exact hno

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

