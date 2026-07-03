import IndisputableMonolith.Mathematics.HodgeDeltaBridge.DisplayMap
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FiniteCertificateTransfer

/-!
# δ-Hodge Bridge: conservative Hodge completion

This module instantiates the Delta-native completion discipline for Hodge.

The central predicate is intentionally explicit:

`AdmissibleRationalHodgeClass cl α`

means that `α` is displayed by a finite algebraic distinction certificate under
the fixed canonical cycle-class map `cl`.  This is not hidden inside the
classical Hodge statement.  The final classical proof must still prove
universality: every rational Hodge class compatible with `cl` is admissible.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement
open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity
open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FiniteCertificateTransfer

universe u

/-- A rational Hodge class is δ-admissible for a fixed cycle-class map exactly
when it is displayed by a finite algebraic distinction certificate. -/
def AdmissibleRationalHodgeClass
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) : Prop :=
  ∃ C : FiniteAlgebraicDistinctionCertificate X p, CertificateDisplaysClass cl C α

/-- Hodge display completion for a fixed `(X,p,cl)`: native data are finite
algebraic certificates, display data are rational Hodge classes, and
certification is exactly certificate display.  The `display` field is a harmless
projection to a chosen compatible display when such a class is supplied by the
certificate consumer; the proof-relevant content is `certifies`. -/
def hodgeCompletion
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) :
    Completion
      (FiniteAlgebraicDistinctionCertificate X p)
      (RationalHodgeClass.{u, u} X p)
      (FiniteAlgebraicDistinctionCertificate X p) where
  display := fun _ =>
    { cohomologyClass := cl.targetCohomology
      classVector := cl.targetCohomology.zero
      isHodge :=
        { degree_eq := cl.degree_eq
          complexifiedCarrier := fun _ => 0
          ppProjection := fun _ => 0
          ppProjection_exhausts := fun _ => rfl
          conjugation_symmetry := fun _ => by simp } }
  certifies := fun C α => CertificateDisplaysClass cl C α

/-- Conservative Hodge completion: every compatible rational Hodge class has a
finite algebraic distinction certificate.  This is the real hard bridge, kept as
a named condition rather than hidden in the theorem. -/
def ConservativeHodgeCompletion
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) : Prop :=
  ∀ (α : RationalHodgeClass.{u, u} X p)
    (_hcompat : α.cohomologyClass = cl.targetCohomology),
    AdmissibleRationalHodgeClass cl α

/-- Admissibility is equivalent to being in the display image of finite
algebraic distinction certificates. -/
theorem admissible_iff_certificate_display
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) :
    AdmissibleRationalHodgeClass cl α ↔
      ∃ C : FiniteAlgebraicDistinctionCertificate X p, CertificateDisplaysClass cl C α :=
  Iff.rfl

/-- A compatible class under a conservative Hodge completion has a finite
certificate. -/
theorem conservative_hodge_completion_transfers
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    {cl : CanonicalCycleClassMap.{u} X p}
    (hC : ConservativeHodgeCompletion cl)
    (α : RationalHodgeClass.{u, u} X p)
    (hcompat : α.cohomologyClass = cl.targetCohomology) :
    ∃ C : FiniteAlgebraicDistinctionCertificate X p, CertificateDisplaysClass cl C α :=
  hC α hcompat

/-- Conservative Hodge completion makes the generic finite-certificate transfer
theorem concrete for Hodge admissibility. -/
theorem hodge_completion_is_conservative_for_admissibility
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p) :
    ConservativeFor (hodgeCompletion cl) (AdmissibleRationalHodgeClass cl) := by
  intro α hα
  rcases hα with ⟨C, hC⟩
  exact ⟨C, hC⟩

/-- A rational Hodge class outside the finite-certificate display image is a
non-native completion artifact relative to the fixed Hodge completion. -/
def HodgeCompletionArtifact
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) : Prop :=
  ¬ AdmissibleRationalHodgeClass cl α

/-- Artifact criterion: non-admissibility is exactly absence of a finite
algebraic distinction certificate display. -/
theorem artifact_iff_no_certificate_display
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (cl : CanonicalCycleClassMap.{u} X p)
    (α : RationalHodgeClass.{u, u} X p) :
    HodgeCompletionArtifact cl α ↔
      ¬ ∃ C : FiniteAlgebraicDistinctionCertificate X p, CertificateDisplaysClass cl C α :=
  Iff.rfl

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

