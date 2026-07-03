/-
  PrimitiveRecognitionCalculus/RealCompletion.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K1 (`classical extension`), K4.14, A5

  This is the honest real-completion boundary. It embeds the quotient-native
  PRC rational surface into Lean's `ℝ` and records completeness as a
  classical-extension fact. It is not a claim that the PRC-internal Cauchy
  quotient has already been built.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Strength

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K4.14. The first real boundary: Lean's complete real line, reached only
under the classical-extension tag. -/
abbrev PRCRealBoundary : Type := ℝ

namespace PRCRealBoundary

/-- K4.14/A5. Embed a PRC rational into the real boundary through its
conservative rational display. -/
def ofRat (q : PRCRat) : PRCRealBoundary :=
  (q.toRat : ℝ)

@[simp] theorem ofRat_add (a b : PRCRat) :
    ofRat (a + b) = ofRat a + ofRat b := by
  unfold ofRat
  rw [PRCRat.toRat_add']
  norm_num

@[simp] theorem ofRat_mul (a b : PRCRat) :
    ofRat (a * b) = ofRat a * ofRat b := by
  unfold ofRat
  rw [PRCRat.toRat_mul']
  norm_num

@[simp] theorem ofRat_neg (a : PRCRat) :
    ofRat (-a) = -ofRat a := by
  unfold ofRat
  rw [PRCRat.toRat_neg']
  norm_num

@[simp] theorem ofRat_inv (a : PRCRat) :
    ofRat (a⁻¹) = (ofRat a)⁻¹ := by
  unfold ofRat
  rw [PRCRat.toRat_inv']
  norm_num

/-- K4.14. The real boundary carries Lean's complete-space structure. -/
theorem complete_space : CompleteSpace PRCRealBoundary := by
  infer_instance

end PRCRealBoundary

/-- K1/K4.14. Audit record: the real-completion boundary is a classical
extension until an internal PRC Cauchy quotient is built. -/
def realCompletionClaim : StrengthClaim where
  label := "K4.14_real_completion_boundary"
  tag := StrengthTag.classicalExtension
  statement := "The first PRC real boundary embeds PRCRat into Lean Real and uses classical completeness."

/-- K4.14. First real-completion boundary certificate. -/
structure RealCompletionBoundaryCertificate : Prop where
  real_boundary_exists : Nonempty PRCRealBoundary
  rational_embedding_exists : Nonempty (PRCRat → PRCRealBoundary)
  preserves_add : ∀ a b : PRCRat,
    PRCRealBoundary.ofRat (a + b) =
      PRCRealBoundary.ofRat a + PRCRealBoundary.ofRat b
  preserves_mul : ∀ a b : PRCRat,
    PRCRealBoundary.ofRat (a * b) =
      PRCRealBoundary.ofRat a * PRCRealBoundary.ofRat b
  complete : CompleteSpace PRCRealBoundary
  strength_tag : realCompletionClaim.tag = StrengthTag.classicalExtension

/-- K4.14. The classical real boundary is available and tagged honestly. -/
theorem real_completion_boundary_certificate :
    RealCompletionBoundaryCertificate where
  real_boundary_exists := ⟨0⟩
  rational_embedding_exists := ⟨PRCRealBoundary.ofRat⟩
  preserves_add := PRCRealBoundary.ofRat_add
  preserves_mul := PRCRealBoundary.ofRat_mul
  complete := PRCRealBoundary.complete_space
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
