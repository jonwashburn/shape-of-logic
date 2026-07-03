/-
  PrimitiveRecognitionCalculus/PRCJCostDistanceVerifierTriangle.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 9b: prove or isolate the verifier-rational triangle
    inequality for the displayed J-cost distance.

  This pass removes endpoint bookkeeping. The displayed distance depends only
  on the rational increment, so the remaining blocker is an additive two-leg
  modulus for increments `p` and `q`.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceTriangle

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- One-increment display of the rational J-cost distance. -/
def PRCJCostDistanceIncrementDisplay (t : ℚ) : ℚ :=
  PRCJCostDistanceRatDisplay 0 t

/-- The displayed distance is translation-invariant: it depends only on the
increment between the endpoints. -/
theorem PRCJCostDistanceRatDisplay_as_increment (x y : ℚ) :
    PRCJCostDistanceRatDisplay x y =
      PRCJCostDistanceIncrementDisplay (x - y) := by
  simp [PRCJCostDistanceIncrementDisplay, PRCJCostDistanceRatDisplay]
  ring_nf

/-- Sharper exact blocker: an additive two-leg modulus for rational increments.
This is the mathematical core behind the three-endpoint verifier triangle
target. -/
def PRCJCostDistanceIncrementTriangleTarget : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ delta : PRCRat, PRCRat.positive delta ∧
      ∀ p q : ℚ,
        PRCJCostDistanceIncrementDisplay p < delta.toRat →
          PRCJCostDistanceIncrementDisplay q < delta.toRat →
            PRCJCostDistanceIncrementDisplay (p + q) < eps.toRat

/-- The increment-only triangle target implies the verifier-rational
three-endpoint triangle target. -/
theorem PRCJCostDistanceVerifierTriangleTarget_of_increment
    (h : PRCJCostDistanceIncrementTriangleTarget) :
    PRCJCostDistanceVerifierTriangleTarget := by
  intro eps heps
  rcases h eps heps with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, hdelta_pos, ?_⟩
  intro x y z hxy hyz
  have hxy' :
      PRCJCostDistanceIncrementDisplay (x - y) < delta.toRat := by
    rwa [PRCJCostDistanceRatDisplay_as_increment] at hxy
  have hyz' :
      PRCJCostDistanceIncrementDisplay (y - z) < delta.toRat := by
    rwa [PRCJCostDistanceRatDisplay_as_increment] at hyz
  have hsum :
      PRCJCostDistanceIncrementDisplay ((x - y) + (y - z)) < eps.toRat :=
    hdelta (x - y) (y - z) hxy' hyz'
  have hxz :
      PRCJCostDistanceRatDisplay x z =
        PRCJCostDistanceIncrementDisplay ((x - y) + (y - z)) := by
    rw [PRCJCostDistanceRatDisplay_as_increment]
    congr
    ring
  rwa [hxz]

/-- The increment-only blocker closes the whole PRC null-distance setoid chain. -/
theorem PRCNullDistanceSetoidTarget_of_increment_triangle
    (h : PRCJCostDistanceIncrementTriangleTarget) :
    PRCNullDistanceSetoidTarget :=
  PRCNullDistanceSetoidTarget_of_verifier_triangle
    (PRCJCostDistanceVerifierTriangleTarget_of_increment h)

/-- Conditional certificate for step 9b. The only remaining theorem is now the
increment-only modulus target. -/
structure PRCJCostDistanceVerifierTriangleConditionalCertificate : Prop where
  translation_invariance :
    ∀ x y : ℚ,
      PRCJCostDistanceRatDisplay x y =
        PRCJCostDistanceIncrementDisplay (x - y)
  increment_triangle_target :
    PRCJCostDistanceIncrementTriangleTarget = PRCJCostDistanceIncrementTriangleTarget
  verifier_from_increment :
    PRCJCostDistanceIncrementTriangleTarget → PRCJCostDistanceVerifierTriangleTarget
  setoid_from_increment :
    PRCJCostDistanceIncrementTriangleTarget → PRCNullDistanceSetoidTarget

/-- Build Order step 9b conditional closure: the verifier triangle target is
reduced to a one-dimensional additive increment estimate. -/
theorem prc_jcost_distance_verifier_triangle_conditional_certificate :
    PRCJCostDistanceVerifierTriangleConditionalCertificate where
  translation_invariance := PRCJCostDistanceRatDisplay_as_increment
  increment_triangle_target := rfl
  verifier_from_increment := PRCJCostDistanceVerifierTriangleTarget_of_increment
  setoid_from_increment := PRCNullDistanceSetoidTarget_of_increment_triangle

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
