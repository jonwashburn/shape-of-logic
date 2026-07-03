/-
  PrimitiveRecognitionCalculus/PRCJCostDistanceTriangle.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 9a: prove or isolate the local triangle modulus for
    `PRCJCostDistance`.

  This pass translates the remaining PRC distance theorem into an exact
  verifier-rational inequality. No PRC object is redefined in verifier terms;
  the verifier formula is only a display theorem and blocker statement.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealNullSetoid

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Verifier display of the J-cost square-gap distance. This is not the PRC
definition; it is the rational formula shown by `PRCJCostDistance_toRat`. -/
def PRCJCostDistanceRatDisplay (x y : ℚ) : ℚ :=
  let g : ℚ := 1 + (x - y) * (x - y)
  (g + g⁻¹) / 2 - 1

/-- Display theorem for the PRC J-cost distance. -/
theorem PRCJCostDistance_toRat (a b : PRCRat) :
    (PRCJCostDistance a b).toRat =
      PRCJCostDistanceRatDisplay a.toRat b.toRat := by
  unfold PRCJCostDistance PRCJCostDistanceRatDisplay
  rw [PRCJCost.onPRCRat_toRat, PRCSquareGap_toRat]

/-- Exact verifier-rational inequality still needed for the null-distance
quotient. It supplies a PRC rational `delta`, but the analytic estimate itself
is stated only on the conservative rational displays. -/
def PRCJCostDistanceVerifierTriangleTarget : Prop :=
  ∀ eps : PRCRat, PRCRat.positive eps →
    ∃ delta : PRCRat, PRCRat.positive delta ∧
      ∀ x y z : ℚ,
        PRCJCostDistanceRatDisplay x y < delta.toRat →
          PRCJCostDistanceRatDisplay y z < delta.toRat →
            PRCJCostDistanceRatDisplay x z < eps.toRat

/-- The verifier-rational triangle inequality closes the PRC triangle-modulus
target by display transport. -/
theorem PRCJCostDistanceTriangleModulusTarget_of_verifier
    (h : PRCJCostDistanceVerifierTriangleTarget) :
    PRCJCostDistanceTriangleModulusTarget := by
  intro eps heps
  rcases h eps heps with ⟨delta, hdelta_pos, hdelta⟩
  refine ⟨delta, hdelta_pos, ?_⟩
  intro a b c hab hbc
  rw [PRCRat.lt_iff_toRat_lt] at hab hbc ⊢
  rw [PRCJCostDistance_toRat] at hab hbc ⊢
  exact hdelta a.toRat b.toRat c.toRat hab hbc

/-- Once the verifier-rational inequality is proved, the final null-distance
setoid target follows. -/
theorem PRCNullDistanceSetoidTarget_of_verifier_triangle
    (h : PRCJCostDistanceVerifierTriangleTarget) :
    PRCNullDistanceSetoidTarget :=
  PRCNullDistanceSetoidTarget_of_triangle_modulus
    (PRCJCostDistanceTriangleModulusTarget_of_verifier h)

/-- Conditional certificate for step 9a. The only remaining mathematical
problem is now the explicit rational inequality in
`PRCJCostDistanceVerifierTriangleTarget`. -/
structure PRCJCostDistanceTriangleConditionalCertificate : Prop where
  distance_display :
    ∀ a b : PRCRat,
      (PRCJCostDistance a b).toRat =
        PRCJCostDistanceRatDisplay a.toRat b.toRat
  verifier_triangle_target :
    PRCJCostDistanceVerifierTriangleTarget = PRCJCostDistanceVerifierTriangleTarget
  triangle_from_verifier :
    PRCJCostDistanceVerifierTriangleTarget → PRCJCostDistanceTriangleModulusTarget
  setoid_from_verifier :
    PRCJCostDistanceVerifierTriangleTarget → PRCNullDistanceSetoidTarget

/-- Build Order step 9a conditional closure: PRC triangle transport is reduced
to the displayed rational inequality. -/
theorem prc_jcost_distance_triangle_conditional_certificate :
    PRCJCostDistanceTriangleConditionalCertificate where
  distance_display := PRCJCostDistance_toRat
  verifier_triangle_target := rfl
  triangle_from_verifier := PRCJCostDistanceTriangleModulusTarget_of_verifier
  setoid_from_verifier := PRCNullDistanceSetoidTarget_of_verifier_triangle

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
