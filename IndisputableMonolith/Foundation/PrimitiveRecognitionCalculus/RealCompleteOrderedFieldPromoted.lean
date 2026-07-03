/-
  PrimitiveRecognitionCalculus/RealCompleteOrderedFieldPromoted.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10: promote the proved add, neg, mul, order, and
    representative-completeness targets into one complete ordered-field
    certificate surface over `PRCRealNullClosed`.

  This is a certificate-promotion layer. It does not alias the internal carrier
  to Lean `ℝ`; it bundles the theorem surfaces already proved for the PRC null
  quotient.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompleteness

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Promoted Step 10 certificate: the internal null quotient has the closed
operations and theorem surfaces needed by the current complete ordered-field
layer. Full Mathlib typeclass instances remain a later packaging pass. -/
structure PRCRealCompleteOrderedFieldPromotedCertificate : Prop where
  carrier : Nonempty PRCRealNullClosed
  rat_embedding : Nonempty (PRCRat → PRCRealNullClosed)
  add_closure : PRCRealAddClosureTarget
  add_congruence : PRCRealAddCongruenceTarget
  add_operation :
    Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)
  neg_closure : PRCRealNegClosureTarget
  neg_congruence : PRCRealNegCongruenceTarget
  neg_operation : Nonempty (PRCRealNullClosed → PRCRealNullClosed)
  mul_closure : PRCRealMulClosureTarget
  mul_congruence : PRCRealMulCongruenceTarget
  mul_operation :
    Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)
  order_congruence : PRCRealOrderCongruenceTarget
  representative_completeness : PRCRealCompletenessTarget
  first_pass_certificate : PRCRealCompleteOrderedFieldConditionalCertificate
  product_continuity_certificate : PRCRealProductContinuityCertificate
  order_congruence_certificate : PRCRealOrderCongruenceCertificate
  completeness_certificate : PRCRealCompletenessSharpenedCertificate
  strength_tag : StrengthTag.traceClosure = StrengthTag.traceClosure

theorem prc_real_complete_ordered_field_promoted_certificate :
    PRCRealCompleteOrderedFieldPromotedCertificate where
  carrier := ⟨PRCRealNullClosed.ofRat 0⟩
  rat_embedding := ⟨PRCRealNullClosed.ofRat⟩
  add_closure := PRCRealAddClosureTarget_proved
  add_congruence := PRCRealAddCongruenceTarget_proved
  add_operation :=
    ⟨PRCRealNullClosed.addOf
      PRCRealAddClosureTarget_proved
      PRCRealAddCongruenceTarget_proved⟩
  neg_closure := PRCRealNegClosureTarget_proved
  neg_congruence := PRCRealNegCongruenceTarget_proved
  neg_operation :=
    ⟨PRCRealNullClosed.negOf
      PRCRealNegClosureTarget_proved
      PRCRealNegCongruenceTarget_proved⟩
  mul_closure := PRCRealMulClosureTarget_of_bounded_continuity
    PRCCauchySeqEventuallyBoundedTarget_proved
    PRCJCostDistanceMulBoundedContinuityTarget_proved
  mul_congruence := PRCRealMulCongruenceTarget_of_bounded_continuity
    PRCCauchySeqEventuallyBoundedTarget_proved
    PRCJCostDistanceMulBoundedContinuityTarget_proved
  mul_operation :=
    ⟨PRCRealNullClosed.mulOf
      (PRCRealMulClosureTarget_of_bounded_continuity
        PRCCauchySeqEventuallyBoundedTarget_proved
        PRCJCostDistanceMulBoundedContinuityTarget_proved)
      (PRCRealMulCongruenceTarget_of_bounded_continuity
        PRCCauchySeqEventuallyBoundedTarget_proved
        PRCJCostDistanceMulBoundedContinuityTarget_proved)⟩
  order_congruence := PRCRealOrderCongruenceTarget_proved
  representative_completeness := PRCRealCompletenessTarget_proved
  first_pass_certificate := prc_real_complete_ordered_field_conditional_certificate
  product_continuity_certificate := prc_real_product_continuity_certificate
  order_congruence_certificate := prc_real_order_congruence_certificate
  completeness_certificate := prc_real_completeness_sharpened_certificate
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
