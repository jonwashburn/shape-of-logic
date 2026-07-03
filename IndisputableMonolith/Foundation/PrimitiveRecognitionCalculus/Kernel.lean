/-
  PrimitiveRecognitionCalculus/Kernel.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Aggregate import for the first PRC kernel pass:

    δ → trace → SameT/DiffT → substitution → quotient → ℕ → ℤ → ℚ

  The ℤ and ℚ stages are PRC-owned quotient surfaces with internal
  equivalence relations (balanced length for `PRCInt`; cross-multiplication
  for `PRCRat`). The maps into Lean's `ℤ` and `ℚ` are conservative verifier
  displays, proved well-defined from the internal characterizations.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Strength
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Basic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.SameDiff
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.TraceLogic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FormalSystem
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Inevitability
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Quotient
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitArithmetic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitDivisibility
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitEuclidean
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RationalField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RecognizerBridge
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.TraceClosure
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCauchy
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealNullSetoid
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceTriangle
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceVerifierTriangle
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceIncrementTriangle
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompleteOrderedField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealMulBoundedContinuity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealBoundednessModulus
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealProductContinuity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealOrderCongruence
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompleteness
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompleteOrderedFieldPromoted
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealCompletion

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K7/A2. First-pass PRC kernel certificate:
the analytic specification has concrete Lean objects for each stage in the
first theorem chain. This is a bundling certificate, not yet the final
inevitability theorem. -/
structure KernelFirstPassCertificate : Prop where
  strength_tags_exist : Nonempty StrengthTag
  trace_syntax_exists : Nonempty Trace
  judgment_surface_exists : Nonempty TraceJudgment
  /-- Stable finite-trace predicates carry the first PRC logic surface. -/
  trace_logic : TraceLogicCertificate
  /-- Expressive formal systems admit a PRC trace embedding. -/
  formal_system : FormalSystemCertificate
  /-- Every admissible foundation carries a PRC trace core. -/
  inevitability : PRCInevitabilityCertificate
  quotient_surface_exists :
    ∀ (J : TraceJudgment) (T : Trace), Nonempty (EndpointClass J T)
  orbit_nat_equivalence : Nonempty (DistinctionNat ≃ Nat)
  /-- Orbit addition is verifier-faithful. -/
  orbit_add_faithful :
    ∀ a b : DistinctionNat, (a + b).toNat = a.toNat + b.toNat
  /-- Orbit multiplication is verifier-faithful. -/
  orbit_mul_faithful :
    ∀ a b : DistinctionNat, (a * b).toNat = a.toNat * b.toNat
  prc_integer_surface_exists : Nonempty PRCInt
  prc_rational_surface_exists : Nonempty PRCRat
  /-- The internal balanced-length relation characterizes signed-orbit
  equivalence in PRC integers (K4.9). -/
  prc_int_balanced_iff_display :
    ∀ a b : SignedOrbit,
      SignedOrbit.balanced a b ↔ a.toInt = b.toInt
  /-- The internal cross-multiplication relation characterizes ratio-orbit
  equivalence in PRC rationals (K4.10). -/
  prc_rat_cross_iff_display :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq a b ↔ a.toRat = b.toRat
  /-- The PRC integer display is injective on the quotient. -/
  prc_int_display_injective : Function.Injective PRCInt.toInt
  /-- The PRC rational display is injective on the quotient. -/
  prc_rat_display_injective : Function.Injective PRCRat.toRat
  /-- The PRC integer surface is isomorphic to verifier `ℤ`. -/
  prc_int_equiv_int : Nonempty (PRCInt ≃ ℤ)
  /-- Internal signed-orbit order and absolute value are closed. -/
  integer_order : IntegerOrderCertificate
  /-- Native orbit divisibility, units, factorization, and prime-orbit predicates are closed. -/
  orbit_divisibility : DistinctionNat.OrbitDivisibilityCertificate
  /-- Native Euclidean quotient/remainder, GCD, and coprime predicates are closed. -/
  orbit_euclidean : DistinctionNat.OrbitEuclideanCertificate
  /-- PRC rational J-cost, canonical RCL, and bridge to existing real uniqueness are closed. -/
  prc_jcost : PRCJCost.PRCJCostCertificate
  /-- PRC rational field-style laws, division, positivity, and quotient-level J-cost are packaged. -/
  rational_field : RationalFieldCertificate
  /-- Positive PRC ratios carry recognition cost and bridge to the Law-of-Logic J-cost chain. -/
  recognizer_bridge : PRCRecognizerBridgeCertificate
  /-- Addition on PRC integers is commutative. -/
  prc_int_add_comm : ∀ a b : PRCInt, a + b = b + a
  /-- Addition on PRC integers is associative. -/
  prc_int_add_assoc : ∀ a b c : PRCInt, a + b + c = a + (b + c)
  /-- Multiplication on PRC integers is commutative. -/
  prc_int_mul_comm : ∀ a b : PRCInt, a * b = b * a
  /-- Multiplication on PRC integers is associative. -/
  prc_int_mul_assoc : ∀ a b c : PRCInt, a * b * c = a * (b * c)
  /-- Multiplication distributes over addition. -/
  prc_int_left_distrib :
    ∀ a b c : PRCInt, a * (b + c) = a * b + a * c
  /-- Negation is the additive inverse on PRC integers. -/
  prc_int_add_negate : ∀ a : PRCInt, a + (-a) = 0
  /-- The PRC rational display preserves addition. -/
  prc_rat_display_add :
    ∀ a b : PRCRat, (a + b).toRat = a.toRat + b.toRat
  /-- The PRC rational display preserves multiplication. -/
  prc_rat_display_mul :
    ∀ a b : PRCRat, (a * b).toRat = a.toRat * b.toRat
  /-- The PRC rational display preserves reciprocal. -/
  prc_rat_display_inv :
    ∀ a : PRCRat, (a⁻¹).toRat = (a.toRat)⁻¹
  /-- Ratio reciprocal uses internal signed-orbit absolute value for the denominator. -/
  ratio_recip_internal_den :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recipNonzero a h).den = a.num.abs
  /-- Addition on PRC rationals is commutative. -/
  prc_rat_add_comm : ∀ a b : PRCRat, a + b = b + a
  /-- Multiplication on PRC rationals is commutative. -/
  prc_rat_mul_comm : ∀ a b : PRCRat, a * b = b * a
  /-- Multiplication distributes over addition on PRC rationals. -/
  prc_rat_left_distrib :
    ∀ a b c : PRCRat, a * (b + c) = a * b + a * c
  /-- Nonzero PRC rationals multiply by their reciprocal to one. -/
  prc_rat_mul_recip_cancel :
    ∀ a : PRCRat, a.toRat ≠ 0 → a * a⁻¹ = 1
  /-- The completed trace boundary is inhabited and trace-closure tagged. -/
  trace_closure_boundary : TraceClosureCertificate
  /-- Internal Cauchy ledgers and the first PRC real quotient carrier are trace-closure tagged. -/
  real_cauchy : PRCRealCauchyCertificate
  /-- The final null-distance setoid is reduced to the exact J-cost triangle-modulus target. -/
  real_null_setoid : PRCRealNullSetoidConditionalCertificate
  /-- The J-cost distance triangle target is reduced to an exact rational display inequality. -/
  jcost_distance_triangle : PRCJCostDistanceTriangleConditionalCertificate
  /-- The verifier-rational triangle target is reduced to an increment-only modulus. -/
  jcost_distance_verifier_triangle : PRCJCostDistanceVerifierTriangleConditionalCertificate
  /-- The increment-only J-cost modulus closes the null-distance setoid chain. -/
  jcost_distance_increment_triangle : PRCJCostDistanceIncrementTriangleCertificate
  /-- The first complete ordered field pass closes add/neg and names mul/order/completeness targets. -/
  real_complete_ordered_field : PRCRealCompleteOrderedFieldConditionalCertificate
  /-- Multiplication on the null quotient is reduced to boundedness and bounded product continuity. -/
  real_mul_bounded_continuity : PRCRealMulBoundedContinuityConditionalCertificate
  /-- Every J-cost Cauchy ledger is eventually PRC-bounded. -/
  real_boundedness_modulus : PRCRealBoundednessModulusCertificate
  /-- Bounded product-continuity closes multiplication on the null quotient. -/
  real_product_continuity : PRCRealProductContinuityCertificate
  /-- Eventual non-strict order descends to the null-distance quotient. -/
  real_order_congruence : PRCRealOrderCongruenceCertificate
  /-- Internal completeness is sharpened to the exact Cauchy-of-Cauchy diagonal target. -/
  real_completeness : PRCRealCompletenessSharpenedCertificate
  /-- The complete ordered-field certificate surface now carries proved mul, order, and completeness targets. -/
  real_complete_ordered_field_promoted :
    PRCRealCompleteOrderedFieldPromotedCertificate
  /-- The real-completion boundary is inhabited and classical-extension tagged. -/
  real_completion_boundary : RealCompletionBoundaryCertificate
  signed_orbit_display : Nonempty (SignedOrbit → ℤ)
  ratio_orbit_display : Nonempty (RatioOrbit → ℚ)

/-- K7/A2. The first-pass kernel certificate is inhabited. -/
theorem kernel_first_pass_certificate :
    KernelFirstPassCertificate where
  strength_tags_exist := ⟨StrengthTag.deltaOnly⟩
  trace_syntax_exists := ⟨Trace.empty⟩
  judgment_surface_exists := ⟨verifierEqualityJudgment⟩
  trace_logic := trace_logic_certificate
  formal_system := formal_system_certificate
  inevitability := prc_inevitability_certificate
  quotient_surface_exists := by
    intro J T
    exact ⟨endpointClassOf J T Endpoint.left⟩
  orbit_nat_equivalence := ⟨DistinctionNat.equivNat⟩
  orbit_add_faithful := DistinctionNat.toNat_add
  orbit_mul_faithful := DistinctionNat.toNat_mul
  prc_integer_surface_exists := ⟨PRCInt.zero⟩
  prc_rational_surface_exists := by
    let one : DistinctionNat := DistinctionNat.succ DistinctionNat.zero
    have hone : one ≠ DistinctionNat.zero := by
      intro h
      exact DistinctionNat.zero_ne_succ DistinctionNat.zero h.symm
    exact ⟨PRCRat.mk ⟨SignedOrbit.zero, one, hone⟩⟩
  prc_int_balanced_iff_display := SignedOrbit.balanced_iff_toInt_eq
  prc_rat_cross_iff_display := RatioOrbit.crossEq_iff_toRat_eq
  prc_int_display_injective := PRCInt.toInt_injective
  prc_rat_display_injective := PRCRat.toRat_injective
  prc_int_equiv_int := ⟨PRCInt.equivInt⟩
  integer_order := integer_order_certificate
  orbit_divisibility := DistinctionNat.orbit_divisibility_certificate
  orbit_euclidean := DistinctionNat.orbit_euclidean_certificate
  prc_jcost := PRCJCost.prc_jcost_certificate
  rational_field := rational_field_certificate
  recognizer_bridge := prc_recognizer_bridge_certificate
  prc_int_add_comm := PRCInt.add_comm
  prc_int_add_assoc := PRCInt.add_assoc
  prc_int_mul_comm := PRCInt.mul_comm
  prc_int_mul_assoc := PRCInt.mul_assoc
  prc_int_left_distrib := PRCInt.left_distrib
  prc_int_add_negate := PRCInt.add_negate
  prc_rat_display_add := PRCRat.toRat_add'
  prc_rat_display_mul := PRCRat.toRat_mul'
  prc_rat_display_inv := PRCRat.toRat_inv'
  ratio_recip_internal_den := by
    intro a h
    rfl
  prc_rat_add_comm := PRCRat.add_comm
  prc_rat_mul_comm := PRCRat.mul_comm
  prc_rat_left_distrib := PRCRat.left_distrib
  prc_rat_mul_recip_cancel := by
    intro a h
    simpa using PRCRat.mul_recip_cancel (a := a) h
  trace_closure_boundary := trace_closure_certificate
  real_cauchy := real_cauchy_certificate
  real_null_setoid := real_null_setoid_conditional_certificate
  jcost_distance_triangle := prc_jcost_distance_triangle_conditional_certificate
  jcost_distance_verifier_triangle :=
    prc_jcost_distance_verifier_triangle_conditional_certificate
  jcost_distance_increment_triangle :=
    prc_jcost_distance_increment_triangle_certificate
  real_complete_ordered_field :=
    prc_real_complete_ordered_field_conditional_certificate
  real_mul_bounded_continuity :=
    prc_real_mul_bounded_continuity_conditional_certificate
  real_boundedness_modulus :=
    prc_real_boundedness_modulus_certificate
  real_product_continuity :=
    prc_real_product_continuity_certificate
  real_order_congruence :=
    prc_real_order_congruence_certificate
  real_completeness :=
    prc_real_completeness_sharpened_certificate
  real_complete_ordered_field_promoted :=
    prc_real_complete_ordered_field_promoted_certificate
  real_completion_boundary := real_completion_boundary_certificate
  signed_orbit_display := ⟨SignedOrbit.toInt⟩
  ratio_orbit_display := ⟨RatioOrbit.toRat⟩

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
