/-
  PrimitiveRecognitionCalculus/RealBoundednessModulus.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10b: prove every J-cost Cauchy ledger is eventually
    PRC-bounded.

  The proof uses the verifier rational display only to extract the ordinary
  square bound from small J-cost distance. The eventual bound itself is stated
  on the PRC rational ledger.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealMulBoundedContinuity

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- A fixed PRC rational distance threshold small enough to force ordinary
increment square below one. -/
def PRCBoundednessDelta : PRCRat :=
  let two : PRCRat := (1 : PRCRat) + (1 : PRCRat)
  let four : PRCRat := two * two
  (1 : PRCRat) * ((four * two)⁻¹)

theorem PRCBoundednessDelta_toRat :
    PRCBoundednessDelta.toRat = (1 / 8 : ℚ) := by
  unfold PRCBoundednessDelta
  simp [PRCRat.toRat_mul, PRCRat.toRat_recip]
  norm_num

theorem PRCBoundednessDelta_positive :
    PRCRat.positive PRCBoundednessDelta := by
  rw [PRCRat.positive_iff_toRat_pos, PRCBoundednessDelta_toRat]
  norm_num

/-- Small increment display at the fixed threshold forces ordinary square
increment below one. -/
theorem PRCJCostDistanceIncrementDisplay_sq_lt_one {t : ℚ}
    (hsmall : PRCJCostDistanceIncrementDisplay t < (1 / 8 : ℚ)) :
    t * t < 1 := by
  by_contra hnot
  have hge : (1 : ℚ) ≤ t * t := by
    have hsq_nonneg : (0 : ℚ) ≤ t * t := mul_self_nonneg t
    nlinarith
  rw [PRCJCostDistanceIncrementDisplay_formula] at hsmall
  let s : ℚ := t * t
  have hs_ge : (1 : ℚ) ≤ s := by simpa [s] using hge
  have hs_den_pos : (0 : ℚ) < 2 * (1 + s) := by nlinarith
  have hmono : (1 / 8 : ℚ) ≤ (s * s) / (2 * (1 + s)) := by
    field_simp [ne_of_gt hs_den_pos]
    nlinarith [mul_self_nonneg s]
  exact not_lt_of_ge hmono (by simpa [s] using hsmall)

/-- Small PRC J-cost distance at the fixed threshold forces the ordinary
rational display increment to have square below one. -/
theorem PRCJCostDistance_sq_diff_lt_one_of_lt_boundedness_delta
    {a b : PRCRat}
    (hsmall : PRCRat.lt (PRCJCostDistance a b) PRCBoundednessDelta) :
    (a.toRat - b.toRat) * (a.toRat - b.toRat) < 1 := by
  rw [PRCRat.lt_iff_toRat_lt] at hsmall
  rw [PRCJCostDistance_toRat, PRCJCostDistanceRatDisplay_as_increment,
    PRCBoundednessDelta_toRat] at hsmall
  exact PRCJCostDistanceIncrementDisplay_sq_lt_one hsmall

/-- A J-cost Cauchy ledger is eventually contained in a PRC symmetric rational
interval. -/
theorem PRCCauchySeqEventuallyBoundedTarget_proved :
    PRCCauchySeqEventuallyBoundedTarget := by
  intro u
  rcases u.cauchy PRCBoundednessDelta PRCBoundednessDelta_positive with
    ⟨N, hN⟩
  let anchor : PRCRat := u.term N
  let two : PRCRat := (1 : PRCRat) + (1 : PRCRat)
  let B : PRCRat := anchor * anchor + two
  have hB_pos : PRCRat.positive B := by
    rw [PRCRat.positive_iff_toRat_pos]
    have hsq : (0 : ℚ) ≤ anchor.toRat * anchor.toRat :=
      mul_self_nonneg anchor.toRat
    simp [B, two]
    nlinarith
  refine ⟨B, hB_pos, N, ?_⟩
  intro n hn
  have hdist : PRCRat.lt (PRCJCostDistance (u.term n) anchor) PRCBoundednessDelta := by
    simpa [anchor] using hN n N hn (Nat.le_refl N)
  have hsquare :
      ((u.term n).toRat - anchor.toRat) *
          ((u.term n).toRat - anchor.toRat) < 1 :=
    PRCJCostDistance_sq_diff_lt_one_of_lt_boundedness_delta hdist
  let x : ℚ := (u.term n).toRat
  let q : ℚ := anchor.toRat
  have hsquare_xq : (x - q) * (x - q) < 1 := by
    simpa [x, q] using hsquare
  have hdiff_lt_one : x - q < 1 := by
    nlinarith [mul_self_nonneg ((x - q) - 1)]
  have hdiff_gt_neg_one : -1 < x - q := by
    nlinarith [mul_self_nonneg ((x - q) + 1)]
  constructor
  · rw [PRCRat.lt_iff_toRat_lt]
    simp [B, two, anchor]
    nlinarith [mul_self_nonneg (2 * q + 1)]
  · rw [PRCRat.lt_iff_toRat_lt]
    simp [B, two, anchor]
    nlinarith [mul_self_nonneg (2 * q - 1)]

/-- Step 10b closure certificate: eventual boundedness is proved, so the
remaining multiplication blocker is only bounded product-continuity. -/
structure PRCRealBoundednessModulusCertificate : Prop where
  boundedness_delta_positive : PRCRat.positive PRCBoundednessDelta
  distance_sq_bound :
    ∀ a b : PRCRat,
      PRCRat.lt (PRCJCostDistance a b) PRCBoundednessDelta →
        (a.toRat - b.toRat) * (a.toRat - b.toRat) < 1
  eventual_boundedness : PRCCauchySeqEventuallyBoundedTarget
  mul_closure_from_product_continuity :
    PRCJCostDistanceMulBoundedContinuityTarget → PRCRealMulClosureTarget
  mul_congruence_from_product_continuity :
    PRCJCostDistanceMulBoundedContinuityTarget → PRCRealMulCongruenceTarget

theorem prc_real_boundedness_modulus_certificate :
    PRCRealBoundednessModulusCertificate where
  boundedness_delta_positive := PRCBoundednessDelta_positive
  distance_sq_bound := by
    intro a b h
    exact PRCJCostDistance_sq_diff_lt_one_of_lt_boundedness_delta h
  eventual_boundedness := PRCCauchySeqEventuallyBoundedTarget_proved
  mul_closure_from_product_continuity := by
    intro hcont
    exact PRCRealMulClosureTarget_of_bounded_continuity
      PRCCauchySeqEventuallyBoundedTarget_proved hcont
  mul_congruence_from_product_continuity := by
    intro hcont
    exact PRCRealMulCongruenceTarget_of_bounded_continuity
      PRCCauchySeqEventuallyBoundedTarget_proved hcont

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
