/-
  PrimitiveRecognitionCalculus/RealProductContinuity.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10c: prove the bounded product-continuity modulus for
    `PRCJCostDistance`.

  The object-level statement remains PRC-rational. The proof uses verifier
  rationals only as display transport for the analytic inequality.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealBoundednessModulus

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

theorem PRCJCostDistanceIncrementDisplay_lt_of_sq_lt
    {t eta eps : ℚ} (heta_pos : 0 < eta) (heta_lt_one : eta < 1)
    (hsq : t * t < eta) (heta_sq_half_lt_eps : eta * eta / 2 < eps) :
    PRCJCostDistanceIncrementDisplay t < eps := by
  rw [PRCJCostDistanceIncrementDisplay_formula]
  have hs_nonneg : (0 : ℚ) ≤ t * t := mul_self_nonneg t
  have hden_pos : (0 : ℚ) < 2 * (1 + t * t) := by positivity
  have hs_lt_one : t * t < 1 := lt_trans hsq heta_lt_one
  have hnum_lt : (t * t) * (t * t) < eta * eta := by nlinarith
  have hfrac_le : ((t * t) * (t * t)) / (2 * (1 + t * t)) ≤
      ((t * t) * (t * t)) / 2 := by
    have hden_ge_two : (2 : ℚ) ≤ 2 * (1 + t * t) := by nlinarith
    have hnum_nonneg : (0 : ℚ) ≤ (t * t) * (t * t) :=
      mul_nonneg hs_nonneg hs_nonneg
    exact div_le_div_of_nonneg_left hnum_nonneg (by norm_num) hden_ge_two
  have hnum_half_lt : ((t * t) * (t * t)) / 2 < eta * eta / 2 := by
    nlinarith
  exact lt_of_le_of_lt hfrac_le (lt_trans hnum_half_lt heta_sq_half_lt_eps)

theorem PRCJCostDistance_sq_lt_of_display_lt_delta
    {t eta delta : ℚ} (heta_pos : 0 < eta) (_hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ eta * eta / (4 * (1 + eta)))
    (hsmall : PRCJCostDistanceIncrementDisplay t < delta) :
    t * t < eta := by
  by_contra hnot
  have hge : eta ≤ t * t := by nlinarith
  rw [PRCJCostDistanceIncrementDisplay_formula] at hsmall
  have hs_nonneg : (0 : ℚ) ≤ t * t := mul_self_nonneg t
  have hs_pos : (0 : ℚ) < t * t := lt_of_lt_of_le heta_pos hge
  have hden_s_pos : (0 : ℚ) < 2 * (1 + t * t) := by positivity
  have hmono :
      eta * eta / (4 * (1 + eta)) ≤
        ((t * t) * (t * t)) / (2 * (1 + t * t)) := by
    let s : ℚ := t * t
    have hs_ge : eta ≤ s := by simpa [s] using hge
    have hs_nonneg' : (0 : ℚ) ≤ s := by simpa [s] using hs_nonneg
    have hs_den_pos : (0 : ℚ) < 2 * (1 + s) := by positivity
    have h_eta_den_two_pos : (0 : ℚ) < 2 * (1 + eta) := by positivity
    have h_eta_den_four_pos : (0 : ℚ) < 4 * (1 + eta) := by positivity
    have hhalf :
        eta * eta / (4 * (1 + eta)) ≤
          eta * eta / (2 * (1 + eta)) := by
      have hnum_nonneg : (0 : ℚ) ≤ eta * eta := by nlinarith
      have hden_le : 2 * (1 + eta) ≤ 4 * (1 + eta) := by nlinarith
      exact div_le_div_of_nonneg_left hnum_nonneg h_eta_den_two_pos hden_le
    have hmon :
        eta * eta / (2 * (1 + eta)) ≤
          (s * s) / (2 * (1 + s)) := by
      have hdiff_nonneg :
          0 ≤ s * s * (1 + eta) - eta * eta * (1 + s) := by
        have hleft : 0 ≤ s - eta := by nlinarith
        have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
        have hright : 0 ≤ s + eta + s * eta := by
          nlinarith [mul_nonneg hs_nonneg' heta_nonneg]
        have hprod : 0 ≤ (s - eta) * (s + eta + s * eta) :=
          mul_nonneg hleft hright
        nlinarith
      field_simp [ne_of_gt hs_den_pos, ne_of_gt h_eta_den_two_pos]
      nlinarith [hdiff_nonneg]
    exact le_trans hhalf (by simpa [s] using hmon)
  exact not_lt_of_ge (le_trans hdelta_le hmono) hsmall

theorem PRCRat.InBound_sq_lt {B x : PRCRat}
    (hB : PRCRat.positive B) (hx : PRCRat.InBound B x) :
    x.toRat * x.toRat < B.toRat * B.toRat := by
  rcases hx with ⟨hlo, hhi⟩
  rw [PRCRat.lt_iff_toRat_lt] at hlo hhi
  have hB_pos : (0 : ℚ) < B.toRat := (PRCRat.positive_iff_toRat_pos B).mp hB
  have hneg : (-B).toRat = -B.toRat := by simp
  rw [hneg] at hlo
  have hleft : 0 < B.toRat - x.toRat := by nlinarith
  have hright : 0 < B.toRat + x.toRat := by nlinarith
  have hprod : 0 < (B.toRat - x.toRat) * (B.toRat + x.toRat) :=
    mul_pos hleft hright
  nlinarith

private theorem product_factor_sq_lt
    {da b eta M : ℚ}
    (hda : da * da < eta)
    (hb : b * b < M * M)
    (hM_pos : 0 < M) :
    (da * b) * (da * b) < eta * (M * M) := by
  have hda_nonneg : 0 ≤ da * da := mul_self_nonneg da
  have hb_nonneg : 0 ≤ b * b := mul_self_nonneg b
  have hM_sq_pos : 0 < M * M := mul_pos hM_pos hM_pos
  have hgap1 : 0 < eta - da * da := by nlinarith
  have hgap2 : 0 < M * M - b * b := by nlinarith
  have hterm1 : 0 < (eta - da * da) * (M * M) :=
    mul_pos hgap1 hM_sq_pos
  have hterm2 : 0 ≤ (da * da) * (M * M - b * b) :=
    mul_nonneg hda_nonneg (le_of_lt hgap2)
  have hgap :
      0 < eta * (M * M) - (da * da) * (b * b) := by
    nlinarith
  have hsq : (da * b) * (da * b) = (da * da) * (b * b) := by ring
  rw [hsq]
  nlinarith

private theorem rational_product_increment_sq_lt
    {a a' b b' M eta rho : ℚ}
    (hM_pos : 0 < M) (hrho_pos : 0 < rho)
    (heta_eq : eta = rho / (4 * (1 + M * M)))
    (ha' : a' * a' < M * M)
    (hb : b * b < M * M)
    (hda : (a - a') * (a - a') < eta)
    (hdb : (b - b') * (b - b') < eta) :
    (a * b - a' * b') * (a * b - a' * b') < rho := by
  let u : ℚ := (a - a') * b
  let v : ℚ := a' * (b - b')
  have hu : u * u < eta * (M * M) := by
    simpa [u] using product_factor_sq_lt
      (da := a - a') (b := b) (eta := eta) (M := M)
      hda hb hM_pos
  have hv : v * v < eta * (M * M) := by
    simpa [v, mul_comm, mul_left_comm, mul_assoc] using product_factor_sq_lt
      (da := b - b') (b := a') (eta := eta) (M := M)
      hdb ha' hM_pos
  have hsum_le : (u + v) * (u + v) ≤ 2 * (u * u) + 2 * (v * v) := by
    nlinarith [mul_self_nonneg (u - v)]
  have hsum_lt : (u + v) * (u + v) < 4 * eta * (M * M) := by
    nlinarith
  have hscale : 4 * eta * (M * M) < rho := by
    rw [heta_eq]
    have hden_pos : (0 : ℚ) < 4 * (1 + M * M) := by positivity
    field_simp [ne_of_gt hden_pos]
    have hM_sq_pos : 0 < M * M := mul_pos hM_pos hM_pos
    nlinarith
  have hidentity : a * b - a' * b' = u + v := by
    dsimp [u, v]
    ring
  rw [hidentity]
  exact lt_trans hsum_lt hscale

theorem PRCJCostDistanceMulBoundedContinuityTarget_proved :
    PRCJCostDistanceMulBoundedContinuityTarget := by
  intro eps B heps hB
  let two : PRCRat := (1 : PRCRat) + (1 : PRCRat)
  let four : PRCRat := two * two
  let rho : PRCRat := eps * (((1 : PRCRat) + eps)⁻¹)
  let K : PRCRat := (1 : PRCRat) + (B * B)
  let eta : PRCRat := rho * ((four * K)⁻¹)
  let delta : PRCRat := (eta * eta) * ((four * ((1 : PRCRat) + eta))⁻¹)
  have heps_pos : (0 : ℚ) < eps.toRat :=
    (PRCRat.positive_iff_toRat_pos eps).mp heps
  have hB_pos : (0 : ℚ) < B.toRat :=
    (PRCRat.positive_iff_toRat_pos B).mp hB
  have htwo : two.toRat = (2 : ℚ) := by
    dsimp [two]
    change (PRCRat.add PRCRat.one PRCRat.one).toRat = (2 : ℚ)
    rw [PRCRat.toRat_add]
    norm_num [PRCRat.one_toRat]
  have hfour : four.toRat = (4 : ℚ) := by
    dsimp [four]
    change (PRCRat.mul two two).toRat = (4 : ℚ)
    rw [PRCRat.toRat_mul]
    norm_num [htwo]
  have h_one_add_eps :
      (((1 : PRCRat) + eps).toRat) = 1 + eps.toRat := by
    change (PRCRat.add PRCRat.one eps).toRat = 1 + eps.toRat
    rw [PRCRat.toRat_add, PRCRat.one_toRat]
  have hK : K.toRat = 1 + B.toRat * B.toRat := by
    dsimp [K]
    change (PRCRat.add PRCRat.one (PRCRat.mul B B)).toRat =
      1 + B.toRat * B.toRat
    rw [PRCRat.toRat_add, PRCRat.one_toRat, PRCRat.toRat_mul]
  have hK_pos : (0 : ℚ) < K.toRat := by
    rw [hK]
    nlinarith [mul_self_nonneg B.toRat]
  have hrho : rho.toRat = eps.toRat / (1 + eps.toRat) := by
    dsimp [rho]
    simp [PRCRat.toRat_mul, PRCRat.toRat_recip, PRCRat.toRat_add,
      PRCRat.one_toRat]
    ring
  have hrho_pos : (0 : ℚ) < rho.toRat := by
    rw [hrho]
    positivity
  have hrho_lt_one : rho.toRat < 1 := by
    rw [hrho]
    field_simp [ne_of_gt (by positivity : (0 : ℚ) < 1 + eps.toRat)]
    nlinarith
  have hrho_sq_half_lt_eps : rho.toRat * rho.toRat / 2 < eps.toRat := by
    have hrho_lt_eps : rho.toRat < eps.toRat := by
      rw [hrho]
      field_simp [ne_of_gt (by positivity : (0 : ℚ) < 1 + eps.toRat)]
      nlinarith
    nlinarith [hrho_pos, hrho_lt_one, hrho_lt_eps]
  have heta : eta.toRat = rho.toRat / (4 * K.toRat) := by
    dsimp [eta]
    rw [PRCRat.toRat_mul, PRCRat.toRat_recip, PRCRat.toRat_mul, hfour]
    ring
  have heta_pos : (0 : ℚ) < eta.toRat := by
    rw [heta]
    positivity
  have heta_lt_one : eta.toRat < 1 := by
    rw [heta]
    have hden_pos : (0 : ℚ) < 4 * K.toRat := by positivity
    field_simp [ne_of_gt hden_pos]
    have hK_gt_zero : 0 < 4 * K.toRat := by positivity
    nlinarith [hrho_lt_one, hrho_pos, hK_pos]
  have h_one_add_eta :
      (((1 : PRCRat) + eta).toRat) = 1 + eta.toRat := by
    change (PRCRat.add PRCRat.one eta).toRat = 1 + eta.toRat
    rw [PRCRat.toRat_add, PRCRat.one_toRat]
  have hdelta :
      delta.toRat = eta.toRat * eta.toRat / (4 * (1 + eta.toRat)) := by
    dsimp [delta]
    simp [PRCRat.toRat_mul, PRCRat.toRat_recip, PRCRat.toRat_add,
      PRCRat.one_toRat, hfour]
    have hden_pos : (0 : ℚ) < 4 * (1 + eta.toRat) := by positivity
    field_simp [ne_of_gt hden_pos]
  have hdelta_pos_rat : (0 : ℚ) < delta.toRat := by
    rw [hdelta]
    positivity
  have hdelta_pos : PRCRat.positive delta := by
    rw [PRCRat.positive_iff_toRat_pos]
    exact hdelta_pos_rat
  refine ⟨delta, hdelta_pos, ?_⟩
  intro a a' b b' ha ha' hb hb' haa hbb
  have ha'_sq : a'.toRat * a'.toRat < B.toRat * B.toRat :=
    PRCRat.InBound_sq_lt hB ha'
  have hb_sq : b.toRat * b.toRat < B.toRat * B.toRat :=
    PRCRat.InBound_sq_lt hB hb
  have haa_rat : PRCJCostDistanceIncrementDisplay (a.toRat - a'.toRat) < delta.toRat := by
    rw [PRCRat.lt_iff_toRat_lt] at haa
    rw [PRCJCostDistance_toRat, PRCJCostDistanceRatDisplay_as_increment] at haa
    exact haa
  have hbb_rat : PRCJCostDistanceIncrementDisplay (b.toRat - b'.toRat) < delta.toRat := by
    rw [PRCRat.lt_iff_toRat_lt] at hbb
    rw [PRCJCostDistance_toRat, PRCJCostDistanceRatDisplay_as_increment] at hbb
    exact hbb
  have hda_sq : (a.toRat - a'.toRat) * (a.toRat - a'.toRat) < eta.toRat :=
    PRCJCostDistance_sq_lt_of_display_lt_delta
      (t := a.toRat - a'.toRat) (eta := eta.toRat) (delta := delta.toRat)
      heta_pos hdelta_pos_rat (by rw [hdelta]) haa_rat
  have hdb_sq : (b.toRat - b'.toRat) * (b.toRat - b'.toRat) < eta.toRat :=
    PRCJCostDistance_sq_lt_of_display_lt_delta
      (t := b.toRat - b'.toRat) (eta := eta.toRat) (delta := delta.toRat)
      heta_pos hdelta_pos_rat (by rw [hdelta]) hbb_rat
  have hprod_sq :
      ((a * b).toRat - (a' * b').toRat) *
          ((a * b).toRat - (a' * b').toRat) < rho.toRat := by
    simp [PRCRat.toRat_mul]
    exact rational_product_increment_sq_lt
      (a := a.toRat) (a' := a'.toRat) (b := b.toRat) (b' := b'.toRat)
      (M := B.toRat) (eta := eta.toRat) (rho := rho.toRat)
      hB_pos hrho_pos (by rw [heta, hK]) ha'_sq hb_sq hda_sq hdb_sq
  rw [PRCRat.lt_iff_toRat_lt]
  rw [PRCJCostDistance_toRat, PRCJCostDistanceRatDisplay_as_increment]
  exact PRCJCostDistanceIncrementDisplay_lt_of_sq_lt
    (t := (a * b).toRat - (a' * b').toRat)
    (eta := rho.toRat) (eps := eps.toRat)
    hrho_pos hrho_lt_one hprod_sq hrho_sq_half_lt_eps

structure PRCRealProductContinuityCertificate : Prop where
  product_continuity : PRCJCostDistanceMulBoundedContinuityTarget
  mul_closure : PRCRealMulClosureTarget
  mul_congruence : PRCRealMulCongruenceTarget
  mul_operation :
    Nonempty (PRCRealNullClosed → PRCRealNullClosed → PRCRealNullClosed)

theorem prc_real_product_continuity_certificate :
    PRCRealProductContinuityCertificate where
  product_continuity := PRCJCostDistanceMulBoundedContinuityTarget_proved
  mul_closure :=
    PRCRealMulClosureTarget_of_bounded_continuity
      PRCCauchySeqEventuallyBoundedTarget_proved
      PRCJCostDistanceMulBoundedContinuityTarget_proved
  mul_congruence :=
    PRCRealMulCongruenceTarget_of_bounded_continuity
      PRCCauchySeqEventuallyBoundedTarget_proved
      PRCJCostDistanceMulBoundedContinuityTarget_proved
  mul_operation := by
    exact ⟨PRCRealNullClosed.mulOf
      (PRCRealMulClosureTarget_of_bounded_continuity
        PRCCauchySeqEventuallyBoundedTarget_proved
        PRCJCostDistanceMulBoundedContinuityTarget_proved)
      (PRCRealMulCongruenceTarget_of_bounded_continuity
        PRCCauchySeqEventuallyBoundedTarget_proved
        PRCJCostDistanceMulBoundedContinuityTarget_proved)⟩

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
