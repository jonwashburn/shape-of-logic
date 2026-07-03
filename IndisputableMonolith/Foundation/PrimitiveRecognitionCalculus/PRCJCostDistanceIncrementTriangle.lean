/-
  PrimitiveRecognitionCalculus/PRCJCostDistanceIncrementTriangle.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 9c: prove the one-dimensional additive increment modulus
    for the displayed rational J-cost distance.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCostDistanceVerifierTriangle

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

theorem PRCJCostDistanceIncrementDisplay_formula (t : ℚ) :
    PRCJCostDistanceIncrementDisplay t =
      ((t * t) * (t * t)) / (2 * (1 + t * t)) := by
  unfold PRCJCostDistanceIncrementDisplay PRCJCostDistanceRatDisplay
  have hg_pos : (0 : ℚ) < 1 + t * t := by
    nlinarith [mul_self_nonneg t]
  have hg_ne : (1 + t * t : ℚ) ≠ 0 := ne_of_gt hg_pos
  field_simp [hg_ne]
  ring

private theorem increment_display_lt_of_sq_lt
    {t eta eps : ℚ} (heta_pos : 0 < eta) (heta_lt_one : eta < 1)
    (hsq : t * t < eta) (heta_sq_half_lt_eps : eta * eta / 2 < eps) :
    PRCJCostDistanceIncrementDisplay t < eps := by
  rw [PRCJCostDistanceIncrementDisplay_formula]
  have hs_nonneg : (0 : ℚ) ≤ t * t := mul_self_nonneg t
  have hden_pos : (0 : ℚ) < 2 * (1 + t * t) := by positivity
  have hden_ne : (2 * (1 + t * t) : ℚ) ≠ 0 := ne_of_gt hden_pos
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

private theorem sq_lt_of_display_lt_delta
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
  have hden_eta_pos : (0 : ℚ) < 4 * (1 + eta) := by positivity
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

theorem PRCJCostDistanceIncrementTriangleTarget_proved :
    PRCJCostDistanceIncrementTriangleTarget := by
  intro eps heps
  let two : PRCRat := (1 : PRCRat) + (1 : PRCRat)
  let four : PRCRat := two + two
  let rho : PRCRat := eps / (1 + eps)
  let eta : PRCRat := rho / four
  let delta : PRCRat := (eta * eta) / (four * (1 + eta))
  refine ⟨delta, ?_, ?_⟩
  · rw [PRCRat.positive_iff_toRat_pos]
    have heps_pos : (0 : ℚ) < eps.toRat := (PRCRat.positive_iff_toRat_pos eps).mp heps
    have htwo : two.toRat = (2 : ℚ) := by
      dsimp [two]
      change (PRCRat.add PRCRat.one PRCRat.one).toRat = (2 : ℚ)
      rw [PRCRat.toRat_add]
      norm_num [PRCRat.one_toRat]
    have hfour : four.toRat = (4 : ℚ) := by
      dsimp [four]
      change (PRCRat.add two two).toRat = (4 : ℚ)
      rw [PRCRat.toRat_add]
      norm_num [htwo]
    have h_one_add_eps : ((1 : PRCRat) + eps).toRat = 1 + eps.toRat := by
      change (PRCRat.add PRCRat.one eps).toRat = 1 + eps.toRat
      rw [PRCRat.toRat_add, PRCRat.one_toRat]
    have h_one_add_eta : ((1 : PRCRat) + eta).toRat = 1 + eta.toRat := by
      change (PRCRat.add PRCRat.one eta).toRat = 1 + eta.toRat
      rw [PRCRat.toRat_add, PRCRat.one_toRat]
    have heta_pos : (0 : ℚ) < eta.toRat := by
      rw [PRCRat.toRat_div, hfour]
      have hrho_pos : (0 : ℚ) < rho.toRat := by
        rw [PRCRat.toRat_div, h_one_add_eps]
        positivity
      positivity
    rw [PRCRat.toRat_div, PRCRat.toRat_mul', PRCRat.toRat_mul',
      h_one_add_eta, hfour]
    positivity
  · intro p q hp hq
    have heps_pos : (0 : ℚ) < eps.toRat := (PRCRat.positive_iff_toRat_pos eps).mp heps
    have htwo : two.toRat = (2 : ℚ) := by
      dsimp [two]
      change (PRCRat.add PRCRat.one PRCRat.one).toRat = (2 : ℚ)
      rw [PRCRat.toRat_add]
      norm_num [PRCRat.one_toRat]
    have hfour : four.toRat = (4 : ℚ) := by
      dsimp [four]
      change (PRCRat.add two two).toRat = (4 : ℚ)
      rw [PRCRat.toRat_add]
      norm_num [htwo]
    have h_one_add_eps : ((1 : PRCRat) + eps).toRat = 1 + eps.toRat := by
      change (PRCRat.add PRCRat.one eps).toRat = 1 + eps.toRat
      rw [PRCRat.toRat_add, PRCRat.one_toRat]
    have h_one_add_eta : ((1 : PRCRat) + eta).toRat = 1 + eta.toRat := by
      change (PRCRat.add PRCRat.one eta).toRat = 1 + eta.toRat
      rw [PRCRat.toRat_add, PRCRat.one_toRat]
    have hrho : rho.toRat = eps.toRat / (1 + eps.toRat) := by
      rw [PRCRat.toRat_div, h_one_add_eps]
    have hrho_pos : (0 : ℚ) < rho.toRat := by
      rw [hrho]
      positivity
    have hrho_lt_one : rho.toRat < 1 := by
      rw [hrho]
      field_simp [ne_of_gt (by positivity : (0 : ℚ) < 1 + eps.toRat)]
      nlinarith
    have heta : eta.toRat = rho.toRat / 4 := by
      rw [PRCRat.toRat_div, hfour]
    have heta_pos : (0 : ℚ) < eta.toRat := by
      rw [heta]
      positivity
    have heta_lt_one : eta.toRat < 1 := by
      rw [heta]
      nlinarith
    have hdelta :
        delta.toRat = eta.toRat * eta.toRat / (4 * (1 + eta.toRat)) := by
      rw [PRCRat.toRat_div, PRCRat.toRat_mul', PRCRat.toRat_mul',
        h_one_add_eta, hfour]
    have hdelta_pos : (0 : ℚ) < delta.toRat := by
      rw [hdelta]
      positivity
    have hp_sq : p * p < eta.toRat := by
      exact sq_lt_of_display_lt_delta
        (t := p) (eta := eta.toRat) (delta := delta.toRat)
        heta_pos hdelta_pos (by rw [hdelta]) hp
    have hq_sq : q * q < eta.toRat := by
      exact sq_lt_of_display_lt_delta
        (t := q) (eta := eta.toRat) (delta := delta.toRat)
        heta_pos hdelta_pos (by rw [hdelta]) hq
    have hpq_sq_lt_rho : (p + q) * (p + q) < rho.toRat := by
      have hsq_bound : (p + q) * (p + q) ≤ 2 * (p * p) + 2 * (q * q) := by
        nlinarith [mul_self_nonneg (p - q)]
      rw [heta] at hp_sq hq_sq
      nlinarith
    have hrho_sq_half_lt_eps : rho.toRat * rho.toRat / 2 < eps.toRat := by
      have hrho_lt_eps : rho.toRat < eps.toRat := by
        rw [hrho]
        field_simp [ne_of_gt (by positivity : (0 : ℚ) < 1 + eps.toRat)]
        nlinarith
      nlinarith [hrho_pos, hrho_lt_one, hrho_lt_eps]
    exact increment_display_lt_of_sq_lt
      (t := p + q) (eta := rho.toRat) (eps := eps.toRat)
      hrho_pos hrho_lt_one hpq_sq_lt_rho hrho_sq_half_lt_eps

/-- Final closure for the rational increment modulus. -/
theorem PRCJCostDistanceVerifierTriangleTarget_proved :
    PRCJCostDistanceVerifierTriangleTarget :=
  PRCJCostDistanceVerifierTriangleTarget_of_increment
    PRCJCostDistanceIncrementTriangleTarget_proved

/-- The PRC null-distance setoid target is now closed by the explicit rational
increment modulus. -/
theorem PRCNullDistanceSetoidTarget_proved :
    PRCNullDistanceSetoidTarget :=
  PRCNullDistanceSetoidTarget_of_increment_triangle
    PRCJCostDistanceIncrementTriangleTarget_proved

/-- The PRC triangle modulus is now closed by the explicit rational increment
estimate. -/
theorem PRCJCostDistanceTriangleModulusTarget_proved :
    PRCJCostDistanceTriangleModulusTarget :=
  PRCJCostDistanceTriangleModulusTarget_of_verifier
    PRCJCostDistanceVerifierTriangleTarget_proved

/-- The null-distance relation is transitive. -/
theorem PRCNullDistanceTransitiveTarget_proved :
    PRCNullDistanceTransitiveTarget :=
  PRCNullDistanceTransitiveTarget_of_triangle_modulus
    PRCJCostDistanceTriangleModulusTarget_proved

/-- The final PRC real carrier: Cauchy ledgers quotiented by null distance. -/
def PRCRealNullClosed : Type :=
  PRCRealNull PRCNullDistanceTransitiveTarget_proved

namespace PRCRealNullClosed

/-- Embed a PRC rational into the closed null-distance quotient carrier. -/
def ofRat (q : PRCRat) : PRCRealNullClosed :=
  PRCRealNull.ofRat PRCNullDistanceTransitiveTarget_proved q

end PRCRealNullClosed

/-- Build Order step 9c closure certificate. -/
structure PRCJCostDistanceIncrementTriangleCertificate : Prop where
  increment_formula :
    ∀ t : ℚ,
      PRCJCostDistanceIncrementDisplay t =
        ((t * t) * (t * t)) / (2 * (1 + t * t))
  increment_triangle : PRCJCostDistanceIncrementTriangleTarget
  verifier_triangle : PRCJCostDistanceVerifierTriangleTarget
  triangle_modulus : PRCJCostDistanceTriangleModulusTarget
  null_distance_transitive : PRCNullDistanceTransitiveTarget
  null_distance_setoid : PRCNullDistanceSetoidTarget
  real_null_carrier : Nonempty PRCRealNullClosed
  rat_embedding : Nonempty (PRCRat → PRCRealNullClosed)

/-- The explicit rational increment estimate closes the whole J-cost
null-distance setoid chain. -/
theorem prc_jcost_distance_increment_triangle_certificate :
    PRCJCostDistanceIncrementTriangleCertificate where
  increment_formula := PRCJCostDistanceIncrementDisplay_formula
  increment_triangle := PRCJCostDistanceIncrementTriangleTarget_proved
  verifier_triangle := PRCJCostDistanceVerifierTriangleTarget_proved
  triangle_modulus := PRCJCostDistanceTriangleModulusTarget_proved
  null_distance_transitive := PRCNullDistanceTransitiveTarget_proved
  null_distance_setoid := PRCNullDistanceSetoidTarget_proved
  real_null_carrier := ⟨PRCRealNullClosed.ofRat 0⟩
  rat_embedding := ⟨PRCRealNullClosed.ofRat⟩

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
