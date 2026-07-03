/-
  PrimitiveRecognitionCalculus/RealOrderCongruence.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 10d: prove that the eventual non-strict order candidate
    descends to the null-distance quotient.

  The proof uses verifier rationals only to read the J-cost distance as an
  ordinary small increment. The order statement itself remains over PRC raw
  ledgers.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RealProductContinuity

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

private theorem rat_sq_lt_sq_bounds {x gamma : ℚ}
    (hgamma : 0 < gamma) (hsq : x * x < gamma * gamma) :
    -gamma < x ∧ x < gamma := by
  constructor
  · by_contra hnot
    have hxle : x ≤ -gamma := by linarith
    have hnonneg : 0 ≤ -x - gamma := by linarith
    have hprod : 0 ≤ (-x - gamma) * (-x + gamma) := by
      have hright : 0 ≤ -x + gamma := by linarith
      exact mul_nonneg hnonneg hright
    nlinarith
  · by_contra hnot
    have hxge : gamma ≤ x := by linarith
    have hnonneg : 0 ≤ x - gamma := by linarith
    have hprod : 0 ≤ (x - gamma) * (x + gamma) := by
      have hright : 0 ≤ x + gamma := by linarith
      exact mul_nonneg hnonneg hright
    nlinarith

theorem PRCJCostDistance_sq_diff_lt_of_lt_modulus
    {a b eta delta : PRCRat}
    (heta : PRCRat.positive eta)
    (hdelta_pos : PRCRat.positive delta)
    (hdelta_le :
      delta.toRat ≤ eta.toRat * eta.toRat / (4 * (1 + eta.toRat)))
    (hsmall : PRCRat.lt (PRCJCostDistance a b) delta) :
    (a.toRat - b.toRat) * (a.toRat - b.toRat) < eta.toRat := by
  have heta_pos : 0 < eta.toRat := (PRCRat.positive_iff_toRat_pos eta).mp heta
  have hdelta_pos_rat : 0 < delta.toRat :=
    (PRCRat.positive_iff_toRat_pos delta).mp hdelta_pos
  have hdisplay :
      PRCJCostDistanceIncrementDisplay (a.toRat - b.toRat) < delta.toRat := by
    rw [PRCRat.lt_iff_toRat_lt] at hsmall
    rw [PRCJCostDistance_toRat, PRCJCostDistanceRatDisplay_as_increment] at hsmall
    exact hsmall
  exact PRCJCostDistance_sq_lt_of_display_lt_delta
    (t := a.toRat - b.toRat) (eta := eta.toRat) (delta := delta.toRat)
    heta_pos hdelta_pos_rat hdelta_le hdisplay

theorem PRCJCostDistance_abs_diff_lt_of_lt_order_delta
    {a b gamma delta : PRCRat}
    (hgamma : PRCRat.positive gamma)
    (hdelta_pos : PRCRat.positive delta)
    (hdelta_le :
      delta.toRat ≤
        (gamma.toRat * gamma.toRat) * (gamma.toRat * gamma.toRat) /
          (4 * (1 + gamma.toRat * gamma.toRat)))
    (hsmall : PRCRat.lt (PRCJCostDistance a b) delta) :
    -gamma.toRat < a.toRat - b.toRat ∧
      a.toRat - b.toRat < gamma.toRat := by
  let eta : PRCRat := gamma * gamma
  have heta : PRCRat.positive eta := by
    rw [PRCRat.positive_iff_toRat_pos]
    have hgamma_pos : 0 < gamma.toRat :=
      (PRCRat.positive_iff_toRat_pos gamma).mp hgamma
    simp [eta, PRCRat.toRat_mul]
    nlinarith
  have heta_toRat : eta.toRat = gamma.toRat * gamma.toRat := by
    simp [eta, PRCRat.toRat_mul]
  have hsq :
      (a.toRat - b.toRat) * (a.toRat - b.toRat) <
        gamma.toRat * gamma.toRat := by
    have hcore := PRCJCostDistance_sq_diff_lt_of_lt_modulus
      (a := a) (b := b) (eta := eta) (delta := delta)
      heta hdelta_pos (by simpa [heta_toRat] using hdelta_le) hsmall
    simpa [heta_toRat] using hcore
  exact rat_sq_lt_sq_bounds
    ((PRCRat.positive_iff_toRat_pos gamma).mp hgamma) hsq

theorem PRCRawEventuallyLe_of_null_equiv
    {u u' v v' : PRCCauchySeq}
    (huu : PRCNullEquivalent u u')
    (hvv : PRCNullEquivalent v v')
    (hle : PRCRawEventuallyLe u.raw v.raw) :
    PRCRawEventuallyLe u'.raw v'.raw := by
  intro eps heps
  let two : PRCRat := (1 : PRCRat) + (1 : PRCRat)
  let four : PRCRat := two * two
  let gamma : PRCRat := eps * (four⁻¹)
  let eta : PRCRat := gamma * gamma
  let delta : PRCRat := (eta * eta) * ((four * ((1 : PRCRat) + eta))⁻¹)
  have heps_pos : 0 < eps.toRat :=
    (PRCRat.positive_iff_toRat_pos eps).mp heps
  have htwo : two.toRat = (2 : ℚ) := by
    dsimp [two]
    change (PRCRat.add PRCRat.one PRCRat.one).toRat = (2 : ℚ)
    rw [PRCRat.toRat_add, PRCRat.one_toRat]
    norm_num
  have hfour : four.toRat = (4 : ℚ) := by
    dsimp [four]
    change (PRCRat.mul two two).toRat = (4 : ℚ)
    rw [PRCRat.toRat_mul]
    norm_num [htwo]
  have hgamma_toRat : gamma.toRat = eps.toRat / 4 := by
    dsimp [gamma]
    rw [PRCRat.toRat_mul, PRCRat.toRat_recip, hfour]
    ring
  have hgamma_pos_rat : 0 < gamma.toRat := by
    rw [hgamma_toRat]
    positivity
  have hgamma_pos : PRCRat.positive gamma := by
    rw [PRCRat.positive_iff_toRat_pos]
    exact hgamma_pos_rat
  have heta_toRat : eta.toRat = gamma.toRat * gamma.toRat := by
    simp [eta, PRCRat.toRat_mul]
  have heta_pos_rat : 0 < eta.toRat := by
    rw [heta_toRat]
    nlinarith
  have h_one_add_eta :
      (((1 : PRCRat) + eta).toRat) = 1 + eta.toRat := by
    change (PRCRat.add PRCRat.one eta).toRat = 1 + eta.toRat
    rw [PRCRat.toRat_add, PRCRat.one_toRat]
  have hdelta_toRat :
      delta.toRat =
        eta.toRat * eta.toRat / (4 * (1 + eta.toRat)) := by
    dsimp [delta]
    simp [PRCRat.toRat_mul, PRCRat.toRat_recip, PRCRat.toRat_add,
      PRCRat.one_toRat, hfour]
    have hden_pos : (0 : ℚ) < 4 * (1 + eta.toRat) := by positivity
    field_simp [ne_of_gt hden_pos]
  have hdelta_pos_rat : 0 < delta.toRat := by
    rw [hdelta_toRat]
    positivity
  have hdelta_pos : PRCRat.positive delta := by
    rw [PRCRat.positive_iff_toRat_pos]
    exact hdelta_pos_rat
  rcases huu delta hdelta_pos with ⟨Nu, hNu⟩
  rcases hvv delta hdelta_pos with ⟨Nv, hNv⟩
  rcases hle gamma hgamma_pos with ⟨Nle, hNle⟩
  refine ⟨max (max Nu Nv) Nle, ?_⟩
  intro n hn
  have hNu_n : Nu ≤ n :=
    le_trans (Nat.le_max_left Nu Nv)
      (le_trans (Nat.le_max_left (max Nu Nv) Nle) hn)
  have hNv_n : Nv ≤ n :=
    le_trans (Nat.le_max_right Nu Nv)
      (le_trans (Nat.le_max_left (max Nu Nv) Nle) hn)
  have hNle_n : Nle ≤ n :=
    le_trans (Nat.le_max_right (max Nu Nv) Nle) hn
  have hu_close := PRCJCostDistance_abs_diff_lt_of_lt_order_delta
    (a := u.term n) (b := u'.term n) (gamma := gamma) (delta := delta)
    hgamma_pos hdelta_pos (by simp [hdelta_toRat, heta_toRat])
    (hNu n hNu_n)
  have hv_close := PRCJCostDistance_abs_diff_lt_of_lt_order_delta
    (a := v.term n) (b := v'.term n) (gamma := gamma) (delta := delta)
    hgamma_pos hdelta_pos (by simp [hdelta_toRat, heta_toRat])
    (hNv n hNv_n)
  have hu'_lt : (u'.term n).toRat < (u.term n).toRat + gamma.toRat := by
    rcases hu_close with ⟨hlo, _hhi⟩
    nlinarith
  have hv_lt : (v.term n).toRat < (v'.term n).toRat + gamma.toRat := by
    rcases hv_close with ⟨hlo, _hhi⟩
    nlinarith
  have huv_lt : (u.term n).toRat < (v.term n).toRat + gamma.toRat := by
    have hle_n := hNle n hNle_n
    rw [PRCRat.lt_iff_toRat_lt] at hle_n
    simpa [PRCCauchySeq.raw, PRCRat.toRat_add] using hle_n
  rw [PRCRat.lt_iff_toRat_lt]
  simp [PRCCauchySeq.raw, PRCRat.toRat_add]
  have hthree_gamma_lt_eps : 3 * gamma.toRat < eps.toRat := by
    rw [hgamma_toRat]
    nlinarith
  nlinarith

theorem PRCRealOrderCongruenceTarget_proved :
    PRCRealOrderCongruenceTarget := by
  intro u u' v v' huu hvv
  constructor
  · intro hle
    exact PRCRawEventuallyLe_of_null_equiv huu hvv hle
  · intro hle
    exact PRCRawEventuallyLe_of_null_equiv
      (PRCNullEquivalent.symm huu) (PRCNullEquivalent.symm hvv) hle

structure PRCRealOrderCongruenceCertificate : Prop where
  order_congruence : PRCRealOrderCongruenceTarget

theorem prc_real_order_congruence_certificate :
    PRCRealOrderCongruenceCertificate where
  order_congruence := PRCRealOrderCongruenceTarget_proved

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
