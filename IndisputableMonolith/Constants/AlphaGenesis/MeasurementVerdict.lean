import Mathlib
import IndisputableMonolith.Constants.AlphaGenesis.LoopCertificate
import IndisputableMonolith.Constants.AlphaGenesis.ResidualTarget
import IndisputableMonolith.Constants.ExternalAnchors
import IndisputableMonolith.Numerics.Interval.AlphaBounds
import IndisputableMonolith.Numerics.Interval.W8Bounds

/-!
# Alpha Genesis M7: Measurement Verdict (quarantine module)

This module formalizes Anil Thapa's strongest measurement-side objection.
It is quarantined: it imports CODATA through `ExternalAnchors`, and nothing in
the forward Alpha Genesis construction imports this module.

The theorem proved here is intentionally coarse but decisive:

`alphaInvGenesis > alpha_inv_CODATA + 0.0007`.

Since CODATA's one-sigma uncertainty for `α⁻¹` is `2.1e-8`, this also implies
the first-order Alpha Genesis value is more than `30000σ` high. The exact
reported residual is about `7.67e-4`; the certified margin here is the stronger
honest fact needed for the reply: the current first-order value is excluded by
measurement before any seam correction is derived.

STATUS: THEOREM for the comparison; QUARANTINE because it imports CODATA.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis
namespace MeasurementVerdict

noncomputable section

open Constants.ExternalAnchors

/-! ## Tight local interval inputs -/

private def exp_taylor_12_at_048122 : ℚ :=
  let x : ℚ := (48122 : ℚ) / 100000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040
    + x^8/40320 + x^9/362880 + x^10/3628800 + x^11/39916800

private def exp_error_12_at_048122 : ℚ :=
  let x : ℚ := (48122 : ℚ) / 100000
  x^12 * 13 / (Nat.factorial 12 * 12)

private lemma exp_048122_taylor_floor :
    (80902 / 50000 : ℚ) < exp_taylor_12_at_048122 - exp_error_12_at_048122 := by
  native_decide

/-- `exp(0.48122) > 1.61804`, enough to prove `log φ < 0.48122`. -/
private lemma exp_048122_gt : (1.61804 : ℝ) < Real.exp (0.48122 : ℝ) := by
  have hx_abs : |(0.48122 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 12) (by norm_num : 0 < 12)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 12, (0.48122 : ℝ)^m / m.factorial) =
        (exp_taylor_12_at_048122 : ℝ) := by
    simp only [exp_taylor_12_at_048122, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial]
    norm_num
  have h_err_eq :
      |(0.48122 : ℝ)|^12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) =
        (exp_error_12_at_048122 : ℝ) := by
    simp only [exp_error_12_at_048122, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lower_raw :
      (exp_taylor_12_at_048122 : ℝ) ≤
        |(0.48122 : ℝ)|^12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) +
          Real.exp (0.48122 : ℝ) := by
    simpa [h_taylor_eq, add_comm, add_left_comm, add_assoc] using h_abs.2
  have h_lower :
      (exp_taylor_12_at_048122 : ℝ) - (exp_error_12_at_048122 : ℝ) ≤
        Real.exp (0.48122 : ℝ) := by
    have h_lower' :
        (exp_taylor_12_at_048122 : ℝ) ≤
          (exp_error_12_at_048122 : ℝ) + Real.exp (0.48122 : ℝ) := by
      calc
        (exp_taylor_12_at_048122 : ℝ)
            ≤ |(0.48122 : ℝ)|^12 *
                ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) +
                  Real.exp (0.48122 : ℝ) := h_lower_raw
        _ = (exp_error_12_at_048122 : ℝ) + Real.exp (0.48122 : ℝ) := by
              rw [h_err_eq]
    linarith
  have h_num :
      (1.61804 : ℝ) <
        (exp_taylor_12_at_048122 : ℝ) - (exp_error_12_at_048122 : ℝ) := by
    have h' : (((80902 / 50000 : ℚ) : ℝ)) <
        (exp_taylor_12_at_048122 : ℝ) - (exp_error_12_at_048122 : ℝ) := by
      exact_mod_cast exp_048122_taylor_floor
    norm_num at h' ⊢
    exact h'
  exact lt_of_lt_of_le h_num h_lower

/-- Tight enough upper bound on `log φ` for the measurement verdict. -/
theorem log_phi_lt_048122 : Real.log Constants.phi < (0.48122 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp Constants.phi_pos]
  have hphi_hi : Constants.phi < (1.6180340 : ℝ) :=
    Numerics.W8Bounds.phi_lt_16180340
  exact lt_trans hphi_hi (by linarith [exp_048122_gt])

private def exp_taylor_12_at_neg_0086705 : ℚ :=
  let x : ℚ := -(86705 : ℚ) / 10000000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040
    + x^8/40320 + x^9/362880 + x^10/3628800 + x^11/39916800

private def exp_error_12_at_neg_0086705 : ℚ :=
  let x : ℚ := (86705 : ℚ) / 10000000
  x^12 * 13 / (Nat.factorial 12 * 12)

private lemma exp_neg_0086705_taylor_floor :
    (49568347 / 50000000 : ℚ) <
      exp_taylor_12_at_neg_0086705 - exp_error_12_at_neg_0086705 := by
  native_decide

/-- `exp(-0.0086705) > 0.99136694`. -/
private lemma exp_neg_0086705_gt : (0.99136694 : ℝ) < Real.exp (-0.0086705 : ℝ) := by
  have hx_abs : |(-0.0086705 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 12) (by norm_num : 0 < 12)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 12, (-0.0086705 : ℝ)^m / m.factorial) =
        (exp_taylor_12_at_neg_0086705 : ℝ) := by
    simp only [exp_taylor_12_at_neg_0086705, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial]
    norm_num
  have h_err_eq :
      |(-0.0086705 : ℝ)|^12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) =
        (exp_error_12_at_neg_0086705 : ℝ) := by
    simp only [exp_error_12_at_neg_0086705, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lower_raw :
      (exp_taylor_12_at_neg_0086705 : ℝ) ≤
        |(-0.0086705 : ℝ)|^12 * ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) +
          Real.exp (-0.0086705 : ℝ) := by
    simpa [h_taylor_eq, add_comm, add_left_comm, add_assoc] using h_abs.2
  have h_lower :
      (exp_taylor_12_at_neg_0086705 : ℝ) - (exp_error_12_at_neg_0086705 : ℝ) ≤
        Real.exp (-0.0086705 : ℝ) := by
    have h_lower' :
        (exp_taylor_12_at_neg_0086705 : ℝ) ≤
          (exp_error_12_at_neg_0086705 : ℝ) + Real.exp (-0.0086705 : ℝ) := by
      calc
        (exp_taylor_12_at_neg_0086705 : ℝ)
            ≤ |(-0.0086705 : ℝ)|^12 *
                ((Nat.succ 12 : ℕ) / ((Nat.factorial 12 : ℕ) * 12)) +
                  Real.exp (-0.0086705 : ℝ) := h_lower_raw
        _ = (exp_error_12_at_neg_0086705 : ℝ) + Real.exp (-0.0086705 : ℝ) := by
              rw [h_err_eq]
    linarith
  have h_num :
      (0.99136694 : ℝ) <
        (exp_taylor_12_at_neg_0086705 : ℝ) - (exp_error_12_at_neg_0086705 : ℝ) := by
    have h' : (((49568347 / 50000000 : ℚ) : ℝ)) <
        (exp_taylor_12_at_neg_0086705 : ℝ) - (exp_error_12_at_neg_0086705 : ℝ) := by
      exact_mod_cast exp_neg_0086705_taylor_floor
    norm_num at h' ⊢
    exact h'
  exact lt_of_lt_of_le h_num h_lower

/-! ## Certified first-order exclusion -/

/-- Tight upper bound on the natural exponential load `f_gap / alpha_seed`. -/
theorem exponentialLoad_lt_0086705 :
    Constants.f_gap / Constants.alpha_seed < (0.0086705 : ℝ) := by
  have hfg_hi : Constants.f_gap < (1.198514 : ℝ) := by
    unfold Constants.f_gap
    have hw_hi := Numerics.W8Bounds.w8_computed_lt
    have hlog_hi := log_phi_lt_048122
    have hw_pos : 0 < Constants.w8_from_eight_tick := Constants.w8_pos
    have hlog_pos : 0 < Real.log Constants.phi := by
      exact Real.log_pos Constants.one_lt_phi
    calc
      Constants.w8_from_eight_tick * Real.log Constants.phi
          < Constants.w8_from_eight_tick * (0.48122 : ℝ) :=
            mul_lt_mul_of_pos_left hlog_hi hw_pos
      _ < (2.490572090 : ℝ) * (0.48122 : ℝ) :=
            mul_lt_mul_of_pos_right hw_hi (by norm_num)
      _ < (1.198514 : ℝ) := by norm_num
  have hseed_lo : (138.230048 : ℝ) < Constants.alpha_seed := Numerics.alpha_seed_gt
  have hseed_pos : 0 < Constants.alpha_seed := lt_trans (by norm_num) hseed_lo
  rw [div_lt_iff₀ hseed_pos]
  calc
    Constants.f_gap < (1.198514 : ℝ) := hfg_hi
    _ < (0.0086705 : ℝ) * Constants.alpha_seed := by nlinarith [hseed_lo]

/-- The first-order Alpha Genesis value is above CODATA by at least `0.0007`.
This is the formal version of Anil's measurement objection, stated coarsely
but with a fully certified margin. -/
theorem alphaInvGenesis_exceeds_CODATA_by_0007 :
    alpha_inv_CODATA + (0.0007 : ℝ) < alphaInvGenesis := by
  rw [alphaInvGenesis_eq_alphaInv]
  unfold Constants.alphaInv
  have hseed_lo : (138.230048 : ℝ) < Constants.alpha_seed := Numerics.alpha_seed_gt
  have hseed_pos : 0 < Constants.alpha_seed := lt_trans (by norm_num) hseed_lo
  have hload_hi : Constants.f_gap / Constants.alpha_seed < (0.0086705 : ℝ) :=
    exponentialLoad_lt_0086705
  have hexp_mono : Real.exp (-0.0086705 : ℝ) < Real.exp (-(Constants.f_gap / Constants.alpha_seed)) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp_lo : (0.99136694 : ℝ) < Real.exp (-(Constants.f_gap / Constants.alpha_seed)) :=
    lt_trans exp_neg_0086705_gt hexp_mono
  have hmul :
      (138.230048 : ℝ) * (0.99136694 : ℝ) <
        Constants.alpha_seed * Real.exp (-(Constants.f_gap / Constants.alpha_seed)) := by
    have h1 :
        (138.230048 : ℝ) * (0.99136694 : ℝ) <
          Constants.alpha_seed * (0.99136694 : ℝ) :=
      mul_lt_mul_of_pos_right hseed_lo (by norm_num)
    have h2 :
        Constants.alpha_seed * (0.99136694 : ℝ) <
          Constants.alpha_seed * Real.exp (-(Constants.f_gap / Constants.alpha_seed)) :=
      mul_lt_mul_of_pos_left hexp_lo hseed_pos
    exact lt_trans h1 h2
  have htarget :
      alpha_inv_CODATA + (0.0007 : ℝ) <
        (138.230048 : ℝ) * (0.99136694 : ℝ) := by
    norm_num [alpha_inv_CODATA]
  exact lt_trans htarget hmul

/-- CODATA uncertainty is exactly the stored one-sigma value. -/
theorem alpha_inv_uncertainty_eq : alpha_inv_CODATA_uncertainty = (0.000000021 : ℝ) := rfl

/-- The certified `0.0007` overshoot is more than `30000` one-sigma
uncertainties. -/
theorem margin_0007_gt_30000_sigma :
    (30000 : ℝ) * alpha_inv_CODATA_uncertainty < (0.0007 : ℝ) := by
  norm_num [alpha_inv_CODATA_uncertainty]

/-- Measurement verdict certificate: the first-order genesis value is excluded
by a CODATA comparison with a margin greater than `30000σ`. -/
structure MeasurementVerdictCert where
  exceeds_by_margin : alpha_inv_CODATA + (0.0007 : ℝ) < alphaInvGenesis
  margin_many_sigma : (30000 : ℝ) * alpha_inv_CODATA_uncertainty < (0.0007 : ℝ)
  quarantine : True

def measurementVerdictCert : MeasurementVerdictCert where
  exceeds_by_margin := alphaInvGenesis_exceeds_CODATA_by_0007
  margin_many_sigma := margin_0007_gt_30000_sigma
  quarantine := trivial

end

end MeasurementVerdict
end AlphaGenesis
end Constants
end IndisputableMonolith
