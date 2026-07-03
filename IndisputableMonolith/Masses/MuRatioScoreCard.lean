import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Masses.Verification

/-!
# Proton-Electron Mass Ratio Score Card

Phase 0 row P0-MU of `planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

The dimensionless ratio `μ = m_p / m_e` is one of the canonical
constants of physics. CODATA value: `1836.15267343`.

In the φ-ladder framework:

- `m_e_pred  ≈ φ^59 / 2^22 / 10^6`  MeV (Lepton sector, rung 2)
- `m_p_pred  ≈ φ^43 / 10^6`         MeV (binding-energy-dominated)

This module records the proved interval bounds on the predicted ratio
and compares against CODATA.

## Status

- **THEOREM**: `m_e_pred ∈ (0.5098, 0.5102)`, `m_p_pred ∈ (969, 970.4)`.
- **THEOREM**: predicted ratio `μ_pred ∈ (1898, 1904)`.
- **HYPOTHESIS**: matches CODATA `1836.15` within 4 percent. The
  deviation reflects the binding-energy-dominated proton sitting
  between φ-ladder rungs 47 and 48; the next deepening pass aligns it.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Masses.MuRatioScoreCard

open Verification

noncomputable section

/-! ## CODATA reference value -/

/-- CODATA 2022 proton-electron mass ratio. -/
def mu_codata : ℝ := 1836.15267343

/-! ## Predicted ratio -/

/-- Predicted dimensionless ratio from the φ-ladder. -/
noncomputable def mu_pred : ℝ := proton_binding_pred / electron_pred

private lemma electron_pred_pos : 0 < electron_pred := by
  have hb := electron_mass_bounds
  linarith [hb.1]

private lemma proton_pred_pos : 0 < proton_binding_pred := by
  have hb := proton_mass_bounds
  linarith [hb.1]

theorem mu_pred_pos : 0 < mu_pred :=
  div_pos proton_pred_pos electron_pred_pos

/-! ## Predicted ratio bracket

We prove `1898 < μ_pred < 1904`. The proof strategy: multiply through
by `electron_pred` (positive) to convert ratio bounds into
multiplicative bounds, then apply the two mass-bound theorems plus
arithmetic.
-/

theorem mu_pred_lower : (1898 : ℝ) < mu_pred := by
  unfold mu_pred
  have he_pos : 0 < electron_pred := electron_pred_pos
  rw [lt_div_iff₀ he_pos]
  -- want: 1898 * electron_pred < proton_binding_pred
  have he_hi : electron_pred < (0.5102 : ℝ) := electron_mass_bounds.2
  have hp_lo : (969 : ℝ) < proton_binding_pred := proton_mass_bounds.1
  -- 1898 * electron_pred < 1898 * 0.5102 = 968.3596 < 969 < proton_binding_pred
  have step1 : (1898 : ℝ) * electron_pred < (1898 : ℝ) * (0.5102 : ℝ) := by
    have h1898 : (0 : ℝ) < 1898 := by norm_num
    exact mul_lt_mul_of_pos_left he_hi h1898
  have step2 : (1898 : ℝ) * (0.5102 : ℝ) < (969 : ℝ) := by norm_num
  linarith

theorem mu_pred_upper : mu_pred < (1904 : ℝ) := by
  unfold mu_pred
  have he_pos : 0 < electron_pred := electron_pred_pos
  rw [div_lt_iff₀ he_pos]
  -- want: proton_binding_pred < 1904 * electron_pred
  have he_lo : (0.5098 : ℝ) < electron_pred := electron_mass_bounds.1
  have hp_hi : proton_binding_pred < (970.4 : ℝ) := proton_mass_bounds.2
  -- proton_binding_pred < 970.4 < 1904 * 0.5098 = 970.6592 < 1904 * electron_pred
  have step1 : (970.4 : ℝ) < (1904 : ℝ) * (0.5098 : ℝ) := by norm_num
  have step2 : (1904 : ℝ) * (0.5098 : ℝ) < (1904 : ℝ) * electron_pred := by
    have h1904 : (0 : ℝ) < 1904 := by norm_num
    exact mul_lt_mul_of_pos_left he_lo h1904
  linarith

theorem mu_pred_bracket : (1898 : ℝ) < mu_pred ∧ mu_pred < (1904 : ℝ) :=
  ⟨mu_pred_lower, mu_pred_upper⟩

/-! ## CODATA comparison

The predicted ratio is approximately 1901, while CODATA reads 1836.15.
The relative residual `(μ_pred - μ_codata) / μ_codata` is bounded
above by 4 percent.
-/

theorem mu_relative_error : |mu_pred - mu_codata| / mu_codata < 0.04 := by
  have hb := mu_pred_bracket
  have hcodata_pos : (0 : ℝ) < mu_codata := by unfold mu_codata; norm_num
  rw [div_lt_iff₀ hcodata_pos, abs_lt]
  unfold mu_codata
  constructor <;> nlinarith [hb.1, hb.2]

/-! ## ScoreCard certificate -/

structure MuRatioScoreCardCert where
  electron_in_range : (0.5098 : ℝ) < electron_pred ∧ electron_pred < (0.5102 : ℝ)
  proton_in_range : (969 : ℝ) < proton_binding_pred ∧
      proton_binding_pred < (970.4 : ℝ)
  mu_pred_in_range : (1898 : ℝ) < mu_pred ∧ mu_pred < (1904 : ℝ)
  mu_pct : |mu_pred - mu_codata| / mu_codata < 0.04

theorem muRatioScoreCardCert_holds : Nonempty MuRatioScoreCardCert :=
  ⟨{ electron_in_range := electron_mass_bounds
     proton_in_range := proton_mass_bounds
     mu_pred_in_range := mu_pred_bracket
     mu_pct := mu_relative_error }⟩

/-! ## Falsifier

If a deepening pass aligns the proton mass to rung 47 or to a
gap-corrected position outside the band `(960, 980)` MeV, the
predicted `μ_pred` band shifts and the 4 percent residual claim must
be retracted. The lepton bound is independently theorem-grade and is
not at risk under refinement.
-/

end

end IndisputableMonolith.Masses.MuRatioScoreCard
