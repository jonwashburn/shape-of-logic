import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Electron g-2 Score Card

Phase 1 row **P1-C05** in `planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

The theorem-grade slice is the leading Schwinger term

`a_e^(1) = α / (2π)`.

Using the certified RS `alphaInv` interval, this module proves

`0.001161 < a_e^(1) < 0.001162`.

The CODATA electron anomaly is

`a_e = 0.00115965218059...`.

The leading term alone is within `0.3%` of CODATA, but the full electron
g-2 row remains **PARTIAL_THEOREM** because the higher-order loop series
has not yet been derived from RS primitives in this module.

Falsifier: CODATA `a_e` outside the stated residual band for the
Schwinger-only slice, or failure to derive the missing loop terms from
the RS/QED bridge.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Physics.ElectronGMinus2ScoreCard

open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

noncomputable section

/-! ## Re-exported row aliases -/

/-- P1-C05 leading electron anomaly prediction. -/
noncomputable def row_electron_ae_leading : ℝ :=
  alpha / (2 * Real.pi)

/-- CODATA electron anomalous magnetic moment, dimensionless. -/
def row_electron_ae_codata : ℝ := 0.00115965218059

private theorem alphaInv_pos : 0 < alphaInv := by
  linarith [alphaInv_gt]

theorem row_electron_ae_leading_eq :
    row_electron_ae_leading = 1 / (2 * Real.pi * alphaInv) := by
  unfold row_electron_ae_leading alpha
  field_simp [ne_of_gt alphaInv_pos, Real.pi_ne_zero]

private theorem ae_den_pos : 0 < 2 * Real.pi * alphaInv := by
  nlinarith [Real.pi_pos, alphaInv_pos]

theorem row_electron_ae_leading_lower :
    (0.001161 : ℝ) < row_electron_ae_leading := by
  rw [row_electron_ae_leading_eq]
  rw [lt_div_iff₀ ae_den_pos]
  have hpiUB : (Real.pi : ℝ) < 3.142 := by
    linarith [Real.pi_lt_d6, Real.pi_pos]
  have h2piUB : (2 : ℝ) * Real.pi < 2 * 3.142 := by
    exact mul_lt_mul_of_pos_left hpiUB (by norm_num)
  have hden1 : (2 : ℝ) * Real.pi * alphaInv < (2 * 3.142) * alphaInv := by
    exact mul_lt_mul_of_pos_right h2piUB alphaInv_pos
  have hden2 : (2 * 3.142 : ℝ) * alphaInv < (2 * 3.142) * (137.039 : ℝ) := by
    exact mul_lt_mul_of_pos_left alphaInv_lt (by norm_num)
  have hnum : (0.001161 : ℝ) * ((2 * 3.142 : ℝ) * (137.039 : ℝ)) < 1 := by
    norm_num
  have hLpos : (0 : ℝ) < 0.001161 := by norm_num
  have hden : (2 : ℝ) * Real.pi * alphaInv < (2 * 3.142 : ℝ) * (137.039 : ℝ) := by
    linarith
  have hmul : (0.001161 : ℝ) * ((2 : ℝ) * Real.pi * alphaInv) <
      (0.001161 : ℝ) * ((2 * 3.142 : ℝ) * (137.039 : ℝ)) := by
    exact mul_lt_mul_of_pos_left hden hLpos
  linarith

theorem row_electron_ae_leading_upper :
    row_electron_ae_leading < (0.001162 : ℝ) := by
  rw [row_electron_ae_leading_eq]
  rw [div_lt_iff₀ ae_den_pos]
  have hpiLB : (3.1415 : ℝ) < (Real.pi : ℝ) := by
    linarith [Real.pi_gt_d6, Real.pi_pos]
  have h2piLB : (2 : ℝ) * 3.1415 < 2 * Real.pi := by
    exact mul_lt_mul_of_pos_left hpiLB (by norm_num)
  have hden1 : (2 * 3.1415 : ℝ) * (137.030 : ℝ) <
      (2 * Real.pi) * (137.030 : ℝ) := by
    exact mul_lt_mul_of_pos_right h2piLB (by norm_num)
  have hden2 : (2 * Real.pi : ℝ) * (137.030 : ℝ) < (2 * Real.pi) * alphaInv := by
    exact mul_lt_mul_of_pos_left alphaInv_gt (mul_pos (by norm_num) Real.pi_pos)
  have hnum : 1 < (0.001162 : ℝ) * ((2 * 3.1415 : ℝ) * (137.030 : ℝ)) := by
    norm_num
  have hUpos : (0 : ℝ) < 0.001162 := by norm_num
  have hden : (2 * 3.1415 : ℝ) * (137.030 : ℝ) < (2 * Real.pi) * alphaInv := by
    linarith
  have hmul : (0.001162 : ℝ) * ((2 * 3.1415 : ℝ) * (137.030 : ℝ)) <
      (0.001162 : ℝ) * ((2 * Real.pi) * alphaInv) := by
    exact mul_lt_mul_of_pos_left hden hUpos
  linarith

theorem row_electron_ae_leading_bracket :
    (0.001161 : ℝ) < row_electron_ae_leading ∧
      row_electron_ae_leading < (0.001162 : ℝ) :=
  ⟨row_electron_ae_leading_lower, row_electron_ae_leading_upper⟩

theorem row_electron_ae_codata_pos :
    0 < row_electron_ae_codata := by
  unfold row_electron_ae_codata
  norm_num

theorem row_electron_ae_schwinger_relative_residual :
    |row_electron_ae_leading - row_electron_ae_codata| /
      row_electron_ae_codata < (0.003 : ℝ) := by
  have hb := row_electron_ae_leading_bracket
  rw [div_lt_iff₀ row_electron_ae_codata_pos, abs_lt]
  unfold row_electron_ae_codata
  constructor <;> nlinarith [hb.1, hb.2]

structure ElectronGMinus2ScoreCardCert where
  leading_bracket :
    (0.001161 : ℝ) < row_electron_ae_leading ∧
      row_electron_ae_leading < (0.001162 : ℝ)
  schwinger_residual :
    |row_electron_ae_leading - row_electron_ae_codata| /
      row_electron_ae_codata < (0.003 : ℝ)

theorem electronGMinus2ScoreCardCert_holds :
    Nonempty ElectronGMinus2ScoreCardCert :=
  ⟨{ leading_bracket := row_electron_ae_leading_bracket
     schwinger_residual := row_electron_ae_schwinger_relative_residual }⟩

end

end IndisputableMonolith.Physics.ElectronGMinus2ScoreCard
