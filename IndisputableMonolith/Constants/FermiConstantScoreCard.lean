import Mathlib
import IndisputableMonolith.Constants.ElectroweakVEVStructure
import IndisputableMonolith.Numerics.Interval.W8Bounds

/-!
# Fermi Constant Score Card

Phase 1 row **P1-C01** in `planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

The theorem-grade slice is the natural-unit electroweak identity

`G_F = 1 / (sqrt 2 * v^2)`

with the canonical RS electroweak VEV surface `v = 246 GeV`.

## Measurement target

CODATA / PDG:

`G_F = 1.1663787 x 10^-5 GeV^-2`.

This module proves the interval

`1.16 x 10^-5 < G_F^RS < 1.17 x 10^-5`,

so the CODATA value sits inside the bracket. The row remains
**PARTIAL_THEOREM** because `ElectroweakVEVStructure.vev_canonical = 246`
is the canonical GeV display value; the fully derived SI/GeV VEV bridge
is still open.

Falsifier: CODATA/PDG `G_F` outside `(1.16e-5, 1.17e-5) GeV^-2`, or a
future VEV bridge that does not recover the canonical 246 GeV scale.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Constants.FermiConstantScoreCard

open IndisputableMonolith.Constants.ElectroweakVEVStructure
open IndisputableMonolith.Numerics
open IndisputableMonolith.Numerics.W8Bounds

noncomputable section

/-! ## Re-exported row aliases -/

/-- P1-C01 Fermi constant prediction in GeV^-2 natural units. -/
noncomputable def row_fermi_pred : ℝ :=
  1 / (Real.sqrt 2 * vev_canonical ^ 2)

/-- CODATA/PDG Fermi constant in GeV^-2. -/
def row_fermi_codata : ℝ := 1.1663787e-5

theorem row_fermi_pred_eq :
    row_fermi_pred = 1 / (Real.sqrt 2 * vev_canonical ^ 2) := rfl

private theorem sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private theorem fermi_den_pos : 0 < Real.sqrt 2 * vev_canonical ^ 2 := by
  have hv : 0 < vev_canonical ^ 2 := sq_pos_of_ne_zero (ne_of_gt vev_canonical_pos)
  nlinarith [sqrt2_pos, hv]

theorem row_fermi_pred_lower :
    (1.16e-5 : ℝ) < row_fermi_pred := by
  unfold row_fermi_pred
  rw [lt_div_iff₀ fermi_den_pos]
  have hs : Real.sqrt 2 < (1.4143 : ℝ) := sqrt2_lt_14143
  have hden :
      Real.sqrt 2 * vev_canonical ^ 2 < (1.4143 : ℝ) * (246 : ℝ) ^ 2 := by
    have hv : vev_canonical = (246 : ℝ) := rfl
    have hvpos : 0 < vev_canonical ^ 2 := sq_pos_of_ne_zero (ne_of_gt vev_canonical_pos)
    rw [hv]
    nlinarith
  have hnum : (1.16e-5 : ℝ) * ((1.4143 : ℝ) * (246 : ℝ) ^ 2) < 1 := by
    norm_num
  nlinarith

theorem row_fermi_pred_upper :
    row_fermi_pred < (1.17e-5 : ℝ) := by
  unfold row_fermi_pred
  rw [div_lt_iff₀ fermi_den_pos]
  have hs : (1.4142 : ℝ) < Real.sqrt 2 := sqrt2_gt_14142
  have hden :
      (1.4142 : ℝ) * (246 : ℝ) ^ 2 < Real.sqrt 2 * vev_canonical ^ 2 := by
    have hv : vev_canonical = (246 : ℝ) := rfl
    rw [hv]
    nlinarith
  have hnum : 1 < (1.17e-5 : ℝ) * ((1.4142 : ℝ) * (246 : ℝ) ^ 2) := by
    norm_num
  nlinarith

theorem row_fermi_pred_bracket :
    (1.16e-5 : ℝ) < row_fermi_pred ∧ row_fermi_pred < (1.17e-5 : ℝ) :=
  ⟨row_fermi_pred_lower, row_fermi_pred_upper⟩

theorem row_fermi_codata_in_bracket :
    (1.16e-5 : ℝ) < row_fermi_codata ∧ row_fermi_codata < (1.17e-5 : ℝ) := by
  unfold row_fermi_codata
  constructor <;> norm_num

structure FermiConstantScoreCardCert where
  fermi_bracket :
    (1.16e-5 : ℝ) < row_fermi_pred ∧ row_fermi_pred < (1.17e-5 : ℝ)
  codata_in_bracket :
    (1.16e-5 : ℝ) < row_fermi_codata ∧ row_fermi_codata < (1.17e-5 : ℝ)
  vev_range : (244 : ℝ) < vev_canonical ∧ vev_canonical < (248 : ℝ)

theorem fermiConstantScoreCardCert_holds :
    Nonempty FermiConstantScoreCardCert :=
  ⟨{ fermi_bracket := row_fermi_pred_bracket
     codata_in_bracket := row_fermi_codata_in_bracket
     vev_range := vev_in_range }⟩

end

end IndisputableMonolith.Constants.FermiConstantScoreCard
