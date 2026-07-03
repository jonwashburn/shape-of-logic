import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Hartree, Rydberg, and Bohr Dimensionless Score Card

Phase 1 rows **P1-C04** (Hartree energy) and **P1-C02** (Rydberg
constant / hydrogen ground binding scale), plus **P1-C03** (Bohr radius)
in
`planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

The theorem-grade, unit-free content is:

* `E_h / (m_e c^2) = α^2`
* `E_R / (m_e c^2) = α^2 / 2`
* `a_0 / λbar_C = 1/α`

using the certified RS inverse fine-structure constant `alphaInv`.

## Measurement target

CODATA / NIST Hartree, Rydberg, and Bohr-radius constants in SI units.
This module does not claim a Joule or meter value, because that requires
the electron-mass, `h`, `c`, and SI display bridge. It records the
dimensionless ratios and their tight interval bounds.

Falsifier: CODATA `α^-1` outside `(137.030, 137.039)` or an SI bridge that
does not map the dimensionless `α²` / `α²/2` ratios to Hartree/Rydberg
measurements.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Constants.HartreeRydbergScoreCard

open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

noncomputable section

/-! ## Re-exported row aliases -/

/-- P1-C04 dimensionless Hartree/rest-energy ratio. -/
noncomputable def row_hartree_over_rest : ℝ := alpha ^ 2

/-- P1-C02 dimensionless Rydberg/rest-energy ratio. -/
noncomputable def row_rydberg_over_rest : ℝ := alpha ^ 2 / 2

/-- P1-C03 dimensionless Bohr/reduced-Compton radius ratio. -/
noncomputable def row_bohr_over_reduced_compton : ℝ := alphaInv

private theorem alphaInv_pos : 0 < alphaInv := by
  linarith [alphaInv_gt]

theorem row_hartree_over_rest_eq : row_hartree_over_rest = 1 / alphaInv ^ 2 := by
  unfold row_hartree_over_rest alpha
  field_simp [ne_of_gt alphaInv_pos]

theorem row_rydberg_over_rest_eq :
    row_rydberg_over_rest = 1 / (2 * alphaInv ^ 2) := by
  unfold row_rydberg_over_rest alpha
  field_simp [ne_of_gt alphaInv_pos]

/-! ## Certified interval bounds -/

theorem row_hartree_over_rest_lower :
    (5.32e-5 : ℝ) < row_hartree_over_rest := by
  rw [row_hartree_over_rest_eq]
  have hpos : 0 < alphaInv ^ 2 := sq_pos_of_ne_zero (ne_of_gt alphaInv_pos)
  rw [lt_div_iff₀ hpos]
  have hsq : alphaInv ^ 2 < (137.039 : ℝ) ^ 2 := by
    nlinarith [alphaInv_lt, alphaInv_gt]
  have hnum : (5.32e-5 : ℝ) * (137.039 : ℝ) ^ 2 < 1 := by norm_num
  nlinarith

theorem row_hartree_over_rest_upper :
    row_hartree_over_rest < (5.33e-5 : ℝ) := by
  rw [row_hartree_over_rest_eq]
  have hpos : 0 < alphaInv ^ 2 := sq_pos_of_ne_zero (ne_of_gt alphaInv_pos)
  rw [div_lt_iff₀ hpos]
  have hsq : (137.030 : ℝ) ^ 2 < alphaInv ^ 2 := by
    nlinarith [alphaInv_gt, alphaInv_lt]
  have hnum : 1 < (5.33e-5 : ℝ) * (137.030 : ℝ) ^ 2 := by norm_num
  nlinarith

theorem row_hartree_over_rest_bracket :
    (5.32e-5 : ℝ) < row_hartree_over_rest ∧
      row_hartree_over_rest < (5.33e-5 : ℝ) :=
  ⟨row_hartree_over_rest_lower, row_hartree_over_rest_upper⟩

theorem row_rydberg_over_rest_lower :
    (2.66e-5 : ℝ) < row_rydberg_over_rest := by
  rw [row_rydberg_over_rest_eq]
  have hsqpos : 0 < alphaInv ^ 2 := sq_pos_of_ne_zero (ne_of_gt alphaInv_pos)
  have hpos : 0 < 2 * alphaInv ^ 2 := by nlinarith
  rw [lt_div_iff₀ hpos]
  have hsq : alphaInv ^ 2 < (137.039 : ℝ) ^ 2 := by
    nlinarith [alphaInv_lt, alphaInv_gt]
  have hnum : (2.66e-5 : ℝ) * (2 * (137.039 : ℝ) ^ 2) < 1 := by norm_num
  nlinarith

theorem row_rydberg_over_rest_upper :
    row_rydberg_over_rest < (2.665e-5 : ℝ) := by
  rw [row_rydberg_over_rest_eq]
  have hsqpos : 0 < alphaInv ^ 2 := sq_pos_of_ne_zero (ne_of_gt alphaInv_pos)
  have hpos : 0 < 2 * alphaInv ^ 2 := by nlinarith
  rw [div_lt_iff₀ hpos]
  have hsq : (137.030 : ℝ) ^ 2 < alphaInv ^ 2 := by
    nlinarith [alphaInv_gt, alphaInv_lt]
  have hnum : 1 < (2.665e-5 : ℝ) * (2 * (137.030 : ℝ) ^ 2) := by norm_num
  nlinarith

theorem row_rydberg_over_rest_bracket :
    (2.66e-5 : ℝ) < row_rydberg_over_rest ∧
      row_rydberg_over_rest < (2.665e-5 : ℝ) :=
  ⟨row_rydberg_over_rest_lower, row_rydberg_over_rest_upper⟩

theorem row_bohr_over_reduced_compton_eq :
    row_bohr_over_reduced_compton = alphaInv := rfl

theorem row_bohr_over_reduced_compton_bracket :
    (137.030 : ℝ) < row_bohr_over_reduced_compton ∧
      row_bohr_over_reduced_compton < (137.039 : ℝ) :=
  ⟨alphaInv_gt, alphaInv_lt⟩

structure HartreeRydbergScoreCardCert where
  hartree_closed : row_hartree_over_rest = 1 / alphaInv ^ 2
  rydberg_closed : row_rydberg_over_rest = 1 / (2 * alphaInv ^ 2)
  bohr_closed : row_bohr_over_reduced_compton = alphaInv
  hartree_bracket :
    (5.32e-5 : ℝ) < row_hartree_over_rest ∧
      row_hartree_over_rest < (5.33e-5 : ℝ)
  rydberg_bracket :
    (2.66e-5 : ℝ) < row_rydberg_over_rest ∧
      row_rydberg_over_rest < (2.665e-5 : ℝ)
  bohr_bracket :
    (137.030 : ℝ) < row_bohr_over_reduced_compton ∧
      row_bohr_over_reduced_compton < (137.039 : ℝ)

theorem hartreeRydbergScoreCardCert_holds :
    Nonempty HartreeRydbergScoreCardCert :=
  ⟨{ hartree_closed := row_hartree_over_rest_eq
     rydberg_closed := row_rydberg_over_rest_eq
     bohr_closed := row_bohr_over_reduced_compton_eq
     hartree_bracket := row_hartree_over_rest_bracket
     rydberg_bracket := row_rydberg_over_rest_bracket
     bohr_bracket := row_bohr_over_reduced_compton_bracket }⟩

end

end IndisputableMonolith.Constants.HartreeRydbergScoreCard
