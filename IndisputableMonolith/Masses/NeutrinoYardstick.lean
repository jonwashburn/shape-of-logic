import Mathlib
import IndisputableMonolith.Constants

/-!
# Neutrino Yardstick Derivation

The neutrino sector yardstick is the last unfixed mass parameter.
This module derives constraints on the neutrino yardstick from the
existing mass law structure and cosmological bounds.

## Neutrino Sector Properties

- ZOf = 0 (neutral, chiral) — unique among fermion sectors
- Gap function: gap(0) = 0 (no gap correction)
- Rungs: ν₁ = 0, ν₂ = 11, ν₃ = 19 (from RSBridge.Anchor)
- Baseline: neutrino_baseline_int = -54

## Constraint: Cosmological Mass Sum Bound

Planck+DESI: Σmᵢ < 0.12 eV (95% CL).
The yardstick Y_ν must satisfy:
  Y_ν × (φ^(0-8) + φ^(11-8) + φ^(19-8)) < 0.12 eV

## Status: THEOREM (constraints) + HYPOTHESIS (unique determination)
-/

namespace IndisputableMonolith.Masses.NeutrinoYardstick

open Constants

/-- The three neutrino rung assignments. -/
def nu_rungs : Fin 3 → ℤ := ![0, 11, 19]

/-- Mass formula: m_i = Y × φ^(rung_i - 8). -/
noncomputable def nuMass (Y : ℝ) (i : Fin 3) : ℝ :=
  Y * phi ^ (nu_rungs i - 8)

/-- Sum of neutrino masses as function of yardstick. -/
noncomputable def nuMassSum (Y : ℝ) : ℝ :=
  nuMass Y 0 + nuMass Y 1 + nuMass Y 2

/-- The mass sum factor: φ^(-8) + φ^3 + φ^11. -/
noncomputable def sumFactor : ℝ :=
  phi ^ (-8 : ℤ) + phi ^ (3 : ℤ) + phi ^ (11 : ℤ)

theorem sum_factor_pos : sumFactor > 0 := by
  unfold sumFactor
  have h1 : phi ^ (-8 : ℤ) > 0 := zpow_pos phi_pos _
  have h2 : phi ^ (3 : ℤ) > 0 := zpow_pos phi_pos _
  have h3 : phi ^ (11 : ℤ) > 0 := zpow_pos phi_pos _
  linarith

/-- The mass sum is linear in the yardstick. -/
theorem nuMassSum_eq_Y_times_factor (Y : ℝ) :
    nuMassSum Y = Y * sumFactor := by
  unfold nuMassSum nuMass sumFactor nu_rungs
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Cosmological bound constrains the yardstick.
    Σmᵢ < 0.12 eV ⟹ Y < 0.12 / sumFactor. -/
theorem yardstick_upper_bound (Y : ℝ) (hY : Y > 0)
    (h_cosmo : nuMassSum Y < 0.12) :
    Y < 0.12 / sumFactor := by
  rw [nuMassSum_eq_Y_times_factor] at h_cosmo
  rw [lt_div_iff₀ sum_factor_pos]
  linarith [mul_comm Y sumFactor]

/-- Normal mass ordering: ν₃ > ν₂ > ν₁ for positive yardstick. -/
theorem normal_ordering (Y : ℝ) (hY : Y > 0) :
    nuMass Y 0 < nuMass Y 1 ∧ nuMass Y 1 < nuMass Y 2 := by
  unfold nuMass nu_rungs
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  constructor
  · apply mul_lt_mul_of_pos_left _ hY
    exact zpow_lt_zpow_right₀ one_lt_phi (by omega : (-8 : ℤ) < 3)
  · apply mul_lt_mul_of_pos_left _ hY
    exact zpow_lt_zpow_right₀ one_lt_phi (by omega : (3 : ℤ) < 11)

/-- Mass ratio ν₃/ν₂ is determined by rung differences.
    ν₃/ν₂ = Y·φ^11 / (Y·φ^3) = φ^8. -/
theorem mass_ratio_from_rungs (Y : ℝ) (hY : Y > 0) :
    nuMass Y 2 / nuMass Y 1 = phi ^ (8 : ℤ) := by
  show Y * phi ^ ((19 : ℤ) - 8) / (Y * phi ^ ((11 : ℤ) - 8)) = phi ^ (8 : ℤ)
  norm_num
  rw [mul_div_mul_left _ _ (ne_of_gt hY)]
  rw [← zpow_sub₀ (ne_of_gt phi_pos)]
  norm_num

/-- Neutrino mass structure certificate. -/
structure NeutrinoYardstickCert where
  sum_linear : ∀ Y : ℝ, nuMassSum Y = Y * sumFactor
  sum_factor_positive : sumFactor > 0
  normal_order : ∀ Y : ℝ, Y > 0 →
    nuMass Y 0 < nuMass Y 1 ∧ nuMass Y 1 < nuMass Y 2
  ratio_from_rungs : ∀ Y : ℝ, Y > 0 →
    nuMass Y 2 / nuMass Y 1 = phi ^ (8 : ℤ)

noncomputable def neutrinoYardstickCert_holds : NeutrinoYardstickCert where
  sum_linear := nuMassSum_eq_Y_times_factor
  sum_factor_positive := sum_factor_pos
  normal_order := normal_ordering
  ratio_from_rungs := mass_ratio_from_rungs

end IndisputableMonolith.Masses.NeutrinoYardstick
