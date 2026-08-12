import Mathlib
import IndisputableMonolith.Constants

/-!
# The dark-matter gap correction, derived from the closure machinery

The manuscripts printed Ω_dm = sin(π/12) + 1/(8 ln φ) ≈ 0.264934. The printed
gap term is arithmetically broken: 1/(8 ln φ) ≈ 0.2598, roughly 43 times the
claimed total correction δ ≈ 0.0061, and the six-digit sum does not follow
from it. The registry demoted the claim 2026-07-24 "until Lean target exists"
(Recognition-Science-Full-Theory.txt, CERT;OmegaDM_Value). This module is
that target: the gap is derived from the closure machinery and the corrected
prediction is certified here.

## The derivation

Two closure readings, one number.

(1) **Closure-work reading.** A single unresolved channel among the 12 edge
    channels carries its share of the closure-work ceiling J(φ) = φ − 3/2
    (the phantom-Carnot ceiling), attenuated by the single-channel closure
    ratio φ⁻¹: δ = J(φ)/(12φ).

(2) **Dilution reading.** The dimension-uniform multiplicative closure law
    attenuates by φ⁻¹ per unit of dimension; over d = 4 that is φ⁻⁴.
    Spread over the 24 = 2×12 phases of the 12-channel interference (the
    same 24 that fixes the base angle π/12 = 2π/24): δ = φ⁻⁴/24.

`gap_forms_agree` proves the two readings are the same number: the identity
reduces to 2φ⁵ − 3φ⁴ = φ, exact from φ² = φ + 1.

## Status and honesty boundary

THEOREM (this module, axiom-clean): the identity, the numerical band, the
target match, the Planck contact, and the defect magnitude of the printed
term. The composition step is now FORCED at the conditional-uniqueness
standard in `Gravity.DarkMatterGapForcing`: every cycle-symmetric, minimal,
dimension-four closed occupancy equals φ⁻⁴/24 (`gap_forced`), the named
rivals give different numbers (`rival_*_ne`), and two irreducible premises
remain named there (P1 instantiation, P2 the ledger-probability bridge).

Falsifier: any measurement of Ω_c more than 0.021 (3σ of the current Planck
uncertainty) from 0.264898 kills this prediction.
-/

namespace IndisputableMonolith
namespace Gravity

open Constants

noncomputable section

/-- **Closure-work form of the gap**: J(φ) per channel at the closure ratio. -/
def gapClosureWork : ℝ := (phi - 3 / 2) / (12 * phi)

/-- **Dilution form of the gap**: φ⁻⁴ over the 24 channel phases. -/
def gapDilution : ℝ := 1 / (24 * phi ^ 4)

/-- **The two closure readings are the same number.**
    Reduces to 2φ⁵ − 3φ⁴ = φ, exact from φ² = φ + 1. -/
theorem gap_forms_agree : gapClosureWork = gapDilution := by
  have h45 : 2 * phi ^ 5 - 3 * phi ^ 4 = phi := by
    rw [phi_fifth_eq, phi_fourth_eq]; ring
  have h34 : 2 * phi ^ 4 - 3 * phi ^ 3 = 1 := by
    rw [phi_fourth_eq, phi_cubed_eq]; ring
  have hp := phi_pos
  have h12 : (0 : ℝ) < 12 * phi := by positivity
  have h24 : (0 : ℝ) < 24 * phi ^ 4 := by positivity
  unfold gapClosureWork gapDilution
  field_simp [h12.ne', h24.ne']
  ring_nf
  linarith [h45, h34]

/-- **The printed leading term is not the gap.** It exceeds 0.17, more than
    27 times the true gap: 1/(8 ln φ) > 0.17 while φ⁻⁴/24 < 0.0061. The
    manuscripts' series with leading term 1/(8 ln φ) cannot sum to the
    claimed correction. -/
theorem printed_term_not_gap :
    (0.17 : ℝ) < 1 / (8 * Real.log phi) := by
  have hlogpos : 0 < Real.log phi := Real.log_pos one_lt_phi
  have hloglt : Real.log phi < Real.log 2 :=
    Real.log_lt_log phi_pos phi_lt_two
  have h8 : 8 * Real.log phi < 5.546 := by
    linarith [Real.log_two_lt_d9]
  have h1 : (0.17 : ℝ) < 1 / 5.546 := by norm_num
  exact h1.trans (one_div_lt_one_div_of_lt (by positivity) h8)

/-- Tight bounds on √5 for the φ⁴ bounds below. -/
private lemma sqrt5_bounds : (2.236 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.2361 := by
  have hlo : (2.236 : ℝ) ^ 2 < (Real.sqrt 5) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num
  have hhi : (Real.sqrt 5) ^ 2 < (2.2361 : ℝ) ^ 2 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num
  exact ⟨lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg 5) hlo,
         lt_of_pow_lt_pow_left₀ 2 (by norm_num) hhi⟩

/-- The gap lies in (0.006079, 0.0060792). -/
theorem gap_bounds :
    (0.006079 : ℝ) < gapDilution ∧ gapDilution < 0.0060792 := by
  obtain ⟨h5lo, h5hi⟩ := sqrt5_bounds
  have hphi_lo : (1.618 : ℝ) < phi := by
    unfold phi; linarith
  have hphi_hi : phi < (1.61805 : ℝ) := by
    unfold phi; linarith
  have h4lo : (6.854 : ℝ) < phi ^ 4 := by
    rw [phi_fourth_eq]; linarith
  have h4hi : phi ^ 4 < (6.85415 : ℝ) := by
    rw [phi_fourth_eq]; linarith
  have h24 : (0 : ℝ) < 24 * phi ^ 4 := by positivity
  constructor
  · rw [gapDilution, lt_div_iff₀ h24]
    nlinarith
  · rw [gapDilution, div_lt_iff₀ h24]
    nlinarith

/-- sin²(π/12) = (2 − √3)/4, from the half-angle identity and cos(π/6) = √3/2. -/
theorem sin_pi_div_twelve_sq :
    Real.sin (Real.pi / 12) ^ 2 = (2 - Real.sqrt 3) / 4 := by
  have h := Real.sin_sq_eq_half_sub (Real.pi / 12)
  rw [show 2 * (Real.pi / 12) = Real.pi / 6 by ring, Real.cos_pi_div_six] at h
  rw [h]; field_simp; ring

/-- sin(π/12) lies in (0.25879, 0.25886). -/
theorem sin_pi_div_twelve_bounds :
    (0.25879 : ℝ) < Real.sin (Real.pi / 12) ∧
    Real.sin (Real.pi / 12) < 0.25886 := by
  have hsq := sin_pi_div_twelve_sq
  have hpos : 0 < Real.sin (Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have h3lo : (1.732 : ℝ) < Real.sqrt 3 := by
    have h : (1.732 : ℝ) ^ 2 < (Real.sqrt 3) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg 3) h
  have h3hi : Real.sqrt 3 < (1.7321 : ℝ) := by
    have h : (Real.sqrt 3) ^ 2 < (1.7321 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h
  constructor
  · have h1 : (0.25879 : ℝ) ^ 2 < Real.sin (Real.pi / 12) ^ 2 := by
      rw [hsq]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hpos.le h1
  · have h2 : Real.sin (Real.pi / 12) ^ 2 < (0.25886 : ℝ) ^ 2 := by
      rw [hsq]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) h2

/-- **The derived dark-matter fraction**: Ω_dm = sin(π/12) + φ⁻⁴/24. -/
def omega_DM_derived : ℝ := Real.sin (Real.pi / 12) + gapDilution

/-- The derived fraction lies in (0.2648, 0.2650). -/
theorem omega_DM_derived_band :
    (0.2648 : ℝ) < omega_DM_derived ∧ omega_DM_derived < 0.2650 := by
  obtain ⟨hslo, hshi⟩ := sin_pi_div_twelve_bounds
  obtain ⟨hglo, hghi⟩ := gap_bounds
  unfold omega_DM_derived
  constructor <;> linarith

/-- The derived fraction reproduces the printed 4-digit target 0.2649
    to better than 4 × 10⁻⁵. -/
theorem omega_DM_derived_target :
    |omega_DM_derived - 0.2649| < 0.00004 := by
  obtain ⟨hslo, hshi⟩ := sin_pi_div_twelve_bounds
  obtain ⟨hglo, hghi⟩ := gap_bounds
  unfold omega_DM_derived
  rw [abs_lt]
  constructor <;> linarith

/-- **Planck contact**: the derived fraction sits within 2 × 10⁻⁴ of the
    Planck 2018 central value Ω_c = 0.265 (uncertainty ±0.007), i.e. inside
    0.03σ, with the point estimate 0.264898 at 0.015σ. -/
theorem omega_DM_derived_planck :
    |omega_DM_derived - 0.265| < 0.0002 := by
  obtain ⟨hslo, hshi⟩ := sin_pi_div_twelve_bounds
  obtain ⟨hglo, hghi⟩ := gap_bounds
  unfold omega_DM_derived
  rw [abs_lt]
  constructor <;> linarith

end

/-! ## Axiom audit -/

#print axioms gap_forms_agree
#print axioms printed_term_not_gap
#print axioms omega_DM_derived_band
#print axioms omega_DM_derived_target
#print axioms omega_DM_derived_planck

end Gravity
end IndisputableMonolith
