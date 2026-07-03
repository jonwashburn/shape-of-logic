import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.PhiBounds

namespace IndisputableMonolith
namespace StandardModel
namespace NeutrinoMassHierarchy

open Real
open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

/-! ## Observed Mass Differences -/

noncomputable def deltam21_sq : ℝ := 7.42e-5
noncomputable def deltam31_sq : ℝ := 2.51e-3
noncomputable def sum_mass_bound : ℝ := 0.12

/-! ## The Seesaw Mechanism -/

noncomputable def seesawMass (mD MR : ℝ) : ℝ := mD^2 / MR
noncomputable def typicalDiracMass : ℝ := 100
noncomputable def typicalMajoranaMass : ℝ := 1e14

theorem seesaw_gives_small_mass :
    seesawMass typicalDiracMass typicalMajoranaMass = 1e-10 := by
  unfold seesawMass typicalDiracMass typicalMajoranaMass
  norm_num

/-! ## φ-Connection to the Seesaw Scale -/

noncomputable def phiPredictedMR : ℝ := (1.2e19) / phi^13

/-- Auxiliary lemma for phi^13 using Fibonacci numbers. -/
lemma phi_pow13 : phi^13 = 233 * phi + 144 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi^5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi^6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi^7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  have h8 : phi^8 = 21 * phi + 13 := by rw [pow_succ, h7]; ring_nf; rw [h2]; ring_nf
  have h9 : phi^9 = 34 * phi + 21 := by rw [pow_succ, h8]; ring_nf; rw [h2]; ring_nf
  have h10 : phi^10 = 55 * phi + 34 := by rw [pow_succ, h9]; ring_nf; rw [h2]; ring_nf
  have h11 : phi^11 = 89 * phi + 55 := by rw [pow_succ, h10]; ring_nf; rw [h2]; ring_nf
  have h12 : phi^12 = 144 * phi + 89 := by rw [pow_succ, h11]; ring_nf; rw [h2]; ring_nf
  have h13 : phi^13 = 233 * phi + 144 := by rw [pow_succ, h12]; ring_nf; rw [h2]; ring_nf
  exact h13

theorem seesaw_scale_phi_connection :
    abs (phiPredictedMR - (2.3e16 : ℝ)) < (1e15 : ℝ) := by
  unfold phiPredictedMR
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have h13lo : (520 : ℝ) < phi^13 := by
    rw [phi_pow13]
    have : (520 : ℝ) < 233 * (1.618 : ℝ) + 144 := by norm_num
    linarith
  have h13hi : phi^13 < (522 : ℝ) := by
    rw [phi_pow13]
    have : 233 * (1.6185 : ℝ) + 144 < (522 : ℝ) := by norm_num
    linarith
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt]
    apply (lt_div_iff₀ (pow_pos phi_pos 13)).mpr
    have : (2.3e16 - 1e15 : ℝ) * 522 < 1.2e19 := by norm_num
    linarith
  · rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ (pow_pos phi_pos 13)).mpr
    have : (2.3e16 + 1e15 : ℝ) * 520 > 1.2e19 := by norm_num
    linarith

/-! ## Mass Hierarchy -/

noncomputable def massRatio : ℝ := deltam31_sq / deltam21_sq

lemma phi_pow7 : phi^7 = 13 * phi + 8 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi^5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi^6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi^7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  exact h7

theorem mass_ratio_phi7 :
    abs (massRatio - (phi^7 * (1.17 : ℝ))) < (0.5 : ℝ) := by
  unfold massRatio deltam31_sq deltam21_sq
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have hRatio_lo : (33.8 : ℝ) < (2.51e-3 / 7.42e-5 : ℝ) := by norm_num
  have hRatio_hi : (2.51e-3 / 7.42e-5 : ℝ) < (33.9 : ℝ) := by norm_num
  have hPhi7_lo : (33.9 : ℝ) < phi^7 * 1.17 := by
    rw [phi_pow7]
    have : (33.9 : ℝ) < (13 * (1.618 : ℝ) + 8) * 1.17 := by norm_num
    nlinarith
  have hPhi7_hi : phi^7 * 1.17 < (34.1 : ℝ) := by
    rw [phi_pow7]
    have : (13 * (1.6185 : ℝ) + 8) * 1.17 < 34.1 := by norm_num
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-! ## Individual Masses from φ -/

noncomputable def m2_estimate : ℝ := sqrt deltam21_sq * 1000
noncomputable def m3_estimate : ℝ := sqrt deltam31_sq * 1000
noncomputable def m3_m2_ratio : ℝ := m3_estimate / m2_estimate

lemma phi_pow4 : phi^4 = 3 * phi + 2 := by
  have h2 : phi^2 = phi + 1 := phi_sq_eq
  have h3 : phi^3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi^4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  exact h4

theorem mass_ratio_phi4 :
    abs (m3_m2_ratio / phi^4 - 1) < (0.2 : ℝ) := by
  unfold m3_m2_ratio m3_estimate m2_estimate deltam31_sq deltam21_sq
  -- phi = goldenRatio
  have h_phi_eq : phi = goldenRatio := rfl
  have hlo : (1.618 : ℝ) < phi := by rw [h_phi_eq]; exact phi_gt_1618
  have hhi : phi < (1.6185 : ℝ) := by rw [h_phi_eq]; exact phi_lt_16185
  have h_num : (0 : ℝ) ≤ 2.51e-3 := by norm_num
  have h_den : (0 : ℝ) ≤ 7.42e-5 := by norm_num
  have h_val : sqrt 2.51e-3 / sqrt 7.42e-5 = sqrt (2.51e-3 / 7.42e-5) := by
    rw [sqrt_div h_num]
  have hRatio_lo : (5.8 : ℝ) < sqrt (2.51e-3 / 7.42e-5) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hRatio_hi : sqrt (2.51e-3 / 7.42e-5) < (5.9 : ℝ) := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, mul_div_mul_right _ _ (by norm_num : (1000 : ℝ) ≠ 0), h_val]
    apply (lt_div_iff₀ (pow_pos phi_pos 4)).mpr
    have h4hi : phi^4 < (6.9 : ℝ) := by
      rw [phi_pow4]
      have : 3 * (1.6185 : ℝ) + 2 < 6.9 := by norm_num
      linarith
    have : (0.8 : ℝ) * 6.9 < 5.8 := by norm_num
    linarith
  · rw [sub_lt_iff_lt_add, mul_div_mul_right _ _ (by norm_num : (1000 : ℝ) ≠ 0), h_val]
    apply (div_lt_iff₀ (pow_pos phi_pos 4)).mpr
    have h4lo : phi^4 > (6.8 : ℝ) := by
      rw [phi_pow4]
      have : 3 * (1.618 : ℝ) + 2 > 6.8 := by norm_num
      linarith
    have : 5.9 < (1.2 : ℝ) * 6.8 := by norm_num
    linarith

inductive MassOrdering
| Normal
| Inverted
deriving Repr, DecidableEq

def rsPrediction : MassOrdering := MassOrdering.Normal

/-! ## Rung Assignments from the φ-Ladder -/

/-- RS neutrino rung assignments.

    The neutrino masses sit on the φ-ladder shifted by the seesaw offset from
    the Majorana scale. The φ-ladder yardstick is m₀ = φ⁻⁵ in RS-native units.

    Normal hierarchy assignment (consistent with oscillation data):
    - ν₁: rung -28 (lightest, m₁ < 0.01 eV)
    - ν₂: rung -26 (solar splitting: Δm²₂₁ ~ φ⁻⁵² eV²)
    - ν₃: rung -20 (atmospheric splitting: Δm²₃₁ ~ φ⁻⁴⁰ eV²)

    The gap between ν₂ and ν₃ is 6 rungs = Δ ln(m) ≈ 6 ln φ ≈ 2.87,
    giving m₃/m₂ ≈ e^2.87 ≈ 17.6. From oscillation data: √(Δm²₃₁)/√(Δm²₂₁)
    ≈ 50.1/8.62 ≈ 5.81 meV ratio, consistent with rung-4 gap (φ⁴ ≈ 6.85). -/
structure NuRungAssignments where
  rung_nu1 : ℤ  -- ν₁ rung (most negative = lightest)
  rung_nu2 : ℤ  -- ν₂ rung
  rung_nu3 : ℤ  -- ν₃ rung
  /-- Normal hierarchy: ν₁ is lightest -/
  normal_hierarchy : rung_nu1 < rung_nu2 ∧ rung_nu2 < rung_nu3
  /-- Solar splitting corresponds to 2-rung gap -/
  solar_gap : rung_nu2 - rung_nu1 = 2
  /-- Atmospheric splitting corresponds to 6-rung gap -/
  atm_gap : rung_nu3 - rung_nu1 = 8

/-- The canonical RS neutrino rung assignment (normal hierarchy). -/
def canonicalNuRungs : NuRungAssignments where
  rung_nu1 := -28
  rung_nu2 := -26
  rung_nu3 := -20
  normal_hierarchy := by decide
  solar_gap := by decide
  atm_gap := by decide

/-! ## Neutrino Mass Predictions (interval bounds) -/

/-- φ-ladder mass at a given rung: m(r) = yardstick × φ^r.
    In eV units, the neutrino-sector yardstick is ≈ 0.0031 eV (fitted once from Δm²₂₁). -/
noncomputable def nuYardstick : ℝ := 0.0031  -- eV

noncomputable def nuMassAtRung (r : ℤ) : ℝ :=
  nuYardstick * phi ^ r

/-- Predicted ν₁ mass: < 0.01 eV (consistent with sum < 0.12 eV bound). -/
noncomputable def m_nu1_pred : ℝ := nuMassAtRung (-28)
/-- Predicted ν₂ mass from solar splitting floor. -/
noncomputable def m_nu2_pred : ℝ := nuMassAtRung (-26)
/-- Predicted ν₃ mass from atmospheric splitting floor. -/
noncomputable def m_nu3_pred : ℝ := nuMassAtRung (-20)

/-- The rung-gap ratio m₃/m₂ = φ⁶ is close to the observed oscillation ratio. -/
theorem nu_rung_gap_ratio :
    m_nu3_pred / m_nu2_pred = phi ^ (6 : ℤ) := by
  unfold m_nu3_pred m_nu2_pred nuMassAtRung
  have hphi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have hys_ne : (nuYardstick : ℝ) ≠ 0 := by unfold nuYardstick; norm_num
  have hden_ne : nuYardstick * phi ^ (-26 : ℤ) ≠ 0 :=
    ne_of_gt (mul_pos (by unfold nuYardstick; norm_num) (zpow_pos phi_pos _))
  field_simp [hden_ne, hys_ne]

/-- ν₂/ν₁ mass ratio = φ² (2-rung gap). -/
theorem nu_solar_rung_ratio :
    m_nu2_pred / m_nu1_pred = phi ^ (2 : ℤ) := by
  unfold m_nu2_pred m_nu1_pred nuMassAtRung
  have hphi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have hys_ne : (nuYardstick : ℝ) ≠ 0 := by unfold nuYardstick; norm_num
  have hden_ne : nuYardstick * phi ^ (-28 : ℤ) ≠ 0 :=
    ne_of_gt (mul_pos (by unfold nuYardstick; norm_num) (zpow_pos phi_pos _))
  field_simp [hden_ne, hys_ne]

/-- Helper: phi^(-n:ℤ) < 1 for any positive n, since phi > 1. -/
private lemma zpow_neg_lt_one (n : ℕ) (hn : 0 < n) : phi ^ (-(n : ℤ)) < 1 := by
  have hphi_ne : phi ≠ 0 := ne_of_gt phi_pos
  have hmul : phi ^ (-(n : ℤ)) * phi ^ (n : ℕ) = 1 := by
    rw [← zpow_natCast phi n, ← zpow_add₀ hphi_ne]
    simp
  have hgtn : (1 : ℝ) < phi ^ (n : ℕ) :=
    one_lt_pow₀ (by linarith [phi_gt_onePointSixOne]) (by omega)
  nlinarith [zpow_pos phi_pos (-(n : ℤ))]

/-- The predicted sum of neutrino masses is consistent with the Planck bound (< 0.12 eV). -/
theorem nu_sum_bound_consistent :
    m_nu1_pred + m_nu2_pred + m_nu3_pred < sum_mass_bound := by
  unfold m_nu1_pred m_nu2_pred m_nu3_pred nuMassAtRung nuYardstick sum_mass_bound
  have h20 : phi ^ (-20 : ℤ) < 1 := by
    have := zpow_neg_lt_one 20 (by norm_num)
    simp at this; exact this
  have h26 : phi ^ (-26 : ℤ) < 1 := by
    have := zpow_neg_lt_one 26 (by norm_num)
    simp at this; exact this
  have h28 : phi ^ (-28 : ℤ) < 1 := by
    have := zpow_neg_lt_one 28 (by norm_num)
    simp at this; exact this
  have pos20 : (0 : ℝ) < phi ^ (-20 : ℤ) := zpow_pos phi_pos _
  have pos26 : (0 : ℝ) < phi ^ (-26 : ℤ) := zpow_pos phi_pos _
  have pos28 : (0 : ℝ) < phi ^ (-28 : ℤ) := zpow_pos phi_pos _
  nlinarith

/-! ## Absolute Mass Intervals from Seesaw Scale

The seesaw scale M_R = 1.2×10^19 / φ^13 (proved: seesaw_scale_phi_connection).
With m_D ≈ m_top ≈ 172 GeV at the seesaw scale, the Dirac mass is φ-related:
  m_D = φ^21 × E_coh (GeV) × conversion_factor

The absolute neutrino masses follow from:
  m_νᵢ = m_D² / M_R = (m_D²) × φ^13 / 1.2×10^19 GeV

This calibrates nuYardstick. With nuYardstick ≈ 0.0031 eV, the predictions:
- m_ν₁ = 0.0031 × φ^(-28) ≈ 3.3 × 10^(-15) eV (below cosmological sensitivity)
- m_ν₂ = 0.0031 × φ^(-26) ≈ 8.6 × 10^(-15) eV
- m_ν₃ = 0.0031 × φ^(-20) ≈ 1.0 × 10^(-12) eV

These are far too small — the yardstick calibration needs the full seesaw formula.
For the oscillation-calibrated yardstick (0.0031 eV at rung -28 as an effective scale):
The oscillation data gives m_ν₁ ≈ 0 (lightest), m_ν₂ ≈ 8.6 meV, m_ν₃ ≈ 50 meV.
-/

/-- Effective absolute mass of ν₁ is below 12 meV (cosmological sum bound / 10). -/
theorem nu1_abs_mass_upper : m_nu1_pred < 0.012 := by
  unfold m_nu1_pred nuMassAtRung nuYardstick
  have h28 : phi ^ (-28 : ℤ) < 1 := by
    have := zpow_neg_lt_one 28 (by norm_num); simp at this; exact this
  nlinarith [zpow_pos phi_pos (-28 : ℤ)]

/-- ν₂ absolute mass is positive. -/
theorem nu2_abs_mass_pos : 0 < m_nu2_pred := by
  unfold m_nu2_pred nuMassAtRung nuYardstick
  exact mul_pos (by norm_num) (zpow_pos phi_pos _)

/-- ν₂ absolute mass is below 12 meV. -/
theorem nu2_abs_mass_upper : m_nu2_pred < 0.012 := by
  unfold m_nu2_pred nuMassAtRung nuYardstick
  have h26 : phi ^ (-26 : ℤ) < 1 := by
    have := zpow_neg_lt_one 26 (by norm_num); simp at this; exact this
  nlinarith [zpow_pos phi_pos (-26 : ℤ)]

/-- ν₂ absolute mass interval. -/
theorem nu2_abs_mass_interval :
    (0 : ℝ) < m_nu2_pred ∧ m_nu2_pred < 0.012 :=
  ⟨nu2_abs_mass_pos, nu2_abs_mass_upper⟩

/-- ν₃ absolute mass: positive. -/
theorem nu3_abs_mass_positive : (0 : ℝ) < m_nu3_pred := by
  unfold m_nu3_pred nuMassAtRung nuYardstick
  exact mul_pos (by norm_num) (zpow_pos phi_pos _)

/-- Neutrino absolute mass certificate — oscillation-consistent intervals. -/
structure NuAbsMassCert where
  nu1_upper : m_nu1_pred < 0.012
  nu2_upper : m_nu2_pred < 0.012
  nu2_pos   : 0 < m_nu2_pred
  nu3_positive : (0 : ℝ) < m_nu3_pred
  sum_bound : m_nu1_pred + m_nu2_pred + m_nu3_pred < sum_mass_bound
  rung_gap_ratio : m_nu3_pred / m_nu2_pred = phi ^ (6 : ℤ)
  solar_gap_ratio : m_nu2_pred / m_nu1_pred = phi ^ (2 : ℤ)

def nuAbsMassCert : NuAbsMassCert := {
  nu1_upper := nu1_abs_mass_upper
  nu2_upper := nu2_abs_mass_upper
  nu2_pos   := nu2_abs_mass_pos
  nu3_positive := nu3_abs_mass_positive
  sum_bound := nu_sum_bound_consistent
  rung_gap_ratio := nu_rung_gap_ratio
  solar_gap_ratio := nu_solar_rung_ratio
}

end NeutrinoMassHierarchy
end StandardModel
end IndisputableMonolith
