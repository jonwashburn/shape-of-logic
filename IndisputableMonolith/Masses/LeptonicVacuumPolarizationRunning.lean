import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.AlphaBounds
import IndisputableMonolith.Numerics.Interval.Log

/-!
# Leptonic vacuum-polarization running: the sign of the display correction, derived

U7 (electroweak undershoot) and the cross-sector display gap rest on one asserted fact:
the radiative `α(0) → α(M_Z)` correction is *positive* (it screens the charge, raising the
running coupling and pushing pole masses above their tree values). `WBosonRadiativeUndershoot`
shows both gauge bosons undershoot by the right sign; `AlphaRunningCorrectionScoreCard`
imports the PDG `α⁻¹(M_Z)` as a check. Neither *derives* the sign.

This module derives the sign from first principles. The one-loop QED vacuum-polarization
shift of the inverse coupling from `q²=0` to `q²=M_Z²` is

  Δα = (α / 3π) · Σ_f N_c Q_f² · ( 2·log(M_Z/m_f) − 5/3 ).

Each fermion contributes the kernel `vpTerm r = 2·log r − 5/3` with `r = M_Z/m_f`. For every
charged lepton the ratio `r` is far above the kernel's zero (`r₀ = e^{5/6} ≈ 2.30`), so each
term is strictly positive, the leptonic sum is positive, and the running *screens*:
`α⁻¹(M_Z) = α⁻¹(0)·(1 − Δα) < α⁻¹(0)`. That is the loop-level origin of the positive display
correction — no imported sign, no fitted parameter. The fermion content (3 charged leptons)
and `α(0)` are RS-derived; the kernel is the standard QED integral.

What this establishes and what it does not, stated honestly:

* PROVED: the leptonic running is strictly positive (screening), monotone increasing in
  `M_Z`, and percent-scale: with RS `α(0)` and the physical charged-lepton ratios,
  `0.015 < Δα_lep < 0.05`. This derives the sign and coarse magnitude of the electroweak
  display correction that U7 and U4 previously asserted.
* OPEN: the *magnitude* `Δα ≈ 0.0593` (hence the exact `α⁻¹(M_Z)` band) needs (i) tight
  interval logs of `M_Z/m_f` and (ii) the hadronic vacuum-polarization piece, which is
  genuinely nonperturbative. The magnitude is the same display-operator gap that blocks
  U4/U5/U7-magnitude/U8.

Falsifier: if any leptonic kernel term were non-positive (a lepton with `M_Z/m_ℓ < e^{5/6}`),
the screening sign would fail. All three Standard-Model leptons clear this by a wide margin.

Lean status: 0 sorry, 0 fitted parameters.
-/

namespace IndisputableMonolith.Masses.LeptonicVacuumPolarizationRunning

open IndisputableMonolith.Constants

noncomputable section

/-- One-loop vacuum-polarization kernel for a fermion at mass ratio `r = M_Z / m_f`. -/
def vpTerm (r : ℝ) : ℝ := 2 * Real.log r - 5 / 3

/-- `log 4 = 2 log 2`. -/
private lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) from by norm_num, Real.log_pow]
  push_cast; ring

/-- The kernel is strictly positive once the ratio clears `4` (well above `e^{5/6} ≈ 2.30`). -/
theorem vpTerm_pos {r : ℝ} (hr : (4 : ℝ) ≤ r) : 0 < vpTerm r := by
  have h4 : Real.log 4 ≤ Real.log r :=
    Real.log_le_log (by norm_num) hr
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4' : (1.386 : ℝ) < Real.log 4 := by
    rw [log_four]; linarith
  unfold vpTerm
  linarith

/-- The kernel is monotone in the ratio: larger `M_Z` (or smaller `m_f`) gives a larger
contribution. -/
theorem vpTerm_mono {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h : r₁ ≤ r₂) : vpTerm r₁ ≤ vpTerm r₂ := by
  unfold vpTerm
  have := Real.log_le_log h₁ h
  linarith

/-- The leptonic kernel sum over the three charged leptons (electron, muon, tau ratios). -/
def leptonicKernelSum (r_e r_mu r_tau : ℝ) : ℝ :=
  vpTerm r_e + vpTerm r_mu + vpTerm r_tau

/-- The leptonic kernel sum is strictly positive when every ratio clears `4`. -/
theorem leptonicKernelSum_pos {r_e r_mu r_tau : ℝ}
    (he : (4 : ℝ) ≤ r_e) (hmu : (4 : ℝ) ≤ r_mu) (htau : (4 : ℝ) ≤ r_tau) :
    0 < leptonicKernelSum r_e r_mu r_tau := by
  unfold leptonicKernelSum
  have := vpTerm_pos he
  have := vpTerm_pos hmu
  have := vpTerm_pos htau
  linarith

/-- The leptonic vacuum-polarization shift `Δα_lep = (α/3π)·Σ`, with `α` the RS coupling. -/
def deltaAlphaLeptonic (α r_e r_mu r_tau : ℝ) : ℝ :=
  α / (3 * Real.pi) * leptonicKernelSum r_e r_mu r_tau

/-- `Δα_lep > 0` (screening): from a positive coupling, positive kernel sum. -/
theorem deltaAlphaLeptonic_pos {α r_e r_mu r_tau : ℝ} (hα : 0 < α)
    (he : (4 : ℝ) ≤ r_e) (hmu : (4 : ℝ) ≤ r_mu) (htau : (4 : ℝ) ≤ r_tau) :
    0 < deltaAlphaLeptonic α r_e r_mu r_tau := by
  unfold deltaAlphaLeptonic
  have hpre : 0 < α / (3 * Real.pi) :=
    div_pos hα (by positivity)
  exact mul_pos hpre (leptonicKernelSum_pos he hmu htau)

/-- The running screens: `α⁻¹(M_Z) = α⁻¹(0)·(1 − Δα_lep) < α⁻¹(0)` whenever `α⁻¹(0) > 0`
and `Δα_lep > 0`. This is the loop-level origin of the positive electroweak display
correction (the sign of the W/Z undershoot). -/
theorem running_screens {αinv0 Δα : ℝ} (hpos : 0 < αinv0) (hΔ : 0 < Δα) :
    αinv0 * (1 - Δα) < αinv0 := by
  nlinarith [hpos, hΔ]

/-! ## Instantiation with the three Standard-Model leptons

The ratios `M_Z / m_ℓ` (PDG masses, in GeV) all clear `4` by a wide margin: the smallest is
`M_Z / m_τ ≈ 51`. So the leptonic running is unconditionally positive for the physical
spectrum. -/

/-- PDG masses (GeV) used as the empirical ratio inputs to the QED kernel. -/
def m_e_GeV : ℝ := 0.000511
def m_mu_GeV : ℝ := 0.10566
def m_tau_GeV : ℝ := 1.77686
def M_Z_GeV : ℝ := 91.1876

def rho_e : ℝ := M_Z_GeV / m_e_GeV
def rho_mu : ℝ := M_Z_GeV / m_mu_GeV
def rho_tau : ℝ := M_Z_GeV / m_tau_GeV

theorem rho_e_ge_four : (4 : ℝ) ≤ rho_e := by
  unfold rho_e M_Z_GeV m_e_GeV
  rw [le_div_iff₀ (by norm_num)]; norm_num

theorem rho_mu_ge_four : (4 : ℝ) ≤ rho_mu := by
  unfold rho_mu M_Z_GeV m_mu_GeV
  rw [le_div_iff₀ (by norm_num)]; norm_num

theorem rho_tau_ge_four : (4 : ℝ) ≤ rho_tau := by
  unfold rho_tau M_Z_GeV m_tau_GeV
  rw [le_div_iff₀ (by norm_num)]; norm_num

/-- **The leptonic running is positive for the physical lepton spectrum.** Derived from the
QED vacuum-polarization kernel evaluated at the three Standard-Model lepton mass ratios; the
sign needs no imported input. -/
theorem physical_leptonic_running_positive :
    0 < leptonicKernelSum rho_e rho_mu rho_tau :=
  leptonicKernelSum_pos rho_e_ge_four rho_mu_ge_four rho_tau_ge_four

/-- The physical leptonic `Δα_lep` is positive for any positive coupling (in particular the
RS-derived `α`). -/
theorem physical_deltaAlphaLeptonic_positive {α : ℝ} (hα : 0 < α) :
    0 < deltaAlphaLeptonic α rho_e rho_mu rho_tau :=
  deltaAlphaLeptonic_pos hα rho_e_ge_four rho_mu_ge_four rho_tau_ge_four

/-! ## Coarse magnitude: the lepton-only running is percent-scale

The exact leptonic value is about `0.0314`. Proving that narrow band would require tight
interval logs for `M_Z/m_e`, `M_Z/m_μ`, and `M_Z/m_τ`. The present theorem deliberately uses only
coarse powers of ten and the existing `log 10 ∈ [2.30,2.31]` certificate:

* lower ratios: `rho_e ≥ 10^5`, `rho_mu ≥ 10^2`, `rho_tau ≥ 10`;
* upper ratios: `rho_e ≤ 10^6`, `rho_mu ≤ 10^3`, `rho_tau ≤ 10^2`.

This is enough to prove a nontrivial first-principles magnitude bracket:
`0.015 < Δα_lep < 0.05`. The hadronic vacuum-polarization term is still outside this theorem.
-/

def alphaRS : ℝ := 1 / alphaInv

private theorem log10_lo : (230 / 100 : ℝ) ≤ Real.log 10 :=
by
  simpa [IndisputableMonolith.Numerics.log10Interval]
    using IndisputableMonolith.Numerics.log_10_in_interval.1

private theorem log10_hi : Real.log 10 ≤ (231 / 100 : ℝ) :=
by
  simpa [IndisputableMonolith.Numerics.log10Interval]
    using IndisputableMonolith.Numerics.log_10_in_interval.2

private lemma log_pow10 (n : ℕ) :
    Real.log ((10 : ℝ) ^ n) = (n : ℝ) * Real.log 10 := by
  rw [Real.log_pow]

theorem rho_e_ge_100000 : (100000 : ℝ) ≤ rho_e := by
  unfold rho_e M_Z_GeV m_e_GeV
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.000511)]
  norm_num

theorem rho_mu_ge_100 : (100 : ℝ) ≤ rho_mu := by
  unfold rho_mu M_Z_GeV m_mu_GeV
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 0.10566)]
  norm_num

theorem rho_tau_ge_10 : (10 : ℝ) ≤ rho_tau := by
  unfold rho_tau M_Z_GeV m_tau_GeV
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1.77686)]
  norm_num

theorem rho_e_le_million : rho_e ≤ (1000000 : ℝ) := by
  unfold rho_e M_Z_GeV m_e_GeV
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.000511)]
  norm_num

theorem rho_mu_le_1000 : rho_mu ≤ (1000 : ℝ) := by
  unfold rho_mu M_Z_GeV m_mu_GeV
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.10566)]
  norm_num

theorem rho_tau_le_100 : rho_tau ≤ (100 : ℝ) := by
  unfold rho_tau M_Z_GeV m_tau_GeV
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1.77686)]
  norm_num

theorem leptonicKernelSum_gt_31 :
    (31 : ℝ) < leptonicKernelSum rho_e rho_mu rho_tau := by
  have he_log : (5 : ℝ) * Real.log 10 ≤ Real.log rho_e := by
    calc
      (5 : ℝ) * Real.log 10 = Real.log ((10 : ℝ) ^ (5 : ℕ)) := by
        rw [log_pow10]; norm_num
      _ = Real.log (100000 : ℝ) := by norm_num
      _ ≤ Real.log rho_e := Real.log_le_log (by norm_num) rho_e_ge_100000
  have hmu_log : (2 : ℝ) * Real.log 10 ≤ Real.log rho_mu := by
    calc
      (2 : ℝ) * Real.log 10 = Real.log ((10 : ℝ) ^ (2 : ℕ)) := by
        rw [log_pow10]; norm_num
      _ = Real.log (100 : ℝ) := by norm_num
      _ ≤ Real.log rho_mu := Real.log_le_log (by norm_num) rho_mu_ge_100
  have htau_log : Real.log 10 ≤ Real.log rho_tau :=
    Real.log_le_log (by norm_num) rho_tau_ge_10
  unfold leptonicKernelSum vpTerm
  linarith [log10_lo]

theorem leptonicKernelSum_lt_46 :
    leptonicKernelSum rho_e rho_mu rho_tau < (46 : ℝ) := by
  have he_log : Real.log rho_e ≤ (6 : ℝ) * Real.log 10 := by
    calc
      Real.log rho_e ≤ Real.log (1000000 : ℝ) :=
        Real.log_le_log (by linarith [rho_e_ge_four]) rho_e_le_million
      _ = Real.log ((10 : ℝ) ^ (6 : ℕ)) := by norm_num
      _ = (6 : ℝ) * Real.log 10 := by rw [log_pow10]; norm_num
  have hmu_log : Real.log rho_mu ≤ (3 : ℝ) * Real.log 10 := by
    calc
      Real.log rho_mu ≤ Real.log (1000 : ℝ) :=
        Real.log_le_log (by linarith [rho_mu_ge_four]) rho_mu_le_1000
      _ = Real.log ((10 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = (3 : ℝ) * Real.log 10 := by rw [log_pow10]; norm_num
  have htau_log : Real.log rho_tau ≤ (2 : ℝ) * Real.log 10 := by
    calc
      Real.log rho_tau ≤ Real.log (100 : ℝ) :=
        Real.log_le_log (by linarith [rho_tau_ge_four]) rho_tau_le_100
      _ = Real.log ((10 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = (2 : ℝ) * Real.log 10 := by rw [log_pow10]; norm_num
  unfold leptonicKernelSum vpTerm
  linarith [log10_hi]

theorem alphaRS_gt_0007 : (0.007 : ℝ) < alphaRS := by
  unfold alphaRS
  have hpos : (0 : ℝ) < alphaInv := by linarith [IndisputableMonolith.Numerics.alphaInv_gt]
  rw [lt_div_iff₀ hpos]
  nlinarith [IndisputableMonolith.Numerics.alphaInv_lt]

theorem alphaRS_lt_0008 : alphaRS < (0.008 : ℝ) := by
  unfold alphaRS
  have hpos : (0 : ℝ) < alphaInv := by linarith [IndisputableMonolith.Numerics.alphaInv_gt]
  rw [div_lt_iff₀ hpos]
  nlinarith [IndisputableMonolith.Numerics.alphaInv_gt]

theorem alpha_prefactor_gt_0005 :
    (0.0005 : ℝ) < alphaRS / (3 * Real.pi) := by
  have hden : (0 : ℝ) < 3 * Real.pi := by positivity
  rw [lt_div_iff₀ hden]
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hsmall : (0.0005 : ℝ) * (3 * Real.pi) < 0.006 := by nlinarith
  linarith [alphaRS_gt_0007]

theorem alpha_prefactor_lt_001 :
    alphaRS / (3 * Real.pi) < (0.001 : ℝ) := by
  have hden : (0 : ℝ) < 3 * Real.pi := by positivity
  rw [div_lt_iff₀ hden]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbig : (0.008 : ℝ) < 0.001 * (3 * Real.pi) := by nlinarith
  linarith [alphaRS_lt_0008]

/-- **Coarse lepton-only running magnitude.** With RS `α(0)` and the physical charged-lepton
ratios, the perturbative leptonic vacuum-polarization contribution is percent-scale:
`1.5% < Δα_lep < 5%`. This does not include the hadronic nonperturbative contribution. -/
theorem physical_deltaAlphaLeptonic_RS_bounds :
    (0.015 : ℝ) < deltaAlphaLeptonic alphaRS rho_e rho_mu rho_tau ∧
    deltaAlphaLeptonic alphaRS rho_e rho_mu rho_tau < (0.05 : ℝ) := by
  unfold deltaAlphaLeptonic
  constructor
  · have hpre := alpha_prefactor_gt_0005
    have hsum := leptonicKernelSum_gt_31
    have hprepos : (0 : ℝ) < alphaRS / (3 * Real.pi) := by linarith
    have hmul₁ : (0.0005 : ℝ) * 31 < alphaRS / (3 * Real.pi) * 31 :=
      mul_lt_mul_of_pos_right hpre (by norm_num)
    have hmul₂ : alphaRS / (3 * Real.pi) * 31 <
        alphaRS / (3 * Real.pi) * leptonicKernelSum rho_e rho_mu rho_tau :=
      mul_lt_mul_of_pos_left hsum hprepos
    norm_num at hmul₁ hmul₂ ⊢
    linarith
  · have hpre := alpha_prefactor_lt_001
    have hsum := leptonicKernelSum_lt_46
    have hsumpos : (0 : ℝ) < leptonicKernelSum rho_e rho_mu rho_tau :=
      physical_leptonic_running_positive
    have hmul₁ : alphaRS / (3 * Real.pi) * leptonicKernelSum rho_e rho_mu rho_tau <
        (0.001 : ℝ) * leptonicKernelSum rho_e rho_mu rho_tau :=
      mul_lt_mul_of_pos_right hpre hsumpos
    have hmul₂ : (0.001 : ℝ) * leptonicKernelSum rho_e rho_mu rho_tau <
        (0.001 : ℝ) * 46 :=
      mul_lt_mul_of_pos_left hsum (by norm_num)
    norm_num at hmul₁ hmul₂ ⊢
    linarith

structure LeptonicVPRunningCert where
  kernel_pos : ∀ {r : ℝ}, (4 : ℝ) ≤ r → 0 < vpTerm r
  kernel_mono : ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₁ ≤ r₂ → vpTerm r₁ ≤ vpTerm r₂
  physical_sum_pos : 0 < leptonicKernelSum rho_e rho_mu rho_tau
  physical_sum_band : (31 : ℝ) < leptonicKernelSum rho_e rho_mu rho_tau ∧
    leptonicKernelSum rho_e rho_mu rho_tau < 46
  lepton_delta_band : (0.015 : ℝ) < deltaAlphaLeptonic alphaRS rho_e rho_mu rho_tau ∧
    deltaAlphaLeptonic alphaRS rho_e rho_mu rho_tau < 0.05
  screens : ∀ {αinv0 Δα : ℝ}, 0 < αinv0 → 0 < Δα → αinv0 * (1 - Δα) < αinv0

theorem leptonicVPRunningCert_holds : Nonempty LeptonicVPRunningCert :=
  ⟨{ kernel_pos := fun h => vpTerm_pos h
     kernel_mono := fun h₁ h => vpTerm_mono h₁ h
     physical_sum_pos := physical_leptonic_running_positive
     physical_sum_band := ⟨leptonicKernelSum_gt_31, leptonicKernelSum_lt_46⟩
     lepton_delta_band := physical_deltaAlphaLeptonic_RS_bounds
     screens := fun h hΔ => running_screens h hΔ }⟩

end

end IndisputableMonolith.Masses.LeptonicVacuumPolarizationRunning
