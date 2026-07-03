import Mathlib
import IndisputableMonolith.Constants

/-!
# C24: DFT-8 Harmonic Spectrum — Wave 64 Cross-Domain

Structural claim: the eight DFT modes carry physical content via the
fundamental frequency 5φ Hz (theta band). The full RS frequency comb is

  ν_k = (k · 5φ / 8) Hz   for k = 0, 1, ..., 7

This is the canonical RS sound-therapy and brain-rhythm frequency comb
(RS_PAT_026, RS_PAT_025).

Key properties:
  • 8 modes (k = 0..7), one per Q₃ vertex
  • Carrier frequency 5φ ≈ 8.09 Hz (theta band)
  • All ν_k are non-negative
  • Highest mode ν_7 = 35φ/8 ≈ 7.08 Hz (still theta band)

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.CrossDomain.DFTHarmonicSpectrum

open Constants

/-- The DFT mode index. -/
abbrev DFTMode : Type := Fin 8

theorem dftMode_count : Fintype.card DFTMode = 8 := by decide

/-- The k-th harmonic frequency of the RS comb: ν_k = k · 5φ / 8 Hz. -/
noncomputable def harmonicFrequency (k : DFTMode) : ℝ :=
  (k.val : ℝ) * 5 * phi / 8

/-- Carrier frequency: 5φ ≈ 8.09 Hz (theta band). -/
noncomputable def carrierFreq : ℝ := 5 * phi

theorem carrierFreq_pos : 0 < carrierFreq := by
  unfold carrierFreq
  exact mul_pos (by norm_num) phi_pos

/-- Theta-band lower bound: 5φ > 5 · 1.6 = 8. -/
theorem carrier_gt_8 : carrierFreq > 8 := by
  unfold carrierFreq
  have := phi_gt_onePointSixOne
  linarith

/-- Theta-band upper bound: 5φ < 5 · 1.62 = 8.1. -/
theorem carrier_lt_8point1 : carrierFreq < 8.1 := by
  unfold carrierFreq
  have := phi_lt_onePointSixTwo
  linarith

/-- All harmonics are non-negative. -/
theorem harmonics_nonneg (k : DFTMode) : 0 ≤ harmonicFrequency k := by
  unfold harmonicFrequency
  apply div_nonneg
  · apply mul_nonneg
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · norm_num
    · exact le_of_lt phi_pos
  · norm_num

/-- The k-th harmonic is k · (carrier / 8). -/
theorem harmonics_factored (k : DFTMode) :
    harmonicFrequency k = (k.val : ℝ) * (carrierFreq / 8) := by
  unfold harmonicFrequency carrierFreq
  ring

/-- Mode 0 has frequency 0 (DC). -/
theorem mode_zero : harmonicFrequency ⟨0, by decide⟩ = 0 := by
  unfold harmonicFrequency
  simp

/-- Mode 7 = highest harmonic: 35φ/8. -/
theorem mode_seven : harmonicFrequency ⟨7, by decide⟩ = 35 * phi / 8 := by
  unfold harmonicFrequency
  push_cast; ring

/-- Mode 7 < carrier (since 7/8 < 1). -/
theorem mode_seven_lt_carrier :
    harmonicFrequency ⟨7, by decide⟩ < carrierFreq := by
  rw [mode_seven]
  unfold carrierFreq
  -- 35φ/8 < 5φ iff 35/8 < 5, which is 4.375 < 5
  have hpos := phi_pos
  rw [div_lt_iff₀ (by norm_num : (8 : ℝ) > 0)]
  -- Goal: 35*phi < 5*phi*8 = 40*phi
  linarith [phi_pos]

/-- The highest harmonic is bounded above by 9 Hz (still theta band). -/
theorem mode_seven_lt_9 : harmonicFrequency ⟨7, by decide⟩ < 9 := by
  rw [mode_seven]
  have := phi_lt_onePointSixTwo
  -- 35φ/8 < 35 · 1.62 / 8 = 56.7/8 = 7.0875 < 9
  linarith

/-- Strict monotonicity of the comb. -/
theorem harmonic_strict_mono (j k : DFTMode) (hjk : j.val < k.val) :
    harmonicFrequency j < harmonicFrequency k := by
  unfold harmonicFrequency
  apply div_lt_div_of_pos_right _ (by norm_num : (8 : ℝ) > 0)
  apply mul_lt_mul_of_pos_right _ phi_pos
  · exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hjk) (by norm_num)

structure DFTHarmonicSpectrumCert where
  modes_eight : Fintype.card DFTMode = 8
  carrier_in_theta_band : 8 < carrierFreq ∧ carrierFreq < 8.1
  all_modes_nonneg : ∀ k : DFTMode, 0 ≤ harmonicFrequency k
  mode_zero_dc : harmonicFrequency ⟨0, by decide⟩ = 0
  mode_seven_under_9 : harmonicFrequency ⟨7, by decide⟩ < 9
  comb_monotone : ∀ j k : DFTMode, j.val < k.val →
    harmonicFrequency j < harmonicFrequency k

noncomputable def dftHarmonicSpectrumCert : DFTHarmonicSpectrumCert where
  modes_eight := dftMode_count
  carrier_in_theta_band := ⟨carrier_gt_8, carrier_lt_8point1⟩
  all_modes_nonneg := harmonics_nonneg
  mode_zero_dc := mode_zero
  mode_seven_under_9 := mode_seven_lt_9
  comb_monotone := harmonic_strict_mono

end IndisputableMonolith.CrossDomain.DFTHarmonicSpectrum
