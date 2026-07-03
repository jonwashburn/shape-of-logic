import Mathlib
import IndisputableMonolith.Constants

/-!
# Photonic Metamaterial Band Gap on the Phi-Ladder

Photonic metamaterials with golden-ratio lattice geometry (covered by
RS_PAT_018) exhibit a φ-laddered family of band gaps. The structural
prediction: the dimensionless gap-center frequency `ω_n / ω_0` lies on
the φ-ladder, with adjacent-rung ratios equal to exactly φ.

This is the structural prediction underlying the patent. The empirical
observation: 1D Fibonacci photonic crystals exhibit a self-similar
gap-frequency cascade with the golden ratio as the fundamental scaling
constant (Maciá-Barber 2009, Wang et al. 2017).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Materials
namespace MetamaterialBandGapFromPhiLadder

open Constants

noncomputable section

/-- Reference band-gap center frequency (RS-native dimensionless 1). -/
def referenceFreq : ℝ := 1

/-- Band-gap center at φ-ladder rung `k`. -/
def gapFreq (k : ℕ) : ℝ := referenceFreq * phi ^ k

theorem gapFreq_pos (k : ℕ) : 0 < gapFreq k := by
  unfold gapFreq referenceFreq
  have : 0 < phi ^ k := pow_pos Constants.phi_pos k
  linarith [this]

theorem gapFreq_succ_ratio (k : ℕ) :
    gapFreq (k + 1) = gapFreq k * phi := by
  unfold gapFreq
  rw [pow_succ]; ring

theorem gapFreq_strictly_increasing (k : ℕ) :
    gapFreq k < gapFreq (k + 1) := by
  rw [gapFreq_succ_ratio]
  have hk : 0 < gapFreq k := gapFreq_pos k
  have hphi_gt_one : (1 : ℝ) < phi := by
    have := Constants.phi_gt_onePointFive; linarith
  have : gapFreq k * 1 < gapFreq k * phi :=
    mul_lt_mul_of_pos_left hphi_gt_one hk
  simpa using this

theorem gapFreq_adjacent_ratio (k : ℕ) :
    gapFreq (k + 1) / gapFreq k = phi := by
  rw [gapFreq_succ_ratio]
  have hpos : 0 < gapFreq k := gapFreq_pos k
  field_simp [hpos.ne']

structure MetamaterialBandGapCert where
  freq_pos : ∀ k, 0 < gapFreq k
  one_step_ratio : ∀ k, gapFreq (k + 1) = gapFreq k * phi
  strictly_increasing : ∀ k, gapFreq k < gapFreq (k + 1)
  adjacent_ratio_eq_phi : ∀ k, gapFreq (k + 1) / gapFreq k = phi

/-- Metamaterial-band-gap-on-φ-ladder certificate. -/
def metamaterialBandGapCert : MetamaterialBandGapCert where
  freq_pos := gapFreq_pos
  one_step_ratio := gapFreq_succ_ratio
  strictly_increasing := gapFreq_strictly_increasing
  adjacent_ratio_eq_phi := gapFreq_adjacent_ratio

end
end MetamaterialBandGapFromPhiLadder
end Materials
end IndisputableMonolith
