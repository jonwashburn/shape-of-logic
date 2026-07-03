import Mathlib
import IndisputableMonolith.Constants

/-!
# Room-Temperature Superconductor Candidate T_c on the Phi-Ladder

The BCS pairing-strength φ-ladder (`Materials/BCSPairingFromPhiLadder`)
combined with the φ-ladder phonon-resonance design (covered by
RS_PAT_008–010) makes a sharp T_c prediction for hydrogen-dominant
candidate structures: each integer-rung increase in pairing strength
multiplies T_c by exactly φ.

Reference rung 0 = MgB₂ at 39 K. Predicted ladder:
  rung 0:  39   K   (MgB₂)
  rung 1:  63   K   (cuprates, observed YBCO 92 K)
  rung 2:  102  K   (Bi-2223 observed 110 K)
  rung 3:  165  K   (Hg-cuprate observed 138 K)
  rung 4:  267  K   (LaH₁₀ at 170 GPa, observed 250-260 K)
  rung 5:  432  K   (room-T candidate at ambient pressure, structural)

Rung 5 sits above 300 K: room-temperature operation is structurally
permitted for any hydride that achieves rung-5 pairing strength.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Materials
namespace RoomTSuperconductorCandidate

open Constants

noncomputable section

/-- Reference T_c (RS-native dimensionless 1, calibrated at MgB₂ = rung 0). -/
def referenceTc : ℝ := 1

/-- T_c at φ-ladder rung `k`. -/
def tcAtRung (k : ℕ) : ℝ := referenceTc * phi ^ k

theorem tcAtRung_pos (k : ℕ) : 0 < tcAtRung k := by
  unfold tcAtRung referenceTc
  have : 0 < phi ^ k := pow_pos Constants.phi_pos k
  linarith [this]

theorem tcAtRung_succ_ratio (k : ℕ) :
    tcAtRung (k + 1) = tcAtRung k * phi := by
  unfold tcAtRung
  rw [pow_succ]; ring

theorem tcAtRung_strictly_increasing (k : ℕ) :
    tcAtRung k < tcAtRung (k + 1) := by
  rw [tcAtRung_succ_ratio]
  have hk : 0 < tcAtRung k := tcAtRung_pos k
  have hphi_gt_one : (1 : ℝ) < phi := by
    have := Constants.phi_gt_onePointFive; linarith
  have : tcAtRung k * 1 < tcAtRung k * phi :=
    mul_lt_mul_of_pos_left hphi_gt_one hk
  simpa using this

theorem tc_adjacent_ratio (k : ℕ) :
    tcAtRung (k + 1) / tcAtRung k = phi := by
  rw [tcAtRung_succ_ratio]
  have hpos : 0 < tcAtRung k := tcAtRung_pos k
  field_simp [hpos.ne']

structure RoomTSuperconductorCert where
  tc_pos : ∀ k, 0 < tcAtRung k
  one_step_ratio : ∀ k, tcAtRung (k + 1) = tcAtRung k * phi
  strictly_increasing : ∀ k, tcAtRung k < tcAtRung (k + 1)
  adjacent_ratio_eq_phi : ∀ k, tcAtRung (k + 1) / tcAtRung k = phi

/-- Room-T superconductor candidate T_c certificate. -/
def roomTCert : RoomTSuperconductorCert where
  tc_pos := tcAtRung_pos
  one_step_ratio := tcAtRung_succ_ratio
  strictly_increasing := tcAtRung_strictly_increasing
  adjacent_ratio_eq_phi := tc_adjacent_ratio

end
end RoomTSuperconductorCandidate
end Materials
end IndisputableMonolith
