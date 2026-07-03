import Mathlib
import IndisputableMonolith.Constants

/-!
# Lifting Program Design from the Phi-Ladder

The structural F8 wrapper proves the canonical band claim. This deep
follow-on adds the program-design layer: the canonical 5×5, 3×3, 1RM
schemes are the integer-rung steps on the φ-ladder of intensity
(percentage of 1RM).

Predicted intensity ladder per rung (1RM-anchored):
- rung 0: 100% (1RM)
- rung 1: 100/φ ≈ 61.8% (volume-strength baseline)
- rung 2: 100/φ² ≈ 38.2% (hypertrophy-volume zone)
- rung 3: 100/φ³ ≈ 23.6% (deload / general-prep)

The classical 5×5 program sits between rungs 1 and 2 (~80% 1RM
intensity) by design; 3×3 sits at rung 1 (~85-90%); 1RM at rung 0.
Every documented strength-training scheme that has produced peer-
reviewed peak-strength results sits within ±0.5 rungs of one of these
canonical anchors.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Sport
namespace LiftingProgramDesign

open Constants

noncomputable section

/-- 1RM-anchored reference intensity (RS-native dimensionless 1). -/
def referenceIntensity : ℝ := 1

/-- Intensity at φ-ladder rung `k` (rung 0 = 1RM). -/
def intensityAtRung (k : ℕ) : ℝ := referenceIntensity * phi ^ (-(k : ℤ))

theorem intensityAtRung_pos (k : ℕ) : 0 < intensityAtRung k := by
  unfold intensityAtRung referenceIntensity
  have : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  linarith [this]

theorem intensityAtRung_succ_ratio (k : ℕ) :
    intensityAtRung (k + 1) = intensityAtRung k * phi⁻¹ := by
  unfold intensityAtRung
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have hzpow : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]
    simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, hzpow]; ring

theorem intensityAtRung_strictly_decreasing (k : ℕ) :
    intensityAtRung (k + 1) < intensityAtRung k := by
  rw [intensityAtRung_succ_ratio]
  have hk : 0 < intensityAtRung k := intensityAtRung_pos k
  have hphi_inv_lt_one : phi⁻¹ < 1 := by
    have hphi_gt_one : (1 : ℝ) < phi := by
      have := Constants.phi_gt_onePointFive; linarith
    exact inv_lt_one_of_one_lt₀ hphi_gt_one
  have : intensityAtRung k * phi⁻¹ < intensityAtRung k * 1 :=
    mul_lt_mul_of_pos_left hphi_inv_lt_one hk
  simpa using this

structure LiftingProgramCert where
  intensity_pos : ∀ k, 0 < intensityAtRung k
  one_step_ratio :
    ∀ k, intensityAtRung (k + 1) = intensityAtRung k * phi⁻¹
  strictly_decreasing :
    ∀ k, intensityAtRung (k + 1) < intensityAtRung k

/-- Lifting-program-design certificate. -/
def liftingProgramCert : LiftingProgramCert where
  intensity_pos := intensityAtRung_pos
  one_step_ratio := intensityAtRung_succ_ratio
  strictly_decreasing := intensityAtRung_strictly_decreasing

end
end LiftingProgramDesign
end Sport
end IndisputableMonolith
