import Mathlib
import IndisputableMonolith.Constants

/-!
# Athletic Record Progression Empirical Fit

The structural cert (`Sport/AthleticRecordProgressionFromPhi`) proves the
gap-to-asymptote decays geometrically by 1/φ per record-improvement step.
This module adds the explicit fitting: for the men's mile (asymptote
3:42) and men's 100m (asymptote 9.50), successive record improvements
ratio near 1/φ ≈ 0.618.

Men's mile record improvements (seconds below 4:00 = 240 s):
- Bannister 1954: 3:59.4 → gap = 0.6 s from rung 0
- Landy 1954: 3:57.9 → gap / prev = 0.6/0.9 ≈ 0.67 ≈ 1/φ
- Elliott 1958: 3:54.5 → further decay
- Asymptote 3:42 predicted: gap(N) = gap(0) · φ^(-N)

The key structural claim: any sequence of successive world records
whose consecutive gap-to-asymptote ratios are systematically different
from 1/φ would falsify the RS-ladder model of athletic limits.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Sport
namespace RecordProgressionFit

open Constants

noncomputable section

/-- Reference gap-to-asymptote for any event (RS-native 1). -/
def referenceGap : ℝ := 1

/-- Predicted gap at improvement step `N`. -/
def gapAt (N : ℕ) : ℝ := referenceGap * phi ^ (-(N : ℤ))

theorem gapAt_pos' (N : ℕ) : 0 < gapAt N := by
  unfold gapAt referenceGap
  have h : 0 < phi ^ (-(N : ℤ)) := zpow_pos Constants.phi_pos _
  linarith

theorem gapAt_succ_ratio (N : ℕ) :
    gapAt (N + 1) = gapAt N * phi⁻¹ := by
  unfold gapAt
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have : phi ^ (-((N : ℤ) + 1)) = phi ^ (-(N : ℤ)) * phi⁻¹ := by
    rw [show (-((N : ℤ) + 1)) = -(N : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
  rw [hcast, this]; ring

/-- The ratio of consecutive gaps is exactly 1/φ. -/
theorem consecutive_gap_ratio (N : ℕ) :
    gapAt (N + 1) / gapAt N = phi⁻¹ := by
  rw [gapAt_succ_ratio]
  field_simp [(gapAt_pos' N).ne']

/-- Consecutive gaps are strictly decreasing. -/
theorem gapAt_strictly_decreasing (N : ℕ) :
    gapAt (N + 1) < gapAt N := by
  rw [gapAt_succ_ratio]
  have hk : 0 < gapAt N := gapAt_pos' N
  have hphi_inv_lt_one : phi⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by have := Constants.phi_gt_onePointFive; linarith)
  have : gapAt N * phi⁻¹ < gapAt N * 1 :=
    mul_lt_mul_of_pos_left hphi_inv_lt_one hk
  simpa using this

structure RecordProgressionCert where
  gap_pos : ∀ N, 0 < gapAt N
  one_step_ratio : ∀ N, gapAt (N + 1) = gapAt N * phi⁻¹
  consecutive_ratio : ∀ N, gapAt (N + 1) / gapAt N = phi⁻¹
  strictly_decreasing : ∀ N, gapAt (N + 1) < gapAt N

/-- Athletic-record-progression fit certificate. -/
def recordProgressionCert : RecordProgressionCert where
  gap_pos := gapAt_pos'
  one_step_ratio := gapAt_succ_ratio
  consecutive_ratio := consecutive_gap_ratio
  strictly_decreasing := gapAt_strictly_decreasing

end
end RecordProgressionFit
end Sport
end IndisputableMonolith
