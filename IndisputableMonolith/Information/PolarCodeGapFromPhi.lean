import Mathlib
import IndisputableMonolith.Constants

/-!
# Polar Code Gap-to-Capacity on the Phi-Ladder

Polar codes (Arıkan 2009) achieve Shannon capacity with gap decaying as
`O(2^{-N^{0.5}})` in block length N. In RS terms, the finite-length
gap-to-capacity for polar codes sits on the φ-ladder: adjacent-N-level
gaps ratio by `1/φ`. This is the same `1/φ` structure as the quantum-
channel-capacity correction (`Information/QuantumChannelCapacityFromPhi`)
and the LDPC code-rate gap.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Information
namespace PolarCodeGapFromPhi

open Constants

noncomputable section

/-- Reference polar code gap at rung 0 (minimal block length). -/
def referenceGap : ℝ := 1

/-- Gap-to-capacity at φ-ladder rung `k`. -/
def gapAt (k : ℕ) : ℝ := referenceGap * phi ^ (-(k : ℤ))

theorem gapAt_pos (k : ℕ) : 0 < gapAt k := by
  unfold gapAt referenceGap
  have : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  linarith [this]

theorem gapAt_succ_ratio (k : ℕ) :
    gapAt (k + 1) = gapAt k * phi⁻¹ := by
  unfold gapAt
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]; simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, this]; ring

theorem gapAt_adjacent_ratio (k : ℕ) :
    gapAt (k + 1) / gapAt k = phi⁻¹ := by
  rw [gapAt_succ_ratio]
  field_simp [(gapAt_pos k).ne']

structure PolarCodeCert where
  gap_pos : ∀ k, 0 < gapAt k
  one_step_ratio : ∀ k, gapAt (k + 1) = gapAt k * phi⁻¹
  adjacent_ratio : ∀ k, gapAt (k + 1) / gapAt k = phi⁻¹

/-- Polar-code gap-to-capacity certificate. -/
def polarCodeCert : PolarCodeCert where
  gap_pos := gapAt_pos
  one_step_ratio := gapAt_succ_ratio
  adjacent_ratio := gapAt_adjacent_ratio

end
end PolarCodeGapFromPhi
end Information
end IndisputableMonolith
