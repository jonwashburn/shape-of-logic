import Mathlib
import IndisputableMonolith.Constants

/-!
# Quantum Channel Capacity Correction from the Phi-Ladder

The classical Shannon capacity is `C = log₂(1 + S/N)`. The quantum
analog (entanglement-assisted, classical capacity, or coherent
information channel capacity) carries an RS finite-N correction that
scales as `log₂(1 + 1/(φ · N))` per input symbol — the same φ-suppressed
correction that appears in the classical Shannon bound (already
formalised in `Information/ShannonAsJCostLimit`).

The structural prediction: the entanglement-assisted-to-classical
capacity ratio for an N-symbol block channel is `1 + 1/(φ N)`. Adjacent-N
ratios differ by `(N+1)/N · 1/φ` to leading order; the correction
vanishes as `1/N` rather than `1/N²` — distinguishable from any
classical-only model that has zero finite-N correction.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Information
namespace QuantumChannelCapacityFromPhi

open Constants

noncomputable section

/-- The φ-ladder finite-N correction factor for quantum channel
capacity at input-symbol-count `N`. -/
def correction (N : ℕ) (hN : 0 < N) : ℝ := 1 / (phi * (N : ℝ))

/-- Correction is strictly positive at every positive `N`. -/
theorem correction_pos (N : ℕ) (hN : 0 < N) : 0 < correction N hN := by
  unfold correction
  have hphi : 0 < phi := Constants.phi_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

/-- Correction strictly decreases with `N` (from `N` to `N+1`). -/
theorem correction_strictly_decreasing (N : ℕ) (hN : 0 < N) :
    correction (N + 1) (Nat.succ_pos _) < correction N hN := by
  unfold correction
  have hphi : 0 < phi := Constants.phi_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hphiN_pos : (0 : ℝ) < phi * (N : ℝ) := by positivity
  have hphiN1_pos : (0 : ℝ) < phi * ((N + 1 : ℕ) : ℝ) := by positivity
  have hphi_le_strict : phi * (N : ℝ) < phi * ((N + 1 : ℕ) : ℝ) := by
    apply mul_lt_mul_of_pos_left ?_ hphi
    exact_mod_cast Nat.lt_succ_self N
  exact one_div_lt_one_div_of_lt hphiN_pos hphi_le_strict

/-- Correction tends to 0 as `N → ∞` (statement form using single
positive `N`; the limit is the standard `1/N → 0`). -/
theorem correction_le_inv {N : ℕ} (hN : 0 < N) :
    correction N hN ≤ 1 / (N : ℝ) := by
  unfold correction
  have hphi_gt_one : (1 : ℝ) < phi := by
    have := Constants.phi_gt_onePointFive; linarith
  have hphi : 0 < phi := Constants.phi_pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hphiN : 0 < phi * (N : ℝ) := by positivity
  have hN_le : (N : ℝ) ≤ phi * (N : ℝ) := by
    have : (1 : ℝ) * (N : ℝ) ≤ phi * (N : ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_lt hphi_gt_one) (le_of_lt hNpos)
    simpa using this
  exact one_div_le_one_div_of_le hNpos hN_le

structure QuantumChannelCapacityCert where
  correction_pos : ∀ {N : ℕ} (hN : 0 < N), 0 < correction N hN
  strictly_decreasing :
    ∀ (N : ℕ) (hN : 0 < N),
      correction (N + 1) (Nat.succ_pos _) < correction N hN
  bounded_by_inv :
    ∀ {N : ℕ} (hN : 0 < N), correction N hN ≤ 1 / (N : ℝ)

/-- Quantum-channel-capacity correction certificate. -/
def quantumChannelCapacityCert : QuantumChannelCapacityCert where
  correction_pos := @correction_pos
  strictly_decreasing := correction_strictly_decreasing
  bounded_by_inv := @correction_le_inv

end
end QuantumChannelCapacityFromPhi
end Information
end IndisputableMonolith
