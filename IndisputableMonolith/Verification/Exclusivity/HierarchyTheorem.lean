/-
  HierarchyTheorem.lean — Bridge B1

  Proves: (A2) + Hierarchical Structure (HS) ⟹ (A3) Self-similarity with φ.
-/

import Mathlib
import IndisputableMonolith.Verification.Exclusivity.Framework
import IndisputableMonolith.Foundation.HierarchyMinimality
import IndisputableMonolith.Foundation.PhiForcing

namespace IndisputableMonolith.Verification.Exclusivity

open IndisputableMonolith.Foundation.HierarchyMinimality
open IndisputableMonolith.Foundation.PhiForcing

structure HierarchicalLedger where
  scale : ℝ
  scale_gt_one : 1 < scale
  level_size : ℕ → ℝ
  level_size_pos : ∀ k, 0 < level_size k
  uniform_scaling : ∀ k, level_size (k + 1) = scale * level_size k
  composition : level_size 2 = level_size 1 + level_size 0

theorem hierarchy_forces_fibonacci_recurrence (L : HierarchicalLedger) :
    L.scale ^ 2 = L.scale + 1 := by
  have h0 : L.level_size 0 ≠ 0 := ne_of_gt (L.level_size_pos 0)
  have h_s1 : L.level_size 1 = L.scale * L.level_size 0 := L.uniform_scaling 0
  have h_s2 : L.level_size 2 = L.scale * L.level_size 1 := L.uniform_scaling 1
  have h_sq : L.level_size 2 = L.scale ^ 2 * L.level_size 0 := by
    rw [h_s2, h_s1]
    ring
  have h_rhs : L.level_size 2 = (L.scale + 1) * L.level_size 0 := by
    rw [L.composition, h_s1]
    ring
  have h_mul : (L.scale ^ 2 - (L.scale + 1)) * L.level_size 0 = 0 := by
    calc
      (L.scale ^ 2 - (L.scale + 1)) * L.level_size 0
          = L.scale ^ 2 * L.level_size 0 - (L.scale + 1) * L.level_size 0 := by ring
      _ = L.level_size 2 - L.level_size 2 := by rw [← h_sq, h_rhs]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_mul with hzero | hsize
  · exact sub_eq_zero.mp hzero
  · exact (h0 hsize).elim

/-- Bridge B1: Hierarchical structure ⟹ scale = φ.

    The Fibonacci recurrence σ² = σ + 1 has unique positive root > 1 at φ.
    The root uniqueness uses the existing phi_forced infrastructure. -/
theorem bridge_B1_hierarchy_implies_phi (L : HierarchicalLedger) :
    L.scale = φ := by
  let S : IndisputableMonolith.Foundation.PhiForcingDerived.GeometricScaleSequence :=
    { ratio := L.scale
      ratio_pos := lt_trans (by norm_num) L.scale_gt_one
      ratio_ne_one := by linarith [L.scale_gt_one] }
  have h_closed : S.isClosed := by
    unfold IndisputableMonolith.Foundation.PhiForcingDerived.GeometricScaleSequence.isClosed
    unfold IndisputableMonolith.Foundation.PhiForcingDerived.ledgerCompose
    unfold IndisputableMonolith.Foundation.PhiForcingDerived.GeometricScaleSequence.scale
    have hrec := hierarchy_forces_fibonacci_recurrence L
    nlinarith [hrec]
  exact hierarchy_forces_phi ⟨S, h_closed⟩

end IndisputableMonolith.Verification.Exclusivity
