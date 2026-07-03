import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.NavierStokes.PhiLadderCutoff

/-!
# φ as the Unique Optimal Cascade Ratio

This module formalizes a simplified variational model for the φ-ladder.
The idea is to measure the failure of a geometric ratio `r > 1` to satisfy the
self-similar closure relation `r^2 = r + 1`. The canonical cost of that defect
is minimized exactly at `r = φ`.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace PhiOptimalCascade

open Constants
open PhiLadderCutoff

noncomputable section

/-- Self-similarity defect ratio for a geometric cascade. -/
def selfSimilarityDefect (r : ℝ) : ℝ :=
  r ^ 2 / (r + 1)

/-- Simplified cascade cost: the J-cost of the self-similarity defect. -/
def simplifiedCascadeCost (r : ℝ) : ℝ :=
  Jcost (selfSimilarityDefect r)

theorem selfSimilarityDefect_pos {r : ℝ} (hr : 1 < r) :
    0 < selfSimilarityDefect r := by
  unfold selfSimilarityDefect
  positivity

theorem selfSimilarityDefect_phi : selfSimilarityDefect phi = 1 := by
  unfold selfSimilarityDefect
  have hphi1 : phi + 1 ≠ 0 := by linarith [phi_pos]
  rw [phi_sq_eq]
  field_simp [hphi1]

theorem simplifiedCascadeCost_phi : simplifiedCascadeCost phi = 0 := by
  unfold simplifiedCascadeCost
  rw [selfSimilarityDefect_phi]
  exact Jcost_one

theorem selfSimilarityDefect_eq_one_iff {r : ℝ} (hr : 1 < r) :
    selfSimilarityDefect r = 1 ↔ r ^ 2 = r + 1 := by
  unfold selfSimilarityDefect
  have hr1 : r + 1 ≠ 0 := by linarith
  constructor
  · intro h
    field_simp [hr1] at h
    linarith
  · intro h
    rw [h]
    field_simp [hr1]

theorem positive_root_unique_above_one {r : ℝ} (hr : 1 < r)
    (hroot : r ^ 2 = r + 1) : r = phi := by
  have hroot0 : r ^ 2 - r - 1 = 0 := by nlinarith [hroot]
  have hphi0 : phi ^ 2 - phi - 1 = 0 := by nlinarith [phi_sq_eq]
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have hmono : r ^ 2 - r - 1 < phi ^ 2 - phi - 1 := by
      nlinarith [hr, one_lt_phi, hlt]
    nlinarith
  · have hmono : phi ^ 2 - phi - 1 < r ^ 2 - r - 1 := by
      nlinarith [hr, one_lt_phi, hgt]
    nlinarith

theorem simplifiedCascadeCost_eq_zero_iff {r : ℝ} (hr : 1 < r) :
    simplifiedCascadeCost r = 0 ↔ r = phi := by
  have hpos : 0 < selfSimilarityDefect r := selfSimilarityDefect_pos hr
  constructor
  · intro h
    have hdefect : selfSimilarityDefect r = 1 :=
      (Jcost_eq_zero_iff hpos).mp h
    exact positive_root_unique_above_one hr ((selfSimilarityDefect_eq_one_iff hr).mp hdefect)
  · intro h
    rw [h]
    exact simplifiedCascadeCost_phi

theorem simplifiedCascadeCost_nonneg {r : ℝ} (hr : 1 < r) :
    0 ≤ simplifiedCascadeCost r := by
  unfold simplifiedCascadeCost
  exact Jcost_nonneg (selfSimilarityDefect_pos hr)

/-- φ is the unique minimizer of the simplified cascade cost on `(1, ∞)`. -/
theorem phi_is_unique_optimal_ratio {r : ℝ} (hr : 1 < r) :
    simplifiedCascadeCost phi ≤ simplifiedCascadeCost r ∧
    (simplifiedCascadeCost r = simplifiedCascadeCost phi ↔ r = phi) := by
  have hnonneg : 0 ≤ simplifiedCascadeCost r := simplifiedCascadeCost_nonneg hr
  constructor
  · simpa [simplifiedCascadeCost_phi] using hnonneg
  · constructor
    · intro heq
      have hz : simplifiedCascadeCost r = 0 := by
        simpa [simplifiedCascadeCost_phi] using heq
      exact (simplifiedCascadeCost_eq_zero_iff hr).mp hz
    · intro h
      rw [h]

end

end PhiOptimalCascade
end NavierStokes
end IndisputableMonolith
