import Mathlib.Tactic
import IndisputableMonolith.Erdos132.SlotCerts
import IndisputableMonolith.Erdos132.SlotBound

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Erdos132.SlotBound

open IndisputableMonolith.Erdos132.SlotCerts

/-- Prototype: one branch of `offline_no_four_slots` dispatched to `leaf_0000`.
Type-multiset: points 0,1 type `uu` (s=t=u²); points 2,3 type `uv` (s=u²,t=v²);
all six pair colors `u²`. This nails the exact incantation for the full emit. -/
theorem branch_test
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (P : Fin 4 → ℝ × ℝ)
    (hinj : Function.Injective P)
    (hnd : ∀ i, IsNonDiameter u v (P i))
    (hoff : ∀ i, (P i).2 ≠ 0)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    -- commit to the leaf_0000 branch:
    (e0a : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (e0b : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (e1a : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (e1b : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (e2a : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (e2b : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (e3a : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (e3b : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (c01 : d2 (P 0) (P 1) = u^2) (c02 : d2 (P 0) (P 2) = u^2)
    (c03 : d2 (P 0) (P 3) = u^2) (c12 : d2 (P 1) (P 2) = u^2)
    (c13 : d2 (P 1) (P 3) = u^2) (c23 : d2 (P 2) (P 3) = u^2) :
    False := by
  -- x-coordinates (linear in the two distance equations)
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at e0a e0b; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at e1a e1b; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at e2a e2b; linarith
  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at e3a e3b; linarith
  -- y² (= slotYsq), expanded to the leaf's literal form
  have g0 : (P 0).2^2 = u^2 - 1/4 := by
    simp only [d2] at e0a; rw [hx0] at e0a; linear_combination e0a
  have g1 : (P 1).2^2 = u^2 - 1/4 := by
    simp only [d2] at e1a; rw [hx1] at e1a; linear_combination e1a
  have g2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by
    simp only [d2] at e2a; rw [hx2] at e2a; linear_combination e2a
  have g3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by
    simp only [d2] at e3a; rw [hx3] at e3a; linear_combination e3a
  -- pairwise: substitute x's into d2 colors
  have hp01 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by
    simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
  have hp02 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by
    simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
  have hp03 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by
    simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
  have hp12 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by
    simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
  have hp13 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by
    simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
  have hp23 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by
    simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
  exact leaf_0000 u v (P 0).2 (P 1).2 (P 2).2 (P 3).2 hu0 hv0 g0 g1 g2 g3
    hp01 hp02 hp03 hp12 hp13 hp23

end Erdos132.SlotBound
