import Mathlib.Tactic
import IndisputableMonolith.Erdos132.SlotCerts
import IndisputableMonolith.Erdos132.SlotBound
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace Erdos132.SlotBound

theorem h_uu_uv_uv_uu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0000 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0002 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0002 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0004 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0001 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0003 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0003 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0005 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0014 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0016 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0016 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0018 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0015 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0017 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0017 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0019 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0002 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0006 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0008 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0010 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0003 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0007 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0009 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0011 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0016 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0020 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0022 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0024 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0017 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0021 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0023 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0025 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0002 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0008 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0006 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0010 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0003 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0009 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0007 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0011 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0016 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0022 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0020 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0024 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0017 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0023 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0021 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0025 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0004 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0010 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0010 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0012 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0005 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0011 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0011 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0013 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0018 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0024 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0024 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0026 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0019 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0025 u v (P 3).2 (P 0).2 (P 1).2 (P 2).2 hu0 hv0 hy3 hy0 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0025 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0027 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_uu_vu_uv_vu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0124 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0125 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0127 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0128 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0125 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0126 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0128 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0129 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0136 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0137 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0140 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0141 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0138 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0139 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0142 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0143 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0130 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0131 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0133 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0134 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0131 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0132 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0134 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0135 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0144 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0145 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0148 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0149 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0146 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0147 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0150 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0151 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0136 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0138 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0140 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0142 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0137 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0139 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0141 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0143 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0152 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0153 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0155 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0156 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0153 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0154 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0156 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0157 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0144 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0146 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0148 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0150 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0145 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0147 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0149 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0151 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0158 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0159 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0161 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0162 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0159 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0160 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0162 u v (P 0).2 (P 3).2 (P 1).2 (P 2).2 hu0 hv0 hy0 hy3 hy1 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0163 u v (P 0).2 (P 1).2 (P 3).2 (P 2).2 hu0 hv0 hy0 hy1 hy3 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_uu_vv_vu_uu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = v^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = u^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0056 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0060 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0058 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0062 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0057 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0061 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0059 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0063 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0076 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0080 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0078 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0082 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0077 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0081 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0079 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0083 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0060 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0070 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0066 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0072 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0061 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0071 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0067 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0073 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0080 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0090 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0086 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0092 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0081 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0091 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0087 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0093 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0058 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0066 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0064 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0068 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0059 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0067 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0065 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0069 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0078 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0086 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0084 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0088 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0079 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0087 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0085 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0089 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0062 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0072 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0068 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0074 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0063 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0073 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0069 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0075 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0082 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0092 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0088 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0094 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0083 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0093 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0089 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0095 u v (P 0).2 (P 3).2 (P 2).2 (P 1).2 hu0 hv0 hy0 hy3 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_uv_uu_vu_vv (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = v^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = u^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0204 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0210 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0206 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0212 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0207 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0213 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0209 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0215 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0232 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0238 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0234 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0240 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0235 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0241 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0237 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0243 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_uv_vu_uu_vu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = u^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0124 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0136 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0127 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0140 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0136 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0152 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0140 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0155 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0125 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0137 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0128 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0141 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0138 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0153 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0142 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0156 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0130 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0144 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0133 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0148 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0144 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0158 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0148 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0161 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0131 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0145 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0134 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0149 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0146 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0159 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0150 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0162 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0125 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0138 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0128 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0142 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0137 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0153 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0141 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0156 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0126 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0139 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0129 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0143 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0139 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0154 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0143 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0157 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0131 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0146 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0134 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0150 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0145 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0159 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0149 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0162 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0132 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0147 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0135 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0151 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0147 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0160 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0151 u v (P 2).2 (P 3).2 (P 1).2 (P 0).2 hu0 hv0 hy2 hy3 hy1 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0163 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_uv_vv_uv_uu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = u^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0164 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0176 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0170 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0184 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0165 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0177 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0171 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0185 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0176 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0192 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0184 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0198 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0178 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0193 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0186 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0199 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0167 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0180 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0173 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0188 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0168 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0181 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0174 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0189 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0180 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0195 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0188 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0201 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0182 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0196 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0190 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0202 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0165 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0178 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0171 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0186 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0166 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0179 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0172 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0187 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0177 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0193 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0185 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0199 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0179 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0194 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0187 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0200 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0168 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0182 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0174 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0190 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0169 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0183 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0175 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0191 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0181 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0196 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0189 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0202 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0183 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0197 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0191 u v (P 3).2 (P 2).2 (P 0).2 (P 1).2 hu0 hv0 hy3 hy2 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0203 u v (P 3).2 (P 0).2 (P 2).2 (P 1).2 hu0 hv0 hy3 hy0 hy2 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vu_uu_uv_vv (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0204 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0210 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0206 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0212 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0207 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0213 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0209 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0215 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0232 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0238 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0234 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0240 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0235 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0241 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0237 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0243 u v (P 1).2 (P 0).2 (P 2).2 (P 3).2 hu0 hv0 hy1 hy0 hy2 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vu_uv_vu_uv (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = v^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = u^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0284 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0286 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0285 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0286 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0288 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0289 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0286 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0288 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 2).2 (P 0).2 (P 1).2 (P 3).2 hu0 hv0 hy2 hy0 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0290 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0291 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0293 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0292 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0285 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0297 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0298 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 3).2 (P 1).2 (P 0).2 (P 2).2 hu0 hv0 hy3 hy1 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0290 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0298 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0299 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0289 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0298 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0299 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0292 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0300 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0301 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0286 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0291 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0292 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0288 u v (P 3).2 (P 1).2 (P 0).2 (P 2).2 hu0 hv0 hy3 hy1 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0293 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0290 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0288 u v (P 2).2 (P 0).2 (P 1).2 (P 3).2 hu0 hv0 hy2 hy0 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0293 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0289 u v (P 2).2 (P 0).2 (P 1).2 (P 3).2 hu0 hv0 hy2 hy0 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 2).2 (P 0).2 (P 1).2 (P 3).2 hu0 hv0 hy2 hy0 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0293 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0295 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0296 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0287 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0292 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0298 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0300 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0289 u v (P 3).2 (P 1).2 (P 0).2 (P 2).2 hu0 hv0 hy3 hy1 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 3).2 (P 1).2 (P 0).2 (P 2).2 hu0 hv0 hy3 hy1 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0299 u v (P 3).2 (P 1).2 (P 0).2 (P 2).2 hu0 hv0 hy3 hy1 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0301 u v (P 0).2 (P 2).2 (P 3).2 (P 1).2 hu0 hv0 hy0 hy2 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0290 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0299 u v (P 2).2 (P 0).2 (P 1).2 (P 3).2 hu0 hv0 hy2 hy0 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0301 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0294 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0296 u v (P 1).2 (P 3).2 (P 0).2 (P 2).2 hu0 hv0 hy1 hy3 hy0 hy2 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0301 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 0).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c02; rw [hx0, hx2] at c02; linear_combination c02
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0302 u v (P 0).2 (P 2).2 (P 1).2 (P 3).2 hu0 hv0 hy0 hy2 hy1 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vu_vv_uu_uv (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = u^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = u^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0204 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0210 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0207 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0213 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0216 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0232 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0224 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0238 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0220 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0235 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0228 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0241 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0205 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0218 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0206 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0211 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0226 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0212 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0208 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0222 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0209 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0214 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0230 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0215 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0217 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0233 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0219 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0234 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0225 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0239 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0227 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0240 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0221 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0236 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0223 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0237 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0229 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0242 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0231 u v (P 2).2 (P 3).2 (P 0).2 (P 1).2 hu0 hv0 hy2 hy3 hy0 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL1 : (1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 0).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c01; rw [hx0, hx1] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0243 u v (P 2).2 (P 0).2 (P 3).2 (P 1).2 hu0 hv0 hy2 hy0 hy3 hy1 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vv_uu_uv_uu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = u^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0056 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0060 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0076 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0080 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0060 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0070 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0080 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0090 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0058 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0062 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0078 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0082 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0066 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0072 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0086 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0092 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0057 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0061 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0077 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0081 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0061 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0071 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0081 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0091 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0059 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0063 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0079 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0083 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0067 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0073 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0087 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0093 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0058 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0066 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0078 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0086 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0062 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0072 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0082 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0092 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0064 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0068 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0084 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0088 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0068 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0074 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0088 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0094 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0059 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0067 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0079 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0087 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0063 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0073 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0083 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0093 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0065 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0069 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0085 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0089 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0069 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0075 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (1/2 - (1/2))^2 + ((P 3).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c13; rw [hx3, hx1] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL2 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL4 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0089 u v (P 3).2 (P 1).2 (P 2).2 (P 0).2 hu0 hv0 hy3 hy1 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL1 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL2 : (1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 3).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c23; rw [hx3, hx2] at c23; linear_combination c23
              have hpL4 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              have hpL5 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0095 u v (P 1).2 (P 3).2 (P 2).2 (P 0).2 hu0 hv0 hy1 hy3 hy2 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vv_uv_uv_vu (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = u^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = v^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = u^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0303 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0307 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0307 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0317 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0323 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0327 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0327 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0337 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0304 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0308 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0308 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0318 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0324 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0328 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0328 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0338 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0305 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0309 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0313 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0319 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0325 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0329 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0333 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0339 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0306 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0310 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0314 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0320 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0326 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0330 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0334 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0340 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0305 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0313 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0309 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0319 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0325 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0333 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0329 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0339 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0306 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0314 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0310 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0320 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0326 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0334 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0330 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0340 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0311 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0315 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0315 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0321 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0331 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0335 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0335 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0341 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0312 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0316 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0316 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0322 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0332 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0336 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0336 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (u^2/2 - v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0342 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

theorem h_vv_vu_uv_vv (u v : ℝ) (hu0 : 0 < u) (hv0 : 0 < v)
    (P : Fin 4 → ℝ × ℝ)
    (hA0 : d2 (P 0) ((0:ℝ),(0:ℝ)) = v^2) (hB0 : d2 (P 0) ((1:ℝ),(0:ℝ)) = v^2)
    (hA1 : d2 (P 1) ((0:ℝ),(0:ℝ)) = v^2) (hB1 : d2 (P 1) ((1:ℝ),(0:ℝ)) = u^2)
    (hA2 : d2 (P 2) ((0:ℝ),(0:ℝ)) = u^2) (hB2 : d2 (P 2) ((1:ℝ),(0:ℝ)) = v^2)
    (hA3 : d2 (P 3) ((0:ℝ),(0:ℝ)) = v^2) (hB3 : d2 (P 3) ((1:ℝ),(0:ℝ)) = v^2)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2)
    : False := by
  have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
  rcases hpair 0 1 (by decide) with c01 | c01
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0371 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0373 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0373 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0377 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0385 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0387 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0387 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0391 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0372 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0374 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0374 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0378 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0386 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0388 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0388 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0392 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0373 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0375 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0379 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0381 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0387 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0389 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0393 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0395 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0374 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0376 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0380 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0382 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0388 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0390 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0394 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0396 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
  · rcases hpair 0 2 (by decide) with c02 | c02
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0373 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0379 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0375 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0381 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0387 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0393 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0389 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0395 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0374 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0380 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0376 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0382 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0388 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0394 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0390 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0396 u v (P 2).2 (P 1).2 (P 0).2 (P 3).2 hu0 hv0 hy2 hy1 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
    · rcases hpair 0 3 (by decide) with c03 | c03
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0377 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0381 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0381 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0383 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0391 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0395 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = u^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0395 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0397 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
      · rcases hpair 1 2 (by decide) with c12 | c12
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0378 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0382 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = u^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0382 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = u^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0384 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
        · rcases hpair 1 3 (by decide) with c13 | c13
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0392 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0396 u v (P 1).2 (P 2).2 (P 3).2 (P 0).2 hu0 hv0 hy1 hy2 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
          · rcases hpair 2 3 (by decide) with c23 | c23
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 2).2 - (P 1).2)^2 = v^2 := by simp only [d2] at c12; rw [hx2, hx1] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = u^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL5 : (1/2 - (1/2))^2 + ((P 3).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c03; rw [hx3, hx0] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0396 u v (P 2).2 (P 1).2 (P 3).2 (P 0).2 hu0 hv0 hy2 hy1 hy3 hy0 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5
            · have hpL0 : (u^2/2 - v^2/2 + 1/2 - (-u^2/2 + v^2/2 + 1/2))^2 + ((P 1).2 - (P 2).2)^2 = v^2 := by simp only [d2] at c12; rw [hx1, hx2] at c12; linear_combination c12
              have hpL1 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c01; rw [hx1, hx0] at c01; linear_combination c01
              have hpL2 : (u^2/2 - v^2/2 + 1/2 - (1/2))^2 + ((P 1).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c13; rw [hx1, hx3] at c13; linear_combination c13
              have hpL3 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 0).2)^2 = v^2 := by simp only [d2] at c02; rw [hx2, hx0] at c02; linear_combination c02
              have hpL4 : (-u^2/2 + v^2/2 + 1/2 - (1/2))^2 + ((P 2).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c23; rw [hx2, hx3] at c23; linear_combination c23
              have hpL5 : (1/2 - (1/2))^2 + ((P 0).2 - (P 3).2)^2 = v^2 := by simp only [d2] at c03; rw [hx0, hx3] at c03; linear_combination c03
              exact IndisputableMonolith.Erdos132.SlotCerts.leaf_0398 u v (P 1).2 (P 2).2 (P 0).2 (P 3).2 hu0 hv0 hy1 hy2 hy0 hy3 hpL0 hpL1 hpL2 hpL3 hpL4 hpL5

end Erdos132.SlotBound
