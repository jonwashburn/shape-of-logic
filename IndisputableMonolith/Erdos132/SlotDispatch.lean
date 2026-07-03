/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdos-132 d=1 slot bound: proven `offline_no_four_slots` (deterministic certificate dispatch).

This module discharges `Erdos132.SlotBound.offline_no_four_slots` by a full finite
case split: a 256-way `rcases` on the two distance choices of each of the 4 points,
then a 64-way `rcases` on the six pairwise colors. The 52 `mult>=3` type-multiplicity
branches are killed by injectivity (`three_same_slot`, `Inj.lean`); the 204 valid
type-combinations are routed to per-type helper theorems (`H00..H15`), each of which
applies one of the 399 axiom-clean `SlotCerts.leaf_NNNN` certificates via
`linear_combination` + `positivity`. Axiom-clean: [propext, Classical.choice, Quot.sound].
-/
import Mathlib.Tactic
import IndisputableMonolith.Erdos132.SlotBound
import IndisputableMonolith.Erdos132.SlotDispatch.Inj
import IndisputableMonolith.Erdos132.SlotDispatch.H00
import IndisputableMonolith.Erdos132.SlotDispatch.H01
import IndisputableMonolith.Erdos132.SlotDispatch.H02
import IndisputableMonolith.Erdos132.SlotDispatch.H03
import IndisputableMonolith.Erdos132.SlotDispatch.H04
import IndisputableMonolith.Erdos132.SlotDispatch.H05
import IndisputableMonolith.Erdos132.SlotDispatch.H06
import IndisputableMonolith.Erdos132.SlotDispatch.H07
import IndisputableMonolith.Erdos132.SlotDispatch.H08
import IndisputableMonolith.Erdos132.SlotDispatch.H09
import IndisputableMonolith.Erdos132.SlotDispatch.H10
import IndisputableMonolith.Erdos132.SlotDispatch.H11
import IndisputableMonolith.Erdos132.SlotDispatch.H12
import IndisputableMonolith.Erdos132.SlotDispatch.H13
import IndisputableMonolith.Erdos132.SlotDispatch.H14
import IndisputableMonolith.Erdos132.SlotDispatch.H15

noncomputable section

namespace Erdos132.SlotBound

set_option maxHeartbeats 4000000 in
theorem offline_no_four_slots
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (P : Fin 4 → ℝ × ℝ)
    (hinj : Function.Injective P)
    (hnd : ∀ i, IsNonDiameter u v (P i))
    (hoff : ∀ i, (P i).2 ≠ 0)
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2) :
    False := by
  obtain ⟨hA0, hB0⟩ := hnd 0
  obtain ⟨hA1, hB1⟩ := hnd 1
  obtain ⟨hA2, hB2⟩ := hnd 2
  obtain ⟨hA3, hB3⟩ := hnd 3
  rcases hA0 with hA0 | hA0
  · rcases hB0 with hB0 | hB0
    · rcases hA1 with hA1 | hA1
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (u^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (u^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (u^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (u^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_uu_uu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_uu_uu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uu_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_uu_uu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_uu_uv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_uv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_uv_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_uu_vu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_uu_vu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = u^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_uu_vv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uu_vv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uu_vv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
    · rcases hA1 with hA1 | hA1
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_uv_uu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_uv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_uv_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_uv_vu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_uv_vv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_uv_vv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
  · rcases hB0 with hB0 | hB0
    · rcases hA1 with hA1 | hA1
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_vu_uu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_vu_uu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_vu_uv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_uv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_uv_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vu_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_vu_vu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_vu_vu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
                · exact h_vu_vu_vv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
                · exact h_vu_vv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vu_vv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vu_vv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
    · rcases hA1 with hA1 | hA1
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = u^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = u^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = u^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (u^2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_vv_uu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx1 : (P 1).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = u^2/2 - v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (u^2/2 - v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_uv_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_uv_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
      · rcases hB1 with hB1 | hB1
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_uu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_uv_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · have hx1 : (P 1).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = -u^2/2 + v^2/2 + 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy1 : (P 1).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (-u^2/2 + v^2/2 + 1/2) (-u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4) hx1 hx2 hx3 hy1 hy2 hy3
                · exact h_vv_vu_vu_vv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_vv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vu_vv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vu_vv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (2:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx2 hx3 hy0 hy2 hy3
        · rcases hA2 with hA2 | hA2
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_uu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vv_uu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_uu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_uv_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vv_uv_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_uv_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
          · rcases hB2 with hB2 | hB2
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_vu_uu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · exact h_vv_vv_vu_uv u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
              · rcases hB3 with hB3 | hB3
                · exact h_vv_vv_vu_vu u v hu0 hv0 P hA0 hB0 hA1 hB1 hA2 hB2 hA3 hB3 hpair
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx3 : (P 3).1 = 1/2 := by simp only [d2] at hA3 hB3; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy3 : (P 3).2^2 = v^2 - 1/4 := by simp only [d2] at hA3; rw [hx3] at hA3; linear_combination hA3
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 3)) (hinj.ne (by decide : (1:Fin 4) ≠ 3)) (1/2) (v^2 - 1/4) hx0 hx1 hx3 hy0 hy1 hy3
            · rcases hA3 with hA3 | hA3
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (v^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (v^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
              · rcases hB3 with hB3 | hB3
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (v^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2
                · have hx0 : (P 0).1 = 1/2 := by simp only [d2] at hA0 hB0; linarith
                  have hx1 : (P 1).1 = 1/2 := by simp only [d2] at hA1 hB1; linarith
                  have hx2 : (P 2).1 = 1/2 := by simp only [d2] at hA2 hB2; linarith
                  have hy0 : (P 0).2^2 = v^2 - 1/4 := by simp only [d2] at hA0; rw [hx0] at hA0; linear_combination hA0
                  have hy1 : (P 1).2^2 = v^2 - 1/4 := by simp only [d2] at hA1; rw [hx1] at hA1; linear_combination hA1
                  have hy2 : (P 2).2^2 = v^2 - 1/4 := by simp only [d2] at hA2; rw [hx2] at hA2; linear_combination hA2
                  exact three_same_slot (hinj.ne (by decide : (0:Fin 4) ≠ 1)) (hinj.ne (by decide : (0:Fin 4) ≠ 2)) (hinj.ne (by decide : (1:Fin 4) ≠ 2)) (1/2) (v^2 - 1/4) hx0 hx1 hx2 hy0 hy1 hy2


/-- Squared distance is symmetric. -/
theorem d2_comm (p q : ℝ × ℝ) : d2 p q = d2 q p := by
  simp only [d2]; ring

/-- Explicit-point form of `no_three_collinear` (three distinct collinear
non-diameter points). Centralizes the `Fin 3` reindexing. -/
private theorem no_three_collinear_pts
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (p0 p1 p2 : ℝ × ℝ)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2)
    (hnd0 : IsNonDiameter u v p0) (hnd1 : IsNonDiameter u v p1)
    (hnd2 : IsNonDiameter u v p2)
    (hc0 : p0.2 = 0) (hc1 : p1.2 = 0) (hc2 : p2.2 = 0) : False := by
  refine no_three_collinear u v hu0 hu1 hv0 hv1 huv ![p0, p1, p2] ?_ ?_ ?_
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd hab h01 | exact absurd hab h02 | exact absurd hab h12
        | exact absurd hab.symm h01 | exact absurd hab.symm h02 | exact absurd hab.symm h12
  · intro i; fin_cases i
    · exact hnd0
    · exact hnd1
    · exact hnd2
  · intro i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2

/-- Explicit-point form of `one_collinear_three_offline`. Centralizes the `Fin 3`
reindexing and the pairwise/cross distance plumbing. -/
private theorem one_collinear_three_offline_pts
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (c p0 p1 p2 : ℝ × ℝ)
    (hndc : IsNonDiameter u v c)
    (hnd0 : IsNonDiameter u v p0) (hnd1 : IsNonDiameter u v p1)
    (hnd2 : IsNonDiameter u v p2)
    (hcol : c.2 = 0) (ho0 : p0.2 ≠ 0) (ho1 : p1.2 ≠ 0) (ho2 : p2.2 ≠ 0)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2)
    (q01 : d2 p0 p1 = u ^ 2 ∨ d2 p0 p1 = v ^ 2)
    (q02 : d2 p0 p2 = u ^ 2 ∨ d2 p0 p2 = v ^ 2)
    (q12 : d2 p1 p2 = u ^ 2 ∨ d2 p1 p2 = v ^ 2)
    (r0 : d2 c p0 = u ^ 2 ∨ d2 c p0 = v ^ 2)
    (r1 : d2 c p1 = u ^ 2 ∨ d2 c p1 = v ^ 2)
    (r2 : d2 c p2 = u ^ 2 ∨ d2 c p2 = v ^ 2) : False := by
  refine one_collinear_three_offline u v hu0 hu1 hv0 hv1 huv c ![p0, p1, p2]
    hndc ?_ hcol ?_ ?_ ?_ ?_
  · intro i; fin_cases i
    · exact hnd0
    · exact hnd1
    · exact hnd2
  · intro i; fin_cases i
    · exact ho0
    · exact ho1
    · exact ho2
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd hab h01 | exact absurd hab h02 | exact absurd hab h12
        | exact absurd hab.symm h01 | exact absurd hab.symm h02 | exact absurd hab.symm h12
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact absurd rfl hab
        | exact q01 | exact q02 | exact q12
        | (rw [d2_comm]; exact q01) | (rw [d2_comm]; exact q02) | (rw [d2_comm]; exact q12)
  · intro i; fin_cases i
    · exact r0
    · exact r1
    · exact r2

/-- Explicit-point form of `two_collinear_two_offline`. Builds the `Finset`-shaped
pairwise hypothesis from the six unordered distance facts. -/
private theorem two_collinear_two_offline_pts
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (c0 c1 q0 q1 : ℝ × ℝ)
    (hndc0 : IsNonDiameter u v c0) (hndc1 : IsNonDiameter u v c1)
    (hndq0 : IsNonDiameter u v q0) (hndq1 : IsNonDiameter u v q1)
    (hcol0 : c0.2 = 0) (hcol1 : c1.2 = 0)
    (hoff0 : q0.2 ≠ 0) (hoff1 : q1.2 ≠ 0)
    (hd01 : c0 ≠ c1) (hd23 : q0 ≠ q1)
    (e0 : d2 c0 c1 = u ^ 2 ∨ d2 c0 c1 = v ^ 2)
    (e1 : d2 c0 q0 = u ^ 2 ∨ d2 c0 q0 = v ^ 2)
    (e2 : d2 c0 q1 = u ^ 2 ∨ d2 c0 q1 = v ^ 2)
    (e3 : d2 c1 q0 = u ^ 2 ∨ d2 c1 q0 = v ^ 2)
    (e4 : d2 c1 q1 = u ^ 2 ∨ d2 c1 q1 = v ^ 2)
    (e5 : d2 q0 q1 = u ^ 2 ∨ d2 q0 q1 = v ^ 2) : False := by
  refine two_collinear_two_offline u v hu0 hu1 hv0 hv1 huv c0 c1 q0 q1
    hndc0 hndc1 hndq0 hndq1 hcol0 hcol1 hoff0 hoff1 ⟨hd01, hd23⟩ ?_
  intro p hp q hq hpq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | exact e0 | exact e1 | exact e2 | exact e3 | exact e4 | exact e5
      | (rw [d2_comm]; exact e0) | (rw [d2_comm]; exact e1) | (rw [d2_comm]; exact e2)
      | (rw [d2_comm]; exact e3) | (rw [d2_comm]; exact e4) | (rw [d2_comm]; exact e5)

/-- **No four non-diameter points.** No four distinct non-diameter points (any mix
of collinear and off-line) can have all six pairwise distances in `{u², v²}`.
Assembled from the four loci above by counting how many of the four points are
collinear (`y = 0`): ≥3 collinear is killed by `no_three_collinear`, exactly 2 by
`two_collinear_two_offline`, exactly 1 by `one_collinear_three_offline`, 0 by
`offline_no_four_slots`. -/
theorem no_four_nondiameter
    (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (P : Fin 4 → ℝ × ℝ)
    (hinj : Function.Injective P)
    (hnd : ∀ i, IsNonDiameter u v (P i))
    (hpair : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2) :
    False := by
  classical
  by_cases h0 : (P 0).2 = 0 <;> by_cases h1 : (P 1).2 = 0 <;>
    by_cases h2 : (P 2).2 = 0 <;> by_cases h3 : (P 3).2 = 0
  -- 1. TTTT : ≥3 collinear (0,1,2)
  · exact no_three_collinear_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 1) (P 2)
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hnd 0) (hnd 1) (hnd 2) h0 h1 h2
  -- 2. TTTF : collinear (0,1,2)
  · exact no_three_collinear_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 1) (P 2)
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hnd 0) (hnd 1) (hnd 2) h0 h1 h2
  -- 3. TTFT : collinear (0,1,3)
  · exact no_three_collinear_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 1) (P 3)
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hnd 0) (hnd 1) (hnd 3) h0 h1 h3
  -- 4. TTFF : collinear (0,1), offline (2,3)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 1) (P 2) (P 3)
      (hnd 0) (hnd 1) (hnd 2) (hnd 3) h0 h1 h2 h3
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 0 3 (by decide))
      (hpair 1 2 (by decide)) (hpair 1 3 (by decide)) (hpair 2 3 (by decide))
  -- 5. TFTT : collinear (0,2,3)
  · exact no_three_collinear_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 2) (P 3)
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hnd 0) (hnd 2) (hnd 3) h0 h2 h3
  -- 6. TFTF : collinear (0,2), offline (1,3)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 2) (P 1) (P 3)
      (hnd 0) (hnd 2) (hnd 1) (hnd 3) h0 h2 h1 h3
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 2 (by decide)) (hpair 0 1 (by decide)) (hpair 0 3 (by decide))
      (hpair 2 1 (by decide)) (hpair 2 3 (by decide)) (hpair 1 3 (by decide))
  -- 7. TFFT : collinear (0,3), offline (1,2)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 3) (P 1) (P 2)
      (hnd 0) (hnd 3) (hnd 1) (hnd 2) h0 h3 h1 h2
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 3 (by decide)) (hpair 0 1 (by decide)) (hpair 0 2 (by decide))
      (hpair 3 1 (by decide)) (hpair 3 2 (by decide)) (hpair 1 2 (by decide))
  -- 8. TFFF : collinear (0), offline (1,2,3)
  · exact one_collinear_three_offline_pts u v hu0 hu1 hv0 hv1 huv (P 0) (P 1) (P 2) (P 3)
      (hnd 0) (hnd 1) (hnd 2) (hnd 3) h0 h1 h2 h3
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 1 2 (by decide)) (hpair 1 3 (by decide)) (hpair 2 3 (by decide))
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 0 3 (by decide))
  -- 9. FTTT : collinear (1,2,3)
  · exact no_three_collinear_pts u v hu0 hu1 hv0 hv1 huv (P 1) (P 2) (P 3)
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hnd 1) (hnd 2) (hnd 3) h1 h2 h3
  -- 10. FTTF : collinear (1,2), offline (0,3)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 1) (P 2) (P 0) (P 3)
      (hnd 1) (hnd 2) (hnd 0) (hnd 3) h1 h2 h0 h3
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 1 2 (by decide)) (hpair 1 0 (by decide)) (hpair 1 3 (by decide))
      (hpair 2 0 (by decide)) (hpair 2 3 (by decide)) (hpair 0 3 (by decide))
  -- 11. FTFT : collinear (1,3), offline (0,2)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 1) (P 3) (P 0) (P 2)
      (hnd 1) (hnd 3) (hnd 0) (hnd 2) h1 h3 h0 h2
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 1 3 (by decide)) (hpair 1 0 (by decide)) (hpair 1 2 (by decide))
      (hpair 3 0 (by decide)) (hpair 3 2 (by decide)) (hpair 0 2 (by decide))
  -- 12. FTFF : collinear (1), offline (0,2,3)
  · exact one_collinear_three_offline_pts u v hu0 hu1 hv0 hv1 huv (P 1) (P 0) (P 2) (P 3)
      (hnd 1) (hnd 0) (hnd 2) (hnd 3) h1 h0 h2 h3
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 2 (by decide)) (hpair 0 3 (by decide)) (hpair 2 3 (by decide))
      (hpair 1 0 (by decide)) (hpair 1 2 (by decide)) (hpair 1 3 (by decide))
  -- 13. FFTT : collinear (2,3), offline (0,1)
  · exact two_collinear_two_offline_pts u v hu0 hu1 hv0 hv1 huv (P 2) (P 3) (P 0) (P 1)
      (hnd 2) (hnd 3) (hnd 0) (hnd 1) h2 h3 h0 h1
      (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 2 3 (by decide)) (hpair 2 0 (by decide)) (hpair 2 1 (by decide))
      (hpair 3 0 (by decide)) (hpair 3 1 (by decide)) (hpair 0 1 (by decide))
  -- 14. FFTF : collinear (2), offline (0,1,3)
  · exact one_collinear_three_offline_pts u v hu0 hu1 hv0 hv1 huv (P 2) (P 0) (P 1) (P 3)
      (hnd 2) (hnd 0) (hnd 1) (hnd 3) h2 h0 h1 h3
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 1 (by decide)) (hpair 0 3 (by decide)) (hpair 1 3 (by decide))
      (hpair 2 0 (by decide)) (hpair 2 1 (by decide)) (hpair 2 3 (by decide))
  -- 15. FFFT : collinear (3), offline (0,1,2)
  · exact one_collinear_three_offline_pts u v hu0 hu1 hv0 hv1 huv (P 3) (P 0) (P 1) (P 2)
      (hnd 3) (hnd 0) (hnd 1) (hnd 2) h3 h0 h1 h2
      (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
      (hpair 3 0 (by decide)) (hpair 3 1 (by decide)) (hpair 3 2 (by decide))
  -- 16. FFFF : all offline
  · exact offline_no_four_slots u v hu0 hu1 hv0 hv1 huv P hinj hnd
      (by intro i; fin_cases i <;> assumption) hpair

/-- The rigid motion taking `A ↦ (0,0)` and `B ↦ (1,0)`, where `e := B - A` is a unit
vector. `φ p = R (p - A)` with `R = [[e₁,e₂],[-e₂,e₁]]`. -/
def isoMap (A B p : ℝ × ℝ) : ℝ × ℝ :=
  ((B.1 - A.1) * (p.1 - A.1) + (B.2 - A.2) * (p.2 - A.2),
   -(B.2 - A.2) * (p.1 - A.1) + (B.1 - A.1) * (p.2 - A.2))

/-- `isoMap` preserves squared distance when `A,B` is a unit pair (`d2 A B = 1`). -/
theorem isoMap_d2 (A B : ℝ × ℝ) (hAB : d2 A B = 1) (p q : ℝ × ℝ) :
    d2 (isoMap A B p) (isoMap A B q) = d2 p q := by
  have he : (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 = 1 := by
    have := hAB; simp only [d2] at this; nlinarith [this]
  simp only [d2, isoMap]
  nlinarith [he, sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]

theorem isoMap_A (A B : ℝ × ℝ) : isoMap A B A = ((0:ℝ),(0:ℝ)) := by
  simp only [isoMap, Prod.mk.injEq]; constructor <;> ring

theorem isoMap_B (A B : ℝ × ℝ) (hAB : d2 A B = 1) : isoMap A B B = ((1:ℝ),(0:ℝ)) := by
  have he : (B.1 - A.1) ^ 2 + (B.2 - A.2) ^ 2 = 1 := by
    have := hAB; simp only [d2] at this; nlinarith [this]
  simp only [isoMap, Prod.mk.injEq]
  constructor
  · show (B.1 - A.1) * (B.1 - A.1) + (B.2 - A.2) * (B.2 - A.2) = 1; nlinarith [he]
  · show -(B.2 - A.2) * (B.1 - A.1) + (B.1 - A.1) * (B.2 - A.2) = 0; ring

/-- **Main theorem (`n ≤ 5`).** A finite planar point set `S` that is a 3-distance
set whose pairwise squared distances take the three values `1, u², v²`
(`0 < u, v < 1`, `u ≠ v`), and whose diameter `1` is attained by a *unique* unordered
pair `{A, B}`, has at most 5 points.

Isometry normalization places the unique diameter pair at `A = (0,0)`, `B = (1,0)`;
then every point of `S \ {A,B}` is `IsNonDiameter u v`, and `no_four_nondiameter`
caps `S \ {A,B}` at 3, so `S.card ≤ 5`. -/
theorem n_le_5
    (S : Finset (ℝ × ℝ)) (u v : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (A B : ℝ × ℝ) (hA : A ∈ S) (hB : B ∈ S) (hAB : d2 A B = 1)
    (hdiam : ∀ p ∈ S, ∀ q ∈ S, d2 p q ≤ 1)
    (huniq : ∀ p ∈ S, ∀ q ∈ S, d2 p q = 1 → (p = A ∧ q = B) ∨ (p = B ∧ q = A))
    (h3 : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → d2 p q = 1 ∨ d2 p q = u ^ 2 ∨ d2 p q = v ^ 2) :
    S.card ≤ 5 := by
  classical
  set T : Finset (ℝ × ℝ) := S \ {A, B} with hT
  have hTmem : ∀ p, p ∈ T → p ∈ S ∧ p ≠ A ∧ p ≠ B := by
    intro p hp
    rw [hT, Finset.mem_sdiff] at hp
    obtain ⟨hpS, hpAB⟩ := hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpAB
    push_neg at hpAB
    exact ⟨hpS, hpAB.1, hpAB.2⟩
  have hsub : S ⊆ insert A (insert B T) := by
    intro p hp
    by_cases hpa : p = A
    · subst hpa; exact Finset.mem_insert_self _ _
    · by_cases hpb : p = B
      · subst hpb; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
        rw [hT, Finset.mem_sdiff]
        refine ⟨hp, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push_neg; exact ⟨hpa, hpb⟩
  have hcardS : S.card ≤ T.card + 2 := by
    calc S.card ≤ (insert A (insert B T)).card := Finset.card_le_card hsub
      _ ≤ (insert B T).card + 1 := Finset.card_insert_le _ _
      _ ≤ (T.card + 1) + 1 := by
            have := Finset.card_insert_le B T; omega
      _ = T.card + 2 := by ring
  have hT3 : T.card ≤ 3 := by
    by_contra hcon
    push_neg at hcon
    have h4 : 4 ≤ T.card := hcon
    obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq h4
    let e : Fin 4 ≃ ↥t := (finCongr htcard.symm).trans t.equivFin.symm
    set P : Fin 4 → ℝ × ℝ := fun i => ((e i : ℝ × ℝ)) with hP
    have hPmemT : ∀ i, P i ∈ T := by
      intro i; exact htsub (e i).property
    have hPinj : Function.Injective P := by
      intro i j hij
      have : (e i : ℝ × ℝ) = (e j : ℝ × ℝ) := hij
      have : e i = e j := Subtype.ext this
      exact e.injective this
    set Q : Fin 4 → ℝ × ℝ := fun i => isoMap A B (P i) with hQ
    have hd2 : ∀ i j, d2 (Q i) (Q j) = d2 (P i) (P j) := by
      intro i j; rw [hQ]; exact isoMap_d2 A B hAB (P i) (P j)
    have hdA : ∀ i, d2 (Q i) ((0:ℝ),(0:ℝ)) = d2 (P i) A := by
      intro i
      rw [hQ, ← isoMap_A A B]
      exact isoMap_d2 A B hAB (P i) A
    have hdB : ∀ i, d2 (Q i) ((1:ℝ),(0:ℝ)) = d2 (P i) B := by
      intro i
      rw [hQ, ← isoMap_B A B hAB]
      exact isoMap_d2 A B hAB (P i) B
    have hQinj : Function.Injective Q := by
      intro i j hij
      apply hPinj
      have h0 : d2 (P i) (P j) = 0 := by
        rw [← hd2 i j, hij]; simp [d2]
      have hx : (P i).1 = (P j).1 ∧ (P i).2 = (P j).2 := by
        simp only [d2] at h0
        constructor <;> nlinarith [sq_nonneg ((P i).1 - (P j).1), sq_nonneg ((P i).2 - (P j).2), h0]
      exact Prod.ext hx.1 hx.2
    have hPS : ∀ i, P i ∈ S := fun i => (hTmem _ (hPmemT i)).1
    have hPneA : ∀ i, P i ≠ A := fun i => (hTmem _ (hPmemT i)).2.1
    have hPneB : ∀ i, P i ≠ B := fun i => (hTmem _ (hPmemT i)).2.2
    have hdistA : ∀ i, d2 (P i) A = u ^ 2 ∨ d2 (P i) A = v ^ 2 := by
      intro i
      rcases h3 (P i) (hPS i) A hA (hPneA i) with h1 | h1
      · exfalso
        rcases huniq (P i) (hPS i) A hA h1 with ⟨ha, _⟩ | ⟨hb, _⟩
        · exact hPneA i ha
        · exact hPneB i hb
      · exact h1
    have hdistB : ∀ i, d2 (P i) B = u ^ 2 ∨ d2 (P i) B = v ^ 2 := by
      intro i
      rcases h3 (P i) (hPS i) B hB (hPneB i) with h1 | h1
      · exfalso
        rcases huniq (P i) (hPS i) B hB h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact hPneA i ha
        · exact hPneB i ha
      · exact h1
    have hpairP : ∀ i j, i ≠ j → d2 (P i) (P j) = u ^ 2 ∨ d2 (P i) (P j) = v ^ 2 := by
      intro i j hijne
      have hne : P i ≠ P j := fun h => hijne (hPinj h)
      rcases h3 (P i) (hPS i) (P j) (hPS j) hne with h1 | h1
      · exfalso
        rcases huniq (P i) (hPS i) (P j) (hPS j) h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact hPneA i ha
        · exact hPneB i ha
      · exact h1
    refine no_four_nondiameter u v hu0 hu1 hv0 hv1 huv Q hQinj ?_ ?_
    · intro i
      refine ⟨?_, ?_⟩
      · rw [hdA i]; exact hdistA i
      · rw [hdB i]; exact hdistB i
    · intro i j hijne
      rw [hd2 i j]; exact hpairP i j hijne
  omega

end Erdos132.SlotBound
