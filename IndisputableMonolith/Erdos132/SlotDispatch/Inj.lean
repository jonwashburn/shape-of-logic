/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Injectivity kill for the Erdos-132 `d=1` slot dispatch.

Three distinct planar points that share the same x-coordinate and the same `y^2`
cannot exist: equal `y^2` forces `y = ±y'`; with equal `x`, the `+` branch makes
the points coincide (`Prod.ext`), so all three would need pairwise opposite `y`,
which is impossible for three values. Used to discharge every type-combo in which
some slot-type is occupied by three or more of the four points.
-/

set_option linter.unusedVariables false

namespace Erdos132.SlotBound

/-- Three distinct points with a common x-coordinate `X` and common `y^2 = Y`
are impossible. -/
lemma three_same_slot {p q r : ℝ × ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (X Y : ℝ)
    (hpx : p.1 = X) (hqx : q.1 = X) (hrx : r.1 = X)
    (hpy : p.2 ^ 2 = Y) (hqy : q.2 ^ 2 = Y) (hry : r.2 ^ 2 = Y) : False := by
  have hxpq : p.1 = q.1 := by rw [hpx, hqx]
  have hxpr : p.1 = r.1 := by rw [hpx, hrx]
  have hy_pq : p.2 ≠ q.2 := fun h => hpq (Prod.ext hxpq h)
  have hy_pr : p.2 ≠ r.2 := fun h => hpr (Prod.ext hxpr h)
  have f_pq : (p.2 - q.2) * (p.2 + q.2) = 0 := by
    have e : p.2 ^ 2 = q.2 ^ 2 := by rw [hpy, hqy]
    linear_combination e
  have s_pq : p.2 + q.2 = 0 := by
    rcases mul_eq_zero.1 f_pq with h | h
    · exact absurd (sub_eq_zero.1 h) hy_pq
    · exact h
  have f_pr : (p.2 - r.2) * (p.2 + r.2) = 0 := by
    have e : p.2 ^ 2 = r.2 ^ 2 := by rw [hpy, hry]
    linear_combination e
  have s_pr : p.2 + r.2 = 0 := by
    rcases mul_eq_zero.1 f_pr with h | h
    · exact absurd (sub_eq_zero.1 h) hy_pr
    · exact h
  -- p.2 = -q.2 and p.2 = -r.2  ⟹  q.2 = r.2 ; with q.1 = r.1 ⟹ q = r, contra hqr
  have hxqr : q.1 = r.1 := by rw [hqx, hrx]
  have hyqr : q.2 = r.2 := by linarith [s_pq, s_pr]
  exact hqr (Prod.ext hxqr hyqr)

end Erdos132.SlotBound
