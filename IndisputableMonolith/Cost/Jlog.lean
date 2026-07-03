import Mathlib
import Mathlib.Analysis.Complex.Trigonometric

namespace IndisputableMonolith
namespace Cost

noncomputable def Jlog (t : ℝ) : ℝ := ((Real.exp t + Real.exp (-t)) / 2) - 1

@[simp] lemma Jlog_as_exp (t : ℝ) : Jlog t = ((Real.exp t + Real.exp (-t)) / 2) - 1 := rfl

@[simp] lemma Jlog_zero : Jlog 0 = 0 := by
  simp [Jlog]

open Complex

@[simp] lemma Jlog_eq_cosh_sub_one (t : ℝ) : Jlog t = Real.cosh t - 1 := by
  -- `Real.cosh_eq` gives `cosh t = (exp t + exp (-t))/2`.
  -- Rewrite the RHS in terms of `exp` and close by reflexivity.
  unfold Jlog
  rw [Real.cosh_eq t]

/-! ## Basic order facts (used in "cost ⇒ atomicity" bridges) -/

@[simp] lemma Jlog_nonneg (t : ℝ) : 0 ≤ Jlog t := by
  -- rewrite to `0 ≤ cosh t - 1` and discharge via `1 ≤ cosh t`
  rw [Jlog_eq_cosh_sub_one]
  exact sub_nonneg.mpr (Real.one_le_cosh t)

@[simp] lemma Jlog_pos_iff (t : ℝ) : 0 < Jlog t ↔ t ≠ 0 := by
  -- rewrite to `0 < cosh t - 1` and use `one_lt_cosh`
  rw [Jlog_eq_cosh_sub_one]
  constructor
  · intro ht
    have : (1 : ℝ) < Real.cosh t := (sub_pos).1 ht
    exact (Real.one_lt_cosh (x := t)).1 this
  · intro hne
    have : (1 : ℝ) < Real.cosh t := (Real.one_lt_cosh (x := t)).2 hne
    exact (sub_pos).2 this

@[simp] lemma Jlog_eq_zero_iff (t : ℝ) : Jlog t = 0 ↔ t = 0 := by
  constructor
  · intro ht
    by_contra hne
    have : 0 < Jlog t := (Jlog_pos_iff t).2 hne
    linarith
  · intro ht
    subst ht
    simp [Jlog]

theorem Jlog_strictMonoOn_Ici0 : StrictMonoOn Jlog (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  -- strict monotonicity inherits from `cosh` on `Ici 0`
  have hcosh : Real.cosh x < Real.cosh y :=
    Real.cosh_strictMonoOn hx hy hxy
  -- subtracting 1 preserves strict inequality
  -- rewrite the goal using `Jlog = cosh - 1`
  rw [Jlog_eq_cosh_sub_one, Jlog_eq_cosh_sub_one]
  exact sub_lt_sub_right hcosh 1

end Cost
end IndisputableMonolith
