import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import IndisputableMonolith.Cost

/-!
# Convexity of J

This module proves that:
1. Jlog(t) = cosh t - 1 is strictly convex on ℝ
2. Jcost(x) = ½(x + x⁻¹) - 1 is strictly convex on ℝ₊

These are foundational for the uniqueness theorem T5.
-/

namespace IndisputableMonolith
namespace Cost

open Real Set

open scoped Real

/-- cosh is strictly convex on ℝ.

    Proof: cosh'' = cosh > 0 everywhere. A function with positive second
    derivative on a convex set is strictly convex. -/
theorem cosh_strictly_convex : StrictConvexOn ℝ univ Real.cosh := by
  apply strictConvexOn_of_deriv2_pos convex_univ
  · -- cosh is continuous
    exact Real.continuous_cosh.continuousOn
  · -- cosh'' = cosh > 0 on interior (which is univ)
    intro x _
    -- deriv^[2] cosh = cosh
    show 0 < deriv^[2] Real.cosh x
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    -- First derivative of cosh is sinh
    have h1 : deriv Real.cosh = Real.sinh := Real.deriv_cosh
    -- Second derivative: deriv sinh = cosh
    have h2 : deriv Real.sinh = Real.cosh := Real.deriv_sinh
    -- So deriv (deriv cosh) x = cosh x > 0
    rw [h1, congrFun h2 x]
    exact Real.cosh_pos x

/-- Strict convexity of `Real.cosh` on the whole line. -/
theorem strictConvexOn_cosh : StrictConvexOn ℝ univ Real.cosh := cosh_strictly_convex

lemma Jlog_eq_cosh_sub_one (t : ℝ) : Jlog t = Real.cosh t - 1 :=
  Jlog_as_cosh t

/-- Strict convexity of `Jlog` on `ℝ`. -/
theorem Jlog_strictConvexOn : StrictConvexOn ℝ univ Jlog := by
  -- Jlog = cosh - 1, and cosh is strictly convex
  -- Subtracting a constant preserves strict convexity
  have h : Jlog = fun t => Real.cosh t - 1 := by ext t; exact Jlog_eq_cosh_sub_one t
  rw [h]
  exact strictConvexOn_cosh.add_const (-1)

/-- First derivative of Jcost: J'(x) = (1 - x⁻²)/2 -/
noncomputable def JcostDeriv (x : ℝ) : ℝ := (1 - x ^ (-2 : ℤ)) / 2

lemma hasDerivAt_Jcost_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt Jcost (JcostDeriv x) x := by
  -- Jcost x = (x + x⁻¹)/2 - 1
  -- Jcost' x = (1 - x⁻²)/2
  unfold Jcost JcostDeriv
  have hne : x ≠ 0 := hx.ne'
  -- d/dx (x + x⁻¹)/2 - 1 = (1 - x⁻²)/2
  have h1 : HasDerivAt (fun y => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y => y⁻¹) (-(x^2)⁻¹) x := by
    have hinv := hasDerivAt_inv hne
    simp only [neg_neg] at hinv
    convert hinv using 1
  have h3 : HasDerivAt (fun y => y + y⁻¹) (1 + (-(x^2)⁻¹)) x := h1.add h2
  have h4 : HasDerivAt (fun y => (y + y⁻¹) / 2) ((1 + (-(x^2)⁻¹)) / 2) x := h3.div_const 2
  have h5 : HasDerivAt (fun y => (y + y⁻¹) / 2 - 1) ((1 + (-(x^2)⁻¹)) / 2) x := h4.sub_const 1
  convert h5 using 1

lemma deriv_Jcost {x : ℝ} (hx : 0 < x) :
    deriv Jcost x = JcostDeriv x := (hasDerivAt_Jcost_pos hx).deriv

/-- Second derivative of Jcost: J''(x) = x⁻³ -/
noncomputable def JcostDeriv' (x : ℝ) : ℝ := x ^ (-3 : ℤ)

lemma hasDerivAt_JcostDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt JcostDeriv (JcostDeriv' x) x := by
  -- JcostDeriv x = (1 - x⁻²)/2
  -- JcostDeriv' x = x⁻³
  -- d/dx (1 - x⁻²)/2 = -(-2x⁻³)/2 = x⁻³
  unfold JcostDeriv JcostDeriv'
  have hne : x ≠ 0 := hx.ne'
  have h1 : HasDerivAt (fun y => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have h2 : HasDerivAt (fun y => y ^ (-2 : ℤ)) ((-2 : ℤ) * x ^ (-2 - 1 : ℤ)) x := by
    exact hasDerivAt_zpow (-2) x (Or.inl hne)
  have h3 : HasDerivAt (fun y => 1 - y ^ (-2 : ℤ)) (0 - (-2 : ℤ) * x ^ (-3 : ℤ)) x := h1.sub h2
  have h4 : HasDerivAt (fun y => (1 - y ^ (-2 : ℤ)) / 2) ((0 - (-2 : ℤ) * x ^ (-3 : ℤ)) / 2) x :=
    h3.div_const 2
  convert h4 using 1
  simp only [sub_neg_eq_add, zero_add, Int.cast_neg, Int.cast_ofNat]
  field_simp
  ring

lemma deriv_JcostDeriv {x : ℝ} (hx : 0 < x) :
    deriv JcostDeriv x = JcostDeriv' x := (hasDerivAt_JcostDeriv hx).deriv

/-- Second derivative of Jcost at x > 0: J''(x) = x⁻³ -/
lemma deriv2_Jcost {x : ℝ} (hx : 0 < x) :
    deriv (deriv Jcost) x = x ^ (-3 : ℤ) := by
  have h_event : ∀ᶠ y in nhds x, deriv Jcost y = JcostDeriv y := by
    have h_mem : Set.Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
    filter_upwards [h_mem] with y hy using deriv_Jcost hy
  have h_deriv2 : deriv (deriv Jcost) x = deriv JcostDeriv x :=
    Filter.EventuallyEq.deriv_eq h_event
  rw [h_deriv2, deriv_JcostDeriv hx]
  rfl

/-- Second derivative of Jcost at 1 equals 1: J''(1) = 1 -/
theorem deriv2_Jcost_one : deriv (deriv Jcost) 1 = 1 := by
  rw [deriv2_Jcost one_pos]
  simp

/-- Strict convexity of `Jcost` on `(0, ∞)`. -/
theorem Jcost_strictConvexOn_pos : StrictConvexOn ℝ (Ioi (0 : ℝ)) Jcost := by
  -- A function is strictly convex if its derivative is strictly increasing
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · -- Continuity on (0, ∞)
    unfold Jcost
    apply ContinuousOn.sub
    · apply ContinuousOn.div_const
      apply ContinuousOn.add continuousOn_id
      exact continuousOn_inv₀.mono (fun x hx => ne_of_gt hx)
    · exact continuousOn_const
  · -- Positive second derivative on interior
    intro x hx
    rw [interior_Ioi] at hx
    -- deriv^[2] Jcost x = x⁻³ > 0
    show 0 < deriv^[2] Jcost x
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply]
    -- In a neighborhood of x, deriv Jcost = JcostDeriv
    have h_event : ∀ᶠ y in nhds x, deriv Jcost y = JcostDeriv y := by
      have h_mem : Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
      filter_upwards [h_mem] with y hy using deriv_Jcost hy
    have h_deriv2 : deriv (deriv Jcost) x = deriv JcostDeriv x := Filter.EventuallyEq.deriv_eq h_event
    rw [h_deriv2, deriv_JcostDeriv hx]
    unfold JcostDeriv'
    -- x ^ (-3) > 0 for x > 0
    have hx_pos : 0 < x := hx
    exact zpow_pos hx_pos (-3)

/-- Helper: Jcost on positive reals via composition with exp -/
lemma Jcost_as_composition {x : ℝ} (hx : 0 < x) :
  Jcost x = Jlog (log x) := by
  -- Jlog t = Jcost (exp t), so Jlog (log x) = Jcost (exp (log x)) = Jcost x
  unfold Jlog
  congr 1
  exact (Real.exp_log hx).symm

end Cost
end IndisputableMonolith
