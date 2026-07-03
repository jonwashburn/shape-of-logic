import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.LogicRealConstants

/-!
  JcostLogic.lean

  The canonical reciprocal cost on recovered reals.

  This is a transport mirror of `Cost.JcostCore`: definitions live on
  `LogicReal`, while theorem proofs reduce to the already-verified real
  theorem surface through `LogicReal.toReal`.
-/

namespace IndisputableMonolith
namespace Cost
namespace JcostLogic

open Foundation.RealsFromLogic
open Foundation.RealsFromLogic.LogicReal

noncomputable section

/-- Canonical reciprocal cost on recovered reals. -/
def JcostL (x : LogicReal) : LogicReal :=
  (x + x⁻¹) / fromReal 2 - fromReal 1

@[simp] theorem toReal_JcostL (x : LogicReal) :
    toReal (JcostL x) = Jcost (toReal x) := by
  simp [JcostL, Jcost, toReal_fromReal]

theorem JcostL_unit0 : JcostL (fromReal 1) = fromReal 0 := by
  rw [eq_iff_toReal_eq, toReal_JcostL, toReal_fromReal, toReal_fromReal]
  exact Jcost_unit0

theorem JcostL_symm {x : LogicReal} (hx : (0 : LogicReal) < x) :
    JcostL x = JcostL x⁻¹ := by
  rw [eq_iff_toReal_eq, toReal_JcostL, toReal_JcostL, toReal_inv]
  have hx' : 0 < toReal x := by simpa [lt_iff_toReal_lt] using hx
  exact Jcost_symm hx'

theorem JcostL_nonneg {x : LogicReal} (hx : (0 : LogicReal) < x) :
    (0 : LogicReal) ≤ JcostL x := by
  rw [le_iff_toReal_le, toReal_zero, toReal_JcostL]
  have hx' : 0 < toReal x := by simpa [lt_iff_toReal_lt] using hx
  exact Jcost_nonneg hx'

theorem JcostL_eq_sq {x : LogicReal} (hx : toReal x ≠ 0) :
    JcostL x = (x - fromReal 1) * (x - fromReal 1) / (fromReal 2 * x) := by
  rw [eq_iff_toReal_eq]
  simp [toReal_JcostL, toReal_fromReal]
  simpa [pow_two] using Jcost_eq_sq hx

theorem JcostL_zero_iff {x : LogicReal} (hx : (0 : LogicReal) < x) :
    JcostL x = fromReal 0 ↔ x = fromReal 1 := by
  constructor
  · intro h
    rw [eq_iff_toReal_eq]
    have hx' : 0 < toReal x := by simpa [lt_iff_toReal_lt] using hx
    have hx0 : toReal x ≠ 0 := ne_of_gt hx'
    have hreal : Jcost (toReal x) = 0 := by
      have := congrArg toReal h
      rwa [toReal_JcostL, toReal_fromReal] at this
    rw [Jcost_eq_sq hx0] at hreal
    have hden : (0 : ℝ) < 2 * toReal x := by nlinarith
    have hsq : (toReal x - 1) ^ 2 = 0 := by
      have := congrArg (fun y : ℝ => y * (2 * toReal x)) hreal
      field_simp [ne_of_gt hden] at this
      simpa using this
    have hsub : toReal x - 1 = 0 := sq_eq_zero_iff.mp hsq
    rw [toReal_fromReal]
    linarith
  · intro h
    rw [h, JcostL_unit0]

/-- Recognition Composition Law on recovered reals for a cost function. -/
def SatisfiesCompositionLawL (F : LogicReal → LogicReal) : Prop :=
  ∀ x y : LogicReal, (0 : LogicReal) < x → (0 : LogicReal) < y →
    F (x * y) + F (x / y)
      = fromReal 2 * F x * F y + fromReal 2 * F x + fromReal 2 * F y

/-- A recovered-real function transported to a real function. -/
def transportCost (F : LogicReal → LogicReal) : ℝ → ℝ :=
  fun x => toReal (F (fromReal x))

/-- Transported RCL: a recovered-real composition law becomes the existing
real composition law under `toReal`. -/
theorem compositionLawL_to_real {F : LogicReal → LogicReal}
    (hF : SatisfiesCompositionLawL F) :
    Cost.FunctionalEquation.SatisfiesCompositionLaw (transportCost F) := by
  intro x y hx hy
  unfold transportCost
  have hxL : (0 : LogicReal) < fromReal x := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hx
  have hyL : (0 : LogicReal) < fromReal y := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hy
  have hxy : fromReal x * fromReal y = fromReal (x * y) := by
    rw [eq_iff_toReal_eq]
    simp [toReal_fromReal]
  have hdiv : fromReal x / fromReal y = fromReal (x / y) := by
    rw [eq_iff_toReal_eq]
    simp [toReal_fromReal]
  have hL := hF (fromReal x) (fromReal y) hxL hyL
  rw [hxy, hdiv] at hL
  have h := congrArg toReal hL
  simpa [toReal_add, toReal_mul, toReal_div, toReal_fromReal] using h

end

end JcostLogic
end Cost
end IndisputableMonolith
