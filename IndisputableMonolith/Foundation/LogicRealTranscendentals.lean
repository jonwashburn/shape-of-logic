import Mathlib
import IndisputableMonolith.Foundation.RealsFromLogic

/-!
  LogicRealTranscendentals.lean

  Transported transcendental functions on `LogicReal`.

  The recovered real line is equivalent to Mathlib's `ℝ` by
  `LogicReal.equivReal`.  This module defines the standard transcendental
  functions by transport through that equivalence and proves the corresponding
  transport lemmas.  This is the right first layer: later modules can reason
  over `LogicReal` while still reducing analytic identities to Mathlib's
  established real-analysis library.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicRealTranscendentals

open RealsFromLogic RealsFromLogic.LogicReal

noncomputable section

/-- Square root on recovered reals, transported from `Real.sqrt`. -/
def sqrtL (x : LogicReal) : LogicReal := fromReal (Real.sqrt (toReal x))

/-- Exponential on recovered reals, transported from `Real.exp`. -/
def expL (x : LogicReal) : LogicReal := fromReal (Real.exp (toReal x))

/-- Natural logarithm on recovered reals, transported from `Real.log`. -/
def logL (x : LogicReal) : LogicReal := fromReal (Real.log (toReal x))

/-- Real power on recovered reals, transported from `Real.rpow`. -/
def rpowL (x y : LogicReal) : LogicReal := fromReal (Real.rpow (toReal x) (toReal y))

/-- The recovered constant π. -/
def piL : LogicReal := fromReal Real.pi

/-- Sine on recovered reals. -/
def sinL (x : LogicReal) : LogicReal := fromReal (Real.sin (toReal x))

/-- Cosine on recovered reals. -/
def cosL (x : LogicReal) : LogicReal := fromReal (Real.cos (toReal x))

/-- Hyperbolic sine on recovered reals. -/
def sinhL (x : LogicReal) : LogicReal := fromReal (Real.sinh (toReal x))

/-- Hyperbolic cosine on recovered reals. -/
def coshL (x : LogicReal) : LogicReal := fromReal (Real.cosh (toReal x))

@[simp] theorem toReal_sqrtL (x : LogicReal) :
    toReal (sqrtL x) = Real.sqrt (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_expL (x : LogicReal) :
    toReal (expL x) = Real.exp (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_logL (x : LogicReal) :
    toReal (logL x) = Real.log (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_rpowL (x y : LogicReal) :
    toReal (rpowL x y) = Real.rpow (toReal x) (toReal y) :=
  toReal_fromReal _

@[simp] theorem toReal_piL : toReal piL = Real.pi :=
  toReal_fromReal _

@[simp] theorem toReal_sinL (x : LogicReal) :
    toReal (sinL x) = Real.sin (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_cosL (x : LogicReal) :
    toReal (cosL x) = Real.cos (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_sinhL (x : LogicReal) :
    toReal (sinhL x) = Real.sinh (toReal x) :=
  toReal_fromReal _

@[simp] theorem toReal_coshL (x : LogicReal) :
    toReal (coshL x) = Real.cosh (toReal x) :=
  toReal_fromReal _

/-- Transported positivity of exponential. -/
theorem expL_pos (x : LogicReal) : (0 : LogicReal) < expL x := by
  rw [lt_iff_toReal_lt, toReal_zero, toReal_expL]
  exact Real.exp_pos _

/-- Transported non-negativity of square root. -/
theorem sqrtL_nonneg (x : LogicReal) : (0 : LogicReal) ≤ sqrtL x := by
  rw [le_iff_toReal_le, toReal_zero, toReal_sqrtL]
  exact Real.sqrt_nonneg _

/-- Transported exponential/log inverse on positive recovered reals. -/
theorem expL_logL {x : LogicReal} (hx : (0 : LogicReal) < x) :
    expL (logL x) = x := by
  rw [eq_iff_toReal_eq, toReal_expL, toReal_logL]
  have hx' : 0 < toReal x := by simpa [lt_iff_toReal_lt] using hx
  exact Real.exp_log hx'

/-- Transported logarithm/exponential inverse. -/
theorem logL_expL (x : LogicReal) : logL (expL x) = x := by
  rw [eq_iff_toReal_eq, toReal_logL, toReal_expL]
  exact Real.log_exp _

/-- Transported hyperbolic cosine definition. -/
theorem coshL_eq_exp (x : LogicReal) :
    coshL x = (expL x + expL (-x)) / fromReal 2 := by
  rw [eq_iff_toReal_eq, toReal_coshL, toReal_div, toReal_add, toReal_expL,
    toReal_expL, toReal_neg, toReal_fromReal]
  exact Real.cosh_eq _

end

end LogicRealTranscendentals
end Foundation
end IndisputableMonolith
