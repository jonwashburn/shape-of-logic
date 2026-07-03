import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Counterexamples for "∃P" ⇒ d'Alembert

This module documents a simple but important fact:

> The mere existence of *some* combiner `P` satisfying
>   `F(xy) + F(x/y) = P(F(x), F(y))`
> does **not** force the d'Alembert structure for the log-lift of `F`.

In particular, the quadratic log-cost

`F(x) := (log x)^2 / 2`

admits the (additive) combiner

`P(u,v) := 2u + 2v`,

but its shifted log-lift `H(t) := F(exp t) + 1 = t^2/2 + 1` does **not** satisfy
the d'Alembert equation.

This is a structural obstruction: any theorem that claims to force the RCL/d'Alembert
form from the weak hypothesis `∃ P` must add at least one further nondegeneracy axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace Counterexamples

open Real
open IndisputableMonolith.Cost

/-! ## The quadratic log-cost -/

noncomputable def Gquad (t : ℝ) : ℝ := t ^ 2 / 2

noncomputable def Fquad : ℝ → ℝ := Cost.F_ofLog Gquad

noncomputable def Padd (u v : ℝ) : ℝ := 2 * u + 2 * v

lemma Fquad_on_exp (t : ℝ) : Fquad (Real.exp t) = Gquad t := by
  -- log(exp t) = t
  simp [Fquad, Cost.F_ofLog, Gquad]

lemma Fquad_unit0 : Fquad 1 = 0 := by
  simp [Fquad, Cost.F_ofLog, Gquad]

lemma Fquad_symm {x : ℝ} (hx : 0 < x) : Fquad x = Fquad x⁻¹ := by
  -- log(x⁻¹) = -log x for x>0
  simp [Fquad, Cost.F_ofLog, Gquad, Real.log_inv, hx.ne']

/-! ## The weak consistency holds with an additive combiner -/

lemma Fquad_consistency :
    ∀ x y : ℝ, 0 < x → 0 < y →
      Fquad (x * y) + Fquad (x / y) = Padd (Fquad x) (Fquad y) := by
  intro x y hx hy
  -- Work in log-coordinates: let t = log x, u = log y
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  have hlog_mul : Real.log (x * y) = Real.log x + Real.log y := by
    simpa using Real.log_mul hx.ne' hy.ne'
  have hlog_div : Real.log (x / y) = Real.log x - Real.log y := by
    simpa [div_eq_mul_inv, Real.log_mul, Real.log_inv, hy0] using Real.log_div hx.ne' hy.ne'
  -- Now compute
  simp [Fquad, Cost.F_ofLog, Gquad, Padd, hlog_mul, hlog_div]
  ring

/-! ## Calibration holds on the log-lift -/

lemma calib_Fquad : deriv (deriv (fun t : ℝ => Fquad (Real.exp t))) 0 = 1 := by
  -- Fquad(exp t) = t^2/2
  have hfun : (fun t : ℝ => Fquad (Real.exp t)) = fun t => t ^ 2 / 2 := by
    funext t
    simp [Fquad_on_exp, Gquad]
  -- Differentiate twice
  rw [hfun]
  -- First derivative: d/dt (t^2/2) = t
  have hderiv_eq : deriv (fun t : ℝ => t ^ 2 / 2) = fun t => t := by
    funext t
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (HasDerivAt.fun_pow (hasDerivAt_id t) 2)
    have hdiv : HasDerivAt (fun s : ℝ => s ^ 2 / 2) ((2 * t) / 2) t :=
      hpow.div_const 2
    have hcoef : ((2 * t) / 2 : ℝ) = t := by ring
    simpa [hcoef] using hdiv.deriv
  -- Second derivative at 0: d/dt (t) at 0 = 1
  simpa [hderiv_eq] using (hasDerivAt_id (0 : ℝ)).deriv

/-! ## The d'Alembert equation fails for the quadratic log-lift -/

noncomputable def Hquad (t : ℝ) : ℝ := (fun t => Fquad (Real.exp t)) t + 1

lemma Hquad_simp (t : ℝ) : Hquad t = t ^ 2 / 2 + 1 := by
  simp [Hquad, Fquad_on_exp, Gquad]

theorem Hquad_not_dAlembert :
    ¬ (Hquad 0 = 1 ∧ ∀ t u : ℝ, Hquad (t + u) + Hquad (t - u) = 2 * Hquad t * Hquad u) := by
  intro h
  have h0 : Hquad 0 = 1 := h.1
  have hdA := h.2
  -- Evaluate the d'Alembert identity at t = 1, u = 1.
  have h11 := hdA 1 1
  -- Compute both sides explicitly; they disagree (4 ≠ 9/2).
  have hL : Hquad (1 + 1) + Hquad (1 - 1) = 4 := by
    calc
      Hquad (1 + 1) + Hquad (1 - 1)
          = ((1 + 1) ^ 2 / 2 + 1) + ((1 - 1) ^ 2 / 2 + 1) := by
              simp [Hquad_simp]
      _ = 4 := by
            norm_num
  have hR : 2 * Hquad 1 * Hquad 1 = (9 : ℝ) / 2 := by
    simp [Hquad_simp]
    ring
  -- Contradiction
  have : (4 : ℝ) = (9 : ℝ) / 2 := by
    calc (4 : ℝ) = Hquad (1 + 1) + Hquad (1 - 1) := by simpa using hL.symm
      _ = 2 * Hquad 1 * Hquad 1 := h11
      _ = (9 : ℝ) / 2 := hR
  norm_num at this

end Counterexamples
end DAlembert
end Foundation
end IndisputableMonolith
