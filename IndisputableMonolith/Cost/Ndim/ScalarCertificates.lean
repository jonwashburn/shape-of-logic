import IndisputableMonolith.Cost.Ndim.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Non-parallelism and non-flatness certificates for the golden/metallic λ-family

This file proves, by direct scalar computation, the two structural claims of the
"Golden and Metallic" note that are not yet covered elsewhere in the library:

1. **`P_λ` is not parallel** with respect to either the canonical flat connection `D`
   (Theorem 1a, `dP00_ne_zero`) or the Levi-Civita connection `∇^λ` of `h_λ`
   (Theorem 1b, `nablaP000_ne_zero`), on the 2-dimensional slice `α = (1,1)`,
   `t = (t, 0)`, `λ = 1`.
2. **`h_λ` is non-flat** for `λ > 0`: the Riemann tensor component `R^0_{1,0,1}`
   is strictly negative for every `t ≠ 0` (Theorem 2, `R0101Closed_neg`).

## Setup

On the 2-slice with potential `Φ_λ(t₀,t₁) = cosh t₀ + cosh t₁ + λ(cosh(t₀+t₁) - 1)`,
metric `h_λ = D + λ g̃` with `D = diag(cosh t₀, cosh t₁)`, `g̃ = cosh(t₀+t₁) · (1,1)⊗(1,1)`,
and `P_λ = (1/μ_λ) h_λ⁻¹ g̃` the projector onto `span(1,1)`, evaluating at the point
`(t₀, t₁) = (t, 0)` gives (all verified independently by hand and by SymPy against the
Christoffel-derivative ground truth `R^0_101(5/4,3/4,1) = -81/4225`):

* `P^0_0(t,0,1) = 1/(cosh t + 1)` =: `P00 t`
* `∂_0 P^0_0 = -sinh t / (cosh t + 1)^2` =: `dP00 t`
* `(∇^λ)_0 P^0_0 = -sinh t · (cosh t + 3) / (2 (cosh t + 1)^2 (cosh t + 2))` =: `nablaP000 t`
* `R^0_{1,0,1}(t,0,λ) = -λ sinh² t (λ cosh t + 1) / (4 cosh² t (λ cosh t + λ + 1)^2)`
  =: `R0101Closed t λ`

These closed forms are the scalar *certificates*: since each is nonvanishing (resp.
negative) for every `t ≠ 0` (resp. `λ > 0`, `t ≠ 0`), non-parallelism and non-flatness
hold universally on the slice, not just at an isolated point, which avoids ever having
to construct a point with `cosh t = 5/4` inside Lean.

The identification of these scalar closed forms with the actual tensor components of
`h_λ` (via the Hessian/Shima curvature formula for `R^0_{1,0,1}`, and the Christoffel
symbols of `h_λ` for `∇^λ`) is the companion geometric bridge; it is recorded as a
tagged hypothesis-level fact in the module docstring above and is not re-derived here.
This file is the self-contained algebraic core: given the closed forms, it proves the
nonvanishing/negativity, including the one nontrivial derivative computation
(`hasDerivAt_P00`) needed for Theorem 1a.

Reference: "Golden and Metallic" note, Theorems (non-parallelism of `P_λ`) and
(non-flatness of `h_λ` for `λ ≠ 0`).
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

noncomputable section

/-- `P^0_0` at the slice point `(t, 0)`, `α = (1,1)`, `λ = 1`. -/
def P00 (t : ℝ) : ℝ := (Real.cosh t + 1)⁻¹

/-- `∂_0 P^0_0` at the slice point, i.e. the derivative of `P00` w.r.t. the flat
    connection `D` (ordinary differentiation). -/
def dP00 (t : ℝ) : ℝ := -(Real.sinh t) / (Real.cosh t + 1) ^ 2

/-- `(∇^λ)_0 P^0_0` at the slice point, `λ = 1`: the covariant derivative of `P_λ`
    w.r.t. the Levi-Civita connection of `h_λ`. -/
def nablaP000 (t : ℝ) : ℝ :=
  -(Real.sinh t) * (Real.cosh t + 3) / (2 * (Real.cosh t + 1) ^ 2 * (Real.cosh t + 2))

/-- `R^0_{1,0,1}` at the slice point `(t, 0)`, `α = (1,1)`, general `λ`. -/
def R0101Closed (t lam : ℝ) : ℝ :=
  -(lam * (Real.sinh t) ^ 2 * (lam * Real.cosh t + 1)) /
    (4 * (Real.cosh t) ^ 2 * (lam * Real.cosh t + lam + 1) ^ 2)

/-! ### Theorem 1a: `P_λ` is not `D`-parallel -/

/-- `P00` is differentiable with derivative `dP00`, via a single `HasDerivAt.inv`
    applied to `cosh + 1`. -/
theorem hasDerivAt_P00 (t : ℝ) : HasDerivAt P00 (dP00 t) t := by
  have hc : HasDerivAt (fun x => Real.cosh x + 1) (Real.sinh t) t :=
    (Real.hasDerivAt_cosh t).add_const 1
  have hne : Real.cosh t + 1 ≠ 0 := ne_of_gt (by linarith [Real.cosh_pos t])
  simpa [P00, dP00] using hc.inv hne

/-- **Theorem 1a** (non-parallelism of `P_λ` w.r.t. the flat connection `D`):
    the ordinary derivative of the `(0,0)` entry of `P_λ` is nonzero for every `t ≠ 0`.
    Hence `D P_λ ≠ 0`, i.e. `P_λ` is not `D`-parallel. -/
theorem dP00_ne_zero (t : ℝ) (ht : t ≠ 0) : dP00 t ≠ 0 := by
  unfold dP00
  apply div_ne_zero
  · exact neg_ne_zero.mpr (Real.sinh_ne_zero.mpr ht)
  · exact pow_ne_zero 2 (ne_of_gt (by linarith [Real.cosh_pos t]))

/-! ### Theorem 1b: `P_λ` is not `∇^λ`-parallel -/

/-- **Theorem 1b** (non-parallelism of `P_λ` w.r.t. the Levi-Civita connection `∇^λ`):
    the covariant derivative of the `(0,0)` entry of `P_λ` is nonzero for every `t ≠ 0`.
    Hence `∇^λ P_λ ≠ 0`, i.e. `P_λ` is not `∇^λ`-parallel. -/
theorem nablaP000_ne_zero (t : ℝ) (ht : t ≠ 0) : nablaP000 t ≠ 0 := by
  unfold nablaP000
  have hsinh_ne : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  have hc3_ne : Real.cosh t + 3 ≠ 0 := ne_of_gt (by linarith [Real.cosh_pos t])
  apply div_ne_zero
  · exact mul_ne_zero (neg_ne_zero.mpr hsinh_ne) hc3_ne
  · have h1 : (0:ℝ) < Real.cosh t + 1 := by linarith [Real.cosh_pos t]
    have h2 : (0:ℝ) < Real.cosh t + 2 := by linarith [Real.cosh_pos t]
    positivity

/-! ### Theorem 2: `h_λ` is non-flat for `λ > 0` -/

/-- **Theorem 2** (non-flatness of `h_λ`, 2D case): the Riemann tensor component
    `R^0_{1,0,1}` is strictly negative for every `λ > 0` and `t ≠ 0`. Hence `h_λ` is
    not flat. This matches the SymPy-verified value `R^0_101(5/4,3/4,1) = -81/4225`
    (i.e. `R0101Closed t 1 = -81/4225` at `cosh t = 5/4`, `sinh t = 3/4`). -/
theorem R0101Closed_neg (t lam : ℝ) (hlam : 0 < lam) (ht : t ≠ 0) :
    R0101Closed t lam < 0 := by
  unfold R0101Closed
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  have hs_ne : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  have hs2_pos : 0 < (Real.sinh t) ^ 2 := sq_pos_of_ne_zero hs_ne
  have h_lc1 : 0 < lam * Real.cosh t + 1 := by nlinarith
  have h_lc2 : 0 < lam * Real.cosh t + lam + 1 := by nlinarith
  have h_den : 0 < 4 * (Real.cosh t) ^ 2 * (lam * Real.cosh t + lam + 1) ^ 2 := by
    positivity
  have hpos : 0 < lam * (Real.sinh t) ^ 2 * (lam * Real.cosh t + 1) :=
    mul_pos (mul_pos hlam hs2_pos) h_lc1
  have h_num : -(lam * (Real.sinh t) ^ 2 * (lam * Real.cosh t + 1)) < 0 := by linarith
  exact div_neg_of_neg_of_pos h_num h_den

/-! ## General `α = (a, b)`: the panel-greenlit extension

The theorems above are specialized to `α = (1,1)`. This section generalizes both
theorems 1 and 2 to arbitrary `α = (a, b)` with `a ≠ 0`, `b ≠ 0`, on the same slice
`t = (t, 0)`. The closed forms below were derived symbolically (SymPy, differentiating
the general-`α` Hessian `Φ(t₀,t₁) = cosh t₀ + cosh t₁ + λ(cosh(a t₀ + b t₁) - 1)` and
its inverse metric / Christoffel symbols) and checked at `a = b = 1` against `P00`,
`dP00`, `nablaP000`, `R0101Closed` above (difference `0` symbolically). They specialize
to the `α = (1,1)` closed forms exactly at `a = b = 1`, so this section is a strict
generalization, not a parallel development.

* `P00Gen a b t = a² / (a² + b² cosh t)`
* `dP00Gen a b t = -a²b² sinh t / (a² + b² cosh t)²`
* `κGen a b λ t := a²λ cosh(at) + b²λ cosh t · cosh(at) + cosh t` (the shared denominator
  base of the covariant derivative and Riemann closed forms)
* `nablaP000Gen a b λ t = -a²b² sinh t · (κGen + cosh t) / (2(a² + b² cosh t)² · κGen)`
* `R0101Gen a b λ t = -b²λ(b²λ cosh(at) + 1) · sinh t · (a sinh(at)) / (4 κGen²)`
-/

/-- `P^0_0` at the slice point `(t, 0)`, general `α = (a, b)`, `λ = 1`. -/
def P00Gen (a b t : ℝ) : ℝ := a ^ 2 / (a ^ 2 + b ^ 2 * Real.cosh t)

/-- `∂_0 P^0_0` for general `α = (a, b)`. -/
def dP00Gen (a b t : ℝ) : ℝ := -(a ^ 2 * b ^ 2 * Real.sinh t) / (a ^ 2 + b ^ 2 * Real.cosh t) ^ 2

/-- Shared denominator base for the general-`α` covariant-derivative and Riemann
    closed forms: `κ = a²λ cosh(at) + b²λ cosh t · cosh(at) + cosh t`. Always positive
    for `a ≠ 0`, `λ > 0` (each of its three summands is nonnegative and the third is
    strictly positive), so it never contributes a zero to either closed form. -/
def kappaGen (a b lam t : ℝ) : ℝ :=
  a ^ 2 * lam * Real.cosh (a * t) + b ^ 2 * lam * Real.cosh t * Real.cosh (a * t) + Real.cosh t

/-- `(∇^λ)_0 P^0_0` at the slice point, general `α = (a, b)`, general `λ`. -/
def nablaP000Gen (a b lam t : ℝ) : ℝ :=
  -(a ^ 2 * b ^ 2 * Real.sinh t) * (kappaGen a b lam t + Real.cosh t) /
    (2 * (a ^ 2 + b ^ 2 * Real.cosh t) ^ 2 * kappaGen a b lam t)

/-- `R^0_{1,0,1}` at the slice point `(t, 0)`, general `α = (a, b)`, general `λ`. -/
def R0101Gen (a b lam t : ℝ) : ℝ :=
  -(b ^ 2 * lam * (b ^ 2 * lam * Real.cosh (a * t) + 1)) *
    (Real.sinh t * (a * Real.sinh (a * t))) / (4 * kappaGen a b lam t ^ 2)

/-- `κGen` is strictly positive whenever `a ≠ 0` and `λ > 0`: each summand is
    nonnegative (`cosh ≥ 1 > 0` everywhere, `a² > 0`, `b² ≥ 0`, `λ > 0`) and the third,
    `cosh t`, is always strictly positive on its own. -/
theorem kappaGen_pos (a b lam t : ℝ) (ha : a ≠ 0) (hlam : 0 < lam) :
    0 < kappaGen a b lam t := by
  unfold kappaGen
  have ha2 : 0 < a ^ 2 := by positivity
  have h1 : 0 ≤ a ^ 2 * lam * Real.cosh (a * t) := by positivity
  have h2 : 0 ≤ b ^ 2 * lam * Real.cosh t * Real.cosh (a * t) := by positivity
  have h3 : 0 < Real.cosh t := Real.cosh_pos t
  linarith

/-- The sign-of-product cross lemma driving the general-`α` Riemann closed form:
    `sinh t · (a · sinh(at))` is strictly positive for `a ≠ 0`, `t ≠ 0`. Intuitively,
    `sinh` preserves the sign of its argument, and `a · sinh(at)` has the same sign as
    `a · (a·t) = a² t`, i.e. the sign of `t`; so the product has the sign of `t²`,
    always positive. -/
theorem sinh_cross_pos (a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 0) :
    0 < Real.sinh t * (a * Real.sinh (a * t)) := by
  rcases ha.lt_or_gt with ha' | ha' <;> rcases ht.lt_or_gt with ht' | ht'
  · have hat : 0 < a * t := mul_pos_of_neg_of_neg ha' ht'
    have hsat : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.mpr hat
    have hst : Real.sinh t < 0 := Real.sinh_neg_iff.mpr ht'
    have has : a * Real.sinh (a * t) < 0 := mul_neg_of_neg_of_pos ha' hsat
    exact mul_pos_of_neg_of_neg hst has
  · have hat : a * t < 0 := mul_neg_of_neg_of_pos ha' ht'
    have hsat : Real.sinh (a * t) < 0 := Real.sinh_neg_iff.mpr hat
    have hst : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht'
    have has : 0 < a * Real.sinh (a * t) := mul_pos_of_neg_of_neg ha' hsat
    exact mul_pos hst has
  · have hat : a * t < 0 := mul_neg_of_pos_of_neg ha' ht'
    have hsat : Real.sinh (a * t) < 0 := Real.sinh_neg_iff.mpr hat
    have hst : Real.sinh t < 0 := Real.sinh_neg_iff.mpr ht'
    have has : a * Real.sinh (a * t) < 0 := mul_neg_of_pos_of_neg ha' hsat
    exact mul_pos_of_neg_of_neg hst has
  · have hat : 0 < a * t := mul_pos ha' ht'
    have hsat : 0 < Real.sinh (a * t) := Real.sinh_pos_iff.mpr hat
    have hst : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht'
    have has : 0 < a * Real.sinh (a * t) := mul_pos ha' hsat
    exact mul_pos hst has

/-! ### Theorem 1a (general `α`): `P_λ` is not `D`-parallel -/

/-- `P00Gen a b` is differentiable with derivative `dP00Gen a b`. -/
theorem hasDerivAt_P00Gen (a b t : ℝ) (ha : a ≠ 0) :
    HasDerivAt (P00Gen a b) (dP00Gen a b t) t := by
  have hc : HasDerivAt (fun x => a ^ 2 + b ^ 2 * Real.cosh x) (b ^ 2 * Real.sinh t) t := by
    have := (Real.hasDerivAt_cosh t).const_mul (b ^ 2)
    simpa using this.const_add (a ^ 2)
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hne : a ^ 2 + b ^ 2 * Real.cosh t ≠ 0 := by
    have : (0:ℝ) ≤ b ^ 2 * Real.cosh t := by positivity
    linarith
  have hnum : HasDerivAt (fun _ : ℝ => a ^ 2) 0 t := hasDerivAt_const t (a ^ 2)
  have := (hnum.div hc hne)
  simpa [P00Gen, dP00Gen, div_eq_mul_inv] using this |>.congr_deriv (by ring)

/-- **Theorem 1a, general `α`**: the ordinary derivative of the `(0,0)` entry of `P_λ`
    is nonzero for every `t ≠ 0`, `a ≠ 0`, `b ≠ 0`. Hence `D P_λ ≠ 0` for the whole
    `α = (a, b)` family, not just `α = (1,1)`. -/
theorem dP00Gen_ne_zero (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    dP00Gen a b t ≠ 0 := by
  unfold dP00Gen
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hb2 : (0:ℝ) < b ^ 2 := by positivity
  apply div_ne_zero
  · exact neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (ne_of_gt ha2) (ne_of_gt hb2)) (Real.sinh_ne_zero.mpr ht))
  · have hpos : (0:ℝ) < a ^ 2 + b ^ 2 * Real.cosh t := by
      have : (0:ℝ) ≤ b ^ 2 * Real.cosh t := by positivity
      linarith
    exact pow_ne_zero 2 (ne_of_gt hpos)

/-! ### Theorem 1b (general `α`): `P_λ` is not `∇^λ`-parallel -/

/-- **Theorem 1b, general `α`**: the covariant derivative of the `(0,0)` entry of `P_λ`
    is nonzero for every `t ≠ 0`, `a ≠ 0`, `b ≠ 0`, `λ > 0`. -/
theorem nablaP000Gen_ne_zero (a b lam t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hlam : 0 < lam)
    (ht : t ≠ 0) : nablaP000Gen a b lam t ≠ 0 := by
  unfold nablaP000Gen
  have hkap : 0 < kappaGen a b lam t := kappaGen_pos a b lam t ha hlam
  have hc : 0 < Real.cosh t := Real.cosh_pos t
  have ha2 : (0:ℝ) < a ^ 2 := by positivity
  have hb2 : (0:ℝ) < b ^ 2 := by positivity
  have hden_block : (0:ℝ) < a ^ 2 + b ^ 2 * Real.cosh t := by
    have : (0:ℝ) ≤ b ^ 2 * Real.cosh t := by positivity
    linarith
  apply div_ne_zero
  · apply mul_ne_zero
    · exact neg_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (ne_of_gt ha2) (ne_of_gt hb2)) (Real.sinh_ne_zero.mpr ht))
    · exact ne_of_gt (by linarith)
  · exact ne_of_gt (by positivity)

/-! ### Theorem 2 (general `α`): `h_λ` is non-flat for `λ > 0` -/

/-- **Theorem 2, general `α`**: the Riemann tensor component `R^0_{1,0,1}` is strictly
    negative for every `a ≠ 0`, `b ≠ 0`, `λ > 0`, `t ≠ 0`. Hence `h_λ` is non-flat for
    the whole `α = (a, b)` family, not just `α = (1,1)`. Specializes to
    `R0101Closed_neg` at `a = b = 1` (checked symbolically to agree with `R0101Closed`
    there). -/
theorem R0101Gen_neg (a b lam t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hlam : 0 < lam)
    (ht : t ≠ 0) : R0101Gen a b lam t < 0 := by
  unfold R0101Gen
  have hkap : 0 < kappaGen a b lam t := kappaGen_pos a b lam t ha hlam
  have hden : 0 < 4 * kappaGen a b lam t ^ 2 := by positivity
  have hb2 : (0:ℝ) < b ^ 2 := by positivity
  have hfac1 : 0 < b ^ 2 * lam * (b ^ 2 * lam * Real.cosh (a * t) + 1) := by
    have hcoshpos : (0:ℝ) < Real.cosh (a * t) := Real.cosh_pos _
    have : (0:ℝ) < b ^ 2 * lam * Real.cosh (a * t) + 1 := by positivity
    positivity
  have hfac2 : 0 < Real.sinh t * (a * Real.sinh (a * t)) := sinh_cross_pos a t ha ht
  have hnum : -(b ^ 2 * lam * (b ^ 2 * lam * Real.cosh (a * t) + 1)) *
      (Real.sinh t * (a * Real.sinh (a * t))) < 0 := by
    have := mul_pos hfac1 hfac2
    linarith
  exact div_neg_of_neg_of_pos hnum hden

/-- Sanity check: `R0101Gen` specializes to `R0101Closed` at `a = b = 1` (verified
    symbolically via SymPy; the two closed forms agree identically as functions of
    `t, λ`, confirming this section is a genuine generalization). -/
example (t lam : ℝ) : R0101Gen 1 1 lam t = R0101Closed t lam := by
  unfold R0101Gen R0101Closed kappaGen
  simp only [one_pow, one_mul]
  ring_nf

end

end Ndim
end Cost
end IndisputableMonolith
