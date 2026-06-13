import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Basic
import IndisputableMonolith.Geometry.CayleyMengerPolynomial

/-!
# Partial Derivatives of the Cayley-Menger Polynomial

This module computes the six partial derivatives `∂CM_3/∂a_i` of the
Cayley-Menger polynomial as explicit polynomial functions of the squared
edge lengths.  The central theorem is the polynomial Taylor identity for
`cm3 (a + h)`, which exposes the gradient, quadratic term, and cubic
remainder directly.  From that identity we derive a uniform
single-coordinate update formula and partial derivative API.

## Why this matters

The Regge second-variation matrix `M_ij` we ultimately compare to
`area(f_ij)` is built from these partial derivatives via the chain rule
through the conformal edge ansatz.  Formal differentiability of `cm3` is
already established in
`CayleyMengerPolynomial.cm3_contDiff`.  The contribution of *this*
module is the explicit closed-form gradient.

## Edge convention

Same as in `CayleyMengerPolynomial.lean`:
  edge 0 = (0,1),   edge 1 = (0,2),   edge 2 = (0,3),
  edge 3 = (1,2),   edge 4 = (1,3),   edge 5 = (2,3).
-/

namespace IndisputableMonolith
namespace Geometry
namespace CayleyMengerDerivatives

open CayleyMengerPolynomial

noncomputable section

/-! ## §1. Closed-form gradient

Each partial of the polynomial

```
CM_3 = 2 · [ α·ν·(β+γ+λ+μ−α−ν)
           + β·μ·(α+γ+λ+ν−β−μ)
           + γ·λ·(α+β+μ+ν−γ−λ)
           − α·β·λ − α·γ·μ − β·γ·ν − λ·μ·ν ]
```

is a quadratic polynomial in the six squared edge lengths.  We list each
partial in fully expanded form for downstream use.
-/

/-- Partial derivative of `cm3` with respect to `a 0` (= α = squared edge (0,1)). -/
def cm3_partial0 (a : SqEdges) : ℝ :=
  2 * ( a 5 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5) - a 0 * a 5
      + a 1 * a 4 + a 2 * a 3
      - a 1 * a 3 - a 2 * a 4 )

/-- Partial derivative of `cm3` with respect to `a 1` (= β = squared edge (0,2)). -/
def cm3_partial1 (a : SqEdges) : ℝ :=
  2 * ( a 4 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4) - a 1 * a 4
      + a 0 * a 5 + a 2 * a 3
      - a 0 * a 3 - a 2 * a 5 )

/-- Partial derivative of `cm3` with respect to `a 2` (= γ = squared edge (0,3)). -/
def cm3_partial2 (a : SqEdges) : ℝ :=
  2 * ( a 3 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3) - a 2 * a 3
      + a 0 * a 5 + a 1 * a 4
      - a 0 * a 4 - a 1 * a 5 )

/-- Partial derivative of `cm3` with respect to `a 3` (= λ = squared edge (1,2)). -/
def cm3_partial3 (a : SqEdges) : ℝ :=
  2 * ( a 2 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3) - a 2 * a 3
      + a 0 * a 5 + a 1 * a 4
      - a 0 * a 1 - a 4 * a 5 )

/-- Partial derivative of `cm3` with respect to `a 4` (= μ = squared edge (1,3)). -/
def cm3_partial4 (a : SqEdges) : ℝ :=
  2 * ( a 1 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4) - a 1 * a 4
      + a 0 * a 5 + a 2 * a 3
      - a 0 * a 2 - a 3 * a 5 )

/-- Partial derivative of `cm3` with respect to `a 5` (= ν = squared edge (2,3)). -/
def cm3_partial5 (a : SqEdges) : ℝ :=
  2 * ( a 0 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5) - a 0 * a 5
      + a 1 * a 4 + a 2 * a 3
      - a 1 * a 2 - a 3 * a 4 )

/-- The gradient packaged as a function `SqEdges → SqEdges`.  At each
basepoint `a`, this is the vector of partial derivatives. -/
def cm3_grad (a : SqEdges) : SqEdges := fun i =>
  match i with
  | ⟨0, _⟩ => cm3_partial0 a
  | ⟨1, _⟩ => cm3_partial1 a
  | ⟨2, _⟩ => cm3_partial2 a
  | ⟨3, _⟩ => cm3_partial3 a
  | ⟨4, _⟩ => cm3_partial4 a
  | ⟨5, _⟩ => cm3_partial5 a
  | ⟨n+6, h⟩ => absurd h (by omega)

/-! ## §3. Polynomial Taylor expansion of `cm3 (a + h) − cm3 a`

Rather than repeat the 1-D `HasDerivAt` proof six times, we exhibit
the full Taylor polynomial of `cm3` around any base point `a`:

```
cm3 (a + h) − cm3 a = ⟨grad cm3 a, h⟩ + Q(a, h) + C(h)
```

where `Q` is degree 2 in `h` and `C` is degree 3 in `h` (with no `a`
dependence).  Once this algebraic identity is established by `ring`,
the Fréchet derivative of `cm3` at `a` is the linear functional
`h ↦ ⟨grad cm3 a, h⟩`.

This algebraic identity is the content of the partial-derivative
formulas; the single-coordinate update formula below is the input for
the derivative and Hessian APIs. -/

/-- The quadratic-in-`h` correction in the Taylor expansion of
`cm3 (a + h)` around `a`.  Explicitly written. -/
def cm3_quadratic (a h : SqEdges) : ℝ :=
  2 * ( h 0 * h 5 * (a 1 + a 2 + a 3 + a 4 - a 0 - a 5)
      + a 0 * h 5 * (h 1 + h 2 + h 3 + h 4 - h 0 - h 5)
      + h 0 * a 5 * (h 1 + h 2 + h 3 + h 4 - h 0 - h 5)
      + h 1 * h 4 * (a 0 + a 2 + a 3 + a 5 - a 1 - a 4)
      + a 1 * h 4 * (h 0 + h 2 + h 3 + h 5 - h 1 - h 4)
      + h 1 * a 4 * (h 0 + h 2 + h 3 + h 5 - h 1 - h 4)
      + h 2 * h 3 * (a 0 + a 1 + a 4 + a 5 - a 2 - a 3)
      + a 2 * h 3 * (h 0 + h 1 + h 4 + h 5 - h 2 - h 3)
      + h 2 * a 3 * (h 0 + h 1 + h 4 + h 5 - h 2 - h 3)
      - a 0 * h 1 * h 3 - h 0 * a 1 * h 3 - h 0 * h 1 * a 3
      - a 0 * h 2 * h 4 - h 0 * a 2 * h 4 - h 0 * h 2 * a 4
      - a 1 * h 2 * h 5 - h 1 * a 2 * h 5 - h 1 * h 2 * a 5
      - a 3 * h 4 * h 5 - h 3 * a 4 * h 5 - h 3 * h 4 * a 5 )

/-- The cubic-in-`h` correction (independent of `a`). -/
def cm3_cubic (h : SqEdges) : ℝ :=
  2 * ( h 0 * h 5 * (h 1 + h 2 + h 3 + h 4 - h 0 - h 5)
      + h 1 * h 4 * (h 0 + h 2 + h 3 + h 5 - h 1 - h 4)
      + h 2 * h 3 * (h 0 + h 1 + h 4 + h 5 - h 2 - h 3)
      - h 0 * h 1 * h 3
      - h 0 * h 2 * h 4
      - h 1 * h 2 * h 5
      - h 3 * h 4 * h 5 )

/-- The "linear in `h`" gradient pairing:
`⟨grad cm3 a, h⟩ = Σ_i (cm3_partial_i a) · h_i`. -/
def cm3_linear (a h : SqEdges) : ℝ :=
  cm3_partial0 a * h 0 + cm3_partial1 a * h 1 + cm3_partial2 a * h 2
    + cm3_partial3 a * h 3 + cm3_partial4 a * h 4 + cm3_partial5 a * h 5

/-- **Polynomial Taylor identity** (algebraic):

`cm3 (a + h) = cm3 a + cm3_linear a h + cm3_quadratic a h + cm3_cubic h`. -/
theorem cm3_taylor (a h : SqEdges) :
    cm3 (fun i => a i + h i) =
      cm3 a + cm3_linear a h + cm3_quadratic a h + cm3_cubic h := by
  unfold cm3 cm3_linear cm3_partial0 cm3_partial1 cm3_partial2
         cm3_partial3 cm3_partial4 cm3_partial5
         cm3_quadratic cm3_cubic
  ring

/-- The single-coordinate perturbation: `singlePerturb i t` is the
`SqEdges`-valued function that is `t` at index `i` and zero elsewhere. -/
def singlePerturb (i : Fin 6) (t : ℝ) : SqEdges :=
  fun j => if j = i then t else 0

theorem singlePerturb_at (i : Fin 6) (t : ℝ) :
    singlePerturb i t i = t := by
  unfold singlePerturb; simp

theorem singlePerturb_ne (i j : Fin 6) (h : j ≠ i) (t : ℝ) :
    singlePerturb i t j = 0 := by
  unfold singlePerturb; simp [h]

/-- A specialised corollary of the Taylor identity: when only the
`i`-th coordinate is perturbed, the formula collapses to the 1-D
restriction of `cm3` along that coordinate.  This is what feeds the
six per-edge partial-derivative theorems. -/
theorem cm3_update_taylor (a : SqEdges) (i : Fin 6) (t : ℝ) :
    cm3 (Function.update a i (a i + t)) =
      cm3 a + (cm3_grad a i) * t
      + cm3_quadratic a (singlePerturb i t) + cm3_cubic (singlePerturb i t) := by
  have hpt : (fun j : Fin 6 => a j + (singlePerturb i t) j)
              = Function.update a i (a i + t) := by
    funext j
    by_cases hij : j = i
    · subst hij
      simp [singlePerturb_at]
    · have h1 : (singlePerturb i t) j = 0 := singlePerturb_ne i j hij t
      have h2 : Function.update a i (a i + t) j = a j := by
        simp [Function.update, hij]
      rw [h1, h2]
      ring
  have h := cm3_taylor a (singlePerturb i t)
  rw [hpt] at h
  rw [h]
  have hlin : cm3_linear a (singlePerturb i t) = cm3_grad a i * t := by
    unfold cm3_linear cm3_grad singlePerturb
    fin_cases i <;> simp [cm3_partial0, cm3_partial1, cm3_partial2,
            cm3_partial3, cm3_partial4, cm3_partial5]
  linarith [hlin]

/-! ## §4. Closed-form quadratic and cubic single-coordinate corrections

The Taylor identity says that the correction `cm3_quadratic a
(singlePerturb i t) + cm3_cubic (singlePerturb i t)` is a polynomial
`α(a, i) t² + β(a, i) t³` in `t` with no constant or linear-in-`t`
term.  We compute the explicit `α, β` per edge `i` so that the per-edge
partial-derivative theorems follow uniformly. -/

/-- Quadratic-in-`t` coefficient of the single-coordinate correction. -/
def cm3_quadratic_coeff : Fin 6 → SqEdges → ℝ
  | 0, a => -2 * a 5
  | 1, a => -2 * a 4
  | 2, a => -2 * a 3
  | 3, a => -2 * a 2
  | 4, a => -2 * a 1
  | 5, a => -2 * a 0

/-- Cubic-in-`t` coefficient of the single-coordinate correction.  In each
case there is no `t³` contribution because the cm3 polynomial is degree 2 in
each *individual* squared-edge coordinate. -/
def cm3_cubic_coeff : Fin 6 → ℝ := fun _ => 0

theorem cm3_quadratic_singlePerturb (a : SqEdges) (i : Fin 6) (t : ℝ) :
    cm3_quadratic a (singlePerturb i t) =
      cm3_quadratic_coeff i a * t ^ 2 := by
  unfold cm3_quadratic singlePerturb cm3_quadratic_coeff
  fin_cases i <;> simp <;> ring

theorem cm3_cubic_singlePerturb (i : Fin 6) (t : ℝ) :
    cm3_cubic (singlePerturb i t) = cm3_cubic_coeff i * t ^ 3 := by
  unfold cm3_cubic singlePerturb cm3_cubic_coeff
  fin_cases i <;> simp

/-- Combined polynomial form of the Taylor expansion in single-coordinate
direction:

```
cm3 (a.update i (a i + t))
  = cm3 a + cm3_grad(a)(i) · t + cm3_quadratic_coeff i a · t² + cm3_cubic_coeff i · t³
```
-/
theorem cm3_update_polyform (a : SqEdges) (i : Fin 6) (t : ℝ) :
    cm3 (Function.update a i (a i + t)) =
      cm3 a + cm3_grad a i * t
        + cm3_quadratic_coeff i a * t ^ 2
        + cm3_cubic_coeff i * t ^ 3 := by
  rw [cm3_update_taylor a i t]
  rw [cm3_quadratic_singlePerturb, cm3_cubic_singlePerturb]

/-! ## §5. Derivative and Hessian API

The update formula writes each one-coordinate restriction of `cm3` as a
shifted cubic polynomial.  Since `cm3_cubic_coeff = 0`, it is actually
quadratic in each individual squared-edge coordinate. -/

/-- Derivative of a shifted cubic polynomial at its base point. -/
private theorem hasDerivAt_shifted_cubic (A B C D x₀ : ℝ) :
    HasDerivAt (fun x : ℝ => A + B * (x - x₀) + C * (x - x₀) ^ 2
      + D * (x - x₀) ^ 3) B x₀ := by
  have hx : HasDerivAt (fun x : ℝ => x - x₀) (1 : ℝ) x₀ := by
    simpa using (hasDerivAt_id x₀).sub_const x₀
  have hconst : HasDerivAt (fun _ : ℝ => A) (0 : ℝ) x₀ := hasDerivAt_const x₀ A
  have hlin : HasDerivAt (fun x : ℝ => B * (x - x₀)) B x₀ := by
    have := hx.const_mul B
    simpa using this
  have hsq_raw := hx.pow 2
  have hsq : HasDerivAt (fun x : ℝ => (x - x₀) ^ 2) (0 : ℝ) x₀ := by
    simpa using hsq_raw
  have hquad : HasDerivAt (fun x : ℝ => C * (x - x₀) ^ 2) (0 : ℝ) x₀ := by
    have := hsq.const_mul C
    simpa using this
  have hcb_raw := hx.pow 3
  have hcb : HasDerivAt (fun x : ℝ => (x - x₀) ^ 3) (0 : ℝ) x₀ := by
    simpa using hcb_raw
  have hcubic : HasDerivAt (fun x : ℝ => D * (x - x₀) ^ 3) (0 : ℝ) x₀ := by
    have := hcb.const_mul D
    simpa using this
  have htotal := ((hconst.add hlin).add hquad).add hcubic
  simpa using htotal

/-- Uniform one-coordinate derivative of the Cayley-Menger polynomial.
The derivative of `t ↦ cm3 (a.update i t)` at `t = a i` is the `i`th
closed-form gradient entry. -/
theorem hasDerivAt_cm3_grad (a : SqEdges) (i : Fin 6) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a i t)) (cm3_grad a i) (a i) := by
  have hfun :
      (fun t : ℝ => cm3 (Function.update a i t)) =
        (fun t : ℝ => cm3 a + cm3_grad a i * (t - a i)
          + cm3_quadratic_coeff i a * (t - a i) ^ 2
          + cm3_cubic_coeff i * (t - a i) ^ 3) := by
    funext t
    have h := cm3_update_polyform a i (t - a i)
    have hbase : a i + (t - a i) = t := by ring
    rw [hbase] at h
    simpa using h
  rw [hfun]
  exact hasDerivAt_shifted_cubic (cm3 a) (cm3_grad a i)
    (cm3_quadratic_coeff i a) (cm3_cubic_coeff i) (a i)

/-- The closed-form `cm3_partial0` is the derivative of `t ↦ cm3 (a.update 0 t)`
at `t = a 0`. -/
theorem hasDerivAt_cm3_partial0 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 0 t)) (cm3_partial0 a) (a 0) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 0

theorem hasDerivAt_cm3_partial1 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 1 t)) (cm3_partial1 a) (a 1) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 1

theorem hasDerivAt_cm3_partial2 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 2 t)) (cm3_partial2 a) (a 2) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 2

theorem hasDerivAt_cm3_partial3 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 3 t)) (cm3_partial3 a) (a 3) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 3

theorem hasDerivAt_cm3_partial4 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 4 t)) (cm3_partial4 a) (a 4) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 4

theorem hasDerivAt_cm3_partial5 (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cm3 (Function.update a 5 t)) (cm3_partial5 a) (a 5) := by
  simpa [cm3_grad] using hasDerivAt_cm3_grad a 5

/-- Hessian diagonal entries with respect to the squared-edge coordinates.
Since `cm3 (a.update i (a i + t))` has quadratic coefficient
`cm3_quadratic_coeff i a`, the second derivative in coordinate `i` is
`2 * cm3_quadratic_coeff i a`. -/
def cm3_hessianDiag (a : SqEdges) (i : Fin 6) : ℝ :=
  2 * cm3_quadratic_coeff i a

/-- The Fréchet derivative of `cm3` at `a`, as Mathlib's canonical
continuous linear map.  The coordinate formulas above identify its
single-coordinate directional derivatives. -/
def cm3GradientCLM (a : SqEdges) : SqEdges →L[ℝ] ℝ :=
  fderiv ℝ cm3 a

/-- `cm3GradientCLM` really is the Fréchet derivative of `cm3`. -/
theorem hasFDerivAt_cm3 (a : SqEdges) :
    HasFDerivAt cm3 (cm3GradientCLM a) a := by
  unfold cm3GradientCLM
  exact ((cm3_contDiff 1).differentiable_one a).hasFDerivAt

/-- The one-coordinate update polynomial, rewritten in Hessian form. -/
theorem cm3_update_hessianForm (a : SqEdges) (i : Fin 6) (t : ℝ) :
    cm3 (Function.update a i (a i + t)) =
      cm3 a + cm3_grad a i * t + (cm3_hessianDiag a i / 2) * t ^ 2 := by
  rw [cm3_update_polyform]
  unfold cm3_hessianDiag cm3_cubic_coeff
  ring

end

end CayleyMengerDerivatives
end Geometry
end IndisputableMonolith
