import Mathlib

/-!
# FRW Componentwise Probe (panel-prescribed tractability test)

Standalone probe, per the cosmo-chain panel verdict (2026-07-02): before locking
the full two-layer Friedmann skeleton, verify that the componentwise `Fin 4`
encoding of flat-FRW geometry is convergence-free differential algebra that
`simp` + `deriv` lemmas can actually discharge.

Encoding: homogeneous flat FRW, k = 0, c = 1. Every field depends only on
cosmic time `t`, so spatial partials vanish identically and `∂₀ = deriv`.

Probe goals:
* `Γ⁰ᵢᵢ = a·ȧ`  (the panel's named first probe)
* `Γⁱ₀ᵢ = ȧ/a`

If these close, the full skeleton (Ricci, Einstein tensor, Friedmann I/II from a
named `EinsteinEqns` Prop) gets locked as loop targets. If they stall, re-encode
before locking anything.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology
namespace FRWComponentsProbe

open Real

/-- Flat FRW metric components (diagonal): `g₀₀ = -1`, `gᵢᵢ = a(t)²`. -/
noncomputable def gMetric (a : ℝ → ℝ) (μ ν : Fin 4) : ℝ → ℝ :=
  fun t => if μ = ν then (if μ = 0 then -1 else (a t) ^ 2) else 0

/-- Inverse metric components (diagonal): `g⁰⁰ = -1`, `gⁱⁱ = 1/a(t)²`. -/
noncomputable def gInv (a : ℝ → ℝ) (μ ν : Fin 4) : ℝ → ℝ :=
  fun t => if μ = ν then (if μ = 0 then -1 else 1 / (a t) ^ 2) else 0

/-- Coordinate partial derivative: `∂₀ = d/dt`, spatial partials vanish
(homogeneity). -/
noncomputable def pd (μ : Fin 4) (f : ℝ → ℝ) : ℝ → ℝ :=
  if μ = 0 then deriv f else 0

/-- Christoffel symbols of the second kind,
`Γ^λ_{μν} = ½ Σ_σ g^{λσ} (∂_μ g_{νσ} + ∂_ν g_{μσ} − ∂_σ g_{μν})`. -/
noncomputable def Γ (a : ℝ → ℝ) (l m n : Fin 4) : ℝ → ℝ :=
  fun t => (1 / 2) * ∑ σ : Fin 4,
    gInv a l σ t *
      (pd m (gMetric a n σ) t + pd n (gMetric a m σ) t - pd σ (gMetric a m n) t)

/-- The spatial metric component is `a²` (as a function). -/
@[simp] lemma gMetric_spatial (a : ℝ → ℝ) (i : Fin 4) (hi : i ≠ 0) :
    gMetric a i i = fun t => (a t) ^ 2 := by
  funext t; simp [gMetric, hi]

/-- Off-diagonal metric components vanish. -/
@[simp] lemma gMetric_offdiag (a : ℝ → ℝ) {μ ν : Fin 4} (h : μ ≠ ν) :
    gMetric a μ ν = fun _ => 0 := by
  funext t; simp [gMetric, h]

/-- Time derivative of `a²`: `d(a²)/dt = 2·a·ȧ` (stated in the lambda form the
metric simp lemma produces, so it chains in `simp`). -/
lemma deriv_a_sq (a : ℝ → ℝ) (ha : Differentiable ℝ a) (t : ℝ) :
    deriv (fun t => (a t) ^ 2) t = 2 * a t * deriv a t := by
  rw [show (fun t => (a t) ^ 2) = (fun x : ℝ => x ^ 2) ∘ a from rfl]
  rw [deriv_comp t (differentiable_pow 2).differentiableAt (ha t)]
  simp

/-- **Probe 1**: `Γ⁰₁₁ = a·ȧ`. -/
theorem Γ_0_11 (a : ℝ → ℝ) (ha : Differentiable ℝ a) (t : ℝ) :
    Γ a 0 1 1 t = a t * deriv a t := by
  simp [Γ, gInv, pd, Fin.sum_univ_four, deriv_a_sq a ha]
  ring

/-- **Probe 2**: `Γ¹₀₁ = ȧ·a / a²` (no division-by-zero commitment). -/
theorem Γ_1_01 (a : ℝ → ℝ) (ha : Differentiable ℝ a) (t : ℝ) :
    Γ a 1 0 1 t = deriv a t * a t / (a t) ^ 2 := by
  simp [Γ, gInv, pd, Fin.sum_univ_four, deriv_a_sq a ha,
        gMetric_offdiag a (show (1 : Fin 4) ≠ 2 by decide),
        gMetric_offdiag a (show (1 : Fin 4) ≠ 3 by decide),
        gMetric_offdiag a (show (0 : Fin 4) ≠ 1 by decide)]
  ring

end FRWComponentsProbe
end Cosmology
end Relativity
end IndisputableMonolith
