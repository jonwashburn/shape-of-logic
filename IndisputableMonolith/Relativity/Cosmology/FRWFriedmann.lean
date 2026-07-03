import Mathlib

/-!
# Friedmann Equations from Componentwise FRW Geometry (Target C skeleton)

Panel-prescribed two-layer derivation (cosmo-chain panel verdict, 2026-07-02),
unlocked by the passing tractability probe `FRWComponentsProbe.lean`.

**Layer 1 (geometry)**: flat FRW metric in componentwise `Fin 4` encoding,
Christoffel symbols, Ricci tensor, Ricci scalar, Einstein tensor. All are
finite `Fin 4` sums of time derivatives: convergence-free differential algebra.

**Layer 2 (field equations)**: a named `EinsteinEqns` Prop (the GR input,
honestly a MODEL premise until the Einstein equations themselves are forced
upstream) plus a comoving perfect fluid, from which Friedmann I and II are
*theorems*, not definitions.

This upgrades `Relativity.Cosmology.Friedmann`'s bare `Prop` definitions
(`FriedmannI`, `FriedmannII`) to derived consequences of the Einstein
equations on FRW.

Conventions: signature (-,+,+,+), c = 1, spatial curvature k = 0,
`κ = 8πG`. Ricci: `R_{μν} = ∂_λ Γ^λ_{μν} − ∂_ν Γ^λ_{μλ}
+ Γ^λ_{λσ} Γ^σ_{μν} − Γ^λ_{νσ} Γ^σ_{μλ}`.

Standard results being formalized (all classical GR):
* `Γ⁰ᵢᵢ = a·ȧ`, `Γⁱ₀ᵢ = ȧ/a`, all others zero
* `R₀₀ = −3ä/a`, `Rᵢᵢ = a·ä + 2ȧ²`
* `R = 6(ä/a + (ȧ/a)²)`
* `G₀₀ = 3(ȧ/a)²`, `Gᵢᵢ = −(2a·ä + ȧ²)`
* Friedmann I: `(ȧ/a)² = κρ/3`
* Friedmann II: `ä/a = −κ(ρ + 3p)/6`

STATUS: skeleton with statement-fixed sorries; the cosmo-formalize loop
grinds these. The probe file has working proofs of the two Christoffel
component shapes.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Cosmology
namespace FRWFriedmann

open Real

/-! ## Layer 1: componentwise FRW geometry -/

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

/-- Ricci tensor from Christoffel symbols (componentwise, all sums finite):
`R_{μν} = ∂_λ Γ^λ_{μν} − ∂_ν Γ^λ_{μλ} + Γ^λ_{λσ} Γ^σ_{μν} − Γ^λ_{νσ} Γ^σ_{μλ}`. -/
noncomputable def RicciT (a : ℝ → ℝ) (μ ν : Fin 4) : ℝ → ℝ :=
  fun t =>
    (∑ l : Fin 4, pd l (Γ a l μ ν) t)
    - (∑ l : Fin 4, pd ν (Γ a l μ l) t)
    + (∑ l : Fin 4, ∑ σ : Fin 4, Γ a l l σ t * Γ a σ μ ν t)
    - (∑ l : Fin 4, ∑ σ : Fin 4, Γ a l ν σ t * Γ a σ μ l t)

/-- Ricci scalar `R = g^{μν} R_{μν}`. -/
noncomputable def RicciScalarT (a : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∑ μ : Fin 4, ∑ ν : Fin 4, gInv a μ ν t * RicciT a μ ν t

/-- Einstein tensor `G_{μν} = R_{μν} − ½ g_{μν} R`. -/
noncomputable def EinsteinT (a : ℝ → ℝ) (μ ν : Fin 4) : ℝ → ℝ :=
  fun t => RicciT a μ ν t - (1 / 2) * gMetric a μ ν t * RicciScalarT a t

/-! ## Layer 2: matter and field equations -/

/-- Comoving perfect fluid stress-energy, componentwise:
`T₀₀ = ρ`, `Tᵢᵢ = p·a²`, off-diagonal zero.
(This is `T_{μν} = (ρ+p) u_μ u_ν + p g_{μν}` with `u = ∂_t`.) -/
noncomputable def Tmn (a ρ p : ℝ → ℝ) (μ ν : Fin 4) : ℝ → ℝ :=
  fun t =>
    if μ = 0 ∧ ν = 0 then ρ t
    else if μ = ν then p t * (a t) ^ 2
    else 0

/-- **The GR input (MODEL premise)**: the Einstein field equations hold
componentwise on this FRW background with coupling `κ = 8πG`. Friedmann I/II
are derived FROM this named premise; the premise itself remains the honest
import until the field equations are forced upstream. -/
def EinsteinEqns (a ρ p : ℝ → ℝ) (κ : ℝ) : Prop :=
  ∀ (μ ν : Fin 4) (t : ℝ), EinsteinT a μ ν t = κ * Tmn a ρ p μ ν t

/-! ## Christoffel component values (statement-fixed targets) -/

/-- `d(a²)/dt = 2·a·ȧ`, in the lambda form the metric produces (proved in the
probe file; reproved here so the module is self-contained). -/
lemma deriv_a_sq (a : ℝ → ℝ) (ha : Differentiable ℝ a) (t : ℝ) :
    deriv (fun t => (a t) ^ 2) t = 2 * a t * deriv a t := by
  rw [show (fun t => (a t) ^ 2) = (fun x : ℝ => x ^ 2) ∘ a from rfl]
  rw [deriv_comp t (differentiable_pow 2).differentiableAt (ha t)]
  simp

/-- The `00` metric component is the constant `-1` (as a function). -/
@[simp] lemma gMetric_00 (a : ℝ → ℝ) : gMetric a 0 0 = fun _ => (-1 : ℝ) := by
  funext t; simp [gMetric]

/-- The spatial metric component is `a²` (as a function). -/
@[simp] lemma gMetric_spatial (a : ℝ → ℝ) (i : Fin 4) (hi : i ≠ 0) :
    gMetric a i i = fun t => (a t) ^ 2 := by
  funext t; simp [gMetric, hi]

/-- Off-diagonal metric components vanish. -/
@[simp] lemma gMetric_offdiag (a : ℝ → ℝ) {μ ν : Fin 4} (h : μ ≠ ν) :
    gMetric a μ ν = fun _ => 0 := by
  funext t; simp [gMetric, h]

/-- `Γ⁰₀₀ = 0` (as a function; needed under `deriv` in the Ricci terms). -/
lemma christoffel_0_00 (a : ℝ → ℝ) : Γ a 0 0 0 = fun _ => 0 := by
  funext t
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four]

/-- `Γ⁰₁₁ = a·ȧ` as a function equation (probe proved it pointwise). -/
theorem christoffel_0_11 (a : ℝ → ℝ) (ha : Differentiable ℝ a) :
    Γ a 0 1 1 = fun t => a t * deriv a t := by
  funext t
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  ring

/-- `Γ⁰₂₂ = a·ȧ`. -/
theorem christoffel_0_22 (a : ℝ → ℝ) (ha : Differentiable ℝ a) :
    Γ a 0 2 2 = fun t => a t * deriv a t := by
  funext t
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  ring

/-- `Γ⁰₃₃ = a·ȧ`. -/
theorem christoffel_0_33 (a : ℝ → ℝ) (ha : Differentiable ℝ a) :
    Γ a 0 3 3 = fun t => a t * deriv a t := by
  funext t
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  ring

/-- `Γ¹₀₁ = ȧ/a` (uses `a > 0` to cancel `a/a²`). -/
theorem christoffel_1_01 (a : ℝ → ℝ) (ha : Differentiable ℝ a)
    (hpos : ∀ t, 0 < a t) :
    Γ a 1 0 1 = fun t => deriv a t / a t := by
  funext t
  have hne : a t ≠ 0 := (hpos t).ne'
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  field_simp

/-- `Γ²₀₂ = ȧ/a`. -/
theorem christoffel_2_02 (a : ℝ → ℝ) (ha : Differentiable ℝ a)
    (hpos : ∀ t, 0 < a t) :
    Γ a 2 0 2 = fun t => deriv a t / a t := by
  funext t
  have hne : a t ≠ 0 := (hpos t).ne'
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  field_simp

/-- `Γ³₀₃ = ȧ/a`. -/
theorem christoffel_3_03 (a : ℝ → ℝ) (ha : Differentiable ℝ a)
    (hpos : ∀ t, 0 < a t) :
    Γ a 3 0 3 = fun t => deriv a t / a t := by
  funext t
  have hne : a t ≠ 0 := (hpos t).ne'
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a ha]
  field_simp

/-- Christoffel symbols are symmetric in the lower indices (definitional:
the bracket is symmetric under `m ↔ n`). -/
theorem christoffel_symm (a : ℝ → ℝ) (l m n : Fin 4) :
    Γ a l m n = Γ a l n m := by
  have hg : gMetric a m n = gMetric a n m := by
    by_cases h : m = n
    · subst h; rfl
    · rw [gMetric_offdiag a h, gMetric_offdiag a (Ne.symm h)]
  funext t
  simp only [Γ, hg]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-! ## Derivative helpers (statement-fixed targets) -/

/-- Quotient rule for the Hubble rate:
`d(ȧ/a)/dt = ä/a − (ȧ/a)²` in cleared form. -/
theorem deriv_hubble (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ t, 0 < a t) (t : ℝ) :
    deriv (fun t => deriv a t / a t) t
      = (deriv (deriv a) t * a t - (deriv a t) ^ 2) / (a t) ^ 2 := by
  have h1 : DifferentiableAt ℝ (deriv a) t := ha.differentiable_deriv_two t
  have h2 : DifferentiableAt ℝ a t := (ha.differentiable (by norm_num)) t
  have hne : a t ≠ 0 := (hpos t).ne'
  have hfun : (fun t => deriv a t / a t) = deriv a / a := rfl
  rw [hfun, deriv_div h1 h2 hne]
  ring

/-- Product rule for `a·ȧ`: `d(a·ȧ)/dt = ȧ² + a·ä`. -/
theorem deriv_a_adot (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (t : ℝ) :
    deriv (fun t => a t * deriv a t) t
      = (deriv a t) ^ 2 + a t * deriv (deriv a) t := by
  have h1 : DifferentiableAt ℝ a t := (ha.differentiable (by norm_num)) t
  have h2 : DifferentiableAt ℝ (deriv a) t := ha.differentiable_deriv_two t
  have hfun : (fun t => a t * deriv a t) = a * deriv a := rfl
  rw [hfun, deriv_mul h1 h2]
  ring

/-! ## Ricci and Einstein components (statement-fixed targets) -/

/-- `R₀₀ = −3ä/a`. -/
theorem ricci_00 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    RicciT a 0 0 t = -3 * deriv (deriv a) t / a t := by
  have hd : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [RicciT, Fin.sum_univ_four]
  rw [christoffel_0_00 a, christoffel_1_01 a hd hpos, christoffel_2_02 a hd hpos,
      christoffel_3_03 a hd hpos]
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a hd,
        deriv_hubble a ha hpos]
  field_simp
  ring

/-- `Γ¹₁₀ = ȧ/a` (lower-index symmetric partner, needed pointwise in Ricci). -/
lemma christoffel_1_10 (a : ℝ → ℝ) (ha : Differentiable ℝ a)
    (hpos : ∀ t, 0 < a t) :
    Γ a 1 1 0 = fun t => deriv a t / a t := by
  rw [christoffel_symm a 1 1 0]; exact christoffel_1_01 a ha hpos

/-- `R₁₁ = a·ä + 2ȧ²`. -/
theorem ricci_11 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    RicciT a 1 1 t = a t * deriv (deriv a) t + 2 * (deriv a t) ^ 2 := by
  have hd : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [RicciT, Fin.sum_univ_four]
  rw [christoffel_0_11 a hd]
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a hd,
        deriv_a_adot a ha]
  field_simp
  ring

/-- `R₂₂ = a·ä + 2ȧ²` (helper; same computation as `ricci_11`). -/
lemma ricci_22 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    RicciT a 2 2 t = a t * deriv (deriv a) t + 2 * (deriv a t) ^ 2 := by
  have hd : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [RicciT, Fin.sum_univ_four]
  rw [christoffel_0_22 a hd]
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a hd,
        deriv_a_adot a ha]
  field_simp
  ring

/-- `R₃₃ = a·ä + 2ȧ²` (helper; same computation as `ricci_11`). -/
lemma ricci_33 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    RicciT a 3 3 t = a t * deriv (deriv a) t + 2 * (deriv a t) ^ 2 := by
  have hd : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [RicciT, Fin.sum_univ_four]
  rw [christoffel_0_33 a hd]
  simp [Γ, gInv, pd, gMetric, Fin.sum_univ_four, deriv_a_sq a hd,
        deriv_a_adot a ha]
  field_simp
  ring

/-- Ricci scalar `R = 6(ä/a + (ȧ/a)²)`. -/
theorem ricci_scalar_eq (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ t, 0 < a t) (t : ℝ) :
    RicciScalarT a t
      = 6 * (deriv (deriv a) t / a t + (deriv a t / a t) ^ 2) := by
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [RicciScalarT, Fin.sum_univ_four]
  rw [ricci_00 a ha hpos t, ricci_11 a ha hpos t, ricci_22 a ha hpos t,
      ricci_33 a ha hpos t]
  simp [gInv]
  field_simp
  ring

/-- `G₀₀ = 3(ȧ/a)²` (the Friedmann-I side). -/
theorem einstein_00 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    EinsteinT a 0 0 t = 3 * (deriv a t / a t) ^ 2 := by
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [EinsteinT]
  rw [ricci_00 a ha hpos t, ricci_scalar_eq a ha hpos t]
  simp [gMetric]
  field_simp
  ring

/-- `G₁₁ = −(2a·ä + ȧ²)` (the Friedmann-II side). -/
theorem einstein_11 (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (hpos : ∀ t, 0 < a t)
    (t : ℝ) :
    EinsteinT a 1 1 t = -(2 * a t * deriv (deriv a) t + (deriv a t) ^ 2) := by
  have hne : a t ≠ 0 := (hpos t).ne'
  simp only [EinsteinT]
  rw [ricci_11 a ha hpos t, ricci_scalar_eq a ha hpos t]
  simp [gMetric]
  field_simp
  ring

/-! ## The Friedmann equations as theorems -/

/-- **Friedmann I** from the Einstein equations on FRW:
`(ȧ/a)² = κρ/3`. -/
theorem friedmann_I (a ρ p : ℝ → ℝ) (κ : ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ t, 0 < a t) (hEE : EinsteinEqns a ρ p κ) (t : ℝ) :
    (deriv a t / a t) ^ 2 = κ / 3 * ρ t := by
  have h00 := hEE 0 0 t
  rw [einstein_00 a ha hpos t] at h00
  simp [Tmn] at h00
  linarith

/-- **Friedmann II** (acceleration equation) from the Einstein equations on
FRW: `ä/a = −κ(ρ + 3p)/6`. -/
theorem friedmann_II (a ρ p : ℝ → ℝ) (κ : ℝ) (ha : ContDiff ℝ 2 a)
    (hpos : ∀ t, 0 < a t) (hEE : EinsteinEqns a ρ p κ) (t : ℝ) :
    deriv (deriv a) t / a t = -(κ / 6) * (ρ t + 3 * p t) := by
  have hne : a t ≠ 0 := (hpos t).ne'
  -- 00-equation: 3(ȧ/a)² = κρ, cleared: 3ȧ² = κρa²
  have h00 := hEE 0 0 t
  rw [einstein_00 a ha hpos t] at h00
  simp [Tmn] at h00
  have h00' : 3 * (deriv a t) ^ 2 = κ * ρ t * (a t) ^ 2 := by
    have := h00
    field_simp at this
    linarith
  -- 11-equation: −(2aä + ȧ²) = κ·p·a²
  have h11 := hEE 1 1 t
  rw [einstein_11 a ha hpos t] at h11
  simp [Tmn] at h11
  -- Combine: 2aä = −κpa² − ȧ² = −κpa² − κρa²/3
  have key : deriv (deriv a) t * a t
      = (-(κ / 6) * (ρ t + 3 * p t) * a t) * a t := by
    nlinarith [h00', h11]
  have h2 : deriv (deriv a) t = -(κ / 6) * (ρ t + 3 * p t) * a t :=
    mul_right_cancel₀ hne key
  rw [h2, mul_div_assoc, div_self hne, mul_one]

/-- Certificate bundling the two Friedmann theorems: from the named
`EinsteinEqns` premise (the honest GR import), both Friedmann equations
hold on any positive C² scale factor. -/
theorem friedmannCert :
    ∀ (a ρ p : ℝ → ℝ) (κ : ℝ), ContDiff ℝ 2 a → (∀ t, 0 < a t) →
      EinsteinEqns a ρ p κ →
      (∀ t, (deriv a t / a t) ^ 2 = κ / 3 * ρ t) ∧
      (∀ t, deriv (deriv a) t / a t = -(κ / 6) * (ρ t + 3 * p t)) := by
  intro a ρ p κ ha hpos hEE
  exact ⟨fun t => friedmann_I a ρ p κ ha hpos hEE t,
         fun t => friedmann_II a ρ p κ ha hpos hEE t⟩

end FRWFriedmann
end Cosmology
end Relativity
end IndisputableMonolith
