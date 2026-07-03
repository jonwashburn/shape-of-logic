import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor

namespace IndisputableMonolith
namespace Relativity
namespace Calculus

open scoped Topology
open Filter Real

/-- Standard basis vector `e_μ`. -/
def basisVec (μ : Fin 4) : Fin 4 → ℝ := fun ν => if ν = μ then 1 else 0

@[simp] lemma basisVec_self (μ : Fin 4) : basisVec μ μ = 1 := by simp [basisVec]

@[simp] lemma basisVec_ne {μ ν : Fin 4} (h : ν ≠ μ) : basisVec μ ν = 0 := by
  simp [basisVec, h]

/-- Coordinate ray `x + t e_μ`. -/
def coordRay (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) : Fin 4 → ℝ :=
  fun ν => x ν + t * basisVec μ ν

@[simp] lemma coordRay_apply (x : Fin 4 → ℝ) (μ : Fin 4) (t : ℝ) (ν : Fin 4) :
    coordRay x μ t ν = x ν + t * basisVec μ ν := rfl

@[simp] lemma coordRay_zero (x : Fin 4 → ℝ) (μ : Fin 4) : coordRay x μ 0 = x := by
  funext ν; simp [coordRay]

@[simp] lemma coordRay_coordRay (x : Fin 4 → ℝ) (μ : Fin 4) (s t : ℝ) :
    coordRay (coordRay x μ s) μ t = coordRay x μ (s + t) := by
  funext ν; simp [coordRay]; ring

/-- Directional derivative `∂_μ f(x)` via real derivative along the coordinate ray. -/
noncomputable def partialDeriv_v2 (f : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun t => f (coordRay x μ t)) 0

/-- The derivative of a constant function is zero. -/
lemma partialDeriv_v2_const {f : (Fin 4 → ℝ) → ℝ} {c : ℝ} (h : ∀ y, f y = c) (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 f μ x = 0 := by
  unfold partialDeriv_v2
  have h_const : (fun t => f (coordRay x μ t)) = (fun _ => c) := by
    funext t
    rw [h]
  rw [h_const]
  exact deriv_const (0 : ℝ) c

/-- Second derivative `∂_μ∂_ν f(x)` as iterated directional derivatives. -/
noncomputable def secondDeriv (f : (Fin 4 → ℝ) → ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ) : ℝ :=
  deriv (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0

/-- Laplacian `∇² = Σ_{i=1}^3 ∂²/∂xᵢ²`. -/
noncomputable def laplacian (f : (Fin 4 → ℝ) → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  secondDeriv f ⟨1, by decide⟩ ⟨1, by decide⟩ x +
  secondDeriv f ⟨2, by decide⟩ ⟨2, by decide⟩ x +
  secondDeriv f ⟨3, by decide⟩ ⟨3, by decide⟩ x

/-- Linearity of the directional derivative. -/
lemma deriv_add_lin (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => f y + g y) μ x =
    partialDeriv_v2 f μ x + partialDeriv_v2 g μ x := by
  unfold partialDeriv_v2
  exact deriv_add hf hg

/-- Linearity of directional derivative (scalar multiplication). -/
lemma partialDeriv_v2_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => c * f y) μ x = c * partialDeriv_v2 f μ x := by
  unfold partialDeriv_v2
  exact deriv_const_mul c hf

/-- Localized version of second derivative linearity (scalar multiplication).
    This only requires differentiability in a neighborhood of the point x. -/
lemma secondDeriv_smul_local (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ)
    (h1 : ∀ᶠ s in 𝓝 0, DifferentiableAt ℝ (fun t => f (coordRay (coordRay x ν s) μ t)) 0)
    (h2 : DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  secondDeriv (fun y => c * f y) μ ν x = c * secondDeriv f μ ν x := by
  unfold secondDeriv
  have h_ev : ∀ᶠ s in 𝓝 0, partialDeriv_v2 (fun z => c * f z) μ (coordRay x ν s) =
                          c * partialDeriv_v2 f μ (coordRay x ν s) := by
    apply h1.mono
    intro s hs
    exact partialDeriv_v2_smul f c μ (coordRay x ν s) hs
  rw [Filter.EventuallyEq.deriv_eq h_ev]
  exact deriv_const_mul c h2

/-- Second derivative linearity (scalar multiplication). -/
lemma secondDeriv_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (μ ν : Fin 4)
    (x : Fin 4 → ℝ)
    (h1 : ∀ y, DifferentiableAt ℝ (fun t => f (coordRay y μ t)) 0)
    (h2 : DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  secondDeriv (fun y => c * f y) μ ν x = c * secondDeriv f μ ν x := by
  unfold secondDeriv
  have h_partial : ∀ y, partialDeriv_v2 (fun z => c * f z) μ y = c * partialDeriv_v2 f μ y := by
    intro y
    exact partialDeriv_v2_smul f c μ y (h1 y)
  simp only [h_partial]
  exact deriv_const_mul c h2

/-- Laplacian linearity (scalar multiplication). -/
lemma laplacian_smul (f : (Fin 4 → ℝ) → ℝ) (c : ℝ) (x : Fin 4 → ℝ)
    (h1 : ∀ μ y, DifferentiableAt ℝ (fun t => f (coordRay y μ t)) 0)
    (h2 : ∀ μ ν, DifferentiableAt ℝ (fun s => partialDeriv_v2 f μ (coordRay x ν s)) 0) :
  laplacian (fun y => c * f y) x = c * laplacian f x := by
  unfold laplacian
  simp only [secondDeriv_smul f c _ _ x (h1 _) (h2 _ _)]
  ring

/-- Product rule for directional derivative. -/
lemma partialDeriv_v2_mul (f g : (Fin 4 → ℝ) → ℝ) (μ : Fin 4)
    (x : Fin 4 → ℝ) (hf : DifferentiableAt ℝ (fun t => f (coordRay x μ t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (coordRay x μ t)) 0) :
  partialDeriv_v2 (fun y => f y * g y) μ x =
    f x * partialDeriv_v2 g μ x + g x * partialDeriv_v2 f μ x := by
  unfold partialDeriv_v2
  have h_mul : deriv (fun ε => f (coordRay x μ ε) * g (coordRay x μ ε)) 0 =
               deriv (fun ε => f (coordRay x μ ε)) 0 * g (coordRay x μ 0) +
               f (coordRay x μ 0) * deriv (fun ε => g (coordRay x μ ε)) 0 :=
    deriv_mul hf hg
  rw [h_mul]
  simp only [coordRay_zero]
  ring

/-- Spatial norm squared `x₁² + x₂² + x₃²`. -/
def spatialNormSq (x : Fin 4 → ℝ) : ℝ := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2

theorem spatialNormSq_nonneg (x : Fin 4 → ℝ) : 0 ≤ spatialNormSq x := by
  unfold spatialNormSq
  positivity

theorem spatialNormSq_eq_zero_iff (x : Fin 4 → ℝ) : spatialNormSq x = 0 ↔ x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := by
  unfold spatialNormSq
  constructor
  · intro h
    have h1 := sq_nonneg (x 1)
    have h2 := sq_nonneg (x 2)
    have h3 := sq_nonneg (x 3)
    have h1_zero : x 1 ^ 2 = 0 := by linarith
    have h2_zero : x 2 ^ 2 = 0 := by linarith
    have h3_zero : x 3 ^ 2 = 0 := by linarith
    simp only [sq_eq_zero_iff] at h1_zero h2_zero h3_zero
    exact ⟨h1_zero, h2_zero, h3_zero⟩
  · intro h
    simp [h]

/-- Spatial radius `r = √(x₁² + x₂² + x₃²)`. -/
noncomputable def spatialRadius (x : Fin 4 → ℝ) : ℝ := Real.sqrt (spatialNormSq x)

theorem spatialRadius_pos_iff (x : Fin 4 → ℝ) : 0 < spatialRadius x ↔ 0 < spatialNormSq x := by
  unfold spatialRadius
  rw [Real.sqrt_pos]

theorem spatialRadius_ne_zero_iff (x : Fin 4 → ℝ) : spatialRadius x ≠ 0 ↔ spatialNormSq x ≠ 0 := by
  unfold spatialRadius
  rw [Real.sqrt_ne_zero (spatialNormSq_nonneg x)]

/-- Nonzero spatial radius is automatically positive. -/
theorem spatialRadius_pos_of_ne_zero (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    0 < spatialRadius x := by
  have h_ne : spatialNormSq x ≠ 0 := (spatialRadius_ne_zero_iff x).mp hx
  exact (spatialRadius_pos_iff x).2 (lt_of_le_of_ne (spatialNormSq_nonneg x) h_ne.symm)

/-- Temporal coordinate ray doesn't change spatial components. -/
lemma coordRay_temporal_spatial (x : Fin 4 → ℝ) (s : ℝ) (i : Fin 4) (hi : i ≠ 0) :
    (coordRay x 0 s) i = x i := by
  simp [coordRay, basisVec, hi]

/-- spatialNormSq is invariant under temporal coordinate ray. -/
lemma spatialNormSq_coordRay_temporal (x : Fin 4 → ℝ) (s : ℝ) :
    spatialNormSq (coordRay x 0 s) = spatialNormSq x := by
  unfold spatialNormSq
  have h1 : (coordRay x 0 s) 1 = x 1 := coordRay_temporal_spatial x s 1 (by decide)
  have h2 : (coordRay x 0 s) 2 = x 2 := coordRay_temporal_spatial x s 2 (by decide)
  have h3 : (coordRay x 0 s) 3 = x 3 := coordRay_temporal_spatial x s 3 (by decide)
  rw [h1, h2, h3]

/-- spatialRadius is invariant under temporal coordinate ray. -/
lemma spatialRadius_coordRay_temporal (x : Fin 4 → ℝ) (s : ℝ) :
    spatialRadius (coordRay x 0 s) = spatialRadius x := by
  unfold spatialRadius
  rw [spatialNormSq_coordRay_temporal]

/-- For any spatial index `i ∈ {1,2,3}`, `x_i² ≤ spatialNormSq x`. -/
private lemma sq_le_spatialNormSq_1 (x : Fin 4 → ℝ) :
    x 1 ^ 2 ≤ spatialNormSq x := by
  unfold spatialNormSq; nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]

private lemma sq_le_spatialNormSq_2 (x : Fin 4 → ℝ) :
    x 2 ^ 2 ≤ spatialNormSq x := by
  unfold spatialNormSq; nlinarith [sq_nonneg (x 1), sq_nonneg (x 3)]

private lemma sq_le_spatialNormSq_3 (x : Fin 4 → ℝ) :
    x 3 ^ 2 ≤ spatialNormSq x := by
  unfold spatialNormSq; nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]

/-- Helper: closed form of `spatialNormSq (coordRay x j s)` when `j` is a fixed
    spatial index. The sum changes only at index `j`, where `x j` becomes `x j + s`. -/
private lemma spatialNormSq_coordRay_spatial_1 (x : Fin 4 → ℝ) (s : ℝ) :
    spatialNormSq (coordRay x 1 s) = (x 1 + s) ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  unfold spatialNormSq coordRay basisVec
  rw [if_pos (rfl : (1 : Fin 4) = 1),
      if_neg (by decide : (2 : Fin 4) ≠ 1),
      if_neg (by decide : (3 : Fin 4) ≠ 1)]
  ring

private lemma spatialNormSq_coordRay_spatial_2 (x : Fin 4 → ℝ) (s : ℝ) :
    spatialNormSq (coordRay x 2 s) = x 1 ^ 2 + (x 2 + s) ^ 2 + x 3 ^ 2 := by
  unfold spatialNormSq coordRay basisVec
  rw [if_neg (by decide : (1 : Fin 4) ≠ 2),
      if_pos (rfl : (2 : Fin 4) = 2),
      if_neg (by decide : (3 : Fin 4) ≠ 2)]
  ring

private lemma spatialNormSq_coordRay_spatial_3 (x : Fin 4 → ℝ) (s : ℝ) :
    spatialNormSq (coordRay x 3 s) = x 1 ^ 2 + x 2 ^ 2 + (x 3 + s) ^ 2 := by
  unfold spatialNormSq coordRay basisVec
  rw [if_neg (by decide : (1 : Fin 4) ≠ 3),
      if_neg (by decide : (2 : Fin 4) ≠ 3),
      if_pos (rfl : (3 : Fin 4) = 3)]
  ring

/-- `spatialRadius` stays nonzero under sufficiently small coordinate perturbations.

    Quantitative version: if `r = spatialRadius x ≠ 0` and `|s| < r/2`, then the
    perturbed point `coordRay x ν s = x + s · e_ν` still has nonzero spatial radius.

    Proof: case-split on `ν ∈ {0,1,2,3}`.
    - `ν = 0`: temporal direction, `spatialRadius (coordRay x 0 s) = spatialRadius x` (proved).
    - `ν ∈ {1,2,3}`: only the `ν`-th spatial component changes by `s`, so
      `spatialNormSq (coordRay x ν s) = ‖x‖² + 2 s · x_ν + s²`. Using `|x_ν| ≤ r`
      and `|s| < r/2`, the polynomial lower bound `(r - |s|)² ≤ ‖x‖² + 2 s x_ν + s²`
      gives `spatialNormSq > 0` and hence `spatialRadius ≠ 0`.

    Closes one of the §XXIII.B′ Mathlib calculus axioms. -/
theorem spatialRadius_coordRay_ne_zero (x : Fin 4 → ℝ) (ν : Fin 4) (s : ℝ)
    (hx : spatialRadius x ≠ 0) (hs : |s| < spatialRadius x / 2) :
    spatialRadius (coordRay x ν s) ≠ 0 := by
  rw [spatialRadius_ne_zero_iff]
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero x hx
  have hr_sq : spatialRadius x ^ 2 = spatialNormSq x := by
    unfold spatialRadius; rw [Real.sq_sqrt (spatialNormSq_nonneg x)]
  have h_s_lo : -(spatialRadius x / 2) < s := (abs_lt.mp hs).1
  have h_s_hi : s < spatialRadius x / 2 := (abs_lt.mp hs).2
  have h_x1_le : x 1 ^ 2 ≤ spatialRadius x ^ 2 := hr_sq ▸ sq_le_spatialNormSq_1 x
  have h_x2_le : x 2 ^ 2 ≤ spatialRadius x ^ 2 := hr_sq ▸ sq_le_spatialNormSq_2 x
  have h_x3_le : x 3 ^ 2 ≤ spatialRadius x ^ 2 := hr_sq ▸ sq_le_spatialNormSq_3 x
  -- Case split on ν using its underlying ℕ.
  obtain ⟨k, hk⟩ := ν
  match k, hk with
  | 0, _ =>
    rw [show ((⟨0, by decide⟩ : Fin 4) = (0 : Fin 4)) from rfl,
        spatialNormSq_coordRay_temporal]
    exact (spatialRadius_ne_zero_iff x).mp hx
  | 1, _ =>
    rw [show ((⟨1, by decide⟩ : Fin 4) = (1 : Fin 4)) from rfl,
        spatialNormSq_coordRay_spatial_1]
    intro h_zero
    have h_sq1 : (x 1 + s) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1 + s), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h_sq2 : x 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1 + s), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h_sq3 : x 3 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1 + s), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h_eq1 : x 1 + s = 0 := sq_eq_zero_iff.mp h_sq1
    have h_eq2 : x 2 = 0 := sq_eq_zero_iff.mp h_sq2
    have h_eq3 : x 3 = 0 := sq_eq_zero_iff.mp h_sq3
    have h_sn_eq : spatialNormSq x = s ^ 2 := by
      show x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = s ^ 2
      have h_x1 : x 1 = -s := by linarith
      rw [h_x1, h_eq2, h_eq3]; ring
    have h_r_sq_eq_s_sq : spatialRadius x ^ 2 = s ^ 2 := by rw [hr_sq, h_sn_eq]
    -- r > 0 and r² = s², so r = √(s²) = |s|. Then |s| < r/2 = |s|/2 contradicts |s| ≥ 0 ∧ r > 0.
    have h_r_eq_abs : spatialRadius x = |s| := by
      have h_pos : 0 ≤ spatialRadius x := le_of_lt hr_pos
      have h_abs_pos : 0 ≤ |s| := abs_nonneg s
      have h_eq : Real.sqrt (spatialRadius x ^ 2) = Real.sqrt (s ^ 2) := by
        rw [h_r_sq_eq_s_sq]
      rw [Real.sqrt_sq h_pos] at h_eq
      rw [show s ^ 2 = |s| ^ 2 from (sq_abs s).symm, Real.sqrt_sq h_abs_pos] at h_eq
      exact h_eq
    rw [h_r_eq_abs] at hs
    linarith [abs_nonneg s]
  | 2, _ =>
    rw [show ((⟨2, by decide⟩ : Fin 4) = (2 : Fin 4)) from rfl,
        spatialNormSq_coordRay_spatial_2]
    intro h_zero
    have h_sq1 : x 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2 + s), sq_nonneg (x 3)]
    have h_sq2 : (x 2 + s) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2 + s), sq_nonneg (x 3)]
    have h_sq3 : x 3 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2 + s), sq_nonneg (x 3)]
    have h_eq1 : x 1 = 0 := sq_eq_zero_iff.mp h_sq1
    have h_eq2 : x 2 + s = 0 := sq_eq_zero_iff.mp h_sq2
    have h_eq3 : x 3 = 0 := sq_eq_zero_iff.mp h_sq3
    have h_sn_eq : spatialNormSq x = s ^ 2 := by
      show x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = s ^ 2
      have h_x2 : x 2 = -s := by linarith
      rw [h_eq1, h_x2, h_eq3]; ring
    have h_r_sq_eq_s_sq : spatialRadius x ^ 2 = s ^ 2 := by rw [hr_sq, h_sn_eq]
    have h_r_eq_abs : spatialRadius x = |s| := by
      have h_pos : 0 ≤ spatialRadius x := le_of_lt hr_pos
      have h_abs_pos : 0 ≤ |s| := abs_nonneg s
      have h_eq : Real.sqrt (spatialRadius x ^ 2) = Real.sqrt (s ^ 2) := by
        rw [h_r_sq_eq_s_sq]
      rw [Real.sqrt_sq h_pos] at h_eq
      rw [show s ^ 2 = |s| ^ 2 from (sq_abs s).symm, Real.sqrt_sq h_abs_pos] at h_eq
      exact h_eq
    rw [h_r_eq_abs] at hs
    linarith [abs_nonneg s]
  | 3, _ =>
    rw [show ((⟨3, by decide⟩ : Fin 4) = (3 : Fin 4)) from rfl,
        spatialNormSq_coordRay_spatial_3]
    intro h_zero
    have h_sq1 : x 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3 + s)]
    have h_sq2 : x 2 ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3 + s)]
    have h_sq3 : (x 3 + s) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3 + s)]
    have h_eq1 : x 1 = 0 := sq_eq_zero_iff.mp h_sq1
    have h_eq2 : x 2 = 0 := sq_eq_zero_iff.mp h_sq2
    have h_eq3 : x 3 + s = 0 := sq_eq_zero_iff.mp h_sq3
    have h_sn_eq : spatialNormSq x = s ^ 2 := by
      show x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = s ^ 2
      have h_x3 : x 3 = -s := by linarith
      rw [h_eq1, h_eq2, h_x3]; ring
    have h_r_sq_eq_s_sq : spatialRadius x ^ 2 = s ^ 2 := by rw [hr_sq, h_sn_eq]
    have h_r_eq_abs : spatialRadius x = |s| := by
      have h_pos : 0 ≤ spatialRadius x := le_of_lt hr_pos
      have h_abs_pos : 0 ≤ |s| := abs_nonneg s
      have h_eq : Real.sqrt (spatialRadius x ^ 2) = Real.sqrt (s ^ 2) := by
        rw [h_r_sq_eq_s_sq]
      rw [Real.sqrt_sq h_pos] at h_eq
      rw [show s ^ 2 = |s| ^ 2 from (sq_abs s).symm, Real.sqrt_sq h_abs_pos] at h_eq
      exact h_eq
    rw [h_r_eq_abs] at hs
    linarith [abs_nonneg s]

/-- Radial inverse function `1/r^n` where r is the spatial radius.
    Used for gravitational potentials. -/
noncomputable def radialInv (n : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  1 / (spatialRadius x) ^ n

/-- Differentiability of a coordinate ray component. -/
theorem differentiableAt_coordRay_i (x : Fin 4 → ℝ) (μ i : Fin 4) :
    DifferentiableAt ℝ (fun t => (coordRay x μ t) i) 0 := by
  simp only [coordRay_apply]
  apply DifferentiableAt.add
  · apply differentiableAt_const
  · apply DifferentiableAt.mul
    · apply differentiableAt_id
    · apply differentiableAt_const

/-- Differentiability of a squared coordinate ray component. -/
theorem differentiableAt_coordRay_i_sq (x : Fin 4 → ℝ) (μ i : Fin 4) :
    DifferentiableAt ℝ (fun t => (coordRay x μ t) i ^ 2) 0 := by
  apply DifferentiableAt.pow (differentiableAt_coordRay_i x μ i) 2

/-- Closed form for ∂μ (xᵢ²). -/
theorem partialDeriv_v2_x_sq (μ i : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 (fun y => y i ^ 2) μ x = 2 * x i * (if i = μ then 1 else 0) := by
  unfold partialDeriv_v2
  simp only [coordRay_apply]
  let f_i := fun t => x i + t * basisVec μ i
  have h_f : DifferentiableAt ℝ f_i 0 := differentiableAt_coordRay_i x μ i
  rw [show (fun t => (x i + t * basisVec μ i) ^ 2) = f_i ^ 2 by rfl]
  rw [deriv_pow h_f 2]
  simp only [f_i]
  split_ifs with h_eq
  · subst h_eq
    simp only [basisVec_self, mul_one]
    rw [deriv_const_add, deriv_id'']
    ring
  · simp only [basisVec_ne h_eq, mul_zero, add_zero]
    rw [deriv_const]
    ring

theorem deriv_coordRay_i (x : Fin 4 → ℝ) (i : Fin 4) :
    deriv (fun t => (coordRay x i t) i) 0 = 1 := by
  simp only [coordRay_apply, basisVec_self, mul_one]
  rw [deriv_const_add, deriv_id'']

theorem deriv_coordRay_j (x : Fin 4 → ℝ) (i j : Fin 4) (h : j ≠ i) :
    deriv (fun t => (coordRay x i t) j) 0 = 0 := by
  simp only [coordRay_apply, basisVec_ne h, mul_zero, add_zero]
  exact deriv_const 0 (x j)

/-- **THEOREM**: Functional derivative of spatialNormSq.
    ∂_μ (∑ x_i²) = 2 x_μ for μ ∈ {1,2,3}, else 0.

    **Derivation**: Using the chain rule and ∂_μ(x_i²) = 2x_i δ_{iμ}, we get:
    ∂_μ(x₁² + x₂² + x₃²) = 2x₁δ_{1μ} + 2x₂δ_{2μ} + 2x₃δ_{3μ} = 2x_μ for μ ∈ {1,2,3}. -/
theorem partialDeriv_v2_spatialNormSq (μ : Fin 4) (x : Fin 4 → ℝ) :
    partialDeriv_v2 spatialNormSq μ x =
    if μ = 0 then 0 else 2 * x μ := by
  -- Each component x_i² gives 2x_i δ_{iμ}
  have hd1 := partialDeriv_v2_x_sq μ 1 x
  have hd2 := partialDeriv_v2_x_sq μ 2 x
  have hd3 := partialDeriv_v2_x_sq μ 3 x
  -- Enumerate all 4 cases for μ
  fin_cases μ <;> simp_all [partialDeriv_v2, spatialNormSq, coordRay_apply, basisVec, deriv_const_add]

/-- Differentiability of spatialNormSq along a coordinate ray. -/
theorem differentiableAt_coordRay_spatialNormSq (x : Fin 4 → ℝ) (μ : Fin 4) :
    DifferentiableAt ℝ (fun t => spatialNormSq (coordRay x μ t)) 0 := by
  unfold spatialNormSq
  apply DifferentiableAt.add
  · apply DifferentiableAt.add
    · exact differentiableAt_coordRay_i_sq x μ 1
    · exact differentiableAt_coordRay_i_sq x μ 2
  · exact differentiableAt_coordRay_i_sq x μ 3

/-- Differentiability of spatialRadius along a coordinate ray. -/
theorem differentiableAt_coordRay_spatialRadius (x : Fin 4 → ℝ) (μ : Fin 4) (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun t => spatialRadius (coordRay x μ t)) 0 := by
  unfold spatialRadius
  have h_sn_ne_zero : spatialNormSq (coordRay x μ 0) ≠ 0 := by
    simp only [coordRay_zero]
    exact (spatialRadius_ne_zero_iff x).mp hx
  apply DifferentiableAt.sqrt (differentiableAt_coordRay_spatialNormSq x μ) h_sn_ne_zero

/-- Differentiability of radialInv along a coordinate ray. -/
theorem differentiableAt_coordRay_radialInv (n : ℕ) (x : Fin 4 → ℝ) (μ : Fin 4) (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun t => radialInv n (coordRay x μ t)) 0 := by
  unfold radialInv
  apply DifferentiableAt.div (differentiableAt_const (1 : ℝ))
  · apply DifferentiableAt.pow (differentiableAt_coordRay_spatialRadius x μ hx)
  · have h_pos : 0 < spatialRadius x := by
      unfold spatialRadius
      apply Real.sqrt_pos.mpr
      have h_nonneg := spatialNormSq_nonneg x
      have h_ne_zero := (spatialRadius_ne_zero_iff x).mp hx
      exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
    simp only [coordRay_zero]
    exact (pow_pos h_pos n).ne'

theorem spatialRadius_coordRay_ne_zero_eventually {x : Fin 4 → ℝ} (hx : spatialRadius x ≠ 0) (μ : Fin 4) :
    ∀ᶠ t in 𝓝 0, spatialRadius (coordRay x μ t) ≠ 0 := by
  have h_cont : Continuous (fun t => spatialRadius (coordRay x μ t)) := by
    unfold spatialRadius spatialNormSq coordRay basisVec
    fun_prop
  apply h_cont.continuousAt.eventually_ne
  simp [coordRay_zero, hx]

/-- Directional derivative of `spatialRadius` in coordinates.

    For temporal direction (μ = 0), the spatial radius is invariant along the
    coordinate ray, so the derivative is 0. For a spatial direction (μ ≠ 0),
    we compose the chain rule for `Real.sqrt` (Mathlib `HasDerivAt.sqrt`)
    with the derivative `∂_μ ‖x‖² = 2 x_μ` (lifted from
    `partialDeriv_v2_spatialNormSq`), giving `(2 x_μ) / (2 √‖x‖²) = x_μ / r`.

    Closes one of the seven §XXIII.B′ Mathlib calculus axioms. -/
theorem partialDeriv_v2_spatialRadius (μ : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    partialDeriv_v2 spatialRadius μ x =
    if μ = 0 then 0 else x μ / spatialRadius x := by
  by_cases hμ : μ = 0
  · -- Temporal direction: `spatialRadius` is invariant along `coordRay x 0 _`.
    simp only [hμ, ↓reduceIte]
    unfold partialDeriv_v2
    have h : ∀ t, spatialRadius (coordRay x 0 t) = spatialRadius x :=
      spatialRadius_coordRay_temporal x
    simp_rw [h]
    exact deriv_const 0 _
  · -- Spatial direction: chain rule for `Real.sqrt`.
    simp only [hμ, ↓reduceIte]
    unfold partialDeriv_v2 spatialRadius
    -- `spatialNormSq x ≠ 0` since `spatialRadius x ≠ 0`.
    have h_sn_ne : spatialNormSq x ≠ 0 := (spatialRadius_ne_zero_iff x).mp hx
    -- Differentiability of `t ↦ ‖coordRay x μ t‖²` at 0.
    have h_sn_da : DifferentiableAt ℝ (fun t => spatialNormSq (coordRay x μ t)) 0 :=
      differentiableAt_coordRay_spatialNormSq x μ
    -- Its derivative at 0 is `2 x_μ` (from `partialDeriv_v2_spatialNormSq`).
    have h_sn_deriv : deriv (fun t => spatialNormSq (coordRay x μ t)) 0 = 2 * x μ := by
      have := partialDeriv_v2_spatialNormSq μ x
      simp only [partialDeriv_v2, hμ, ↓reduceIte] at this
      exact this
    -- Lift to `HasDerivAt`.
    have h_sn_hda : HasDerivAt (fun t => spatialNormSq (coordRay x μ t)) (2 * x μ) 0 := by
      have : HasDerivAt (fun t => spatialNormSq (coordRay x μ t))
          (deriv (fun t => spatialNormSq (coordRay x μ t)) 0) 0 := h_sn_da.hasDerivAt
      simpa [h_sn_deriv] using this
    -- Value at 0 needed for `HasDerivAt.sqrt`.
    have h_sn_eq_at_0 : spatialNormSq (coordRay x μ 0) = spatialNormSq x := by
      simp [coordRay_zero]
    -- Apply Mathlib's chain rule for sqrt.
    have h_sqrt_hda : HasDerivAt (fun t => Real.sqrt (spatialNormSq (coordRay x μ t)))
        (2 * x μ / (2 * Real.sqrt (spatialNormSq (coordRay x μ 0)))) 0 :=
      h_sn_hda.sqrt (by rw [h_sn_eq_at_0]; exact h_sn_ne)
    rw [h_sqrt_hda.deriv, h_sn_eq_at_0]
    -- Goal: `2 x_μ / (2 √‖x‖²) = x_μ / √‖x‖²`.
    have hr_ne : Real.sqrt (spatialNormSq x) ≠ 0 :=
      fun h => h_sn_ne (Real.sqrt_eq_zero (spatialNormSq_nonneg x) |>.mp h)
    field_simp

/-- Directional derivative of `radialInv` in coordinates.

    For temporal direction (μ = 0), `radialInv` is invariant along the ray,
    so the derivative is 0. For a spatial direction (μ ≠ 0), we use the quotient
    rule `HasDerivAt.div` on `1 / r^n`, composing with `HasDerivAt.pow` and
    the derivative `∂_μ r = x_μ / r` (lifted from `partialDeriv_v2_spatialRadius`).

    Closes one of the six remaining §XXIII.B′ Mathlib calculus axioms. -/
theorem partialDeriv_v2_radialInv (n : ℕ) (μ : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    partialDeriv_v2 (radialInv n) μ x =
    if μ = 0 then 0 else - (n : ℝ) * x μ / (spatialRadius x) ^ (n + 2) := by
  unfold partialDeriv_v2 radialInv
  by_cases hμ : μ = 0
  · simp only [hμ, ↓reduceIte]
    have h : ∀ t, spatialRadius (coordRay x 0 t) = spatialRadius x :=
      spatialRadius_coordRay_temporal x
    have h2 : (fun t => 1 / spatialRadius (coordRay x 0 t) ^ n) =
              (fun _ => 1 / spatialRadius x ^ n) := by
      funext t; rw [h]
    simp_rw [h2]; exact deriv_const 0 _
  · simp only [hμ, ↓reduceIte]
    cases n with
    | zero => simp
    | succ k =>
      have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero x hx
      have h_r_da : DifferentiableAt ℝ (fun t => spatialRadius (coordRay x μ t)) 0 :=
        differentiableAt_coordRay_spatialRadius x μ hx
      have h_r_pow_da : DifferentiableAt ℝ (fun t => spatialRadius (coordRay x μ t) ^ (k + 1)) 0 :=
        h_r_da.pow (k + 1)
      have h_r_pow_ne : spatialRadius (coordRay x μ 0) ^ (k + 1) ≠ 0 := by
        simp only [coordRay_zero]
        exact pow_ne_zero (k + 1) hx
      have h_r_deriv : deriv (fun t => spatialRadius (coordRay x μ t)) 0 = x μ / spatialRadius x := by
        have := partialDeriv_v2_spatialRadius μ x hx
        simp only [partialDeriv_v2, hμ, ↓reduceIte] at this
        exact this
      have h_r_hda : HasDerivAt (fun t => spatialRadius (coordRay x μ t)) (x μ / spatialRadius x) 0 := by
        have : HasDerivAt (fun t => spatialRadius (coordRay x μ t))
            (deriv (fun t => spatialRadius (coordRay x μ t)) 0) 0 := h_r_da.hasDerivAt
        simpa [h_r_deriv] using this
      have h_rpow_hda : HasDerivAt (fun t => spatialRadius (coordRay x μ t) ^ (k + 1))
          (↑(k + 1) * spatialRadius x ^ k * (x μ / spatialRadius x)) 0 := by
        have h1 := h_r_hda.pow (k + 1)
        simp only [coordRay_zero] at h1
        convert h1 using 2
      have h_rinv_hda : HasDerivAt (fun t => (spatialRadius (coordRay x μ t) ^ (k + 1))⁻¹)
          (-(↑(k + 1) * spatialRadius x ^ k * (x μ / spatialRadius x)) /
             (spatialRadius x ^ (k + 1)) ^ 2) 0 := by
        have h2 := h_rpow_hda.inv h_r_pow_ne
        simp only [coordRay_zero] at h2
        exact h2
      have h_inv : (fun t => 1 / spatialRadius (coordRay x μ t) ^ (k + 1)) = fun t => (spatialRadius (coordRay x μ t) ^ (k + 1))⁻¹ := by funext t; exact one_div _
      rw [h_inv, h_rinv_hda.deriv]
      have hr_ne : spatialRadius x ≠ 0 := hx
      have h_pow1 : (spatialRadius x ^ (k + 1)) ^ 2 = spatialRadius x ^ (2 * k + 2) := by
        rw [← pow_mul]; congr 1; omega
      have h_pow2 : k + 1 + 2 = k + 3 := by omega
      rw [div_eq_div_iff]
      · change -(↑(k + 1) * spatialRadius x ^ k * (x μ / spatialRadius x)) * spatialRadius x ^ (k + 1 + 2) = -↑(k + 1) * x μ * (spatialRadius x ^ (k + 1)) ^ 2
        rw [h_pow1]
        rw [h_pow2]
        calc -(↑(k + 1) * spatialRadius x ^ k * (x μ / spatialRadius x)) * spatialRadius x ^ (k + 3)
          _ = -(↑(k + 1) * spatialRadius x ^ k * (x μ * (spatialRadius x)⁻¹)) * spatialRadius x ^ (k + 3) := by rw [div_eq_mul_inv]
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ k * (spatialRadius x)⁻¹ * spatialRadius x ^ (k + 3)) := by ring
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ k * spatialRadius x ^ (k + 3) * (spatialRadius x)⁻¹) := by ring
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ (2 * k + 3) * (spatialRadius x)⁻¹) := by
            have : spatialRadius x ^ k * spatialRadius x ^ (k + 3) = spatialRadius x ^ (2 * k + 3) := by rw [← pow_add]; congr 1; omega
            rw [this]
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ (2 * k + 2) * spatialRadius x * (spatialRadius x)⁻¹) := by
            have : spatialRadius x ^ (2 * k + 2) * spatialRadius x = spatialRadius x ^ (2 * k + 3) := by
              calc spatialRadius x ^ (2 * k + 2) * spatialRadius x
                _ = spatialRadius x ^ (2 * k + 2) * spatialRadius x ^ 1 := by rw [pow_one]
                _ = spatialRadius x ^ (2 * k + 2 + 1) := by rw [← pow_add]
                _ = spatialRadius x ^ (2 * k + 3) := by rfl
            rw [← this]
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ (2 * k + 2) * (spatialRadius x * (spatialRadius x)⁻¹)) := by ring
          _ = -↑(k + 1) * x μ * (spatialRadius x ^ (2 * k + 2) * 1) := by rw [mul_inv_cancel₀ hr_ne]
          _ = -↑(k + 1) * x μ * spatialRadius x ^ (2 * k + 2) := by ring
      · exact pow_ne_zero 2 (pow_ne_zero (k + 1) hr_ne)
      · exact pow_ne_zero (k + 1 + 2) hr_ne

/-- Differentiability of `s ↦ ∂(1/r^n)/∂x_μ` along a coordinate ray.

    For temporal direction (μ = 0), `partialDeriv_v2 (radialInv n) 0 y = 0` whenever
    `spatialRadius y ≠ 0`, so the function is locally constant 0 near `s = 0`.

    For spatial direction (μ ≠ 0), `partialDeriv_v2 (radialInv n) μ y =
    -n · y_μ / r(y)^(n+2)` whenever `spatialRadius y ≠ 0`, so the function is
    locally a quotient of differentiable functions:
    - numerator `s ↦ -n · (coordRay x ν s)_μ` is linear in `s`
    - denominator `s ↦ r(coordRay x ν s)^(n+2)` is the `(n+2)`-power of the
      already-proved differentiable `s ↦ r(coordRay x ν s)`
    - denominator is nonzero at `s = 0` since `r(x) ≠ 0`.

    Closes one of the §XXIII.B′ Mathlib calculus axioms. -/
theorem differentiableAt_coordRay_partialDeriv_v2_radialInv
    (n : ℕ) (x : Fin 4 → ℝ) (μ ν : Fin 4) (hx : spatialRadius x ≠ 0) :
    DifferentiableAt ℝ (fun s => partialDeriv_v2 (radialInv n) μ (coordRay x ν s)) 0 := by
  by_cases hμ : μ = 0
  · -- Temporal: `partialDeriv_v2 (radialInv n) 0 y = 0` for `r y ≠ 0`,
    -- so the function is eventually 0 near `s = 0`.
    apply (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq
    apply (spatialRadius_coordRay_ne_zero_eventually hx ν).mono
    intro s hs
    show partialDeriv_v2 (radialInv n) μ (coordRay x ν s) = 0
    rw [partialDeriv_v2_radialInv n μ (coordRay x ν s) hs]
    simp [hμ]
  · -- Spatial: smooth quotient formula `-n · x_μ / r^(n+2)` is differentiable,
    -- and `partialDeriv_v2` agrees with it where `r ≠ 0`.
    have h_num_diff : DifferentiableAt ℝ
        (fun s : ℝ => -(n : ℝ) * (coordRay x ν s) μ) 0 :=
      (differentiableAt_coordRay_i x ν μ).const_mul (-(n : ℝ))
    have h_denom_diff : DifferentiableAt ℝ
        (fun s : ℝ => spatialRadius (coordRay x ν s) ^ (n + 2)) 0 :=
      (differentiableAt_coordRay_spatialRadius x ν hx).pow _
    have h_denom_ne : spatialRadius (coordRay x ν 0) ^ (n + 2) ≠ 0 := by
      simp only [coordRay_zero]; exact pow_ne_zero (n + 2) hx
    have h_smooth_diff : DifferentiableAt ℝ
        (fun s : ℝ => -(n : ℝ) * (coordRay x ν s) μ /
                      (spatialRadius (coordRay x ν s)) ^ (n + 2)) 0 :=
      h_num_diff.div h_denom_diff h_denom_ne
    apply h_smooth_diff.congr_of_eventuallyEq
    apply (spatialRadius_coordRay_ne_zero_eventually hx ν).mono
    intro s hs
    show partialDeriv_v2 (radialInv n) μ (coordRay x ν s) =
         -(n : ℝ) * (coordRay x ν s) μ / (spatialRadius (coordRay x ν s)) ^ (n + 2)
    rw [partialDeriv_v2_radialInv n μ (coordRay x ν s) hs]
    simp [hμ]

/-- Second directional derivative of `radialInv n`:
    `∂_ν ∂_μ (1/r^n) = n · ((n+2) x_μ x_ν / r^{n+4} - δ_{μν} / r^{n+2})` for `μ, ν ∈ {1,2,3}`,
    and `0` whenever either index is `0` (temporal).

    Proof structure:
    - `μ = 0`: `partialDeriv_v2 (radialInv n) 0 = 0` (already proved), so the outer derivative
      is `deriv 0 = 0`.
    - `μ ≠ 0, ν = 0`: spatial partial derivative is invariant along the temporal ray
      (since both `x_μ` and `r` are unchanged), so the outer derivative is `deriv const = 0`.
    - `μ, ν ≠ 0`: apply the quotient rule `HasDerivAt.div` to the smooth formula
      `-n · x_μ / r^{n+2}`, then simplify the resulting algebraic expression
      `(f' g - f g') / g²` to match the target. The simplification uses
      `r^{n+2-1} = r^{n+1}` (natural-number subtraction), `(r^{n+2})² = r^{2(n+2)} = r^{n+4} · r^n`,
      and `field_simp` plus `ring` to clear denominators.

    Closes one of the §XXIII.B′ Mathlib calculus axioms. -/
theorem secondDeriv_radialInv (n : ℕ) (μ ν : Fin 4) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    secondDeriv (radialInv n) μ ν x =
    if μ = 0 ∨ ν = 0 then 0 else
      (n : ℝ) *
        ((n + 2 : ℝ) * x μ * x ν / (spatialRadius x) ^ (n + 4) -
          (if μ = ν then 1 else 0) / (spatialRadius x) ^ (n + 2)) := by
  unfold secondDeriv
  by_cases hμ : μ = 0
  · -- μ = 0: outer function is eventually 0.
    simp only [hμ, true_or, ↓reduceIte]
    have h_ev : (fun s => partialDeriv_v2 (radialInv n) 0 (coordRay x ν s)) =ᶠ[𝓝 0]
                (fun _ => (0 : ℝ)) := by
      apply (spatialRadius_coordRay_ne_zero_eventually hx ν).mono
      intro s hs
      show partialDeriv_v2 (radialInv n) 0 (coordRay x ν s) = 0
      rw [partialDeriv_v2_radialInv n 0 (coordRay x ν s) hs]
      simp
    rw [h_ev.deriv_eq]; exact deriv_const 0 _
  · by_cases hν : ν = 0
    · -- μ ≠ 0, ν = 0: outer function is constant in s.
      simp only [hν, hμ, false_or, ↓reduceIte, or_true]
      have h_const : ∀ s, partialDeriv_v2 (radialInv n) μ (coordRay x 0 s) =
                          partialDeriv_v2 (radialInv n) μ x := by
        intro s
        have hr_s : spatialRadius (coordRay x 0 s) = spatialRadius x :=
          spatialRadius_coordRay_temporal x s
        have h_coord : (coordRay x 0 s) μ = x μ := coordRay_temporal_spatial x s μ hμ
        have hr_ne_s : spatialRadius (coordRay x 0 s) ≠ 0 := by rw [hr_s]; exact hx
        rw [partialDeriv_v2_radialInv n μ (coordRay x 0 s) hr_ne_s,
            partialDeriv_v2_radialInv n μ x hx]
        simp only [hμ, ↓reduceIte]
        rw [hr_s, h_coord]
      simp_rw [h_const]
      exact deriv_const 0 _
    · -- Main case: μ ≠ 0 and ν ≠ 0.
      simp only [hμ, hν, false_or, ↓reduceIte]
      have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero x hx
      have hr_ne : spatialRadius x ≠ 0 := hx
      -- Near 0, the outer function equals the smooth formula `-n · y_μ / r(y)^(n+2)`.
      have h_ev : (fun s => partialDeriv_v2 (radialInv n) μ (coordRay x ν s)) =ᶠ[𝓝 0]
                  (fun s => -(n : ℝ) * (coordRay x ν s) μ /
                            (spatialRadius (coordRay x ν s)) ^ (n + 2)) := by
        apply (spatialRadius_coordRay_ne_zero_eventually hx ν).mono
        intro s hs
        show partialDeriv_v2 (radialInv n) μ (coordRay x ν s) =
             -(n : ℝ) * (coordRay x ν s) μ /
             (spatialRadius (coordRay x ν s)) ^ (n + 2)
        rw [partialDeriv_v2_radialInv n μ (coordRay x ν s) hs]
        simp [hμ]
      rw [h_ev.deriv_eq]
      -- Compute deriv via HasDerivAt.div on the smooth formula.
      -- Numerator: c(s) = -n · (x_μ + s · δ_{μ,ν}); c(0) = -n · x_μ; c'(0) = -n · δ_{μ,ν}.
      have h_num_hda : HasDerivAt (fun s => -(n : ℝ) * (coordRay x ν s) μ)
          (-(n : ℝ) * basisVec ν μ) 0 := by
        simp only [coordRay_apply]
        have h_inner : HasDerivAt (fun s => x μ + s * basisVec ν μ) (basisVec ν μ) 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (basisVec ν μ)).const_add (x μ)
          simpa using this
        exact h_inner.const_mul (-(n : ℝ))
      -- Denominator inner: r(coordRay x ν s); deriv at 0 is `x_ν / r`.
      have h_r_da : DifferentiableAt ℝ (fun s => spatialRadius (coordRay x ν s)) 0 :=
        differentiableAt_coordRay_spatialRadius x ν hx
      have h_r_deriv : deriv (fun s => spatialRadius (coordRay x ν s)) 0 =
                       x ν / spatialRadius x := by
        have := partialDeriv_v2_spatialRadius ν x hx
        simp only [partialDeriv_v2, hν, ↓reduceIte] at this
        exact this
      have h_r_hda : HasDerivAt (fun s => spatialRadius (coordRay x ν s))
          (x ν / spatialRadius x) 0 := by
        have := h_r_da.hasDerivAt
        simpa [h_r_deriv] using this
      -- Denominator: g(s) = r(coordRay x ν s)^(n+2); g(0) = r^(n+2);
      -- g'(0) = (n+2) · r^(n+1) · (x_ν / r) (note `n + 2 - 1 = n + 1` via Nat subtraction).
      have h_den_hda : HasDerivAt (fun s => (spatialRadius (coordRay x ν s)) ^ (n + 2))
          ((n + 2 : ℕ) * spatialRadius x ^ (n + 2 - 1) * (x ν / spatialRadius x)) 0 := by
        have h := h_r_hda.pow (n + 2)
        simp only [coordRay_zero] at h
        exact h
      have h_den_ne : (spatialRadius (coordRay x ν 0)) ^ (n + 2) ≠ 0 := by
        simp only [coordRay_zero]; exact pow_ne_zero (n + 2) hr_ne
      -- Apply the quotient rule.
      have h_quot : HasDerivAt
          (fun s => -(n : ℝ) * (coordRay x ν s) μ /
                    (spatialRadius (coordRay x ν s)) ^ (n + 2))
          ((-(n : ℝ) * basisVec ν μ * spatialRadius x ^ (n + 2) -
              -(n : ℝ) * x μ *
                (↑(n + 2) * spatialRadius x ^ (n + 2 - 1) * (x ν / spatialRadius x))) /
            (spatialRadius x ^ (n + 2)) ^ 2) 0 := by
        have h := h_num_hda.div h_den_hda h_den_ne
        simp only [coordRay_zero] at h
        exact h
      rw [h_quot.deriv]
      -- Algebraic finish.
      -- Step 1: Reduce `r^(n+2-1)` (Nat subtraction) to `r^(n+1)`.
      have h_n_sub : n + 2 - 1 = n + 1 := by omega
      rw [h_n_sub]
      -- Step 2: Identify `basisVec ν μ` with `if μ = ν then 1 else 0` (definitional).
      have h_basisVec : basisVec ν μ = if μ = ν then 1 else 0 := rfl
      rw [h_basisVec]
      -- Step 3: Prepare power identities for the final ring step.
      have h_r_pow_ne : ∀ k, spatialRadius x ^ k ≠ 0 := fun k => pow_ne_zero k hr_ne
      have h_pow_succ_1 : spatialRadius x ^ (n + 1) = spatialRadius x ^ n * spatialRadius x := by
        rw [pow_succ]
      have h_pow_succ_2 : spatialRadius x ^ (n + 2) =
                          spatialRadius x ^ n * spatialRadius x * spatialRadius x := by
        rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ, h_pow_succ_1]
      have h_pow_n_plus_4 : spatialRadius x ^ (n + 4) =
                            spatialRadius x ^ n * spatialRadius x * spatialRadius x *
                            spatialRadius x * spatialRadius x := by
        rw [show n + 4 = ((n + 2) + 1) + 1 from rfl, pow_succ, pow_succ, h_pow_succ_2]
      -- Step 4: Clear denominators (field_simp), then use power identities and ring.
      field_simp
      rw [h_pow_succ_1, h_pow_succ_2, h_pow_n_plus_4]
      push_cast
      ring

/-- Laplacian of `1/r` vanishes (the radial inverse is harmonic away from the origin).

    `∇²(1/r) = ∂₁²(1/r) + ∂₂²(1/r) + ∂₃²(1/r)`.
    Each diagonal second-derivative is `3 x_i² / r^5 - 1/r^3` from `secondDeriv_radialInv` at `n = 1`.
    The sum is `3 ‖x‖² / r^5 - 3/r^3 = 3 r² / r^5 - 3/r^3 = 3/r^3 - 3/r^3 = 0`.

    Closes one of the §XXIII.B′ Mathlib calculus axioms. -/
theorem laplacian_radialInv_zero_no_const
    (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    laplacian (radialInv 1) x = 0 := by
  unfold laplacian
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero x hx
  -- Use `(1 : Fin 4)`, `(2 : Fin 4)`, `(3 : Fin 4)` to match `spatialNormSq` syntactically.
  have h1 := secondDeriv_radialInv 1 (1 : Fin 4) (1 : Fin 4) x hx
  have h2 := secondDeriv_radialInv 1 (2 : Fin 4) (2 : Fin 4) x hx
  have h3 := secondDeriv_radialInv 1 (3 : Fin 4) (3 : Fin 4) x hx
  simp only [show ((1 : Fin 4) ≠ 0) from by decide,
             show ((2 : Fin 4) ≠ 0) from by decide,
             show ((3 : Fin 4) ≠ 0) from by decide,
             or_self, ↓reduceIte] at h1 h2 h3
  -- The `laplacian` definition uses `⟨i, _⟩ : Fin 4` form, but these are defeq to `(i : Fin 4)`.
  -- Convert via `show` to align indices.
  show secondDeriv (radialInv 1) (1 : Fin 4) (1 : Fin 4) x +
       secondDeriv (radialInv 1) (2 : Fin 4) (2 : Fin 4) x +
       secondDeriv (radialInv 1) (3 : Fin 4) (3 : Fin 4) x = 0
  rw [h1, h2, h3]
  -- Algebraic finish: 3 (x₁² + x₂² + x₃²)/r^5 - 3/r^3 = 0 since x₁² + x₂² + x₃² = r².
  have hr_sq : spatialRadius x ^ 2 = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
    unfold spatialRadius
    rw [Real.sq_sqrt (spatialNormSq_nonneg x)]; rfl
  have h_pow5 : spatialRadius x ^ 5 = spatialRadius x ^ 3 * spatialRadius x ^ 2 := by
    rw [← pow_add]
  have h_r3_ne : spatialRadius x ^ 3 ≠ 0 := pow_ne_zero 3 hx
  have h_r5_ne : spatialRadius x ^ 5 ≠ 0 := pow_ne_zero 5 hx
  field_simp
  rw [h_pow5, hr_sq]
  ring

/-- Laplacian of `1/r^n` for general `n`:
    `∇²(1/r^n) = n(n-1)/r^(n+2)` (away from the origin).

    Sum of diagonal `secondDeriv_radialInv n i i x` over `i ∈ {1,2,3}`:
    `n · ((n+2) ‖x‖² / r^(n+4) - 3/r^(n+2)) = n · ((n+2)/r^(n+2) - 3/r^(n+2))`
    `= n(n-1)/r^(n+2)` (using `‖x‖² = r²`).

    Closes one of the §XXIII.B′ Mathlib calculus axioms. -/
theorem laplacian_radialInv_n
    (n : ℕ) (x : Fin 4 → ℝ) (hx : spatialRadius x ≠ 0) :
    laplacian (radialInv n) x =
    (n : ℝ) * ((n : ℝ) - 1) / (spatialRadius x) ^ (n + 2) := by
  unfold laplacian
  have hr_pos : 0 < spatialRadius x := spatialRadius_pos_of_ne_zero x hx
  have h1 := secondDeriv_radialInv n (1 : Fin 4) (1 : Fin 4) x hx
  have h2 := secondDeriv_radialInv n (2 : Fin 4) (2 : Fin 4) x hx
  have h3 := secondDeriv_radialInv n (3 : Fin 4) (3 : Fin 4) x hx
  simp only [show ((1 : Fin 4) ≠ 0) from by decide,
             show ((2 : Fin 4) ≠ 0) from by decide,
             show ((3 : Fin 4) ≠ 0) from by decide,
             or_self, ↓reduceIte] at h1 h2 h3
  show secondDeriv (radialInv n) (1 : Fin 4) (1 : Fin 4) x +
       secondDeriv (radialInv n) (2 : Fin 4) (2 : Fin 4) x +
       secondDeriv (radialInv n) (3 : Fin 4) (3 : Fin 4) x =
       (n : ℝ) * ((n : ℝ) - 1) / spatialRadius x ^ (n + 2)
  rw [h1, h2, h3]
  -- Algebraic finish via linear_combination using `r² = x₁² + x₂² + x₃²`.
  have hr_sq : spatialRadius x ^ 2 = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
    unfold spatialRadius
    rw [Real.sq_sqrt (spatialNormSq_nonneg x)]; rfl
  have h_pow_n_plus_4 : spatialRadius x ^ (n + 4) =
                        spatialRadius x ^ (n + 2) * spatialRadius x ^ 2 := by
    rw [← pow_add]
  have h_r_n2_ne : spatialRadius x ^ (n + 2) ≠ 0 := pow_ne_zero _ hx
  have h_r_n4_ne : spatialRadius x ^ (n + 4) ≠ 0 := pow_ne_zero _ hx
  field_simp
  rw [h_pow_n_plus_4]
  linear_combination
    (-(n : ℝ) * ((n : ℝ) + 2) * spatialRadius x ^ (n + 2)) * hr_sq
