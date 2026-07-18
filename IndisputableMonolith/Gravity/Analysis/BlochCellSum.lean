import Mathlib

/-!
# Bloch cell-sum orthogonality identities (discrete Fourier, torus cells)

Status: THEOREM (pure classical discrete Fourier orthogonality on `Fin N`
index cubes; Mathlib-only analysis and algebra, no campaign imports, no
physics claims).

## Intended consumer

The `ReggeTTContinuumSymbol` program (QG full-theory campaign, Crux-1c)
needs the classical Bloch orthogonality identities to collapse torus
cell-sums of products of cosines into single cosines of phase differences.
The downstream consumer sums, over cells `x : Fin N × Fin N × Fin N`,
terms `cos (θ_m x + α) * cos (θ_m x + β)` with commensurate wave vector
`k = 2 π m / N` (`m : Fin 3 → ℤ` fixed), and needs the exact value
`N ^ 3 * cos (α - β) / 2` whenever the doubled frequency `2 m` is
non-aliased, i.e. some component of `2 m` is not divisible by `N`.
Nothing here touches the `-(1/4)` continuum target, which remains OPEN.

## Phase convention (read before consuming)

`theta N m x = 2 * π * (m 0 * x₀ + m 1 * x₁ + m 2 * x₂ : ℤ) / N` with
`x = (x₀, (x₁, x₂))` and each `xᵢ` the underlying natural number of the
`Fin N` component.  The consumer's phases arrive as
`k · (x + D/2) = theta N m x + α` with the constant `α = k · D / 2`, so
every statement below is shaped as `theta + constant phase`.

## Contents

* `expSum_eq_zero` / `expSum_eq_card`: the 1D geometric exponential sum
  `∑ j : Fin N, exp (2 π I a j / N)` equals `0` when `¬ (N : ℤ) ∣ a` and
  equals `N` when `(N : ℤ) ∣ a`.  Proved from `geom_sum_eq` (no suitable
  ready-made root-of-unity sum exists in Mathlib for non-primitive
  integer frequencies, so the geometric-series route is used).
* `cosSum_eq_zero`: the 1D cosine phase sum
  `∑ j : Fin N, cos (2 π a j / N + φ) = 0` for `¬ (N : ℤ) ∣ a`, any `φ`.
* `cellSum_exp_eq_prod`: the 3D cell exponential sum factorizes into the
  product of three 1D sums.
* `cellSum_cos_eq_zero`: the 3D cosine cell-sum vanishes whenever some
  component frequency is non-aliased.
* `cellSum_cos_mul_cos` (HEADLINE): for `∃ i, ¬ (N : ℤ) ∣ 2 * m i`,
  `∑ x, cos (theta N m x + α) * cos (theta N m x + β)
     = N ^ 3 * cos (α - β) / 2`.
* `eventually_nonaliased`: for fixed `m ≠ 0` the non-aliasing hypothesis
  holds for all sufficiently large `N`.
* `cellSum_cos_sq_three_axis`: concrete non-vacuity instance at `N = 3`,
  `m = (1, 0, 0)`, `α = β = 0`, evaluating to `27 / 2`.

No `sorry`, no `admit`, no new axioms, no `native_decide`.  Expected
axiom footprint: the standard trio (propext, Classical.choice, Quot.sound).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace BlochCellSum

open scoped BigOperators

noncomputable section

/-! ## 1D building blocks -/

/-- The unit ratio `exp (2 π I a / N)` raised to the `N`-th power is `1`
(the ratio is always an `N`-th root of unity, primitive or not). -/
lemma exp_ratio_pow_card (N : ℕ) [NeZero N] (a : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ N = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [← Complex.exp_nat_mul]
  have harg : (N : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ))
      = (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [mul_comm ((N : ℂ)) (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)),
      div_mul_cancel₀ _ hN]
    ring
  rw [harg]
  exact Complex.exp_int_mul_two_pi_mul_I a

/-- The ratio `exp (2 π I a / N)` equals `1` exactly when `N` divides the
integer frequency `a`. -/
lemma exp_ratio_eq_one_iff (N : ℕ) [NeZero N] (a : ℤ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) = 1
      ↔ (N : ℤ) ∣ a := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : 2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)
        = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (N : ℂ) := (div_eq_iff hN).mp hn
    have h3 : (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = ((n : ℂ) * (N : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
      linear_combination h2
    have key : (a : ℂ) = (n : ℂ) * (N : ℂ) :=
      mul_right_cancel₀ Complex.two_pi_I_ne_zero h3
    exact_mod_cast key.trans (mul_comm (n : ℂ) ((N : ℕ) : ℂ))
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    rw [div_eq_iff hN]
    push_cast
    ring

/-- Each 1D summand is a power of the unit ratio. -/
lemma exp_term_eq_pow (N : ℕ) [NeZero N] (a : ℤ) (j : Fin N) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ (j : ℕ) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- GEOMETRIC EXPONENTIAL SUM, non-aliased case: if `N` does not divide the
integer frequency `a`, the sum of `exp (2 π I a j / N)` over one period
vanishes.  Geometric series with ratio `≠ 1` whose `N`-th power is `1`. -/
theorem expSum_eq_zero (N : ℕ) [NeZero N] (a : ℤ) (ha : ¬ (N : ℤ) ∣ a) :
    ∑ j : Fin N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
      = 0 := by
  have hr_ne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ≠ 1 :=
    fun h => ha ((exp_ratio_eq_one_iff N a).mp h)
  calc ∑ j : Fin N,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
      = ∑ j : Fin N,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ (j : ℕ) :=
        Finset.sum_congr rfl fun j _ => exp_term_eq_pow N a j
    _ = ∑ j ∈ Finset.range N,
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ j :=
        Fin.sum_univ_eq_sum_range
          (fun k => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ k) N
    _ = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) ^ N - 1)
          / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (N : ℂ)) - 1) :=
        geom_sum_eq hr_ne N
    _ = 0 := by rw [exp_ratio_pow_card N a, sub_self, zero_div]

/-- GEOMETRIC EXPONENTIAL SUM, aliased case: if `N` divides the integer
frequency `a`, every summand is `1` and the sum equals `N`. -/
theorem expSum_eq_card (N : ℕ) [NeZero N] (a : ℤ) (ha : (N : ℤ) ∣ a) :
    ∑ j : Fin N,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
      = (N : ℂ) := by
  obtain ⟨c, rfl⟩ := ha
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hterm : ∀ j : Fin N,
      Complex.exp
          (2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * c : ℤ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
        = 1 := by
    intro j
    have harg :
        2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * c : ℤ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)
          = ((c * (j : ℕ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [div_eq_iff hN]
      push_cast
      ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I _
  calc ∑ j : Fin N,
          Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * c : ℤ) : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))
      = ∑ _j : Fin N, (1 : ℂ) := Finset.sum_congr rfl fun j _ => hterm j
    _ = (N : ℂ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-! ## Real-part transfer: complex sum zero forces cosine sum zero -/

/-- If the complex exponential sum of phases `θf` vanishes, then the cosine
sum with any constant phase offset `φ` vanishes.  This is the real-part
extraction `cos (θ + φ) = re (exp (θ I) * exp (φ I))` summed. -/
private lemma sum_cos_of_sum_exp_eq_zero {ι : Type*} [Fintype ι] (θf : ι → ℝ) (φ : ℝ)
    (hz : ∑ x : ι, Complex.exp ((θf x : ℂ) * Complex.I) = 0) :
    ∑ x : ι, Real.cos (θf x + φ) = 0 := by
  have hterm : ∀ x : ι,
      Real.cos (θf x + φ)
        = (Complex.exp ((θf x : ℂ) * Complex.I)
            * Complex.exp ((φ : ℂ) * Complex.I)).re := by
    intro x
    rw [← Complex.exp_add]
    have harg : (θf x : ℂ) * Complex.I + (φ : ℂ) * Complex.I
        = ((θf x + φ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg, Complex.exp_ofReal_mul_I_re]
  calc ∑ x : ι, Real.cos (θf x + φ)
      = ∑ x : ι,
          (Complex.exp ((θf x : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I)).re :=
        Finset.sum_congr rfl fun x _ => hterm x
    _ = ((∑ x : ι, Complex.exp ((θf x : ℂ) * Complex.I))
          * Complex.exp ((φ : ℂ) * Complex.I)).re := by
        rw [Finset.sum_mul, Complex.re_sum]
    _ = 0 := by rw [hz, zero_mul, Complex.zero_re]

/-- COSINE PHASE SUM (1D): if `N` does not divide the integer frequency `a`,
the cosine sum over one period vanishes for every constant phase `φ`. -/
theorem cosSum_eq_zero (N : ℕ) [NeZero N] (a : ℤ) (ha : ¬ (N : ℤ) ∣ a) (φ : ℝ) :
    ∑ j : Fin N,
        Real.cos (2 * Real.pi * (a : ℝ) * ((j : ℕ) : ℝ) / (N : ℝ) + φ) = 0 := by
  refine sum_cos_of_sum_exp_eq_zero
    (fun j : Fin N => 2 * Real.pi * (a : ℝ) * ((j : ℕ) : ℝ) / (N : ℝ)) φ ?_
  have hbridge : ∀ j : Fin N,
      Complex.exp (((2 * Real.pi * (a : ℝ) * ((j : ℕ) : ℝ) / (N : ℝ) : ℝ)) * Complex.I : ℂ)
        = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)) := by
    intro j
    congr 1
    push_cast
    ring
  exact (Finset.sum_congr rfl fun j _ => hbridge j).trans (expSum_eq_zero N a ha)

/-! ## 3D torus cell phases -/

/-- Cell phase for the commensurate wave vector `k = 2 π m / N` at cell
`x = (x₀, (x₁, x₂))`:
`theta N m x = 2 π (m 0 * x₀ + m 1 * x₁ + m 2 * x₂) / N`.
The consumer's phases arrive as `k · (x + D/2) = theta N m x + α` with the
constant `α = k · D / 2`, so all statements below take the shape
`theta + constant phase`. -/
def theta (N : ℕ) (m : Fin 3 → ℤ) (x : Fin N × Fin N × Fin N) : ℝ :=
  2 * Real.pi
    * ((m 0 * ((x.1 : ℕ) : ℤ) + m 1 * ((x.2.1 : ℕ) : ℤ) + m 2 * ((x.2.2 : ℕ) : ℤ) : ℤ) : ℝ)
    / (N : ℝ)

/-- Doubling every component of the frequency vector doubles the cell phase. -/
lemma theta_two_mul (N : ℕ) (m : Fin 3 → ℤ) (x : Fin N × Fin N × Fin N) :
    theta N (fun i => 2 * m i) x = 2 * theta N m x := by
  simp only [theta]
  push_cast
  ring

/-- Product sums factor through the product type (helper for the 3D
factorization). -/
private lemma sum_mul_sum_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → ℂ) (v : κ → ℂ) :
    (∑ j : ι, u j) * (∑ k : κ, v k) = ∑ p : ι × κ, u p.1 * v p.2 := by
  rw [Finset.sum_mul_sum]
  exact (Fintype.sum_prod_type fun p : ι × κ => u p.1 * v p.2).symm

/-- The 3D cell exponential sum factorizes into the product of the three 1D
geometric exponential sums (one per axis). -/
theorem cellSum_exp_eq_prod (N : ℕ) [NeZero N] (m : Fin 3 → ℤ) :
    ∑ x : Fin N × Fin N × Fin N, Complex.exp ((theta N m x : ℂ) * Complex.I)
      = (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
        * (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
        * (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))) := by
  have hsplit : ∀ x : Fin N × Fin N × Fin N,
      Complex.exp ((theta N m x : ℂ) * Complex.I)
        = Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((x.1 : ℕ) : ℂ) / (N : ℂ))
          * (Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((x.2.1 : ℕ) : ℂ) / (N : ℂ))
            * Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((x.2.2 : ℕ) : ℂ) / (N : ℂ))) := by
    intro x
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [theta]
    push_cast
    ring
  calc ∑ x : Fin N × Fin N × Fin N, Complex.exp ((theta N m x : ℂ) * Complex.I)
      = ∑ x : Fin N × Fin N × Fin N,
          Complex.exp
              (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((x.1 : ℕ) : ℂ) / (N : ℂ))
            * (Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((x.2.1 : ℕ) : ℂ) / (N : ℂ))
              * Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((x.2.2 : ℕ) : ℂ) / (N : ℂ))) :=
        Finset.sum_congr rfl fun x _ => hsplit x
    _ = (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          * ∑ p : Fin N × Fin N,
              Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((p.1 : ℕ) : ℂ) / (N : ℂ))
                * Complex.exp
                  (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((p.2 : ℕ) : ℂ) / (N : ℂ)) :=
        (sum_mul_sum_prod
          (fun j : Fin N =>
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          (fun p : Fin N × Fin N =>
            Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((p.1 : ℕ) : ℂ) / (N : ℂ))
              * Complex.exp
                (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((p.2 : ℕ) : ℂ) / (N : ℂ)))).symm
    _ = (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          * ((∑ j : Fin N,
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
            * (∑ j : Fin N,
              Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))) := by
        rw [sum_mul_sum_prod
          (fun j : Fin N =>
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          (fun j : Fin N =>
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))]
    _ = (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 0 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          * (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 1 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ)))
          * (∑ j : Fin N,
            Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m 2 : ℂ) * ((j : ℕ) : ℂ) / (N : ℂ))) :=
        (mul_assoc _ _ _).symm

/-- 3D COSINE CELL-SUM VANISHING: if some component frequency `m i` is not
divisible by `N`, the cosine cell-sum with any constant phase `φ` vanishes.
The 3D exponential sum factorizes and the non-aliased axis kills the
product. -/
theorem cellSum_cos_eq_zero (N : ℕ) [NeZero N] (m : Fin 3 → ℤ)
    (h : ∃ i : Fin 3, ¬ (N : ℤ) ∣ m i) (φ : ℝ) :
    ∑ x : Fin N × Fin N × Fin N, Real.cos (theta N m x + φ) = 0 := by
  refine sum_cos_of_sum_exp_eq_zero (theta N m) φ ?_
  rw [cellSum_exp_eq_prod N m]
  obtain ⟨i, hi⟩ := h
  fin_cases i
  · exact mul_eq_zero_of_left (mul_eq_zero_of_left (expSum_eq_zero N (m 0) hi) _) _
  · exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (expSum_eq_zero N (m 1) hi)) _
  · exact mul_eq_zero_of_right _ (expSum_eq_zero N (m 2) hi)

/-! ## Product-to-sum assembly (headline) -/

/-- Product-to-sum identity for cosines, stated for reuse by consumers. -/
theorem cos_mul_cos (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- HEADLINE (PRODUCT-TO-SUM BLOCH CELL SUM): for a commensurate wave vector
`k = 2 π m / N` whose doubled frequency `2 m` is non-aliased on some axis
(`∃ i, ¬ (N : ℤ) ∣ 2 * m i`), the torus cell-sum of the product of two
phase-shifted cosines collapses to the constant term:
`∑ x, cos (theta N m x + α) * cos (theta N m x + β) = N ^ 3 * cos (α - β) / 2`.
The `(A - B)` half of the product-to-sum identity is constant and
contributes `N ^ 3 * cos (α - β) / 2`; the `(A + B)` half is a cell-sum at
doubled frequency and vanishes by `cellSum_cos_eq_zero`. -/
theorem cellSum_cos_mul_cos (N : ℕ) [NeZero N] (m : Fin 3 → ℤ) (α β : ℝ)
    (halias : ∃ i : Fin 3, ¬ (N : ℤ) ∣ 2 * m i) :
    ∑ x : Fin N × Fin N × Fin N,
        Real.cos (theta N m x + α) * Real.cos (theta N m x + β)
      = (N : ℝ) ^ 3 * Real.cos (α - β) / 2 := by
  have hzero :
      ∑ x : Fin N × Fin N × Fin N,
          Real.cos (theta N (fun i => 2 * m i) x + (α + β)) = 0 :=
    cellSum_cos_eq_zero N (fun i => 2 * m i) halias (α + β)
  have hpt : ∀ x : Fin N × Fin N × Fin N,
      Real.cos (theta N m x + α) * Real.cos (theta N m x + β)
        = Real.cos (α - β) / 2
          + Real.cos (theta N (fun i => 2 * m i) x + (α + β)) / 2 := by
    intro x
    rw [cos_mul_cos]
    rw [show theta N m x + α - (theta N m x + β) = α - β from by ring]
    rw [show theta N m x + α + (theta N m x + β) = 2 * theta N m x + (α + β) from by ring]
    rw [← theta_two_mul N m x]
    ring
  calc ∑ x : Fin N × Fin N × Fin N,
          Real.cos (theta N m x + α) * Real.cos (theta N m x + β)
      = ∑ x : Fin N × Fin N × Fin N,
          (Real.cos (α - β) / 2
            + Real.cos (theta N (fun i => 2 * m i) x + (α + β)) / 2) :=
        Finset.sum_congr rfl fun x _ => hpt x
    _ = (∑ _x : Fin N × Fin N × Fin N, Real.cos (α - β) / 2)
          + ∑ x : Fin N × Fin N × Fin N,
              Real.cos (theta N (fun i => 2 * m i) x + (α + β)) / 2 :=
        Finset.sum_add_distrib
    _ = (N : ℝ) ^ 3 * Real.cos (α - β) / 2 := by
        have hconst : (∑ _x : Fin N × Fin N × Fin N, Real.cos (α - β) / 2)
            = (N : ℝ) ^ 3 * Real.cos (α - β) / 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
        have hosc : (∑ x : Fin N × Fin N × Fin N,
              Real.cos (theta N (fun i => 2 * m i) x + (α + β)) / 2) = 0 := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul]
          rw [hzero, zero_mul]
        rw [hconst, hosc, add_zero]

/-! ## Eventual non-aliasing -/

/-- For a fixed nonzero frequency vector `m`, the non-aliasing hypothesis of
`cellSum_cos_mul_cos` holds for all sufficiently large `N`: once
`N > 2 * |m i|` on a nonzero axis, `N` cannot divide `2 * m i`. -/
theorem eventually_nonaliased (m : Fin 3 → ℤ) (hm : ∃ i : Fin 3, m i ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ i : Fin 3, ¬ (N : ℤ) ∣ 2 * m i := by
  obtain ⟨i, hi⟩ := hm
  rw [Filter.eventually_atTop]
  refine ⟨2 * (m i).natAbs + 1, fun N hN => ⟨i, fun hdvd => ?_⟩⟩
  have hne : 2 * m i ≠ 0 := mul_ne_zero two_ne_zero hi
  have hle : (N : ℤ) ≤ |2 * m i| :=
    Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  rw [Int.abs_eq_natAbs] at hle
  omega

/-! ## Concrete non-vacuity instance -/

/-- Non-vacuity witness: the headline identity engages at `N = 3`,
`m = (1, 0, 0)`, `α = β = 0`, where it evaluates the cell-sum of squared
cosines to `27 / 2`. -/
theorem cellSum_cos_sq_three_axis :
    ∑ x : Fin 3 × Fin 3 × Fin 3,
        Real.cos (theta 3 ![1, 0, 0] x + 0) * Real.cos (theta 3 ![1, 0, 0] x + 0)
      = 27 / 2 := by
  haveI : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have halias : ∃ i : Fin 3, ¬ ((3 : ℕ) : ℤ) ∣ 2 * (![1, 0, 0] : Fin 3 → ℤ) i := by
    refine ⟨0, ?_⟩
    simp only [Matrix.cons_val_zero]
    norm_num
  have h := cellSum_cos_mul_cos 3 ![1, 0, 0] 0 0 halias
  rw [h]
  norm_num [sub_self, Real.cos_zero]

end

end BlochCellSum
end Analysis
end Gravity
end IndisputableMonolith
