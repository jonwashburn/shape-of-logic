import IndisputableMonolith.NumberTheory.ZetaFromTheta

/-!
  HadamardFactorization.lean

  Track D of the RH unconditional-closure plan.

  Mathlib gives the completed zeta function and the entire pole-removed
  function `completedRiemannZeta₀`, together with differentiability and the
  functional equation. It does not currently provide a Hadamard product for
  `completedRiemannZeta₀`.

  This module introduces the product interface needed by later explicit-formula
  work. It defines the genus-one primary factor and finite partial products,
  then states the exact data required to identify their limit with
  `completedRiemannZeta₀`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace HadamardFactorization

open Filter

noncomputable section

/-! ## 1. Mathlib facts available for the pole-removed completed zeta -/

/-- Completed zeta with poles removed is differentiable everywhere in Mathlib. -/
theorem completedZeta0_differentiable :
    Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- The pole-removed completed zeta has the same functional equation. -/
theorem completedZeta0_functional_equation (s : ℂ) :
    completedRiemannZeta₀ s = completedRiemannZeta₀ (1 - s) :=
  (completedRiemannZeta₀_one_sub s).symm

/-! ## 2. Genus-one Hadamard factors -/

/-- The genus-one elementary Hadamard factor `E₁(z) = (1-z) exp(z)`. -/
def hadamardE1 (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

@[simp] theorem hadamardE1_zero : hadamardE1 0 = 1 := by
  simp [hadamardE1]

/-- The finite genus-one product over the first `N` listed zeros. -/
def hadamardPartialProduct (zeros : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∏ n ∈ Finset.range N, hadamardE1 (s / zeros n)

@[simp] theorem hadamardPartialProduct_zero
    (zeros : ℕ → ℂ) (N : ℕ) :
    hadamardPartialProduct zeros 0 N = 1 := by
  simp [hadamardPartialProduct]

/-! ## 3. Exact Hadamard product data needed downstream -/

/-- Hadamard product data for the pole-removed completed zeta.

This is the real Track D target. The missing analytic work is the proof that
`completedRiemannZeta₀` has order at most one, that its zeros can be enumerated
with the required convergence properties, and that the corresponding genus-one
partial products converge to the pole-removed completed zeta up to `exp(A+B s)`.
-/
structure CompletedZetaHadamardProduct where
  zeros : ℕ → ℂ
  zero_ne_zero : ∀ n : ℕ, zeros n ≠ 0
  A : ℂ
  B : ℂ
  productLimit : ℂ → ℂ
  partial_products_converge :
    ∀ s : ℂ,
      Filter.Tendsto
        (fun N : ℕ => hadamardPartialProduct zeros s N)
        Filter.atTop
        (nhds (productLimit s))
  completedZeta0_eq_hadamard :
    ∀ s : ℂ,
      completedRiemannZeta₀ s =
        Complex.exp (A + B * s) * productLimit s

/-- Once Hadamard product data is supplied, the pole-removed completed zeta has
the expected genus-one factorization. -/
theorem completedRiemannZeta0_hadamard_product
    (data : CompletedZetaHadamardProduct) (s : ℂ) :
    completedRiemannZeta₀ s =
      Complex.exp (data.A + data.B * s) * data.productLimit s :=
  data.completedZeta0_eq_hadamard s

/-! ## 4. Track D attack surface -/

/-- Practical Track D bundle: the proved Mathlib inputs plus the open Hadamard
product data type. -/
structure HadamardFactorizationStatus where
  completed_zeta0_entire :
    Differentiable ℂ completedRiemannZeta₀
  completed_zeta0_functional_equation :
    ∀ s : ℂ, completedRiemannZeta₀ s = completedRiemannZeta₀ (1 - s)
  hadamard_data_to_product :
    ∀ data : CompletedZetaHadamardProduct,
      ∀ s : ℂ,
        completedRiemannZeta₀ s =
          Complex.exp (data.A + data.B * s) * data.productLimit s

def hadamardFactorizationStatus : HadamardFactorizationStatus where
  completed_zeta0_entire := completedZeta0_differentiable
  completed_zeta0_functional_equation := completedZeta0_functional_equation
  hadamard_data_to_product := completedRiemannZeta0_hadamard_product

end

end HadamardFactorization
end NumberTheory
end IndisputableMonolith
