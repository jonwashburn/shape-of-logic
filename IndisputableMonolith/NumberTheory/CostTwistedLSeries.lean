import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.PrimeCostSpectrum

/-!
# Cost-Twisted Arithmetic Functions and L-Functions

This module generalizes the prime cost spectrum from
`IndisputableMonolith.NumberTheory.PrimeCostSpectrum` to the
character-twisted setting.

For each completely multiplicative arithmetic function `chi : ℕ → ℝ`
(typically the real part of a Dirichlet character), we define the
twisted prime cost spectrum value
  `c_chi(n) := Σ_p v_p(n) · J(p) · chi(p)`,
and prove the elementary properties: complete additivity, the
relationship to the prime-restricted partial sum
`Π_chi(x) := Σ_{p ≤ x} J(p) chi(p)`, and the structural identities.

The Dirichlet series of `c_chi` factorizes through the corresponding
L-function (paper-level result; not formalized analytically here).

## Lean status: 0 sorry
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace CostTwistedLSeries

open Cost PrimeCostSpectrum

noncomputable section

/-! ## Twisted prime cost

For a function `chi : ℕ → ℝ`, the cost of a prime `p` twisted by `chi`
is `J(p) · chi(p)`. -/

/-- The cost of a prime `p` twisted by an arithmetic function `chi`. -/
def twistedPrimeCost (chi : ℕ → ℝ) (p : ℕ) : ℝ :=
  primeCost p * chi p

/-- The cost spectrum value of `n` twisted by `chi`, defined via the
    prime factorization. -/
def twistedCostSpectrumValue (chi : ℕ → ℝ) (n : ℕ) : ℝ :=
  n.factorization.sum fun p k => (k : ℝ) * twistedPrimeCost chi p

@[simp]
theorem twistedCostSpectrumValue_one (chi : ℕ → ℝ) :
    twistedCostSpectrumValue chi 1 = 0 := by
  unfold twistedCostSpectrumValue
  simp [Nat.factorization_one]

@[simp]
theorem twistedCostSpectrumValue_zero (chi : ℕ → ℝ) :
    twistedCostSpectrumValue chi 0 = 0 := by
  unfold twistedCostSpectrumValue
  simp [Nat.factorization_zero]

/-- For a prime `p`, the twisted cost is `J(p) · chi(p)`. -/
theorem twistedCostSpectrumValue_prime (chi : ℕ → ℝ) {p : ℕ}
    (hp : Nat.Prime p) :
    twistedCostSpectrumValue chi p = primeCost p * chi p := by
  unfold twistedCostSpectrumValue twistedPrimeCost
  rw [Nat.Prime.factorization hp]
  simp [Finsupp.sum_single_index]

/-- For a prime power `p^k`, the twisted cost is `k · J(p) · chi(p)`. -/
theorem twistedCostSpectrumValue_pow (chi : ℕ → ℝ) {p k : ℕ}
    (hp : Nat.Prime p) :
    twistedCostSpectrumValue chi (p ^ k) = (k : ℝ) * (primeCost p * chi p) := by
  unfold twistedCostSpectrumValue twistedPrimeCost
  rw [Nat.Prime.factorization_pow hp]
  simp [Finsupp.sum_single_index]

/-- The twisted cost is completely additive over coprime products.
    This generalizes `costSpectrumValue_mul`. -/
theorem twistedCostSpectrumValue_mul (chi : ℕ → ℝ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    twistedCostSpectrumValue chi (m * n)
      = twistedCostSpectrumValue chi m + twistedCostSpectrumValue chi n := by
  unfold twistedCostSpectrumValue
  rw [Nat.factorization_mul hm hn]
  rw [Finsupp.sum_add_index']
  · intro p
    simp
  · intro p i j
    push_cast
    ring

/-- For the trivial character `chi = 1`, the twisted cost spectrum value
    reduces to the standard cost spectrum value. -/
theorem twistedCostSpectrumValue_one_char (n : ℕ) :
    twistedCostSpectrumValue (fun _ => 1) n = costSpectrumValue n := by
  unfold twistedCostSpectrumValue costSpectrumValue twistedPrimeCost
  refine Finsupp.sum_congr ?_
  intro p _
  ring

/-- Negating the character flips the sign of the twisted cost. -/
theorem twistedCostSpectrumValue_eq_neg (chi : ℕ → ℝ) (n : ℕ) :
    twistedCostSpectrumValue (fun p => -chi p) n
      = -twistedCostSpectrumValue chi n := by
  unfold twistedCostSpectrumValue twistedPrimeCost
  rw [Finsupp.sum, Finsupp.sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-! ## The twisted prime cost sum

The twisted analog of the prime cost sum `Π(x)`. -/

/-- The twisted prime cost sum:
    `Π_chi(x) := Σ_{p ≤ x prime} J(p) · chi(p)`.

    Defined as a finite sum over primes ≤ N (using the fact that
    `Nat.primesBelow` returns the finset of primes below N). -/
def twistedPrimeCostSum (chi : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum fun p =>
    if Nat.Prime p then primeCost p * chi p else 0

@[simp]
theorem twistedPrimeCostSum_zero (chi : ℕ → ℝ) :
    twistedPrimeCostSum chi 0 = 0 := by
  simp [twistedPrimeCostSum, Nat.not_prime_zero]

/-- For the trivial character, the twisted prime cost sum equals the
    untwisted version. -/
theorem twistedPrimeCostSum_one_char (N : ℕ) :
    twistedPrimeCostSum (fun _ => 1) N
      = (Finset.range (N + 1)).sum fun p =>
          if Nat.Prime p then primeCost p else 0 := by
  unfold twistedPrimeCostSum
  congr 1
  ext p
  by_cases hp : Nat.Prime p
  · simp [hp]
  · simp [hp]

/-! ## Master certificate -/

/-- Master certificate: the elementary properties of the cost-twisted
    arithmetic function. -/
theorem cost_twisted_certificate :
    -- (1) Twisted cost is zero at n = 1.
    (∀ (chi : ℕ → ℝ), twistedCostSpectrumValue chi 1 = 0) ∧
    -- (2) Twisted cost is completely additive over positive products.
    (∀ (chi : ℕ → ℝ) {m n : ℕ}, m ≠ 0 → n ≠ 0 →
      twistedCostSpectrumValue chi (m * n)
        = twistedCostSpectrumValue chi m + twistedCostSpectrumValue chi n) ∧
    -- (3) Twisted cost on a prime equals J(p) · chi(p).
    (∀ (chi : ℕ → ℝ) {p : ℕ}, Nat.Prime p →
      twistedCostSpectrumValue chi p = primeCost p * chi p) ∧
    -- (4) Twisted cost on a prime power equals k · J(p) · chi(p).
    (∀ (chi : ℕ → ℝ) {p k : ℕ}, Nat.Prime p →
      twistedCostSpectrumValue chi (p ^ k) = (k : ℝ) * (primeCost p * chi p)) ∧
    -- (5) Trivial character recovers untwisted cost.
    (∀ (n : ℕ), twistedCostSpectrumValue (fun _ => 1) n = costSpectrumValue n) ∧
    -- (6) Negation flips sign.
    (∀ (chi : ℕ → ℝ) (n : ℕ),
      twistedCostSpectrumValue (fun p => -chi p) n
        = -twistedCostSpectrumValue chi n) :=
  ⟨twistedCostSpectrumValue_one,
   @twistedCostSpectrumValue_mul,
   @twistedCostSpectrumValue_prime,
   @twistedCostSpectrumValue_pow,
   twistedCostSpectrumValue_one_char,
   twistedCostSpectrumValue_eq_neg⟩

end

end CostTwistedLSeries
end NumberTheory
end IndisputableMonolith
