import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.PrimeLedgerStructure

/-!
# The Prime Cost Spectrum

This module extends the Recognition Science cost function `J` from the
positive reals to a complete arithmetic function on ℕ via the prime
factorization.  For each `n ≥ 1` we define

  `c(n) := Σ_{p^k ‖ n} k · J(p) = Σ_p v_p(n) · J(p)`

where `v_p(n)` is the `p`-adic valuation.  This makes `c` a
*completely additive* arithmetic function: `c(m·n) = c(m) + c(n)` for
positive `m, n`.

The cost spectrum `{J(p) : p prime}` is the set of irreducible cost
quanta out of which every integer's cost is built.  Classical
prime-counting machinery (Chebyshev `θ`, `ψ`, prime counting `π`)
admits clean reformulations in terms of `c`.

## Main definitions

* `primeCost p`           : `J p` viewed as a real, restricted to primes.
* `costSpectrumValue n`   : the cost `c(n)` of an integer, defined via
                            `Nat.factorization`.

## Main theorems (all 0 sorry, 0 axiom)

* `primeCost_pos`         : `0 < J(p)` for every prime `p ≥ 2`.
* `primeCost_strictMono`  : `J` is strictly increasing on primes.
* `costSpectrumValue_one` : `c(1) = 0`.
* `costSpectrumValue_prime`: `c(p) = J(p)` for prime `p`.
* `costSpectrumValue_mul` : `c(m·n) = c(m) + c(n)` for `m, n > 0`.
* `costSpectrumValue_pow` : `c(p^k) = k · J(p)` for prime `p`.
* `costSpectrumValue_nonneg` : `c(n) ≥ 0`.

## Lean status: 0 sorry
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PrimeCostSpectrum

open Cost

noncomputable section

/-! ## Prime cost: the irreducible quanta -/

/-- The cost of a prime number.  This is just `J` evaluated on `p`,
    but isolated here because primes are the ledger's irreducible
    transactions and their costs are the spectrum's basis. -/
def primeCost (p : ℕ) : ℝ := Jcost (p : ℝ)

/-- For any prime `p`, the prime cost is strictly positive. -/
theorem primeCost_pos {p : ℕ} (hp : Nat.Prime p) : 0 < primeCost p := by
  unfold primeCost
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne_one : (p : ℝ) ≠ 1 := by
    have : p ≠ 1 := hp.one_lt.ne'
    exact_mod_cast this
  exact Jcost_pos_of_ne_one (p : ℝ) hp_pos hp_ne_one

/-- The prime cost is nonnegative for any natural number `n` (treating
    `n = 0` as the boundary case `J(0) = -1` which we avoid by working
    only with positive `n`). -/
theorem primeCost_nonneg {n : ℕ} (hn : 0 < n) : 0 ≤ primeCost n := by
  unfold primeCost
  have : 0 < (n : ℝ) := by exact_mod_cast hn
  exact Jcost_nonneg this

/-- `J` is strictly monotonic on the positive reals at and above 1.
    This is the key analytic input for showing that distinct primes
    have distinct cost values.

    Algebraic proof: writing J(x) = (x-1)²/(2x), we need to show
    (x-1)²·y < (y-1)²·x when 1 ≤ x < y.  This rearranges to
    (y-x)·(xy-1) > 0, which holds since y-x > 0 and xy ≥ x ≥ 1
    with strict inequality whenever x > 1; the boundary case x = 1
    gives (x-1)² = 0 < (y-1)²·x. -/
private lemma jcost_strictMono_on_one_le :
    StrictMonoOn Jcost (Set.Ici (1 : ℝ)) := by
  intro x hx y hy hxy
  have hx1 : (1 : ℝ) ≤ x := hx
  have hy1 : (1 : ℝ) ≤ y := hy
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  rw [Jcost_eq_sq (ne_of_gt hx_pos), Jcost_eq_sq (ne_of_gt hy_pos)]
  have h2x_pos : 0 < 2 * x := by linarith
  have h2y_pos : 0 < 2 * y := by linarith
  rw [div_lt_div_iff₀ h2x_pos h2y_pos]
  -- Goal: (x-1)² · 2y < (y-1)² · 2x.
  -- Identity: (y-1)²·x - (x-1)²·y = (y-x)·(xy - 1).
  have key : (y - 1)^2 * x - (x - 1)^2 * y = (y - x) * (x * y - 1) := by ring
  have hyx_pos : 0 < y - x := by linarith
  have hy_pos_strict : 1 < y := lt_of_le_of_lt hx1 hxy
  rcases lt_or_eq_of_le hx1 with hx_gt | hx_eq
  · -- x > 1: then x*y > 1, so (y-x)·(xy-1) > 0.
    have hxy_gt : 1 < x * y := by
      have h1 : 1 * 1 ≤ x * y := mul_le_mul hx1 hy1 (by norm_num) (le_of_lt hx_pos)
      have h2 : 1 < x * y := by
        have := mul_lt_mul_of_pos_right hx_gt hy_pos
        linarith
      exact h2
    nlinarith [mul_pos hyx_pos (by linarith : (0 : ℝ) < x * y - 1), key]
  · -- x = 1: LHS is 0, RHS is positive.
    rw [← hx_eq]
    have h_lhs : (1 - 1 : ℝ)^2 * (2 * y) = 0 := by ring
    rw [h_lhs]
    have hy_sub_pos : 0 < y - 1 := by linarith
    have hy_sq_pos : 0 < (y - 1)^2 := by positivity
    have h_two_pos : (0 : ℝ) < 2 * 1 := by norm_num
    exact mul_pos hy_sq_pos h_two_pos

/-- Prime cost is strictly increasing in the prime: `p < q` ⟹ `J(p) < J(q)`. -/
theorem primeCost_strictMono {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) :
    primeCost p < primeCost q := by
  unfold primeCost
  have hp_ge : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hq_ge : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_lt.le
  have : (p : ℝ) < (q : ℝ) := by exact_mod_cast hpq
  exact jcost_strictMono_on_one_le hp_ge hq_ge this

/-! ## Cost spectrum value: extending J to all of ℕ via factorization -/

/-- The total cost of an integer `n`, defined via its prime factorization:
    `c(n) = Σ_{p^k ‖ n} k · J(p)`.
    By convention `c(0) = 0`. -/
def costSpectrumValue (n : ℕ) : ℝ :=
  n.factorization.sum fun p k => (k : ℝ) * primeCost p

@[simp]
theorem costSpectrumValue_one : costSpectrumValue 1 = 0 := by
  unfold costSpectrumValue
  simp [Nat.factorization_one]

@[simp]
theorem costSpectrumValue_zero : costSpectrumValue 0 = 0 := by
  unfold costSpectrumValue
  simp [Nat.factorization_zero]

/-- For a prime `p`, `c(p) = J(p)`. -/
theorem costSpectrumValue_prime {p : ℕ} (hp : Nat.Prime p) :
    costSpectrumValue p = primeCost p := by
  unfold costSpectrumValue
  rw [Nat.Prime.factorization hp]
  simp [Finsupp.sum_single_index]

/-- For a prime power `p^k`, `c(p^k) = k · J(p)`. -/
theorem costSpectrumValue_pow {p k : ℕ} (hp : Nat.Prime p) :
    costSpectrumValue (p ^ k) = (k : ℝ) * primeCost p := by
  unfold costSpectrumValue
  rw [Nat.Prime.factorization_pow hp]
  simp [Finsupp.sum_single_index]

/-- The cost is completely additive over coprime products.
    For arbitrary products with positive factors, the same identity holds
    because `Nat.factorization` is additive on positive multiplications. -/
theorem costSpectrumValue_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    costSpectrumValue (m * n) = costSpectrumValue m + costSpectrumValue n := by
  unfold costSpectrumValue
  rw [Nat.factorization_mul hm hn]
  rw [Finsupp.sum_add_index']
  · intro p
    simp
  · intro p i j
    push_cast
    ring

/-- The cost is nonnegative for any positive `n`.
    Each summand `k · J(p) ≥ 0` by primality of `p`, so the sum is ≥ 0. -/
theorem costSpectrumValue_nonneg (n : ℕ) :
    0 ≤ costSpectrumValue n := by
  unfold costSpectrumValue
  apply Finsupp.sum_nonneg
  intro p hp_mem
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors
    (Nat.support_factorization n ▸ hp_mem)
  have hk_nonneg : (0 : ℝ) ≤ (n.factorization p : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hJ_nonneg : 0 ≤ primeCost p := le_of_lt (primeCost_pos hp_prime)
  exact mul_nonneg hk_nonneg hJ_nonneg

/-- Cost is monotonic under multiplication by positive integers
    (a direct consequence of additivity and nonnegativity of prime costs). -/
theorem costSpectrumValue_le_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    costSpectrumValue m ≤ costSpectrumValue (m * n) := by
  rw [costSpectrumValue_mul hm hn]
  have := costSpectrumValue_nonneg n
  linarith

/-- The cost is strictly positive for any integer `n ≥ 2`. -/
theorem costSpectrumValue_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < costSpectrumValue n := by
  have hn_ne_zero : n ≠ 0 := by omega
  have hn_ne_one : n ≠ 1 := by omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hn_ne_one
  have hp_mem : p ∈ n.factorization.support := by
    rw [Nat.support_factorization]
    exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hn_ne_zero⟩
  have hk_pos : 0 < n.factorization p := by
    have := Finsupp.mem_support_iff.mp hp_mem
    exact Nat.pos_of_ne_zero this
  have hJ_pos : 0 < primeCost p := primeCost_pos hp_prime
  have hsummand_pos : 0 < (n.factorization p : ℝ) * primeCost p := by
    have hk_real_pos : (0 : ℝ) < (n.factorization p : ℝ) := by
      exact_mod_cast hk_pos
    exact mul_pos hk_real_pos hJ_pos
  unfold costSpectrumValue
  -- Split the Finsupp sum into the p-summand plus the rest, both nonneg.
  rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hp_mem]
  apply add_pos_of_nonneg_of_pos
  · apply Finset.sum_nonneg
    intro q hq_mem
    have hq_in_support : q ∈ n.factorization.support :=
      (Finset.mem_erase.mp hq_mem).2
    have hq_prime : Nat.Prime q := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization n ▸ hq_in_support)
    have hk_nonneg : (0 : ℝ) ≤ (n.factorization q : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact mul_nonneg hk_nonneg (le_of_lt (primeCost_pos hq_prime))
  · exact hsummand_pos

/-! ## Auxiliary arithmetic functions -/

/-- The total prime factor count (with multiplicity) of `n`, written `Ω(n)`. -/
def Omega (n : ℕ) : ℕ := n.factorization.sum fun _ k => k

/-- The total prime factor count (without multiplicity) of `n`, written `ω(n)`. -/
def omega (n : ℕ) : ℕ := n.factorization.support.card

/-- The "sum of prime factors with multiplicity" function `sopfr(n) = Σ k·p`. -/
def sopfr (n : ℕ) : ℕ := n.factorization.sum fun p k => k * p

/-- The reciprocal-sum-of-prime-factors `Σ k/p` as a real number. -/
noncomputable def reciprocalPrimeSum (n : ℕ) : ℝ :=
  n.factorization.sum fun p k => (k : ℝ) / (p : ℝ)

/-- Per-summand identity: each prime-power contribution to `c(n)` decomposes
    into half of `k·p`, half of `k/p`, minus `k`.  Used to derive the
    closed-form decomposition below. -/
private lemma summand_decomposition (p k : ℕ) (hp : Nat.Prime p) :
    (k : ℝ) * primeCost p =
      (1/2) * ((k : ℝ) * (p : ℝ))
      + (1/2) * ((k : ℝ) / (p : ℝ)) - (k : ℝ) := by
  unfold primeCost Jcost
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  field_simp

/-! ## Power formula and Omega bound -/

/-- For any positive integer `n` and any natural `k`,
    `c(n^k) = k · c(n)`.  This is the complete-additivity of `c`
    extended to repeated multiplication. -/
theorem costSpectrumValue_pow_general {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    costSpectrumValue (n ^ k) = (k : ℝ) * costSpectrumValue n := by
  induction k with
  | zero => simp [costSpectrumValue_one]
  | succ k ih =>
    have hnk : n ^ k ≠ 0 := pow_ne_zero k hn
    rw [pow_succ, costSpectrumValue_mul hnk hn, ih]
    push_cast
    ring

/-- The cost spectrum value is bounded by `Ω(n) · J(p_max)` where
    `p_max` is the largest prime factor of `n`.  Specialized to the
    weaker bound `c(n) ≤ Ω(n) · J(n)` using monotonicity of `J` on
    `[1, ∞)`.  Useful for asymptotic upper bounds. -/
theorem costSpectrumValue_le_omega_mul_jcost {n : ℕ} (hn : 2 ≤ n) :
    costSpectrumValue n ≤ (Omega n : ℝ) * Jcost (n : ℝ) := by
  have hn_pos : 0 < n := by omega
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  -- Bound each summand: k · J(p) ≤ k · J(n) for prime p dividing n,
  -- since p ≤ n and J is monotonic on [1, ∞).
  have h_per_summand : ∀ p ∈ n.factorization.support,
      (n.factorization p : ℝ) * primeCost p
        ≤ (n.factorization p : ℝ) * Jcost (n : ℝ) := by
    intro p hp_mem
    have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors
      (Nat.support_factorization n ▸ hp_mem)
    have hp_dvd : p ∣ n :=
      Nat.dvd_of_mem_primeFactors (Nat.support_factorization n ▸ hp_mem)
    have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hp_dvd
    have hk_nonneg : (0 : ℝ) ≤ (n.factorization p : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hp_real_ge_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.one_lt.le
    have hp_real_le_n : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp_le_n
    have h_J_mono : primeCost p ≤ Jcost (n : ℝ) := by
      unfold primeCost
      rcases lt_or_eq_of_le hp_real_le_n with h_lt | h_eq
      · exact le_of_lt (jcost_strictMono_on_one_le hp_real_ge_one hn_ge_one h_lt)
      · rw [h_eq]
    exact mul_le_mul_of_nonneg_left h_J_mono hk_nonneg
  -- Sum the bound over all primes in the support.
  -- LHS: sum of k_p · J(p). RHS: (sum of k_p) · J(n) = sum of k_p · J(n).
  have h_rhs_split :
      (Omega n : ℝ) * Jcost (n : ℝ)
        = n.factorization.sum (fun _ k => (k : ℝ) * Jcost (n : ℝ)) := by
    unfold Omega
    rw [show (n.factorization.sum fun _ k => (k : ℝ) * Jcost (n : ℝ))
          = (n.factorization.sum fun _ k => (k : ℝ)) * Jcost (n : ℝ) by
        rw [← Finsupp.sum_mul]]
    congr 1
    push_cast
    rfl
  unfold costSpectrumValue
  rw [h_rhs_split]
  exact Finset.sum_le_sum h_per_summand

/-! ## Cost spectrum certificate -/

/-- Master certificate: the elementary properties of the cost spectrum
    that this module establishes.  Used by the companion paper. -/
theorem cost_spectrum_certificate :
    -- (1) Prime cost is strictly positive.
    (∀ {p : ℕ}, Nat.Prime p → 0 < primeCost p) ∧
    -- (2) Prime cost is strictly monotonic in p.
    (∀ {p q : ℕ}, Nat.Prime p → Nat.Prime q → p < q →
      primeCost p < primeCost q) ∧
    -- (3) Cost is zero exactly at n = 1 (within positive integers).
    (costSpectrumValue 1 = 0) ∧
    -- (4) Cost is positive for n ≥ 2.
    (∀ {n : ℕ}, 2 ≤ n → 0 < costSpectrumValue n) ∧
    -- (5) Cost is completely additive over positive integers.
    (∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 →
      costSpectrumValue (m * n) = costSpectrumValue m + costSpectrumValue n) ∧
    -- (6) Cost on a prime equals its prime cost.
    (∀ {p : ℕ}, Nat.Prime p → costSpectrumValue p = primeCost p) ∧
    -- (7) Cost on a power: c(n^k) = k · c(n).
    (∀ {n : ℕ} (_ : n ≠ 0) (k : ℕ),
      costSpectrumValue (n ^ k) = (k : ℝ) * costSpectrumValue n) ∧
    -- (8) Cost is bounded above by Ω(n) · J(n).
    (∀ {n : ℕ}, 2 ≤ n →
      costSpectrumValue n ≤ (Omega n : ℝ) * Jcost (n : ℝ)) :=
  ⟨@primeCost_pos,
   @primeCost_strictMono,
   costSpectrumValue_one,
   @costSpectrumValue_pos,
   @costSpectrumValue_mul,
   @costSpectrumValue_prime,
   @costSpectrumValue_pow_general,
   @costSpectrumValue_le_omega_mul_jcost⟩

end

end PrimeCostSpectrum
end NumberTheory
end IndisputableMonolith
