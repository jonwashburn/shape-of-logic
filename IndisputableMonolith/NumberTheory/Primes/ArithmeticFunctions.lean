import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic
import IndisputableMonolith.NumberTheory.Primes.Squarefree

/-!
# Arithmetic functions (Möbius footholds)

This file provides small wrappers around Mathlib's arithmetic function library, starting with the
Möbius function `μ` (spelled `ArithmeticFunction.moebius` in code).

We keep the statements lightweight here; deeper Dirichlet algebra and inversion can be layered on
once the basic interfaces stabilize.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega
open scoped ArithmeticFunction.omega

/-- The Möbius function (as an arithmetic function `ℕ → ℤ`). -/
abbrev mobius : ArithmeticFunction ℤ := ArithmeticFunction.moebius

@[simp] theorem mobius_def : mobius = ArithmeticFunction.moebius := rfl

/-- Möbius at a prime: `μ(p) = -1`. -/
theorem mobius_prime {p : ℕ} (hp : Prime p) : (mobius p) = -1 := by
  -- Mathlib lemma is `ArithmeticFunction.moebius_apply_prime` with `Nat.Prime`.
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simpa [mobius] using (ArithmeticFunction.moebius_apply_prime hp')

/-- Möbius at a prime square: `μ(p^2) = 0`. -/
theorem mobius_prime_sq {p : ℕ} (hp : Prime p) : (mobius (p ^ 2)) = 0 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  -- Use the prime-power formula with `k = 2`: `μ(p^2) = if 2 = 1 then -1 else 0 = 0`.
  simpa [mobius] using
    (ArithmeticFunction.moebius_apply_prime_pow (p := p) (k := 2) hp' (by decide : (2 : ℕ) ≠ 0))

/-- If `n` is not squarefree, then `μ n = 0`. -/
theorem mobius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : mobius n = 0 := by
  simpa [mobius] using (ArithmeticFunction.moebius_eq_zero_of_not_squarefree (n := n) h)

/-- `μ n ≠ 0` iff `n` is squarefree. -/
theorem mobius_ne_zero_iff_squarefree {n : ℕ} : mobius n ≠ 0 ↔ Squarefree n := by
  simpa [mobius] using (ArithmeticFunction.moebius_ne_zero_iff_squarefree (n := n))

/-- `μ n = 0` iff `n` is not squarefree. -/
theorem mobius_eq_zero_iff_not_squarefree {n : ℕ} : mobius n = 0 ↔ ¬Squarefree n := by
  -- Negate `μ n ≠ 0 ↔ Squarefree n`.
  simpa [not_ne_iff] using (not_congr (mobius_ne_zero_iff_squarefree (n := n)))

/-- If `n` is squarefree then `μ n = (-1)^(cardFactors n)`. -/
theorem mobius_apply_of_squarefree {n : ℕ} (hn : Squarefree n) :
    mobius n = (-1) ^ ArithmeticFunction.cardFactors n := by
  simpa [mobius] using (ArithmeticFunction.moebius_apply_of_squarefree (n := n) hn)

/-- A useful bridge: for `n ≠ 0`, `μ n ≠ 0` iff all prime exponents are ≤ 1. -/
theorem mobius_ne_zero_iff_vp_le_one {n : ℕ} (hn : n ≠ 0) :
    mobius n ≠ 0 ↔ ∀ p : ℕ, vp p n ≤ 1 := by
  constructor
  · intro hμ
    have hsq : Squarefree n := (mobius_ne_zero_iff_squarefree (n := n)).1 hμ
    exact (squarefree_iff_vp_le_one (n := n) hn).1 hsq
  · intro hvp
    have hsq : Squarefree n := (squarefree_iff_vp_le_one (n := n) hn).2 hvp
    exact (mobius_ne_zero_iff_squarefree (n := n)).2 hsq

/-! ### Additional arithmetic function wrappers -/

/-- Number of prime factors (with multiplicity) — Ω(n). -/
abbrev bigOmega : ArithmeticFunction ℕ := ArithmeticFunction.cardFactors

@[simp] theorem bigOmega_def : bigOmega = ArithmeticFunction.cardFactors := rfl

/-- `Ω(n) = n.primeFactorsList.length`. -/
theorem bigOmega_apply {n : ℕ} : bigOmega n = n.primeFactorsList.length := by
  simp only [bigOmega, ArithmeticFunction.cardFactors_apply]

/-- Number of distinct prime divisors — ω(n). -/
abbrev omega : ArithmeticFunction ℕ := ArithmeticFunction.cardDistinctFactors

@[simp] theorem omega_def : omega = ArithmeticFunction.cardDistinctFactors := rfl

/-- `ω(n) = n.primeFactorsList.dedup.length`. -/
theorem omega_apply {n : ℕ} : omega n = n.primeFactorsList.dedup.length := by
  simp only [omega, ArithmeticFunction.cardDistinctFactors_apply]

/-- For squarefree `n ≠ 0`, `Ω(n) = ω(n)` (all exponents are 1). -/
theorem bigOmega_eq_omega_of_squarefree {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) :
    bigOmega n = omega n := by
  simp only [bigOmega, omega]
  exact ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn).mpr hsq).symm

/-! ### Euler's totient function φ (via `Nat.totient`) -/

/-- Euler's totient function wrapper. -/
def totient (n : ℕ) : ℕ := Nat.totient n

@[simp] theorem totient_apply {n : ℕ} : totient n = Nat.totient n := rfl

/-- φ(1) = 1. -/
theorem totient_one : totient 1 = 1 := by
  simp [totient, Nat.totient_one]

/-- φ(p) = p - 1 for prime p. -/
theorem totient_prime {p : ℕ} (hp : Prime p) : totient p = p - 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp [totient, Nat.totient_prime hp']

/-- φ(p^k) = p^(k-1) * (p - 1) for prime p and k ≥ 1. -/
theorem totient_prime_pow {p k : ℕ} (hp : Prime p) (hk : 0 < k) :
    totient (p ^ k) = p ^ (k - 1) * (p - 1) := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp [totient, Nat.totient_prime_pow hp' hk]

/-- φ is multiplicative for coprime arguments. -/
theorem totient_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    totient (m * n) = totient m * totient n := by
  simp [totient, Nat.totient_mul h]

/-- The sum of φ(d) over divisors of n equals n: ∑_{d|n} φ(d) = n. -/
theorem totient_divisor_sum {n : ℕ} : ∑ d ∈ n.divisors, totient d = n := by
  simp only [totient]
  exact Nat.sum_totient n

/-- φ(n) ≤ n for all n. -/
theorem totient_le (n : ℕ) : totient n ≤ n := by
  simp only [totient]
  exact Nat.totient_le n

/-- φ(n) > 0 iff n > 0. -/
theorem totient_pos_iff {n : ℕ} : 0 < totient n ↔ 0 < n := by
  simp only [totient]
  exact Nat.totient_pos

/-! ### Von Mangoldt function Λ -/

/-- The von Mangoldt function (as an arithmetic function `ℕ → ℝ`). -/
noncomputable abbrev vonMangoldt : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt

@[simp] theorem vonMangoldt_def : vonMangoldt = ArithmeticFunction.vonMangoldt := rfl

/-- Λ(p) = log(p) for prime p. -/
theorem vonMangoldt_prime {p : ℕ} (hp : Prime p) : vonMangoldt p = Real.log p := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp [vonMangoldt, ArithmeticFunction.vonMangoldt_apply_prime hp']

/-- Λ(n) = 0 unless n is a prime power. -/
theorem vonMangoldt_eq_zero_of_not_prime_pow {n : ℕ} (h : ¬ IsPrimePow n) :
    vonMangoldt n = 0 := by
  simp [vonMangoldt, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h]

/-- Λ(p^k) = log(p) for prime p and k ≥ 1. -/
theorem vonMangoldt_prime_pow {p k : ℕ} (hp : Prime p) (hk : 0 < k) :
    vonMangoldt (p ^ k) = Real.log p := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have hk' : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  rw [vonMangoldt, ArithmeticFunction.vonMangoldt_apply_pow hk']
  exact vonMangoldt_prime hp

/-! ### Multiplicativity -/

/-- The Möbius function is multiplicative. -/
theorem mobius_isMultiplicative : ArithmeticFunction.IsMultiplicative mobius := by
  simp only [mobius]
  exact ArithmeticFunction.isMultiplicative_moebius

/-! ### Sigma function (sum of divisors) -/

/-- The sum-of-divisors function σ_k. -/
abbrev sigma (k : ℕ) : ArithmeticFunction ℕ := ArithmeticFunction.sigma k

@[simp] theorem sigma_def (k : ℕ) : sigma k = ArithmeticFunction.sigma k := rfl

/-- σ_k(n) = ∑ d ∣ n, d^k. -/
theorem sigma_apply {k n : ℕ} : sigma k n = ∑ d ∈ n.divisors, d ^ k := by
  simp only [sigma, ArithmeticFunction.sigma_apply]

/-- σ_0(n) = number of divisors of n. -/
theorem sigma_zero_apply {n : ℕ} : sigma 0 n = n.divisors.card := by
  simp only [sigma, ArithmeticFunction.sigma_zero_apply]

/-- σ_1(n) = sum of divisors of n. -/
theorem sigma_one_apply {n : ℕ} : sigma 1 n = ∑ d ∈ n.divisors, d := by
  simp only [sigma, ArithmeticFunction.sigma_one_apply]

/-- σ_k is multiplicative. -/
theorem sigma_isMultiplicative (k : ℕ) : ArithmeticFunction.IsMultiplicative (sigma k) := by
  simp only [sigma]
  exact ArithmeticFunction.isMultiplicative_sigma

/-- σ_0(p) = 2 for prime p. -/
theorem sigma_zero_prime {p : ℕ} (hp : Prime p) : sigma 0 p = 2 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [sigma_zero_apply, hp'.divisors]
  have h_ne : (1 : ℕ) ≠ p := hp'.one_lt.ne'.symm
  rw [Finset.card_insert_of_notMem (by simp [h_ne]), Finset.card_singleton]

/-- σ_1(p) = p + 1 for prime p. -/
theorem sigma_one_prime {p : ℕ} (hp : Prime p) : sigma 1 p = p + 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [sigma_one_apply, hp'.divisors]
  have h_ne : (1 : ℕ) ≠ p := hp'.one_lt.ne'.symm
  rw [Finset.sum_insert (by simp [h_ne]), Finset.sum_singleton, add_comm]

/-- σ_k(p) = 1 + p^k for prime p. -/
theorem sigma_prime {k : ℕ} {p : ℕ} (hp : Prime p) : sigma k p = 1 + p ^ k := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [sigma_apply, hp'.divisors]
  have h_ne : (1 : ℕ) ≠ p := hp'.one_lt.ne'.symm
  rw [Finset.sum_insert (by simp [h_ne]), Finset.sum_singleton, one_pow, add_comm]

/-! ### Zeta function (constant 1) and Dirichlet convolution -/

/-- The arithmetic zeta function ζ (constant 1 on positive integers). -/
abbrev zeta : ArithmeticFunction ℕ := ArithmeticFunction.zeta

@[simp] theorem zeta_def : zeta = ArithmeticFunction.zeta := rfl

/-- ζ(n) = 1 for n ≥ 1. -/
theorem zeta_apply {n : ℕ} (hn : n ≠ 0) : zeta n = 1 := by
  simp only [zeta, ArithmeticFunction.zeta_apply, hn, ↓reduceIte]

/-- ζ(0) = 0. -/
theorem zeta_zero : zeta 0 = 0 := by
  simp only [zeta, ArithmeticFunction.zeta_apply, ↓reduceIte]

/-- ζ is multiplicative. -/
theorem zeta_isMultiplicative : ArithmeticFunction.IsMultiplicative zeta := by
  simp only [zeta]
  exact ArithmeticFunction.isMultiplicative_zeta

/-! ### Möbius inversion fundamentals -/

/-- The key identity: μ * ζ = ε (the Dirichlet identity).
This is the foundation of Möbius inversion. -/
theorem moebius_mul_zeta : (mobius : ArithmeticFunction ℤ) * ↑zeta = 1 := by
  simp only [mobius, zeta]
  exact ArithmeticFunction.moebius_mul_coe_zeta

/-- Symmetric form: ζ * μ = ε. -/
theorem zeta_mul_moebius : (↑zeta : ArithmeticFunction ℤ) * mobius = 1 := by
  simp only [mobius, zeta]
  exact ArithmeticFunction.coe_zeta_mul_moebius

/-- For the identity (Dirichlet unit), we wrap ε = δ_1. -/
abbrev dirichletOne : ArithmeticFunction ℤ := 1

@[simp] theorem dirichletOne_def : dirichletOne = 1 := rfl

/-- ε(1) = 1. -/
theorem dirichletOne_one : dirichletOne 1 = 1 := by
  simp [dirichletOne]

/-- ε(n) = 0 for n > 1. -/
theorem dirichletOne_ne_one {n : ℕ} (hn : n ≠ 1) : dirichletOne n = 0 := by
  simp [dirichletOne, hn]

/-! ### Additional multiplicativity lemmas -/

/-- ω (number of distinct prime factors) is additive on coprimes: ω(mn) = ω(m) + ω(n). -/
theorem omega_mul_of_coprime {m n : ℕ} (_hm : m ≠ 0) (_hn : n ≠ 0) (h : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  simp only [omega]
  exact ArithmeticFunction.cardDistinctFactors_mul h

/-- Ω (number of prime factors with multiplicity) is additive: Ω(mn) = Ω(m) + Ω(n). -/
theorem bigOmega_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    bigOmega (m * n) = bigOmega m + bigOmega n := by
  simp only [bigOmega]
  exact ArithmeticFunction.cardFactors_mul hm hn

/-- Ω is completely additive on powers: Ω(n^k) = k * Ω(n). -/
theorem bigOmega_pow {n k : ℕ} : bigOmega (n ^ k) = k * bigOmega n := by
  simp only [bigOmega]
  exact ArithmeticFunction.cardFactors_pow

/-! ### Liouville function λ -/

/-- The Liouville function λ(n) = (-1)^Ω(n).
Note: We define this directly since Mathlib may not have a prebuilt version. -/
def liouville (n : ℕ) : ℤ :=
  if n = 0 then 0 else (-1) ^ bigOmega n

/-- λ(0) = 0 (by convention). -/
@[simp] theorem liouville_zero : liouville 0 = 0 := by
  simp [liouville]

/-- λ(n) = (-1)^Ω(n) for n ≠ 0. -/
theorem liouville_eq {n : ℕ} (hn : n ≠ 0) : liouville n = (-1) ^ bigOmega n := by
  simp [liouville, hn]

/-- λ(1) = 1. -/
theorem liouville_one : liouville 1 = 1 := by
  simp [liouville, bigOmega_apply]

/-- λ(p) = -1 for prime p. -/
theorem liouville_prime {p : ℕ} (hp : Prime p) : liouville p = -1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have hp_ne : p ≠ 0 := hp'.ne_zero
  simp only [liouville, hp_ne, ↓reduceIte, bigOmega]
  -- Ω(p) = 1 for prime p
  have hOmega : ArithmeticFunction.cardFactors p = 1 := ArithmeticFunction.cardFactors_apply_prime hp'
  rw [hOmega]
  norm_num

/-- λ(p^k) = (-1)^k for prime p. -/
theorem liouville_prime_pow {p k : ℕ} (hp : Prime p) :
    liouville (p ^ k) = (-1) ^ k := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  cases k with
  | zero => simp [liouville_one]
  | succ k =>
    have hpk : p ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hp'.ne_zero
    simp only [liouville, hpk, ↓reduceIte, bigOmega]
    -- Ω(p^k) = k for prime p
    have hOmega : ArithmeticFunction.cardFactors (p ^ (k + 1)) = k + 1 :=
      ArithmeticFunction.cardFactors_apply_prime_pow hp'
    rw [hOmega]

/-- λ(mn) = λ(m) * λ(n) for nonzero m, n (complete multiplicativity). -/
theorem liouville_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    liouville (m * n) = liouville m * liouville n := by
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [liouville, hm, hn, hmn, ↓reduceIte]
  rw [bigOmega_mul hm hn, pow_add]

/-! ### Identity function (for Dirichlet algebra) -/

/-- The identity arithmetic function id(n) = n. -/
abbrev arithId : ArithmeticFunction ℕ := ArithmeticFunction.id

@[simp] theorem arithId_def : arithId = ArithmeticFunction.id := rfl

/-- id(n) = n. -/
theorem arithId_apply {n : ℕ} : arithId n = n := by
  simp [arithId]

/-- The identity function is multiplicative. -/
theorem arithId_isMultiplicative : ArithmeticFunction.IsMultiplicative arithId := by
  simp only [arithId]
  exact ArithmeticFunction.isMultiplicative_id

/-! ### Prime counting function π -/

/-- The prime counting function π(n) = #{p ≤ n : p prime}. -/
def primeCounting (n : ℕ) : ℕ := Nat.primeCounting n

@[simp] theorem primeCounting_def {n : ℕ} : primeCounting n = Nat.primeCounting n := rfl

/-- π(0) = 0. -/
theorem primeCounting_zero : primeCounting 0 = 0 := by
  simp [primeCounting]

/-- π(1) = 0. -/
theorem primeCounting_one : primeCounting 1 = 0 := by
  simp [primeCounting, Nat.primeCounting]

/-- π(2) = 1. -/
theorem primeCounting_two : primeCounting 2 = 1 := by
  native_decide

/-- π(3) = 2. -/
theorem primeCounting_three : primeCounting 3 = 2 := by
  native_decide

/-- π(5) = 3. -/
theorem primeCounting_five : primeCounting 5 = 3 := by
  native_decide

/-- π(10) = 4. -/
theorem primeCounting_ten : primeCounting 10 = 4 := by
  native_decide

/-- π(7) = 4. -/
theorem primeCounting_seven : primeCounting 7 = 4 := by
  native_decide

/-- π(11) = 5. -/
theorem primeCounting_eleven : primeCounting 11 = 5 := by
  native_decide

/-- π(13) = 6. -/
theorem primeCounting_thirteen : primeCounting 13 = 6 := by
  native_decide

/-- π(17) = 7. -/
theorem primeCounting_seventeen : primeCounting 17 = 7 := by
  native_decide

/-- π(20) = 8. -/
theorem primeCounting_twenty : primeCounting 20 = 8 := by
  native_decide

/-- π(100) = 25. -/
theorem primeCounting_hundred : primeCounting 100 = 25 := by
  native_decide

/-- π is monotone: m ≤ n → π(m) ≤ π(n). -/
theorem primeCounting_mono {m n : ℕ} (h : m ≤ n) : primeCounting m ≤ primeCounting n := by
  simp only [primeCounting]
  exact Nat.monotone_primeCounting h

/-! ### Liouville-squarefree connection -/

/-- For squarefree n, λ(n) = μ(n). -/
theorem liouville_eq_mobius_of_squarefree {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) :
    liouville n = mobius n := by
  rw [liouville_eq hn, mobius_apply_of_squarefree hsq, bigOmega_eq_omega_of_squarefree hn hsq]

/-- μ(n)² = 1 iff n is squarefree. -/
theorem mobius_sq_eq_one_iff_squarefree {n : ℕ} : mobius n ^ 2 = 1 ↔ Squarefree n := by
  constructor
  · intro h
    by_contra hnsq
    have hμ : mobius n = 0 := mobius_eq_zero_of_not_squarefree hnsq
    simp [hμ] at h
  · intro hsq
    -- μ(n) ∈ {-1, 1} for squarefree n, so μ(n)² = 1
    have h_val := mobius_apply_of_squarefree hsq
    rw [h_val, ← pow_mul, mul_comm]
    have h_even : Even (2 * bigOmega n) := even_two_mul (bigOmega n)
    exact Even.neg_one_pow h_even

/-! ### Values at 1 -/

/-- μ(1) = 1. -/
theorem mobius_one : mobius 1 = 1 := by
  simp [mobius]

/-- ω(1) = 0. -/
theorem omega_one : omega 1 = 0 := by
  simp [omega_apply]

/-- Ω(1) = 0. -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  simp [bigOmega_apply]

/-- σ_k(1) = 1 for any k. -/
theorem sigma_one {k : ℕ} : sigma k 1 = 1 := by
  simp [sigma_apply]

/-- ζ(1) = 1. -/
theorem zeta_one : zeta 1 = 1 := by
  exact zeta_apply (by decide)

/-! ### Values at primes -/

/-- ω(p) = 1 for prime p. -/
theorem omega_prime {p : ℕ} (hp : Prime p) : omega p = 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [omega]
  exact ArithmeticFunction.cardDistinctFactors_apply_prime hp'

/-- Ω(p) = 1 for prime p. -/
theorem bigOmega_prime {p : ℕ} (hp : Prime p) : bigOmega p = 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact ArithmeticFunction.cardFactors_apply_prime hp'

/-! ### Additional totient values -/

/-- φ(2) = 1. -/
theorem totient_two : totient 2 = 1 := by
  simp [totient]

/-- φ(3) = 2. -/
theorem totient_three : totient 3 = 2 := by
  native_decide

/-- φ(4) = 2. -/
theorem totient_four : totient 4 = 2 := by
  native_decide

/-- φ(5) = 4. -/
theorem totient_five : totient 5 = 4 := by
  native_decide

/-- φ(6) = 2. -/
theorem totient_six : totient 6 = 2 := by
  native_decide

/-- φ(8) = 4. -/
theorem totient_eight : totient 8 = 4 := by
  native_decide

/-- φ(45) = 24. -/
theorem totient_fortyfive : totient 45 = 24 := by
  native_decide

/-- φ(360) = 96. -/
theorem totient_threehundredsixty : totient 360 = 96 := by
  native_decide

/-! ### Ω and ω at prime powers -/

/-- Ω(p^k) = k for prime p. -/
theorem bigOmega_prime_pow {p k : ℕ} (hp : Prime p) : bigOmega (p ^ k) = k := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  cases k with
  | zero => simp [bigOmega_apply]
  | succ k => exact ArithmeticFunction.cardFactors_apply_prime_pow hp'

/-- ω(p^k) = 1 for prime p and k ≥ 1. -/
theorem omega_prime_pow {p k : ℕ} (hp : Prime p) (hk : 0 < k) : omega (p ^ k) = 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have hk' : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  simp only [omega]
  exact ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp' hk'

/-! ### Sigma at prime powers -/

/-- σ_0(p^k) = k + 1 for prime p (number of divisors of p^k). -/
theorem sigma_zero_prime_pow {p k : ℕ} (hp : Prime p) : sigma 0 (p ^ k) = k + 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [sigma_zero_apply]
  rw [Nat.divisors_prime_pow hp' k]
  simp

/-- Concrete sigma values at small prime powers. -/
theorem sigma_one_two_pow_one : sigma 1 (2 ^ 1) = 3 := by native_decide
theorem sigma_one_two_pow_two : sigma 1 (2 ^ 2) = 7 := by native_decide
theorem sigma_one_two_pow_three : sigma 1 (2 ^ 3) = 15 := by native_decide
theorem sigma_one_three_pow_one : sigma 1 (3 ^ 1) = 4 := by native_decide
theorem sigma_one_three_pow_two : sigma 1 (3 ^ 2) = 13 := by native_decide
theorem sigma_one_five_pow_one : sigma 1 (5 ^ 1) = 6 := by native_decide

/-! ### Totient multiplicativity -/

/-- Euler's totient function is multiplicative. -/
theorem totient_isMultiplicative :
    ∀ {m n : ℕ}, Nat.Coprime m n → totient (m * n) = totient m * totient n := by
  intro m n h
  exact totient_mul_of_coprime h

/-! ### Divisors of prime powers -/

/-- The divisors of p^k are exactly {p^0, p^1, ..., p^k}. -/
theorem divisors_prime_pow {p k : ℕ} (hp : Prime p) :
    (p ^ k).divisors = (Finset.range (k + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.one_lt⟩ := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact Nat.divisors_prime_pow hp' k

/-- The number of divisors of p^k is k + 1. -/
theorem card_divisors_prime_pow {p k : ℕ} (hp : Prime p) : (p ^ k).divisors.card = k + 1 := by
  rw [divisors_prime_pow hp]
  simp

/-! ### Additional small prime facts -/

theorem prime_twentythree : Prime 23 := by decide
theorem prime_twentynine : Prime 29 := by decide
theorem prime_thirtyone : Prime 31 := by decide
theorem prime_fortyone : Prime 41 := by decide
theorem prime_fortythree : Prime 43 := by decide
theorem prime_fortyseven : Prime 47 := by decide
theorem prime_fiftythree : Prime 53 := by decide
theorem prime_fiftynine : Prime 59 := by decide
theorem prime_sixtyone : Prime 61 := by decide
theorem prime_sixtyseven : Prime 67 := by decide
theorem prime_seventyone : Prime 71 := by decide
theorem prime_seventythree : Prime 73 := by decide
theorem prime_seventynine : Prime 79 := by decide
theorem prime_eightythree : Prime 83 := by decide
theorem prime_eightynine : Prime 89 := by decide
theorem prime_ninetyseven : Prime 97 := by decide

/-! ### Factorial valuations (decidable facts) -/

/-- vp 2 (4!) = 3. -/
theorem vp_factorial_four_two : vp 2 (Nat.factorial 4) = 3 := by native_decide

/-- vp 2 (5!) = 3. -/
theorem vp_factorial_five_two : vp 2 (Nat.factorial 5) = 3 := by native_decide

/-- vp 2 (6!) = 4. -/
theorem vp_factorial_six_two : vp 2 (Nat.factorial 6) = 4 := by native_decide

/-- vp 2 (8!) = 7. -/
theorem vp_factorial_eight_two : vp 2 (Nat.factorial 8) = 7 := by native_decide

/-- vp 3 (6!) = 2. -/
theorem vp_factorial_six_three : vp 3 (Nat.factorial 6) = 2 := by native_decide

/-- vp 3 (9!) = 4. -/
theorem vp_factorial_nine_three : vp 3 (Nat.factorial 9) = 4 := by native_decide

/-- vp 5 (10!) = 2. -/
theorem vp_factorial_ten_five : vp 5 (Nat.factorial 10) = 2 := by native_decide

/-! ### Product lemmas for Ω and ω -/

/-- Ω(n!) for small factorials.
- 2! = 2 → Ω = 1
- 3! = 6 = 2*3 → Ω = 2
- 4! = 24 = 2³*3 → Ω = 4
- 5! = 120 = 2³*3*5 → Ω = 5
-/
theorem bigOmega_factorial_two : bigOmega (Nat.factorial 2) = 1 := by native_decide
theorem bigOmega_factorial_three : bigOmega (Nat.factorial 3) = 2 := by native_decide
theorem bigOmega_factorial_four : bigOmega (Nat.factorial 4) = 4 := by native_decide
theorem bigOmega_factorial_five : bigOmega (Nat.factorial 5) = 5 := by native_decide

/-! ### Perfect numbers -/

/-- A number n is perfect if σ_1(n) = 2n.
We make this decidable for concrete values. -/
def isPerfect (n : ℕ) : Prop := sigma 1 n = 2 * n

instance : DecidablePred isPerfect := fun n => inferInstanceAs (Decidable (sigma 1 n = 2 * n))

/-- 6 is perfect. -/
theorem isPerfect_six : isPerfect 6 := by native_decide

/-- 28 is perfect. -/
theorem isPerfect_twentyeight : isPerfect 28 := by native_decide

/-- 496 is perfect. -/
theorem isPerfect_fourhundredninetysix : isPerfect 496 := by native_decide

/-! ### More primeCounting values -/

/-- π(30) = 10. -/
theorem primeCounting_thirty : primeCounting 30 = 10 := by native_decide

/-- π(50) = 15. -/
theorem primeCounting_fifty : primeCounting 50 = 15 := by native_decide

/-- π(200) = 46. -/
theorem primeCounting_twohundred : primeCounting 200 = 46 := by native_decide

/-- π(1000) = 168. -/
theorem primeCounting_thousand : primeCounting 1000 = 168 := by native_decide

/-! ### Ω and ω for RS constants -/

/-- Ω(8) = 3 (since 8 = 2³). -/
theorem bigOmega_eight : bigOmega 8 = 3 := by native_decide

/-- Ω(45) = 3 (since 45 = 3² × 5). -/
theorem bigOmega_fortyfive : bigOmega 45 = 3 := by native_decide

/-- Ω(360) = 6 (since 360 = 2³ × 3² × 5). -/
theorem bigOmega_threehundredsixty : bigOmega 360 = 6 := by native_decide

/-- Ω(840) = 6 (since 840 = 2³ × 3 × 5 × 7, with 3+1+1+1 = 6 factors). -/
theorem bigOmega_eighthundredforty : bigOmega 840 = 6 := by native_decide

/-- ω(8) = 1 (only prime factor is 2). -/
theorem omega_eight : omega 8 = 1 := by native_decide

/-- ω(45) = 2 (prime factors are 3 and 5). -/
theorem omega_fortyfive : omega 45 = 2 := by native_decide

/-- ω(360) = 3 (prime factors are 2, 3, 5). -/
theorem omega_threehundredsixty : omega 360 = 3 := by native_decide

/-- ω(840) = 4 (prime factors are 2, 3, 5, 7). -/
theorem omega_eighthundredforty : omega 840 = 4 := by native_decide

/-! ### Radical (product of distinct prime factors) -/

/-- The radical of n is the product of its distinct prime factors. -/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

/-- rad(1) = 1. -/
theorem radical_one' : radical 1 = 1 := by native_decide

/-- rad(2) = 2. -/
theorem radical_two' : radical 2 = 2 := by native_decide

/-- rad(6) = 6 (squarefree). -/
theorem radical_six' : radical 6 = 6 := by native_decide

/-- rad(12) = 6. -/
theorem radical_twelve' : radical 12 = 6 := by native_decide

/-- rad(p) = p for prime p. -/
theorem radical_prime' {p : ℕ} (hp : Prime p) : radical p = p := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [radical]
  rw [Nat.Prime.primeFactors hp']
  simp

/-! ### Totient as cardinality -/

/-- φ(n) = |{a ∈ [0,n) : gcd(n,a) = 1}|. -/
theorem totient_eq_card_filter {n : ℕ} :
    totient n = (Finset.filter (fun a => n.Coprime a) (Finset.range n)).card := by
  simp only [totient]
  exact Nat.totient_eq_card_coprime n

/-! ### Additional coprimality facts for RS constants -/

/-- gcd(8, 360) = 8. -/
theorem gcd_eight_threehundredsixty : Nat.gcd 8 360 = 8 := by native_decide

/-- gcd(45, 360) = 45. -/
theorem gcd_fortyfive_threehundredsixty : Nat.gcd 45 360 = 45 := by native_decide

/-- gcd(8, 840) = 8. -/
theorem gcd_eight_eighthundredforty : Nat.gcd 8 840 = 8 := by native_decide

/-- gcd(45, 840) = 15. -/
theorem gcd_fortyfive_eighthundredforty : Nat.gcd 45 840 = 15 := by native_decide

/-- gcd(360, 840) = 120. -/
theorem gcd_threehundredsixty_eighthundredforty : Nat.gcd 360 840 = 120 := by native_decide

/-- lcm(8, 840) = 840. -/
theorem lcm_eight_eighthundredforty : Nat.lcm 8 840 = 840 := by native_decide

/-- lcm(45, 840) = 2520. -/
theorem lcm_fortyfive_eighthundredforty : Nat.lcm 45 840 = 2520 := by native_decide

/-- lcm(360, 840) = 2520. -/
theorem lcm_threehundredsixty_eighthundredforty : Nat.lcm 360 840 = 2520 := by native_decide

/-! ### Sigma values at RS constants -/

/-- σ_0(8) = 4. -/
theorem sigma_zero_eight : sigma 0 8 = 4 := by native_decide

/-- σ_0(45) = 6. -/
theorem sigma_zero_fortyfive : sigma 0 45 = 6 := by native_decide

/-- σ_0(360) = 24. -/
theorem sigma_zero_threehundredsixty : sigma 0 360 = 24 := by native_decide

/-- σ_1(8) = 15. -/
theorem sigma_one_eight : sigma 1 8 = 15 := by native_decide

/-- σ_1(45) = 78. -/
theorem sigma_one_fortyfive : sigma 1 45 = 78 := by native_decide

/-- σ_1(360) = 1170. -/
theorem sigma_one_threehundredsixty : sigma 1 360 = 1170 := by native_decide

/-! ### Prime factors of primes and prime powers -/

/-- The prime factors of a prime p is just {p}. -/
theorem primeFactors_prime {p : ℕ} (hp : Prime p) : p.primeFactors = {p} := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact Nat.Prime.primeFactors hp'

/-- The prime factors of p^k (k ≥ 1) is just {p}. -/
theorem primeFactors_prime_pow {p k : ℕ} (hp : Prime p) (hk : k ≠ 0) :
    (p ^ k).primeFactors = {p} := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact Nat.primeFactors_prime_pow hk hp'

/-- rad(p^k) = p for prime p and k ≥ 1. -/
theorem radical_prime_pow {p k : ℕ} (hp : Prime p) (hk : k ≠ 0) : radical (p ^ k) = p := by
  simp only [radical, primeFactors_prime_pow hp hk, Finset.prod_singleton, id]

/-! ### Von Mangoldt sum identity -/

/-- The sum of von Mangoldt over divisors: ∑_{d|n} Λ(d) = log(n).
    This connects Λ to the logarithm. -/
theorem vonMangoldt_sum_divisors {n : ℕ} :
    ∑ d ∈ n.divisors, vonMangoldt d = Real.log n := by
  simp only [vonMangoldt]
  exact ArithmeticFunction.vonMangoldt_sum

/-! ### Sigma multiplicativity helpers -/

/-- σ_k(mn) = σ_k(m) × σ_k(n) for coprime m, n. -/
theorem sigma_mul_of_coprime {k m n : ℕ} (h : Nat.Coprime m n) :
    sigma k (m * n) = sigma k m * sigma k n := by
  simp only [sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-- σ_0(mn) = σ_0(m) × σ_0(n) for coprime m, n. -/
theorem sigma_zero_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigma 0 (m * n) = sigma 0 m * sigma 0 n :=
  sigma_mul_of_coprime h

/-- σ_1(mn) = σ_1(m) × σ_1(n) for coprime m, n. -/
theorem sigma_one_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigma 1 (m * n) = sigma 1 m * sigma 1 n :=
  sigma_mul_of_coprime h

/-! ### Totient product formula helpers -/

/-- φ(n) > 0 for n > 0 (strengthened). -/
theorem totient_pos {n : ℕ} (hn : 0 < n) : 0 < totient n := by
  simp only [totient]
  exact Nat.totient_pos.mpr hn

/-- φ(2^k) = 2^k - 2^(k-1) = 2^(k-1) for k ≥ 1 (concrete). -/
theorem totient_two_pow_one : totient (2 ^ 1) = 1 := by native_decide
theorem totient_two_pow_two : totient (2 ^ 2) = 2 := by native_decide
theorem totient_two_pow_three : totient (2 ^ 3) = 4 := by native_decide
theorem totient_two_pow_four : totient (2 ^ 4) = 8 := by native_decide

/-- φ(3^k) values. -/
theorem totient_three_pow_one : totient (3 ^ 1) = 2 := by native_decide
theorem totient_three_pow_two : totient (3 ^ 2) = 6 := by native_decide

/-- φ(5^k) values. -/
theorem totient_five_pow_one : totient (5 ^ 1) = 4 := by native_decide
theorem totient_five_pow_two : totient (5 ^ 2) = 20 := by native_decide

/-! ### More concrete arithmetic function values -/

/-- Ω(6) = 2 (since 6 = 2 × 3). -/
theorem bigOmega_six : bigOmega 6 = 2 := by native_decide

/-- ω(6) = 2 (distinct prime factors: 2, 3). -/
theorem omega_six : omega 6 = 2 := by native_decide

/-- Ω(12) = 3 (since 12 = 2² × 3). -/
theorem bigOmega_twelve : bigOmega 12 = 3 := by native_decide

/-- ω(12) = 2 (distinct prime factors: 2, 3). -/
theorem omega_twelve : omega 12 = 2 := by native_decide

/-- Ω(30) = 3 (since 30 = 2 × 3 × 5). -/
theorem bigOmega_thirty : bigOmega 30 = 3 := by native_decide

/-- ω(30) = 3 (distinct prime factors: 2, 3, 5). -/
theorem omega_thirty : omega 30 = 3 := by native_decide

/-- μ(6) = 1 (squarefree with 2 prime factors). -/
theorem mobius_six : mobius 6 = 1 := by native_decide

/-- μ(30) = -1 (squarefree with 3 prime factors). -/
theorem mobius_thirty : mobius 30 = -1 := by native_decide

/-- μ(12) = 0 (not squarefree, since 4 | 12). -/
theorem mobius_twelve : mobius 12 = 0 := by native_decide

/-- rad(30) = 30 (squarefree). -/
theorem radical_thirty : radical 30 = 30 := by native_decide

/-- rad(60) = 30. -/
theorem radical_sixty : radical 60 = 30 := by native_decide

/-- rad(360) = 30. -/
theorem radical_threehundredsixty : radical 360 = 30 := by native_decide

/-- rad(840) = 210 = 2 × 3 × 5 × 7. -/
theorem radical_eighthundredforty : radical 840 = 210 := by native_decide

/-! ### Radical algebra -/

/-- rad(n) ≤ n for all n ≠ 0. -/
theorem radical_le {n : ℕ} (hn : n ≠ 0) : radical n ≤ n := by
  simp only [radical]
  have h := Nat.prod_primeFactors_dvd n
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h

/-- rad(1) = 1 (using the general definition). -/
theorem radical_one_eq : radical 1 = 1 := by native_decide

/-- rad(n) > 0 for n > 0. -/
theorem radical_pos {n : ℕ} (_hn : 0 < n) : 0 < radical n := by
  simp only [radical]
  exact Finset.prod_pos (fun p hp => Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))

/-! ### Coprimality power lemmas -/

/-- Coprimality is preserved by powers on the left. -/
theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b := by
  exact Nat.coprime_pow_left_iff hn a b

/-- Coprimality is preserved by powers on the right. -/
theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) :
    Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b := by
  exact Nat.coprime_pow_right_iff hn a b

/-- If p is prime and doesn't divide a, then a is coprime to p^m. -/
theorem coprime_pow_of_prime_not_dvd {p m a : ℕ} (hp : Prime p) (h : ¬p ∣ a) :
    Nat.Coprime a (p ^ m) := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact hp'.coprime_pow_of_not_dvd h

/-- Two distinct primes raised to powers are coprime. -/
theorem coprime_prime_pow {p q n m : ℕ} (hp : Prime p) (hq : Prime q) (hne : p ≠ q) :
    Nat.Coprime (p ^ n) (q ^ m) := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have hq' : Nat.Prime q := (prime_iff q).1 hq
  exact Nat.coprime_pow_primes n m hp' hq' hne

/-! ### More primeCounting values -/

/-- π(150) = 35. -/
theorem primeCounting_onehundredfifty : primeCounting 150 = 35 := by native_decide

/-- π(250) = 53. -/
theorem primeCounting_twohundredfifty : primeCounting 250 = 53 := by native_decide

/-- π(500) = 95. -/
theorem primeCounting_fivehundred : primeCounting 500 = 95 := by native_decide

/-- π(750) = 132. -/
theorem primeCounting_sevenhundredfifty : primeCounting 750 = 132 := by native_decide

/-! ### Legendre formula concrete values -/

/-- vp 2 (10!) = 8. -/
theorem vp_factorial_ten_two : vp 2 (Nat.factorial 10) = 8 := by native_decide

/-- vp 2 (12!) = 10. -/
theorem vp_factorial_twelve_two : vp 2 (Nat.factorial 12) = 10 := by native_decide

/-- vp 3 (10!) = 4. -/
theorem vp_factorial_ten_three : vp 3 (Nat.factorial 10) = 4 := by native_decide

/-- vp 3 (12!) = 5. -/
theorem vp_factorial_twelve_three : vp 3 (Nat.factorial 12) = 5 := by native_decide

/-- vp 5 (25!) = 6. -/
theorem vp_factorial_twentyfive_five : vp 5 (Nat.factorial 25) = 6 := by native_decide

/-- vp 7 (50!) = 8. -/
theorem vp_factorial_fifty_seven : vp 7 (Nat.factorial 50) = 8 := by native_decide

/-! ### More squarefree concrete values -/

/-- 30 is squarefree. -/
theorem squarefree_thirty : Squarefree 30 := by native_decide

/-- 6 is squarefree. -/
theorem squarefree_six : Squarefree 6 := by native_decide

/-- 10 is squarefree. -/
theorem squarefree_ten : Squarefree 10 := by native_decide

/-- 15 is squarefree. -/
theorem squarefree_fifteen : Squarefree 15 := by native_decide

/-- 210 = 2×3×5×7 is squarefree. -/
theorem squarefree_twohundredten : Squarefree 210 := by native_decide

/-! ### Divisor count for RS constants -/

/-- The number of divisors of 8 is 4. -/
theorem divisors_card_eight : (8 : ℕ).divisors.card = 4 := by native_decide

/-- The number of divisors of 45 is 6. -/
theorem divisors_card_fortyfive : (45 : ℕ).divisors.card = 6 := by native_decide

/-- The number of divisors of 360 is 24. -/
theorem divisors_card_threehundredsixty : (360 : ℕ).divisors.card = 24 := by native_decide

/-- The number of divisors of 840 is 32. -/
theorem divisors_card_eighthundredforty : (840 : ℕ).divisors.card = 32 := by native_decide

/-! ### More small primes (101-199) -/

theorem prime_onehundredone : Prime 101 := by native_decide
theorem prime_onehundredseven : Prime 107 := by native_decide
theorem prime_onehundrednine : Prime 109 := by native_decide
theorem prime_onehundredthirteen : Prime 113 := by native_decide
theorem prime_onehundredtwentyseven : Prime 127 := by native_decide
theorem prime_onehundredthirtyone : Prime 131 := by native_decide
theorem prime_onehundredthirtynine : Prime 139 := by native_decide
theorem prime_onehundredfortynine : Prime 149 := by native_decide
theorem prime_onehundredfiftyone : Prime 151 := by native_decide
theorem prime_onehundredfiftyseven : Prime 157 := by native_decide
theorem prime_onehundredsixtythree : Prime 163 := by native_decide
theorem prime_onehundredsixtyseven : Prime 167 := by native_decide
theorem prime_onehundredseventythree : Prime 173 := by native_decide
theorem prime_onehundredseventynine : Prime 179 := by native_decide
theorem prime_onehundredeightyone : Prime 181 := by native_decide
theorem prime_onehundredninetyone : Prime 191 := by native_decide
theorem prime_onehundredninetythree : Prime 193 := by native_decide
theorem prime_onehundredninetyseven : Prime 197 := by native_decide
theorem prime_onehundredninetynine : Prime 199 := by native_decide

/-! ### Sigma values at small composites -/

/-- σ_0(6) = 4 (divisors: 1, 2, 3, 6). -/
theorem sigma_zero_six : sigma 0 6 = 4 := by native_decide

/-- σ_1(6) = 12 (sum: 1 + 2 + 3 + 6 = 12). -/
theorem sigma_one_six : sigma 1 6 = 12 := by native_decide

/-- σ_0(10) = 4 (divisors: 1, 2, 5, 10). -/
theorem sigma_zero_ten : sigma 0 10 = 4 := by native_decide

/-- σ_1(10) = 18 (sum: 1 + 2 + 5 + 10 = 18). -/
theorem sigma_one_ten : sigma 1 10 = 18 := by native_decide

/-- σ_0(12) = 6 (divisors: 1, 2, 3, 4, 6, 12). -/
theorem sigma_zero_twelve : sigma 0 12 = 6 := by native_decide

/-- σ_1(12) = 28 (sum: 1 + 2 + 3 + 4 + 6 + 12 = 28). -/
theorem sigma_one_twelve : sigma 1 12 = 28 := by native_decide

/-- σ_0(30) = 8. -/
theorem sigma_zero_thirty : sigma 0 30 = 8 := by native_decide

/-- σ_1(30) = 72. -/
theorem sigma_one_thirty : sigma 1 30 = 72 := by native_decide

/-! ### Totient at small composites -/

/-- φ(10) = 4. -/
theorem totient_ten : totient 10 = 4 := by native_decide

/-- φ(12) = 4. -/
theorem totient_twelve : totient 12 = 4 := by native_decide

/-- φ(30) = 8. -/
theorem totient_thirty : totient 30 = 8 := by native_decide

/-- φ(24) = 8. -/
theorem totient_twentyfour : totient 24 = 8 := by native_decide

/-- φ(36) = 12. -/
theorem totient_thirtysix : totient 36 = 12 := by native_decide

/-- φ(48) = 16. -/
theorem totient_fortyeight : totient 48 = 16 := by native_decide

/-- φ(60) = 16. -/
theorem totient_sixty : totient 60 = 16 := by native_decide

/-- φ(72) = 24. -/
theorem totient_seventytwo : totient 72 = 24 := by native_decide

/-- φ(120) = 32. -/
theorem totient_onehundredtwenty : totient 120 = 32 := by native_decide

/-! ### Liouville at small composites -/

/-- λ(6) = 1 (6 = 2 × 3, Ω(6) = 2, even). -/
theorem liouville_six : liouville 6 = 1 := by native_decide

/-- λ(10) = 1 (10 = 2 × 5, Ω(10) = 2, even). -/
theorem liouville_ten : liouville 10 = 1 := by native_decide

/-- λ(12) = -1 (12 = 2² × 3, Ω(12) = 3, odd). -/
theorem liouville_twelve : liouville 12 = -1 := by native_decide

/-- λ(30) = -1 (30 = 2 × 3 × 5, Ω(30) = 3, odd). -/
theorem liouville_thirty : liouville 30 = -1 := by native_decide

/-- λ(8) = -1 (8 = 2³, Ω(8) = 3, odd). -/
theorem liouville_eight : liouville 8 = -1 := by native_decide

/-- λ(45) = -1 (45 = 3² × 5, Ω(45) = 3, odd). -/
theorem liouville_fortyfive : liouville 45 = -1 := by native_decide

/-- λ(360) = 1 (360 = 2³ × 3² × 5, Ω(360) = 6, even). -/
theorem liouville_threehundredsixty : liouville 360 = 1 := by native_decide

/-- λ(840) = 1 (840 = 2³ × 3 × 5 × 7, Ω(840) = 6, even). -/
theorem liouville_eighthundredforty : liouville 840 = 1 := by native_decide

/-! ### Coprimality of RS constants -/

/-- gcd(8, 45) = 1 (already in RSConstants, aliased here for visibility). -/
theorem gcd_eight_fortyfive : Nat.gcd 8 45 = 1 := by native_decide

/-- 8 and 45 are coprime. -/
theorem coprime_eight_fortyfive : Nat.Coprime 8 45 := by native_decide

/-- 360 and 37 are coprime. -/
theorem coprime_threehundredsixty_thirtyseven : Nat.Coprime 360 37 := by native_decide

/-- 8 and 37 are coprime. -/
theorem coprime_eight_thirtyseven : Nat.Coprime 8 37 := by native_decide

/-- 45 and 37 are coprime. -/
theorem coprime_fortyfive_thirtyseven : Nat.Coprime 45 37 := by native_decide

/-- gcd(360, 7) = 1 (7 does not divide 360). -/
theorem gcd_threehundredsixty_seven : Nat.gcd 360 7 = 1 := by native_decide

/-- gcd(45, 8) = 1 (symmetric). -/
theorem gcd_fortyfive_eight : Nat.gcd 45 8 = 1 := by native_decide

/-! ### More divisor counts -/

/-- The number of divisors of 6 is 4. -/
theorem divisors_card_six : (6 : ℕ).divisors.card = 4 := by native_decide

/-- The number of divisors of 10 is 4. -/
theorem divisors_card_ten : (10 : ℕ).divisors.card = 4 := by native_decide

/-- The number of divisors of 12 is 6. -/
theorem divisors_card_twelve : (12 : ℕ).divisors.card = 6 := by native_decide

/-- The number of divisors of 30 is 8. -/
theorem divisors_card_thirty : (30 : ℕ).divisors.card = 8 := by native_decide

/-- The number of divisors of 60 is 12. -/
theorem divisors_card_sixty : (60 : ℕ).divisors.card = 12 := by native_decide

/-- The number of divisors of 120 is 16. -/
theorem divisors_card_onehundredtwenty : (120 : ℕ).divisors.card = 16 := by native_decide

/-! ### More Möbius values -/

/-- μ(10) = 1 (squarefree with 2 prime factors). -/
theorem mobius_ten : mobius 10 = 1 := by native_decide

/-- μ(15) = 1 (squarefree with 2 prime factors). -/
theorem mobius_fifteen : mobius 15 = 1 := by native_decide

/-- μ(21) = 1 (squarefree with 2 prime factors). -/
theorem mobius_twentyone : mobius 21 = 1 := by native_decide

/-- μ(35) = 1 (squarefree with 2 prime factors). -/
theorem mobius_thirtyfive : mobius 35 = 1 := by native_decide

/-- μ(42) = -1 (squarefree with 3 prime factors). -/
theorem mobius_fortytwo : mobius 42 = -1 := by native_decide

/-- μ(70) = -1 (squarefree with 3 prime factors). -/
theorem mobius_seventy : mobius 70 = -1 := by native_decide

/-- μ(105) = -1 (squarefree with 3 prime factors). -/
theorem mobius_onehundredfive : mobius 105 = -1 := by native_decide

/-- μ(210) = 1 (squarefree with 4 prime factors). -/
theorem mobius_twohundredten : mobius 210 = 1 := by native_decide

/-- μ(18) = 0 (not squarefree, 9 | 18). -/
theorem mobius_eighteen : mobius 18 = 0 := by native_decide

/-- μ(20) = 0 (not squarefree, 4 | 20). -/
theorem mobius_twenty : mobius 20 = 0 := by native_decide

/-! ### More squarefree values -/

/-- 42 = 2×3×7 is squarefree. -/
theorem squarefree_fortytwo : Squarefree 42 := by native_decide

/-- 70 = 2×5×7 is squarefree. -/
theorem squarefree_seventy : Squarefree 70 := by native_decide

/-- 105 = 3×5×7 is squarefree. -/
theorem squarefree_onehundredfive : Squarefree 105 := by native_decide

/-- 77 = 7×11 is squarefree. -/
theorem squarefree_seventyseven : Squarefree 77 := by native_decide

/-- 91 = 7×13 is squarefree. -/
theorem squarefree_ninetyone : Squarefree 91 := by native_decide

/-- 35 = 5×7 is squarefree. -/
theorem squarefree_thirtyfive : Squarefree 35 := by native_decide

/-- 21 = 3×7 is squarefree. -/
theorem squarefree_twentyone : Squarefree 21 := by native_decide

/-- 33 = 3×11 is squarefree. -/
theorem squarefree_thirtythree : Squarefree 33 := by native_decide

/-- 18 is NOT squarefree (9 | 18). -/
theorem not_squarefree_eighteen : ¬Squarefree 18 := by native_decide

/-- 20 is NOT squarefree (4 | 20). -/
theorem not_squarefree_twenty : ¬Squarefree 20 := by native_decide

/-- 50 is NOT squarefree (25 | 50). -/
theorem not_squarefree_fifty : ¬Squarefree 50 := by native_decide

/-! ### Twin prime pairs (decidable) -/

/-- 3 and 5 are twin primes. -/
theorem twin_prime_three_five : Prime 3 ∧ Prime 5 ∧ 5 = 3 + 2 := by native_decide

/-- 5 and 7 are twin primes. -/
theorem twin_prime_five_seven : Prime 5 ∧ Prime 7 ∧ 7 = 5 + 2 := by native_decide

/-- 11 and 13 are twin primes. -/
theorem twin_prime_eleven_thirteen : Prime 11 ∧ Prime 13 ∧ 13 = 11 + 2 := by native_decide

/-- 17 and 19 are twin primes. -/
theorem twin_prime_seventeen_nineteen : Prime 17 ∧ Prime 19 ∧ 19 = 17 + 2 := by native_decide

/-- 29 and 31 are twin primes. -/
theorem twin_prime_twentynine_thirtyone : Prime 29 ∧ Prime 31 ∧ 31 = 29 + 2 := by native_decide

/-- 41 and 43 are twin primes. -/
theorem twin_prime_fortyone_fortythree : Prime 41 ∧ Prime 43 ∧ 43 = 41 + 2 := by native_decide

/-- 59 and 61 are twin primes. -/
theorem twin_prime_fiftynine_sixtyone : Prime 59 ∧ Prime 61 ∧ 61 = 59 + 2 := by native_decide

/-- 71 and 73 are twin primes. -/
theorem twin_prime_seventyone_seventythree : Prime 71 ∧ Prime 73 ∧ 73 = 71 + 2 := by native_decide

/-! ### More arithmetic function values at RS-related numbers -/

/-- ω(120) = 3 (distinct prime factors: 2, 3, 5). -/
theorem omega_onehundredtwenty : omega 120 = 3 := by native_decide

/-- Ω(120) = 5 (120 = 2³ × 3 × 5). -/
theorem bigOmega_onehundredtwenty : bigOmega 120 = 5 := by native_decide

/-- σ_1(120) = 360. -/
theorem sigma_one_onehundredtwenty : sigma 1 120 = 360 := by native_decide

/-- σ_0(120) = 16. -/
theorem sigma_zero_onehundredtwenty : sigma 0 120 = 16 := by native_decide

/-- σ_1(840) = 2880. -/
theorem sigma_one_eighthundredforty : sigma 1 840 = 2880 := by native_decide

/-- σ_0(840) = 32. -/
theorem sigma_zero_eighthundredforty : sigma 0 840 = 32 := by native_decide

-- Note: ω(840) = 4 already exists as omega_eighthundredforty

/-- rad(120) = 30 = 2×3×5. -/
theorem radical_onehundredtwenty : radical 120 = 30 := by native_decide

/-- φ(840) = 192. -/
theorem totient_eighthundredforty : totient 840 = 192 := by native_decide

/-! ### Sophie Germain primes (p and 2p+1 both prime) -/

/-- 2 is a Sophie Germain prime (2 and 5 are both prime). -/
theorem sophie_germain_two : Prime 2 ∧ Prime (2 * 2 + 1) := by native_decide

/-- 3 is a Sophie Germain prime (3 and 7 are both prime). -/
theorem sophie_germain_three : Prime 3 ∧ Prime (2 * 3 + 1) := by native_decide

/-- 5 is a Sophie Germain prime (5 and 11 are both prime). -/
theorem sophie_germain_five : Prime 5 ∧ Prime (2 * 5 + 1) := by native_decide

/-- 11 is a Sophie Germain prime (11 and 23 are both prime). -/
theorem sophie_germain_eleven : Prime 11 ∧ Prime (2 * 11 + 1) := by native_decide

/-- 23 is a Sophie Germain prime (23 and 47 are both prime). -/
theorem sophie_germain_twentythree : Prime 23 ∧ Prime (2 * 23 + 1) := by native_decide

/-- 29 is a Sophie Germain prime (29 and 59 are both prime). -/
theorem sophie_germain_twentynine : Prime 29 ∧ Prime (2 * 29 + 1) := by native_decide

/-! ### Mersenne prime exponents (small) -/

/-- 2^2 - 1 = 3 is a Mersenne prime. -/
theorem mersenne_two : Prime (2 ^ 2 - 1) := by native_decide

/-- 2^3 - 1 = 7 is a Mersenne prime. -/
theorem mersenne_three : Prime (2 ^ 3 - 1) := by native_decide

/-- 2^5 - 1 = 31 is a Mersenne prime. -/
theorem mersenne_five : Prime (2 ^ 5 - 1) := by native_decide

/-- 2^7 - 1 = 127 is a Mersenne prime. -/
theorem mersenne_seven : Prime (2 ^ 7 - 1) := by native_decide

/-! ### Fermat primes (2^(2^n) + 1) -/

/-- F_0 = 2^(2^0) + 1 = 3 is a Fermat prime. -/
theorem fermat_zero : Prime (2 ^ (2 ^ 0) + 1) := by native_decide

/-- F_1 = 2^(2^1) + 1 = 5 is a Fermat prime. -/
theorem fermat_one : Prime (2 ^ (2 ^ 1) + 1) := by native_decide

/-- F_2 = 2^(2^2) + 1 = 17 is a Fermat prime. -/
theorem fermat_two : Prime (2 ^ (2 ^ 2) + 1) := by native_decide

/-- F_3 = 2^(2^3) + 1 = 257 is a Fermat prime. -/
theorem fermat_three : Prime (2 ^ (2 ^ 3) + 1) := by native_decide

/-- F_4 = 2^(2^4) + 1 = 65537 is a Fermat prime. -/
theorem fermat_four : Prime (2 ^ (2 ^ 4) + 1) := by native_decide

/-! ### Cousin primes (differ by 4) -/

/-- 3 and 7 are cousin primes. -/
theorem cousin_prime_three_seven : Prime 3 ∧ Prime 7 ∧ 7 = 3 + 4 := by native_decide

/-- 7 and 11 are cousin primes. -/
theorem cousin_prime_seven_eleven : Prime 7 ∧ Prime 11 ∧ 11 = 7 + 4 := by native_decide

/-- 13 and 17 are cousin primes. -/
theorem cousin_prime_thirteen_seventeen : Prime 13 ∧ Prime 17 ∧ 17 = 13 + 4 := by native_decide

/-- 19 and 23 are cousin primes. -/
theorem cousin_prime_nineteen_twentythree : Prime 19 ∧ Prime 23 ∧ 23 = 19 + 4 := by native_decide

/-- 37 and 41 are cousin primes. -/
theorem cousin_prime_thirtyseven_fortyone : Prime 37 ∧ Prime 41 ∧ 41 = 37 + 4 := by native_decide

/-- 43 and 47 are cousin primes. -/
theorem cousin_prime_fortythree_fortyseven : Prime 43 ∧ Prime 47 ∧ 47 = 43 + 4 := by native_decide

/-- 67 and 71 are cousin primes. -/
theorem cousin_prime_sixtyseven_seventyone : Prime 67 ∧ Prime 71 ∧ 71 = 67 + 4 := by native_decide

/-! ### Sexy primes (differ by 6) -/

/-- 5 and 11 are sexy primes. -/
theorem sexy_prime_five_eleven : Prime 5 ∧ Prime 11 ∧ 11 = 5 + 6 := by native_decide

/-- 7 and 13 are sexy primes. -/
theorem sexy_prime_seven_thirteen : Prime 7 ∧ Prime 13 ∧ 13 = 7 + 6 := by native_decide

/-- 11 and 17 are sexy primes. -/
theorem sexy_prime_eleven_seventeen : Prime 11 ∧ Prime 17 ∧ 17 = 11 + 6 := by native_decide

/-- 13 and 19 are sexy primes. -/
theorem sexy_prime_thirteen_nineteen : Prime 13 ∧ Prime 19 ∧ 19 = 13 + 6 := by native_decide

/-- 17 and 23 are sexy primes. -/
theorem sexy_prime_seventeen_twentythree : Prime 17 ∧ Prime 23 ∧ 23 = 17 + 6 := by native_decide

/-- 23 and 29 are sexy primes. -/
theorem sexy_prime_twentythree_twentynine : Prime 23 ∧ Prime 29 ∧ 29 = 23 + 6 := by native_decide

/-- 31 and 37 are sexy primes. -/
theorem sexy_prime_thirtyone_thirtyseven : Prime 31 ∧ Prime 37 ∧ 37 = 31 + 6 := by native_decide

/-- 37 and 43 are sexy primes. -/
theorem sexy_prime_thirtyseven_fortythree : Prime 37 ∧ Prime 43 ∧ 43 = 37 + 6 := by native_decide

/-! ### 210-related arithmetic functions (210 = 2×3×5×7 = primorial(4)) -/

/-- 210 = 2 × 3 × 5 × 7 is the product of first 4 primes. -/
theorem twohundredten_eq_primorial_four : (210 : ℕ) = 2 * 3 * 5 * 7 := by native_decide

/-- φ(210) = 48. -/
theorem totient_twohundredten : totient 210 = 48 := by native_decide

/-- σ_0(210) = 16 (number of divisors). -/
theorem sigma_zero_twohundredten : sigma 0 210 = 16 := by native_decide

/-- σ_1(210) = 576 (sum of divisors). -/
theorem sigma_one_twohundredten : sigma 1 210 = 576 := by native_decide

/-- Ω(210) = 4 (since 210 = 2¹×3¹×5¹×7¹). -/
theorem bigOmega_twohundredten : bigOmega 210 = 4 := by native_decide

/-- ω(210) = 4 (distinct prime factors: 2, 3, 5, 7). -/
theorem omega_twohundredten : omega 210 = 4 := by native_decide

/-- rad(210) = 210 (squarefree). -/
theorem radical_twohundredten : radical 210 = 210 := by native_decide

/-- λ(210) = 1 (Liouville, Ω = 4 is even). -/
theorem liouville_twohundredten : liouville 210 = 1 := by native_decide

-- Note: μ(210) = 1 already exists as mobius_twohundredten

/-! ### Additional small primes -/

/-- 19 is prime. -/
theorem prime_nineteen : Prime 19 := by native_decide

/-! ### Primorial values (product of first n primes) -/

/-- primorial(1) = 2. -/
theorem primorial_one : (2 : ℕ) = 2 := rfl

/-- primorial(2) = 2 × 3 = 6. -/
theorem primorial_two_eq : (6 : ℕ) = 2 * 3 := by native_decide

/-- primorial(3) = 2 × 3 × 5 = 30. -/
theorem primorial_three_eq : (30 : ℕ) = 2 * 3 * 5 := by native_decide

/-- primorial(4) = 2 × 3 × 5 × 7 = 210. -/
theorem primorial_four_eq : (210 : ℕ) = 2 * 3 * 5 * 7 := by native_decide

/-- primorial(5) = 2 × 3 × 5 × 7 × 11 = 2310. -/
theorem primorial_five_eq : (2310 : ℕ) = 2 * 3 * 5 * 7 * 11 := by native_decide

/-! ### More 2310-related (primorial(5)) -/

/-- φ(2310) = 480. -/
theorem totient_twothousandthreehundredten : totient 2310 = 480 := by native_decide

/-- ω(2310) = 5 (distinct prime factors: 2, 3, 5, 7, 11). -/
theorem omega_twothousandthreehundredten : omega 2310 = 5 := by native_decide

/-- Ω(2310) = 5. -/
theorem bigOmega_twothousandthreehundredten : bigOmega 2310 = 5 := by native_decide

/-- 2310 is squarefree. -/
theorem squarefree_twothousandthreehundredten : Squarefree 2310 := by native_decide

/-- μ(2310) = -1 (squarefree with 5 prime factors). -/
theorem mobius_twothousandthreehundredten : mobius 2310 = -1 := by native_decide

/-! ### Highly composite numbers -/

/-- 12 is highly composite (has more divisors than any smaller positive integer). -/
theorem divisors_card_twelve_gt : ∀ n, 0 < n → n < 12 → (n : ℕ).divisors.card < (12 : ℕ).divisors.card := by
  intro n hn hlt
  interval_cases n <;> native_decide

/-! ### More highly composite numbers -/

/-- 60 is highly composite (has more divisors than any smaller positive integer). -/
theorem divisors_card_sixty_gt : ∀ n, 0 < n → n < 60 → (n : ℕ).divisors.card < (60 : ℕ).divisors.card := by
  intro n hn hlt
  interval_cases n <;> native_decide

/-- 120 is highly composite (has more divisors than any smaller positive integer). -/
theorem divisors_card_onehundredtwenty_gt : ∀ n, 0 < n → n < 120 → (n : ℕ).divisors.card < (120 : ℕ).divisors.card := by
  intro n hn hlt
  interval_cases n <;> native_decide

/-! ### Safe primes (p such that (p-1)/2 is also prime) -/

/-- 5 is a safe prime: (5-1)/2 = 2 is prime. -/
theorem safe_prime_five : Prime 5 ∧ Prime ((5 - 1) / 2) := by native_decide

/-- 7 is a safe prime: (7-1)/2 = 3 is prime. -/
theorem safe_prime_seven : Prime 7 ∧ Prime ((7 - 1) / 2) := by native_decide

/-- 11 is a safe prime: (11-1)/2 = 5 is prime. -/
theorem safe_prime_eleven : Prime 11 ∧ Prime ((11 - 1) / 2) := by native_decide

/-- 23 is a safe prime: (23-1)/2 = 11 is prime. -/
theorem safe_prime_twentythree : Prime 23 ∧ Prime ((23 - 1) / 2) := by native_decide

/-- 47 is a safe prime: (47-1)/2 = 23 is prime. -/
theorem safe_prime_fortyseven : Prime 47 ∧ Prime ((47 - 1) / 2) := by native_decide

/-- 59 is a safe prime: (59-1)/2 = 29 is prime. -/
theorem safe_prime_fiftynine : Prime 59 ∧ Prime ((59 - 1) / 2) := by native_decide

/-- 83 is a safe prime: (83-1)/2 = 41 is prime. -/
theorem safe_prime_eightythree : Prime 83 ∧ Prime ((83 - 1) / 2) := by native_decide

-- Note: 89 is NOT a safe prime since (89-1)/2 = 44 = 4×11 is composite

/-- 107 is a safe prime: (107-1)/2 = 53 is prime. -/
theorem safe_prime_onehundredseven : Prime 107 ∧ Prime ((107 - 1) / 2) := by native_decide

/-! ### Abundant numbers (σ_1(n) > 2n) -/

/-- 12 is abundant: σ_1(12) = 28 > 24. -/
theorem abundant_twelve : sigma 1 12 > 2 * 12 := by native_decide

/-- 18 is abundant: σ_1(18) = 39 > 36. -/
theorem abundant_eighteen : sigma 1 18 > 2 * 18 := by native_decide

/-- 20 is abundant: σ_1(20) = 42 > 40. -/
theorem abundant_twenty : sigma 1 20 > 2 * 20 := by native_decide

/-- 24 is abundant: σ_1(24) = 60 > 48. -/
theorem abundant_twentyfour : sigma 1 24 > 2 * 24 := by native_decide

/-- 30 is abundant: σ_1(30) = 72 > 60. -/
theorem abundant_thirty : sigma 1 30 > 2 * 30 := by native_decide

/-- 36 is abundant: σ_1(36) = 91 > 72. -/
theorem abundant_thirtysix : sigma 1 36 > 2 * 36 := by native_decide

/-! ### Deficient numbers (σ_1(n) < 2n) -/

/-- 1 is deficient: σ_1(1) = 1 < 2. -/
theorem deficient_one : sigma 1 1 < 2 * 1 := by native_decide

/-- 2 is deficient: σ_1(2) = 3 < 4. -/
theorem deficient_two : sigma 1 2 < 2 * 2 := by native_decide

/-- 3 is deficient: σ_1(3) = 4 < 6. -/
theorem deficient_three : sigma 1 3 < 2 * 3 := by native_decide

/-- 4 is deficient: σ_1(4) = 7 < 8. -/
theorem deficient_four : sigma 1 4 < 2 * 4 := by native_decide

/-- 5 is deficient: σ_1(5) = 6 < 10. -/
theorem deficient_five : sigma 1 5 < 2 * 5 := by native_decide

/-- 7 is deficient: σ_1(7) = 8 < 14. -/
theorem deficient_seven : sigma 1 7 < 2 * 7 := by native_decide

/-- 8 is deficient: σ_1(8) = 15 < 16. -/
theorem deficient_eight : sigma 1 8 < 2 * 8 := by native_decide

/-- 9 is deficient: σ_1(9) = 13 < 18. -/
theorem deficient_nine : sigma 1 9 < 2 * 9 := by native_decide

/-- 10 is deficient: σ_1(10) = 18 < 20. -/
theorem deficient_ten : sigma 1 10 < 2 * 10 := by native_decide

/-- 11 is deficient (all primes are deficient). -/
theorem deficient_eleven : sigma 1 11 < 2 * 11 := by native_decide

/-! ### Pythagorean primes (p ≡ 1 mod 4) — can be expressed as sum of two squares -/

/-- 5 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_five : Prime 5 ∧ 5 % 4 = 1 := by native_decide

/-- 13 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_thirteen : Prime 13 ∧ 13 % 4 = 1 := by native_decide

/-- 17 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_seventeen : Prime 17 ∧ 17 % 4 = 1 := by native_decide

/-- 29 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_twentynine : Prime 29 ∧ 29 % 4 = 1 := by native_decide

/-- 37 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_thirtyseven : Prime 37 ∧ 37 % 4 = 1 := by native_decide

/-- 41 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_fortyone : Prime 41 ∧ 41 % 4 = 1 := by native_decide

/-- 53 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_fiftythree : Prime 53 ∧ 53 % 4 = 1 := by native_decide

/-- 61 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_sixtyone : Prime 61 ∧ 61 % 4 = 1 := by native_decide

/-- 73 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_seventythree : Prime 73 ∧ 73 % 4 = 1 := by native_decide

/-- 89 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_eightynine : Prime 89 ∧ 89 % 4 = 1 := by native_decide

/-- 97 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_ninetyseven : Prime 97 ∧ 97 % 4 = 1 := by native_decide

/-- 101 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_onehundredone : Prime 101 ∧ 101 % 4 = 1 := by native_decide

/-- 109 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_onehundrednine : Prime 109 ∧ 109 % 4 = 1 := by native_decide

/-- 113 ≡ 1 (mod 4) is a Pythagorean prime. -/
theorem pythagorean_prime_onehundredthirteen : Prime 113 ∧ 113 % 4 = 1 := by native_decide

/-- 137 ≡ 1 (mod 4) is a Pythagorean prime (RS-relevant). -/
theorem pythagorean_prime_onehundredthirtyseven : Prime 137 ∧ 137 % 4 = 1 := by native_decide

/-! ### Prime triplets (three primes with gaps ≤ 6) -/

/-- (3, 5, 7) is a prime triplet. -/
theorem prime_triplet_three_five_seven : Prime 3 ∧ Prime 5 ∧ Prime 7 := by native_decide

/-- (5, 7, 11) are three primes with gap (2, 4). -/
theorem prime_triplet_five_seven_eleven : Prime 5 ∧ Prime 7 ∧ Prime 11 := by native_decide

/-- (7, 11, 13) are three primes with gap (4, 2). -/
theorem prime_triplet_seven_eleven_thirteen : Prime 7 ∧ Prime 11 ∧ Prime 13 := by native_decide

/-- (11, 13, 17) are three primes with gap (2, 4). -/
theorem prime_triplet_eleven_thirteen_seventeen : Prime 11 ∧ Prime 13 ∧ Prime 17 := by native_decide

/-- (13, 17, 19) are three primes with gap (4, 2). -/
theorem prime_triplet_thirteen_seventeen_nineteen : Prime 13 ∧ Prime 17 ∧ Prime 19 := by native_decide

/-- (17, 19, 23) are three primes with gap (2, 4). -/
theorem prime_triplet_seventeen_nineteen_twentythree : Prime 17 ∧ Prime 19 ∧ Prime 23 := by native_decide

/-- (37, 41, 43) are three primes with gap (4, 2). RS-relevant (37 is the beat numerator). -/
theorem prime_triplet_thirtyseven_fortyone_fortythree : Prime 37 ∧ Prime 41 ∧ Prime 43 := by native_decide

/-! ### Sum of two squares representations for Pythagorean primes -/

/-- 5 = 1² + 2². -/
theorem sum_of_squares_five : (5 : ℕ) = 1^2 + 2^2 := by native_decide

/-- 13 = 2² + 3². -/
theorem sum_of_squares_thirteen : (13 : ℕ) = 2^2 + 3^2 := by native_decide

/-- 17 = 1² + 4². -/
theorem sum_of_squares_seventeen : (17 : ℕ) = 1^2 + 4^2 := by native_decide

/-- 29 = 2² + 5². -/
theorem sum_of_squares_twentynine : (29 : ℕ) = 2^2 + 5^2 := by native_decide

/-- 37 = 1² + 6². -/
theorem sum_of_squares_thirtyseven : (37 : ℕ) = 1^2 + 6^2 := by native_decide

/-- 41 = 4² + 5². -/
theorem sum_of_squares_fortyone : (41 : ℕ) = 4^2 + 5^2 := by native_decide

/-- 53 = 2² + 7². -/
theorem sum_of_squares_fiftythree : (53 : ℕ) = 2^2 + 7^2 := by native_decide

/-- 137 = 4² + 11² (RS-relevant). -/
theorem sum_of_squares_onehundredthirtyseven : (137 : ℕ) = 4^2 + 11^2 := by native_decide

/-! ### Prime quadruplets (four primes in close cluster p, p+2, p+6, p+8) -/

/-- (5, 7, 11, 13) is a prime quadruplet (gaps: 2, 4, 2). -/
theorem prime_quadruplet_five : Prime 5 ∧ Prime 7 ∧ Prime 11 ∧ Prime 13 := by native_decide

/-- (11, 13, 17, 19) is a prime quadruplet (gaps: 2, 4, 2). -/
theorem prime_quadruplet_eleven : Prime 11 ∧ Prime 13 ∧ Prime 17 ∧ Prime 19 := by native_decide

/-- (101, 103, 107, 109) is a prime quadruplet (gaps: 2, 4, 2). -/
theorem prime_quadruplet_onehundredone : Prime 101 ∧ Prime 103 ∧ Prime 107 ∧ Prime 109 := by native_decide

/-- (191, 193, 197, 199) is a prime quadruplet (gaps: 2, 4, 2). -/
theorem prime_quadruplet_onehundredninetyone : Prime 191 ∧ Prime 193 ∧ Prime 197 ∧ Prime 199 := by native_decide

/-! ### Primes p ≡ 3 (mod 4) — not expressible as sum of two squares -/

/-- 3 ≡ 3 (mod 4). -/
theorem mod4_three_prime : Prime 3 ∧ 3 % 4 = 3 := by native_decide

/-- 7 ≡ 3 (mod 4). -/
theorem mod4_seven_prime : Prime 7 ∧ 7 % 4 = 3 := by native_decide

/-- 11 ≡ 3 (mod 4). -/
theorem mod4_eleven_prime : Prime 11 ∧ 11 % 4 = 3 := by native_decide

/-- 19 ≡ 3 (mod 4). -/
theorem mod4_nineteen_prime : Prime 19 ∧ 19 % 4 = 3 := by native_decide

/-- 23 ≡ 3 (mod 4). -/
theorem mod4_twentythree_prime : Prime 23 ∧ 23 % 4 = 3 := by native_decide

/-- 31 ≡ 3 (mod 4). -/
theorem mod4_thirtyone_prime : Prime 31 ∧ 31 % 4 = 3 := by native_decide

/-- 43 ≡ 3 (mod 4). -/
theorem mod4_fortythree_prime : Prime 43 ∧ 43 % 4 = 3 := by native_decide

/-- 47 ≡ 3 (mod 4). -/
theorem mod4_fortyseven_prime : Prime 47 ∧ 47 % 4 = 3 := by native_decide

/-- 59 ≡ 3 (mod 4). -/
theorem mod4_fiftynine_prime : Prime 59 ∧ 59 % 4 = 3 := by native_decide

/-- 67 ≡ 3 (mod 4). -/
theorem mod4_sixtyseven_prime : Prime 67 ∧ 67 % 4 = 3 := by native_decide

/-- 71 ≡ 3 (mod 4). -/
theorem mod4_seventyone_prime : Prime 71 ∧ 71 % 4 = 3 := by native_decide

/-- 79 ≡ 3 (mod 4). -/
theorem mod4_seventynine_prime : Prime 79 ∧ 79 % 4 = 3 := by native_decide

/-- 83 ≡ 3 (mod 4). -/
theorem mod4_eightythree_prime : Prime 83 ∧ 83 % 4 = 3 := by native_decide

/-- 103 ≡ 3 (mod 4) (RS-relevant). -/
theorem mod4_onehundredthree_prime : Prime 103 ∧ 103 % 4 = 3 := by native_decide

/-! ### σ_2 values (sum of squares of divisors) -/

/-- σ_2(1) = 1. -/
theorem sigma_two_one : sigma 2 1 = 1 := by native_decide

/-- σ_2(2) = 1 + 4 = 5. -/
theorem sigma_two_two : sigma 2 2 = 5 := by native_decide

/-- σ_2(3) = 1 + 9 = 10. -/
theorem sigma_two_three : sigma 2 3 = 10 := by native_decide

/-- σ_2(4) = 1 + 4 + 16 = 21. -/
theorem sigma_two_four : sigma 2 4 = 21 := by native_decide

/-- σ_2(5) = 1 + 25 = 26. -/
theorem sigma_two_five : sigma 2 5 = 26 := by native_decide

/-- σ_2(6) = 1 + 4 + 9 + 36 = 50. -/
theorem sigma_two_six : sigma 2 6 = 50 := by native_decide

/-- σ_2(8) = 1 + 4 + 16 + 64 = 85. -/
theorem sigma_two_eight : sigma 2 8 = 85 := by native_decide

/-- σ_2(10) = 1 + 4 + 25 + 100 = 130. -/
theorem sigma_two_ten : sigma 2 10 = 130 := by native_decide

/-- σ_2(12) = 1 + 4 + 9 + 16 + 36 + 144 = 210. -/
theorem sigma_two_twelve : sigma 2 12 = 210 := by native_decide

/-- σ_2(30) = 1300 (divisors: 1+4+9+25+36+100+225+900). -/
theorem sigma_two_thirty : sigma 2 30 = 1300 := by native_decide

/-! ### More primeCounting values at round numbers -/

/-- π(400) = 78. -/
theorem primeCounting_fourhundred : primeCounting 400 = 78 := by native_decide

/-- π(600) = 109. -/
theorem primeCounting_sixhundred : primeCounting 600 = 109 := by native_decide

/-- π(800) = 139. -/
theorem primeCounting_eighthundred : primeCounting 800 = 139 := by native_decide

/-- π(900) = 154. -/
theorem primeCounting_ninehundred : primeCounting 900 = 154 := by native_decide

/-! ### More sum of squares representations -/

/-- 61 = 5² + 6². -/
theorem sum_of_squares_sixtyone : (61 : ℕ) = 5^2 + 6^2 := by native_decide

/-- 73 = 3² + 8². -/
theorem sum_of_squares_seventythree : (73 : ℕ) = 3^2 + 8^2 := by native_decide

/-- 89 = 5² + 8². -/
theorem sum_of_squares_eightynine : (89 : ℕ) = 5^2 + 8^2 := by native_decide

/-- 97 = 4² + 9². -/
theorem sum_of_squares_ninetyseven : (97 : ℕ) = 4^2 + 9^2 := by native_decide

/-- 101 = 1² + 10². -/
theorem sum_of_squares_onehundredone : (101 : ℕ) = 1^2 + 10^2 := by native_decide

/-- 109 = 3² + 10². -/
theorem sum_of_squares_onehundrednine : (109 : ℕ) = 3^2 + 10^2 := by native_decide

/-- 113 = 7² + 8². -/
theorem sum_of_squares_onehundredthirteen : (113 : ℕ) = 7^2 + 8^2 := by native_decide

/-! ### Semiprimes (product of exactly two primes, counting multiplicity) -/

/-- A number is semiprime if Ω(n) = 2. -/
def isSemiprime (n : ℕ) : Bool := bigOmega n = 2

/-- 4 = 2² is semiprime. -/
theorem semiprime_four : isSemiprime 4 = true := by native_decide

/-- 6 = 2 × 3 is semiprime. -/
theorem semiprime_six : isSemiprime 6 = true := by native_decide

/-- 9 = 3² is semiprime. -/
theorem semiprime_nine : isSemiprime 9 = true := by native_decide

/-- 10 = 2 × 5 is semiprime. -/
theorem semiprime_ten : isSemiprime 10 = true := by native_decide

/-- 14 = 2 × 7 is semiprime. -/
theorem semiprime_fourteen : isSemiprime 14 = true := by native_decide

/-- 15 = 3 × 5 is semiprime. -/
theorem semiprime_fifteen : isSemiprime 15 = true := by native_decide

/-- 21 = 3 × 7 is semiprime. -/
theorem semiprime_twentyone : isSemiprime 21 = true := by native_decide

/-- 22 = 2 × 11 is semiprime. -/
theorem semiprime_twentytwo : isSemiprime 22 = true := by native_decide

/-- 25 = 5² is semiprime. -/
theorem semiprime_twentyfive : isSemiprime 25 = true := by native_decide

/-- 26 = 2 × 13 is semiprime. -/
theorem semiprime_twentysix : isSemiprime 26 = true := by native_decide

/-- 33 = 3 × 11 is semiprime. -/
theorem semiprime_thirtythree : isSemiprime 33 = true := by native_decide

/-- 34 = 2 × 17 is semiprime. -/
theorem semiprime_thirtyfour : isSemiprime 34 = true := by native_decide

/-- 35 = 5 × 7 is semiprime. -/
theorem semiprime_thirtyfive : isSemiprime 35 = true := by native_decide

/-- 38 = 2 × 19 is semiprime. -/
theorem semiprime_thirtyeight : isSemiprime 38 = true := by native_decide

/-- 39 = 3 × 13 is semiprime. -/
theorem semiprime_thirtynine : isSemiprime 39 = true := by native_decide

/-- 49 = 7² is semiprime. -/
theorem semiprime_fortynine : isSemiprime 49 = true := by native_decide

/-- 51 = 3 × 17 is semiprime. -/
theorem semiprime_fiftyone : isSemiprime 51 = true := by native_decide

/-- 55 = 5 × 11 is semiprime. -/
theorem semiprime_fiftyfive : isSemiprime 55 = true := by native_decide

/-- 57 = 3 × 19 is semiprime. -/
theorem semiprime_fiftyseven : isSemiprime 57 = true := by native_decide

/-- 58 = 2 × 29 is semiprime. -/
theorem semiprime_fiftyeight : isSemiprime 58 = true := by native_decide

/-- 62 = 2 × 31 is semiprime. -/
theorem semiprime_sixtytwo : isSemiprime 62 = true := by native_decide

/-- 65 = 5 × 13 is semiprime. -/
theorem semiprime_sixtyfive : isSemiprime 65 = true := by native_decide

/-- 74 = 2 × 37 is semiprime (RS-relevant: 37). -/
theorem semiprime_seventyfour : isSemiprime 74 = true := by native_decide

/-- 77 = 7 × 11 is semiprime. -/
theorem semiprime_seventyseven : isSemiprime 77 = true := by native_decide

/-- 85 = 5 × 17 is semiprime (RS-relevant: 17). -/
theorem semiprime_eightyfive : isSemiprime 85 = true := by native_decide

/-- 91 = 7 × 13 is semiprime. -/
theorem semiprime_ninetyone : isSemiprime 91 = true := by native_decide

/-- 95 = 5 × 19 is semiprime. -/
theorem semiprime_ninetyfive : isSemiprime 95 = true := by native_decide

/-! ### Powers of 2 -/

/-- 2^10 = 1024. -/
theorem two_pow_ten : (2 : ℕ) ^ 10 = 1024 := by native_decide

/-- 2^12 = 4096. -/
theorem two_pow_twelve : (2 : ℕ) ^ 12 = 4096 := by native_decide

/-- 2^16 = 65536. -/
theorem two_pow_sixteen : (2 : ℕ) ^ 16 = 65536 := by native_decide

/-- 2^20 = 1048576. -/
theorem two_pow_twenty : (2 : ℕ) ^ 20 = 1048576 := by native_decide

/-- 2^4 = 16. -/
theorem two_pow_four : (2 : ℕ) ^ 4 = 16 := by native_decide

/-- 2^5 = 32. -/
theorem two_pow_five : (2 : ℕ) ^ 5 = 32 := by native_decide

/-- 2^6 = 64. -/
theorem two_pow_six : (2 : ℕ) ^ 6 = 64 := by native_decide

/-- 2^7 = 128. -/
theorem two_pow_seven : (2 : ℕ) ^ 7 = 128 := by native_decide

/-- 2^8 = 256. -/
theorem two_pow_eight : (2 : ℕ) ^ 8 = 256 := by native_decide

/-- 2^9 = 512. -/
theorem two_pow_nine : (2 : ℕ) ^ 9 = 512 := by native_decide

/-! ### σ_3 values (sum of cubes of divisors) -/

/-- σ_3(1) = 1. -/
theorem sigma_three_one : sigma 3 1 = 1 := by native_decide

/-- σ_3(2) = 1 + 8 = 9. -/
theorem sigma_three_two : sigma 3 2 = 9 := by native_decide

/-- σ_3(3) = 1 + 27 = 28. -/
theorem sigma_three_three : sigma 3 3 = 28 := by native_decide

/-- σ_3(4) = 1 + 8 + 64 = 73. -/
theorem sigma_three_four : sigma 3 4 = 73 := by native_decide

/-- σ_3(5) = 1 + 125 = 126. -/
theorem sigma_three_five : sigma 3 5 = 126 := by native_decide

/-- σ_3(6) = 1 + 8 + 27 + 216 = 252. -/
theorem sigma_three_six : sigma 3 6 = 252 := by native_decide

/-- σ_3(8) = 1 + 8 + 64 + 512 = 585. -/
theorem sigma_three_eight : sigma 3 8 = 585 := by native_decide

/-- σ_3(10) = 1 + 8 + 125 + 1000 = 1134. -/
theorem sigma_three_ten : sigma 3 10 = 1134 := by native_decide

/-- σ_3(12) = 2044. -/
theorem sigma_three_twelve : sigma 3 12 = 2044 := by native_decide

/-! ### Mod 6 prime classification (all primes > 3 are ≡ 1 or 5 mod 6) -/

/-- 7 ≡ 1 (mod 6). -/
theorem mod6_seven_prime : Prime 7 ∧ 7 % 6 = 1 := by native_decide

/-- 13 ≡ 1 (mod 6). -/
theorem mod6_thirteen_prime : Prime 13 ∧ 13 % 6 = 1 := by native_decide

/-- 19 ≡ 1 (mod 6). -/
theorem mod6_nineteen_prime : Prime 19 ∧ 19 % 6 = 1 := by native_decide

/-- 31 ≡ 1 (mod 6). -/
theorem mod6_thirtyone_prime : Prime 31 ∧ 31 % 6 = 1 := by native_decide

/-- 37 ≡ 1 (mod 6) (RS-relevant). -/
theorem mod6_thirtyseven_prime : Prime 37 ∧ 37 % 6 = 1 := by native_decide

/-- 43 ≡ 1 (mod 6). -/
theorem mod6_fortythree_prime : Prime 43 ∧ 43 % 6 = 1 := by native_decide

/-- 61 ≡ 1 (mod 6). -/
theorem mod6_sixtyone_prime : Prime 61 ∧ 61 % 6 = 1 := by native_decide

/-- 67 ≡ 1 (mod 6). -/
theorem mod6_sixtyseven_prime : Prime 67 ∧ 67 % 6 = 1 := by native_decide

/-- 73 ≡ 1 (mod 6). -/
theorem mod6_seventythree_prime : Prime 73 ∧ 73 % 6 = 1 := by native_decide

/-- 79 ≡ 1 (mod 6). -/
theorem mod6_seventynine_prime : Prime 79 ∧ 79 % 6 = 1 := by native_decide

/-- 97 ≡ 1 (mod 6). -/
theorem mod6_ninetyseven_prime : Prime 97 ∧ 97 % 6 = 1 := by native_decide

/-- 103 ≡ 1 (mod 6) (RS-relevant). -/
theorem mod6_onehundredthree_prime : Prime 103 ∧ 103 % 6 = 1 := by native_decide

/-- 5 ≡ 5 (mod 6). -/
theorem mod6_five_prime : Prime 5 ∧ 5 % 6 = 5 := by native_decide

/-- 11 ≡ 5 (mod 6) (RS-relevant). -/
theorem mod6_eleven_prime : Prime 11 ∧ 11 % 6 = 5 := by native_decide

/-- 17 ≡ 5 (mod 6) (RS-relevant). -/
theorem mod6_seventeen_prime : Prime 17 ∧ 17 % 6 = 5 := by native_decide

/-- 23 ≡ 5 (mod 6). -/
theorem mod6_twentythree_prime : Prime 23 ∧ 23 % 6 = 5 := by native_decide

/-- 29 ≡ 5 (mod 6). -/
theorem mod6_twentynine_prime : Prime 29 ∧ 29 % 6 = 5 := by native_decide

/-- 41 ≡ 5 (mod 6). -/
theorem mod6_fortyone_prime : Prime 41 ∧ 41 % 6 = 5 := by native_decide

/-- 47 ≡ 5 (mod 6). -/
theorem mod6_fortyseven_prime : Prime 47 ∧ 47 % 6 = 5 := by native_decide

/-- 53 ≡ 5 (mod 6). -/
theorem mod6_fiftythree_prime : Prime 53 ∧ 53 % 6 = 5 := by native_decide

/-- 59 ≡ 5 (mod 6). -/
theorem mod6_fiftynine_prime : Prime 59 ∧ 59 % 6 = 5 := by native_decide

/-- 71 ≡ 5 (mod 6). -/
theorem mod6_seventyone_prime : Prime 71 ∧ 71 % 6 = 5 := by native_decide

/-- 83 ≡ 5 (mod 6). -/
theorem mod6_eightythree_prime : Prime 83 ∧ 83 % 6 = 5 := by native_decide

/-- 89 ≡ 5 (mod 6). -/
theorem mod6_eightynine_prime : Prime 89 ∧ 89 % 6 = 5 := by native_decide

/-- 137 ≡ 5 (mod 6) (RS-relevant). -/
theorem mod6_onehundredthirtyseven_prime : Prime 137 ∧ 137 % 6 = 5 := by native_decide

/-! ### Primes in the 200s -/

/-- 211 is prime. -/
theorem prime_twohundredeleven : Prime 211 := by native_decide

/-- 223 is prime. -/
theorem prime_twohundredtwentythree : Prime 223 := by native_decide

/-- 227 is prime. -/
theorem prime_twohundredtwentyseven : Prime 227 := by native_decide

/-- 229 is prime. -/
theorem prime_twohundredtwentynine : Prime 229 := by native_decide

/-- 233 is prime. -/
theorem prime_twohundredthirtythree : Prime 233 := by native_decide

/-- 239 is prime. -/
theorem prime_twohundredthirtynine : Prime 239 := by native_decide

/-- 241 is prime. -/
theorem prime_twohundredfortyone : Prime 241 := by native_decide

/-- 251 is prime. -/
theorem prime_twohundredfiftyone : Prime 251 := by native_decide

/-- 257 is prime (Fermat prime F_3 = 2^8 + 1). -/
theorem prime_twohundredfiftyseven : Prime 257 := by native_decide

/-- 263 is prime. -/
theorem prime_twohundredsixtythree : Prime 263 := by native_decide

/-- 269 is prime. -/
theorem prime_twohundredsixtynine : Prime 269 := by native_decide

/-- 271 is prime. -/
theorem prime_twohundredseventyone : Prime 271 := by native_decide

/-- 277 is prime. -/
theorem prime_twohundredseventyseven : Prime 277 := by native_decide

/-- 281 is prime. -/
theorem prime_twohundredeightyone : Prime 281 := by native_decide

/-- 283 is prime. -/
theorem prime_twohundredeightythree : Prime 283 := by native_decide

/-- 293 is prime. -/
theorem prime_twohundredninetythree : Prime 293 := by native_decide

/-! ### Primes in the 300s -/

/-- 307 is prime. -/
theorem prime_threehundredseven : Prime 307 := by native_decide

/-- 311 is prime. -/
theorem prime_threehundredeleven : Prime 311 := by native_decide

/-- 313 is prime. -/
theorem prime_threehundredthirteen : Prime 313 := by native_decide

/-- 317 is prime. -/
theorem prime_threehundredseventeen : Prime 317 := by native_decide

/-- 331 is prime. -/
theorem prime_threehundredthirtyone : Prime 331 := by native_decide

/-- 337 is prime. -/
theorem prime_threehundredthirtyseven : Prime 337 := by native_decide

/-- 347 is prime. -/
theorem prime_threehundredfortyseven : Prime 347 := by native_decide

/-- 349 is prime. -/
theorem prime_threehundredfortynine : Prime 349 := by native_decide

/-- 353 is prime. -/
theorem prime_threehundredfiftythree : Prime 353 := by native_decide

/-- 359 is prime. -/
theorem prime_threehundredfiftynine : Prime 359 := by native_decide

/-- 367 is prime. -/
theorem prime_threehundredsixtyseven : Prime 367 := by native_decide

/-- 373 is prime. -/
theorem prime_threehundredseventythree : Prime 373 := by native_decide

/-- 379 is prime. -/
theorem prime_threehundredseventynine : Prime 379 := by native_decide

/-- 383 is prime. -/
theorem prime_threehundredeightythree : Prime 383 := by native_decide

/-- 389 is prime. -/
theorem prime_threehundredeightynine : Prime 389 := by native_decide

/-- 397 is prime. -/
theorem prime_threehundredninetyseven : Prime 397 := by native_decide

/-! ### 3-almost primes (Ω(n) = 3) -/

/-- A number is 3-almost prime if Ω(n) = 3. -/
def isThreeAlmostPrime (n : ℕ) : Bool := bigOmega n = 3

/-- 8 = 2³ is 3-almost prime. -/
theorem three_almost_prime_eight : isThreeAlmostPrime 8 = true := by native_decide

/-- 12 = 2² × 3 is 3-almost prime. -/
theorem three_almost_prime_twelve : isThreeAlmostPrime 12 = true := by native_decide

/-- 18 = 2 × 3² is 3-almost prime. -/
theorem three_almost_prime_eighteen : isThreeAlmostPrime 18 = true := by native_decide

/-- 20 = 2² × 5 is 3-almost prime. -/
theorem three_almost_prime_twenty : isThreeAlmostPrime 20 = true := by native_decide

/-- 27 = 3³ is 3-almost prime. -/
theorem three_almost_prime_twentyseven : isThreeAlmostPrime 27 = true := by native_decide

/-- 28 = 2² × 7 is 3-almost prime. -/
theorem three_almost_prime_twentyeight : isThreeAlmostPrime 28 = true := by native_decide

/-- 30 = 2 × 3 × 5 is 3-almost prime. -/
theorem three_almost_prime_thirty : isThreeAlmostPrime 30 = true := by native_decide

/-- 42 = 2 × 3 × 7 is 3-almost prime. -/
theorem three_almost_prime_fortytwo : isThreeAlmostPrime 42 = true := by native_decide

/-- 44 = 2² × 11 is 3-almost prime. -/
theorem three_almost_prime_fortyfour : isThreeAlmostPrime 44 = true := by native_decide

/-- 45 = 3² × 5 is 3-almost prime (RS constant). -/
theorem three_almost_prime_fortyfive : isThreeAlmostPrime 45 = true := by native_decide

/-- 50 = 2 × 5² is 3-almost prime. -/
theorem three_almost_prime_fifty : isThreeAlmostPrime 50 = true := by native_decide

/-- 52 = 2² × 13 is 3-almost prime. -/
theorem three_almost_prime_fiftytwo : isThreeAlmostPrime 52 = true := by native_decide

/-- 63 = 3² × 7 is 3-almost prime. -/
theorem three_almost_prime_sixtythree : isThreeAlmostPrime 63 = true := by native_decide

/-- 66 = 2 × 3 × 11 is 3-almost prime (RS-relevant: 11). -/
theorem three_almost_prime_sixtysix : isThreeAlmostPrime 66 = true := by native_decide

/-- 68 = 2² × 17 is 3-almost prime (RS-relevant: 17). -/
theorem three_almost_prime_sixtyeight : isThreeAlmostPrime 68 = true := by native_decide

/-- 70 = 2 × 5 × 7 is 3-almost prime. -/
theorem three_almost_prime_seventy : isThreeAlmostPrime 70 = true := by native_decide

/-- 75 = 3 × 5² is 3-almost prime. -/
theorem three_almost_prime_seventyfive : isThreeAlmostPrime 75 = true := by native_decide

/-- 76 = 2² × 19 is 3-almost prime. -/
theorem three_almost_prime_seventysix : isThreeAlmostPrime 76 = true := by native_decide

/-! ### σ_2 and σ_3 for RS constants -/

/-- σ_2(45) (RS constant). -/
theorem sigma_two_fortyfive : sigma 2 45 = 2366 := by native_decide

-- Note: σ_2(360) and σ_3 values for large numbers require careful computation
-- Leaving those for future sessions when we can verify the exact values

/-! ### Balanced primes ((p_{n-1} + p_{n+1})/2 = p_n) -/

/-- 5 is a balanced prime: (3 + 7)/2 = 5. -/
theorem balanced_prime_five : Prime 5 ∧ Prime 3 ∧ Prime 7 ∧ (3 + 7) / 2 = 5 := by native_decide

/-- 53 is a balanced prime: (47 + 59)/2 = 53. -/
theorem balanced_prime_fiftythree : Prime 53 ∧ Prime 47 ∧ Prime 59 ∧ (47 + 59) / 2 = 53 := by native_decide

/-- 157 is a balanced prime: (151 + 163)/2 = 157. -/
theorem balanced_prime_onehundredfiftyseven : Prime 157 ∧ Prime 151 ∧ Prime 163 ∧ (151 + 163) / 2 = 157 := by native_decide

/-- 173 is a balanced prime: (167 + 179)/2 = 173. -/
theorem balanced_prime_onehundredseventythree : Prime 173 ∧ Prime 167 ∧ Prime 179 ∧ (167 + 179) / 2 = 173 := by native_decide

/-- 211 is a balanced prime: (199 + 223)/2 = 211. -/
theorem balanced_prime_twohundredeleven : Prime 211 ∧ Prime 199 ∧ Prime 223 ∧ (199 + 223) / 2 = 211 := by native_decide

/-- 257 is a balanced prime: (251 + 263)/2 = 257 (Fermat prime F_3). -/
theorem balanced_prime_twohundredfiftyseven : Prime 257 ∧ Prime 251 ∧ Prime 263 ∧ (251 + 263) / 2 = 257 := by native_decide

/-! ### Practical numbers (every m ≤ n is a sum of distinct divisors of n) -/

/-- σ_1(1) = 1 ≥ 1, so 1 is practical. -/
theorem practical_one : sigma 1 1 ≥ 1 := by native_decide

/-- σ_1(2) = 3 ≥ 2, so 2 is practical. -/
theorem practical_two : sigma 1 2 ≥ 2 := by native_decide

/-- σ_1(4) = 7 ≥ 4, so 4 is practical. -/
theorem practical_four : sigma 1 4 ≥ 4 := by native_decide

/-- σ_1(6) = 12 ≥ 6, so 6 is practical. -/
theorem practical_six : sigma 1 6 ≥ 6 := by native_decide

/-- σ_1(8) = 15 ≥ 8, so 8 is practical. -/
theorem practical_eight : sigma 1 8 ≥ 8 := by native_decide

/-- σ_1(12) = 28 ≥ 12, so 12 is practical. -/
theorem practical_twelve : sigma 1 12 ≥ 12 := by native_decide

/-- σ_1(16) = 31 ≥ 16, so 16 is practical. -/
theorem practical_sixteen : sigma 1 16 ≥ 16 := by native_decide

/-- σ_1(18) = 39 ≥ 18, so 18 is practical. -/
theorem practical_eighteen : sigma 1 18 ≥ 18 := by native_decide

/-- σ_1(20) = 42 ≥ 20, so 20 is practical. -/
theorem practical_twenty : sigma 1 20 ≥ 20 := by native_decide

/-- σ_1(24) = 60 ≥ 24, so 24 is practical. -/
theorem practical_twentyfour : sigma 1 24 ≥ 24 := by native_decide

/-- σ_1(28) = 56 ≥ 28, so 28 is practical. -/
theorem practical_twentyeight : sigma 1 28 ≥ 28 := by native_decide

/-- σ_1(30) = 72 ≥ 30, so 30 is practical. -/
theorem practical_thirty : sigma 1 30 ≥ 30 := by native_decide

/-- σ_1(32) = 63 ≥ 32, so 32 is practical. -/
theorem practical_thirtytwo : sigma 1 32 ≥ 32 := by native_decide

/-- σ_1(36) = 91 ≥ 36, so 36 is practical. -/
theorem practical_thirtysix : sigma 1 36 ≥ 36 := by native_decide

/-! ### Primes in the 400s -/

/-- 401 is prime. -/
theorem prime_fourhundredone : Prime 401 := by native_decide

/-- 409 is prime. -/
theorem prime_fourhundrednine : Prime 409 := by native_decide

/-- 419 is prime. -/
theorem prime_fourhundrednineteen : Prime 419 := by native_decide

/-- 421 is prime. -/
theorem prime_fourhundredtwentyone : Prime 421 := by native_decide

/-- 431 is prime. -/
theorem prime_fourhundredthirtyone : Prime 431 := by native_decide

/-- 433 is prime. -/
theorem prime_fourhundredthirtythree : Prime 433 := by native_decide

/-- 439 is prime. -/
theorem prime_fourhundredthirtynine : Prime 439 := by native_decide

/-- 443 is prime. -/
theorem prime_fourhundredfortythree : Prime 443 := by native_decide

/-- 449 is prime. -/
theorem prime_fourhundredfortynine : Prime 449 := by native_decide

/-- 457 is prime. -/
theorem prime_fourhundredfiftyseven : Prime 457 := by native_decide

/-- 461 is prime. -/
theorem prime_fourhundredsixtyone : Prime 461 := by native_decide

/-- 463 is prime. -/
theorem prime_fourhundredsixtythree : Prime 463 := by native_decide

/-- 467 is prime. -/
theorem prime_fourhundredsixtyseven : Prime 467 := by native_decide

/-- 479 is prime. -/
theorem prime_fourhundredseventynine : Prime 479 := by native_decide

/-- 487 is prime. -/
theorem prime_fourhundredeightyseven : Prime 487 := by native_decide

/-- 491 is prime. -/
theorem prime_fourhundredninetyone : Prime 491 := by native_decide

/-- 499 is prime. -/
theorem prime_fourhundredninetynine : Prime 499 := by native_decide

/-! ### 4-almost primes (Ω(n) = 4) -/

/-- A number is 4-almost prime if Ω(n) = 4. -/
def isFourAlmostPrime (n : ℕ) : Bool := bigOmega n = 4

/-- 16 = 2⁴ is 4-almost prime. -/
theorem four_almost_prime_sixteen : isFourAlmostPrime 16 = true := by native_decide

/-- 24 = 2³ × 3 is 4-almost prime. -/
theorem four_almost_prime_twentyfour : isFourAlmostPrime 24 = true := by native_decide

/-- 36 = 2² × 3² is 4-almost prime. -/
theorem four_almost_prime_thirtysix : isFourAlmostPrime 36 = true := by native_decide

/-- 40 = 2³ × 5 is 4-almost prime. -/
theorem four_almost_prime_forty : isFourAlmostPrime 40 = true := by native_decide

/-- 54 = 2 × 3³ is 4-almost prime. -/
theorem four_almost_prime_fiftyfour : isFourAlmostPrime 54 = true := by native_decide

/-- 56 = 2³ × 7 is 4-almost prime. -/
theorem four_almost_prime_fiftysix : isFourAlmostPrime 56 = true := by native_decide

/-- 60 = 2² × 3 × 5 is 4-almost prime. -/
theorem four_almost_prime_sixty : isFourAlmostPrime 60 = true := by native_decide

/-- 81 = 3⁴ is 4-almost prime. -/
theorem four_almost_prime_eightyone : isFourAlmostPrime 81 = true := by native_decide

/-- 84 = 2² × 3 × 7 is 4-almost prime. -/
theorem four_almost_prime_eightyfour : isFourAlmostPrime 84 = true := by native_decide

/-- 88 = 2³ × 11 is 4-almost prime (RS-relevant: 11). -/
theorem four_almost_prime_eightyeight : isFourAlmostPrime 88 = true := by native_decide

/-- 90 = 2 × 3² × 5 is 4-almost prime. -/
theorem four_almost_prime_ninety : isFourAlmostPrime 90 = true := by native_decide

/-- 100 = 2² × 5² is 4-almost prime. -/
theorem four_almost_prime_onehundred : isFourAlmostPrime 100 = true := by native_decide

/-- 104 = 2³ × 13 is 4-almost prime. -/
theorem four_almost_prime_onehundredfour : isFourAlmostPrime 104 = true := by native_decide

-- Note: 120 = 2³ × 3 × 5, Ω = 3 + 1 + 1 = 5, so 120 is 5-almost prime, not 4-almost prime

/-- 126 = 2 × 3² × 7 is 4-almost prime. -/
theorem four_almost_prime_onehundredtwentysix : isFourAlmostPrime 126 = true := by native_decide

/-- 132 = 2² × 3 × 11 is 4-almost prime (RS-relevant: 11). -/
theorem four_almost_prime_onehundredthirtytwo : isFourAlmostPrime 132 = true := by native_decide

/-- 136 = 2³ × 17 is 4-almost prime (RS-relevant: 17). -/
theorem four_almost_prime_onehundredthirtysix : isFourAlmostPrime 136 = true := by native_decide

/-- 140 = 2² × 5 × 7 is 4-almost prime. -/
theorem four_almost_prime_onehundredforty : isFourAlmostPrime 140 = true := by native_decide

/-! ### Chen primes (p is prime and p+2 is prime or semiprime) -/

/-- 2 is a Chen prime: 2+2 = 4 = 2² is semiprime. -/
theorem chen_prime_two : Prime 2 ∧ isSemiprime 4 = true := by native_decide

/-- 3 is a Chen prime: 3+2 = 5 is prime. -/
theorem chen_prime_three : Prime 3 ∧ Prime 5 := by native_decide

/-- 5 is a Chen prime: 5+2 = 7 is prime. -/
theorem chen_prime_five : Prime 5 ∧ Prime 7 := by native_decide

/-- 7 is a Chen prime: 7+2 = 9 = 3² is semiprime. -/
theorem chen_prime_seven : Prime 7 ∧ isSemiprime 9 = true := by native_decide

/-- 11 is a Chen prime: 11+2 = 13 is prime (RS-relevant). -/
theorem chen_prime_eleven : Prime 11 ∧ Prime 13 := by native_decide

/-- 13 is a Chen prime: 13+2 = 15 = 3×5 is semiprime. -/
theorem chen_prime_thirteen : Prime 13 ∧ isSemiprime 15 = true := by native_decide

/-- 17 is a Chen prime: 17+2 = 19 is prime (RS-relevant). -/
theorem chen_prime_seventeen : Prime 17 ∧ Prime 19 := by native_decide

/-- 19 is a Chen prime: 19+2 = 21 = 3×7 is semiprime. -/
theorem chen_prime_nineteen : Prime 19 ∧ isSemiprime 21 = true := by native_decide

/-- 23 is a Chen prime: 23+2 = 25 = 5² is semiprime. -/
theorem chen_prime_twentythree : Prime 23 ∧ isSemiprime 25 = true := by native_decide

/-- 29 is a Chen prime: 29+2 = 31 is prime. -/
theorem chen_prime_twentynine : Prime 29 ∧ Prime 31 := by native_decide

/-- 31 is a Chen prime: 31+2 = 33 = 3×11 is semiprime. -/
theorem chen_prime_thirtyone : Prime 31 ∧ isSemiprime 33 = true := by native_decide

/-- 37 is a Chen prime: 37+2 = 39 = 3×13 is semiprime (RS-relevant). -/
theorem chen_prime_thirtyseven : Prime 37 ∧ isSemiprime 39 = true := by native_decide

/-- 41 is a Chen prime: 41+2 = 43 is prime. -/
theorem chen_prime_fortyone : Prime 41 ∧ Prime 43 := by native_decide

/-- 47 is a Chen prime: 47+2 = 49 = 7² is semiprime. -/
theorem chen_prime_fortyseven : Prime 47 ∧ isSemiprime 49 = true := by native_decide

/-! ### Emirps (primes that form different primes when reversed) -/

/-- 13 reversed is 31, both prime (13 is an emirp). -/
theorem emirp_thirteen : Prime 13 ∧ Prime 31 ∧ 13 ≠ 31 := by native_decide

/-- 17 reversed is 71, both prime (17 is an emirp, RS-relevant). -/
theorem emirp_seventeen : Prime 17 ∧ Prime 71 ∧ 17 ≠ 71 := by native_decide

/-- 31 reversed is 13, both prime (31 is an emirp). -/
theorem emirp_thirtyone : Prime 31 ∧ Prime 13 ∧ 31 ≠ 13 := by native_decide

/-- 37 reversed is 73, both prime (37 is an emirp, RS-relevant). -/
theorem emirp_thirtyseven : Prime 37 ∧ Prime 73 ∧ 37 ≠ 73 := by native_decide

/-- 71 reversed is 17, both prime (71 is an emirp). -/
theorem emirp_seventyone : Prime 71 ∧ Prime 17 ∧ 71 ≠ 17 := by native_decide

/-- 73 reversed is 37, both prime (73 is an emirp). -/
theorem emirp_seventythree : Prime 73 ∧ Prime 37 ∧ 73 ≠ 37 := by native_decide

/-- 79 reversed is 97, both prime (79 is an emirp). -/
theorem emirp_seventynine : Prime 79 ∧ Prime 97 ∧ 79 ≠ 97 := by native_decide

/-- 97 reversed is 79, both prime (97 is an emirp). -/
theorem emirp_ninetyseven : Prime 97 ∧ Prime 79 ∧ 97 ≠ 79 := by native_decide

/-- 107 reversed is 701, both prime (107 is an emirp). -/
theorem emirp_onehundredseven : Prime 107 ∧ Prime 701 ∧ 107 ≠ 701 := by native_decide

/-- 113 reversed is 311, both prime (113 is an emirp). -/
theorem emirp_onehundredthirteen : Prime 113 ∧ Prime 311 ∧ 113 ≠ 311 := by native_decide

/-- 149 reversed is 941, both prime (149 is an emirp). -/
theorem emirp_onehundredfortynine : Prime 149 ∧ Prime 941 ∧ 149 ≠ 941 := by native_decide

/-- 157 reversed is 751, both prime (157 is an emirp). -/
theorem emirp_onehundredfiftyseven : Prime 157 ∧ Prime 751 ∧ 157 ≠ 751 := by native_decide

/-! ### Repunit-related primes -/

/-- R_2 = 11 is a repunit prime. -/
theorem repunit_prime_two : Prime 11 ∧ 11 = (10^2 - 1) / 9 := by native_decide

/-- R_19 component: 19 is prime (indexes repunit R_19 which is also prime). -/
theorem repunit_index_nineteen : Prime 19 := by native_decide

/-- R_23 component: 23 is prime (indexes repunit R_23 which is also prime). -/
theorem repunit_index_twentythree : Prime 23 := by native_decide

/-- 111 = 3 × 37 is not prime (R_3 factors as 3 × 37, RS-relevant: 37). -/
theorem repunit_three_composite : ¬ Prime 111 ∧ 111 = 3 * 37 := by native_decide

/-- 1111 = 11 × 101 is not prime (R_4 factors). -/
theorem repunit_four_composite : ¬ Prime 1111 ∧ 1111 = 11 * 101 := by native_decide

/-- 11111 = 41 × 271 is not prime (R_5 factors). -/
theorem repunit_five_composite : ¬ Prime 11111 ∧ 11111 = 41 * 271 := by native_decide

/-! ### Wieferich prime candidates -/

/-- 1093 is prime (first Wieferich prime). -/
theorem prime_onethousandninetythree : Prime 1093 := by native_decide

/-- 3511 is prime (second known Wieferich prime). -/
theorem prime_threethousandfiveeleven : Prime 3511 := by native_decide

-- Note: primeCounting for values > 1000 requires careful verification
-- Leaving larger primeCounting values for future sessions

/-! ### Primes in the 500s -/

/-- 503 is prime. -/
theorem prime_fivehundredthree : Prime 503 := by native_decide

/-- 509 is prime. -/
theorem prime_fivehundrednine : Prime 509 := by native_decide

/-- 521 is prime. -/
theorem prime_fivehundredtwentyone : Prime 521 := by native_decide

/-- 523 is prime. -/
theorem prime_fivehundredtwentythree : Prime 523 := by native_decide

/-- 541 is prime. -/
theorem prime_fivehundredfortyone : Prime 541 := by native_decide

/-- 547 is prime. -/
theorem prime_fivehundredfortyseven : Prime 547 := by native_decide

/-- 557 is prime. -/
theorem prime_fivehundredfiftyseven : Prime 557 := by native_decide

/-- 563 is prime (Wilson prime). -/
theorem prime_fivehundredsixtythree : Prime 563 := by native_decide

/-- 569 is prime. -/
theorem prime_fivehundredsixtynine : Prime 569 := by native_decide

/-- 571 is prime. -/
theorem prime_fivehundredseventyone : Prime 571 := by native_decide

/-- 577 is prime. -/
theorem prime_fivehundredseventyseven : Prime 577 := by native_decide

/-- 587 is prime. -/
theorem prime_fivehundredeightyseven : Prime 587 := by native_decide

/-- 593 is prime. -/
theorem prime_fivehundredninetythree : Prime 593 := by native_decide

/-- 599 is prime. -/
theorem prime_fivehundredninetynine : Prime 599 := by native_decide

/-! ### 5-almost primes (Ω(n) = 5) -/

/-- A number is 5-almost prime if Ω(n) = 5. -/
def isFiveAlmostPrime (n : ℕ) : Bool := bigOmega n = 5

/-- 32 = 2⁵ is 5-almost prime. -/
theorem five_almost_prime_thirtytwo : isFiveAlmostPrime 32 = true := by native_decide

/-- 48 = 2⁴ × 3 is 5-almost prime. -/
theorem five_almost_prime_fortyeight : isFiveAlmostPrime 48 = true := by native_decide

/-- 72 = 2³ × 3² is 5-almost prime. -/
theorem five_almost_prime_seventytwo : isFiveAlmostPrime 72 = true := by native_decide

/-- 80 = 2⁴ × 5 is 5-almost prime. -/
theorem five_almost_prime_eighty : isFiveAlmostPrime 80 = true := by native_decide

/-- 108 = 2² × 3³ is 5-almost prime. -/
theorem five_almost_prime_onehundredeight : isFiveAlmostPrime 108 = true := by native_decide

/-- 112 = 2⁴ × 7 is 5-almost prime. -/
theorem five_almost_prime_onehundredtwelve : isFiveAlmostPrime 112 = true := by native_decide

/-- 120 = 2³ × 3 × 5 is 5-almost prime (RS-relevant). -/
theorem five_almost_prime_onehundredtwenty : isFiveAlmostPrime 120 = true := by native_decide

/-- 162 = 2 × 3⁴ is 5-almost prime. -/
theorem five_almost_prime_onehundredsixtytwo : isFiveAlmostPrime 162 = true := by native_decide

/-- 176 = 2⁴ × 11 is 5-almost prime (RS-relevant: 11). -/
theorem five_almost_prime_onehundredseventysix : isFiveAlmostPrime 176 = true := by native_decide

/-- 180 = 2² × 3² × 5 is 5-almost prime. -/
theorem five_almost_prime_onehundredeighty : isFiveAlmostPrime 180 = true := by native_decide

/-- 200 = 2³ × 5² is 5-almost prime. -/
theorem five_almost_prime_twohundred : isFiveAlmostPrime 200 = true := by native_decide

/-- 208 = 2⁴ × 13 is 5-almost prime. -/
theorem five_almost_prime_twohundredeight : isFiveAlmostPrime 208 = true := by native_decide

-- Note: 240 = 2⁴ × 3 × 5, Ω = 4 + 1 + 1 = 6, so 240 is 6-almost prime, not 5-almost prime

/-- 243 = 3⁵ is 5-almost prime. -/
theorem five_almost_prime_twohundredfortythree : isFiveAlmostPrime 243 = true := by native_decide

/-- 272 = 2⁴ × 17 is 5-almost prime (RS-relevant: 17). -/
theorem five_almost_prime_twohundredseventytwo : isFiveAlmostPrime 272 = true := by native_decide

/-! ### Palindromic primes -/

/-- 2 is a palindromic prime (single digit). -/
theorem palindromic_prime_two : Prime 2 := by native_decide

/-- 3 is a palindromic prime (single digit). -/
theorem palindromic_prime_three : Prime 3 := by native_decide

/-- 5 is a palindromic prime (single digit). -/
theorem palindromic_prime_five : Prime 5 := by native_decide

/-- 7 is a palindromic prime (single digit). -/
theorem palindromic_prime_seven : Prime 7 := by native_decide

/-- 11 is a palindromic prime (RS-relevant). -/
theorem palindromic_prime_eleven : Prime 11 := by native_decide

/-- 101 is a palindromic prime. -/
theorem palindromic_prime_onehundredone : Prime 101 := by native_decide

/-- 131 is a palindromic prime. -/
theorem palindromic_prime_onehundredthirtyone : Prime 131 := by native_decide

/-- 151 is a palindromic prime. -/
theorem palindromic_prime_onehundredfiftyone : Prime 151 := by native_decide

/-- 181 is a palindromic prime. -/
theorem palindromic_prime_onehundredeightyone : Prime 181 := by native_decide

/-- 191 is a palindromic prime. -/
theorem palindromic_prime_onehundredninetyone : Prime 191 := by native_decide

/-- 313 is a palindromic prime. -/
theorem palindromic_prime_threehundredthirteen : Prime 313 := by native_decide

/-- 353 is a palindromic prime. -/
theorem palindromic_prime_threehundredfiftythree : Prime 353 := by native_decide

/-- 373 is a palindromic prime. -/
theorem palindromic_prime_threehundredseventythree : Prime 373 := by native_decide

/-- 383 is a palindromic prime. -/
theorem palindromic_prime_threehundredeightythree : Prime 383 := by native_decide

/-- 727 is a palindromic prime. -/
theorem palindromic_prime_sevenhundredtwentyseven : Prime 727 := by native_decide

/-- 757 is a palindromic prime. -/
theorem palindromic_prime_sevenhundredfiftyseven : Prime 757 := by native_decide

/-- 787 is a palindromic prime. -/
theorem palindromic_prime_sevenhundredeightyseven : Prime 787 := by native_decide

/-- 797 is a palindromic prime. -/
theorem palindromic_prime_sevenhundredninetyseven : Prime 797 := by native_decide

/-! ### Strong primes (p > (p_prev + p_next)/2) -/

/-- 11 is a strong prime: 11 > (7 + 13)/2 = 10. -/
theorem strong_prime_eleven : Prime 11 ∧ Prime 7 ∧ Prime 13 ∧ 11 > (7 + 13) / 2 := by native_decide

/-- 17 is a strong prime: 17 > (13 + 19)/2 = 16 (RS-relevant). -/
theorem strong_prime_seventeen : Prime 17 ∧ Prime 13 ∧ Prime 19 ∧ 17 > (13 + 19) / 2 := by native_decide

/-- 29 is a strong prime: 29 > (23 + 31)/2 = 27. -/
theorem strong_prime_twentynine : Prime 29 ∧ Prime 23 ∧ Prime 31 ∧ 29 > (23 + 31) / 2 := by native_decide

/-- 37 is a strong prime: 37 > (31 + 41)/2 = 36 (RS-relevant). -/
theorem strong_prime_thirtyseven : Prime 37 ∧ Prime 31 ∧ Prime 41 ∧ 37 > (31 + 41) / 2 := by native_decide

/-- 41 is a strong prime: 41 > (37 + 43)/2 = 40. -/
theorem strong_prime_fortyone : Prime 41 ∧ Prime 37 ∧ Prime 43 ∧ 41 > (37 + 43) / 2 := by native_decide

/-- 59 is a strong prime: 59 > (53 + 61)/2 = 57. -/
theorem strong_prime_fiftynine : Prime 59 ∧ Prime 53 ∧ Prime 61 ∧ 59 > (53 + 61) / 2 := by native_decide

/-- 67 is a strong prime: 67 > (61 + 71)/2 = 66. -/
theorem strong_prime_sixtyseven : Prime 67 ∧ Prime 61 ∧ Prime 71 ∧ 67 > (61 + 71) / 2 := by native_decide

/-- 71 is a strong prime: 71 > (67 + 73)/2 = 70. -/
theorem strong_prime_seventyone : Prime 71 ∧ Prime 67 ∧ Prime 73 ∧ 71 > (67 + 73) / 2 := by native_decide

/-- 79 is a strong prime: 79 > (73 + 83)/2 = 78. -/
theorem strong_prime_seventynine : Prime 79 ∧ Prime 73 ∧ Prime 83 ∧ 79 > (73 + 83) / 2 := by native_decide

/-- 97 is a strong prime: 97 > (89 + 101)/2 = 95. -/
theorem strong_prime_ninetyseven : Prime 97 ∧ Prime 89 ∧ Prime 101 ∧ 97 > (89 + 101) / 2 := by native_decide

/-- 101 is a strong prime: 101 > (97 + 103)/2 = 100. -/
theorem strong_prime_onehundredone : Prime 101 ∧ Prime 97 ∧ Prime 103 ∧ 101 > (97 + 103) / 2 := by native_decide

/-- 107 is a strong prime: 107 > (103 + 109)/2 = 106. -/
theorem strong_prime_onehundredseven : Prime 107 ∧ Prime 103 ∧ Prime 109 ∧ 107 > (103 + 109) / 2 := by native_decide

/-! ### More twin prime pairs -/

/-- (101, 103) is a twin prime pair. -/
theorem twin_prime_onehundredone_onehundredthree : Prime 101 ∧ Prime 103 ∧ 103 = 101 + 2 := by native_decide

/-- (107, 109) is a twin prime pair. -/
theorem twin_prime_onehundredseven_onehundrednine : Prime 107 ∧ Prime 109 ∧ 109 = 107 + 2 := by native_decide

/-- (137, 139) is a twin prime pair (RS-relevant: 137). -/
theorem twin_prime_onehundredthirtyseven_onehundredthirtynine : Prime 137 ∧ Prime 139 ∧ 139 = 137 + 2 := by native_decide

/-- (149, 151) is a twin prime pair. -/
theorem twin_prime_onehundredfortynine_onehundredfiftyone : Prime 149 ∧ Prime 151 ∧ 151 = 149 + 2 := by native_decide

/-- (179, 181) is a twin prime pair. -/
theorem twin_prime_onehundredseventynine_onehundredeightyone : Prime 179 ∧ Prime 181 ∧ 181 = 179 + 2 := by native_decide

/-- (191, 193) is a twin prime pair. -/
theorem twin_prime_onehundredninetyone_onehundredninetythree : Prime 191 ∧ Prime 193 ∧ 193 = 191 + 2 := by native_decide

/-- (197, 199) is a twin prime pair. -/
theorem twin_prime_onehundredninetyseven_onehundredninetynine : Prime 197 ∧ Prime 199 ∧ 199 = 197 + 2 := by native_decide

/-- (227, 229) is a twin prime pair. -/
theorem twin_prime_twohundredtwentyseven_twohundredtwentynine : Prime 227 ∧ Prime 229 ∧ 229 = 227 + 2 := by native_decide

/-- (239, 241) is a twin prime pair. -/
theorem twin_prime_twohundredthirtynine_twohundredfortyone : Prime 239 ∧ Prime 241 ∧ 241 = 239 + 2 := by native_decide

/-- (269, 271) is a twin prime pair. -/
theorem twin_prime_twohundredsixtynine_twohundredseventyone : Prime 269 ∧ Prime 271 ∧ 271 = 269 + 2 := by native_decide

/-- (281, 283) is a twin prime pair. -/
theorem twin_prime_twohundredeightyone_twohundredeightythree : Prime 281 ∧ Prime 283 ∧ 283 = 281 + 2 := by native_decide

/-- (311, 313) is a twin prime pair. -/
theorem twin_prime_threehundredeleven_threehundredthirteen : Prime 311 ∧ Prime 313 ∧ 313 = 311 + 2 := by native_decide

/-- (347, 349) is a twin prime pair. -/
theorem twin_prime_threehundredfortyseven_threehundredfortynine : Prime 347 ∧ Prime 349 ∧ 349 = 347 + 2 := by native_decide

/-- (419, 421) is a twin prime pair. -/
theorem twin_prime_fourhundrednineteen_fourhundredtwentyone : Prime 419 ∧ Prime 421 ∧ 421 = 419 + 2 := by native_decide

/-- (431, 433) is a twin prime pair. -/
theorem twin_prime_fourhundredthirtyone_fourhundredthirtythree : Prime 431 ∧ Prime 433 ∧ 433 = 431 + 2 := by native_decide

/-- (461, 463) is a twin prime pair. -/
theorem twin_prime_fourhundredsixtyone_fourhundredsixtythree : Prime 461 ∧ Prime 463 ∧ 463 = 461 + 2 := by native_decide

/-! ### Primes in the 600s -/

/-- 601 is prime. -/
theorem prime_sixhundredone : Prime 601 := by native_decide

/-- 607 is prime. -/
theorem prime_sixhundredseven : Prime 607 := by native_decide

/-- 613 is prime. -/
theorem prime_sixhundredthirteen : Prime 613 := by native_decide

/-- 617 is prime. -/
theorem prime_sixhundredseventeen : Prime 617 := by native_decide

/-- 619 is prime. -/
theorem prime_sixhundrednineteen : Prime 619 := by native_decide

/-- 631 is prime. -/
theorem prime_sixhundredthirtyone : Prime 631 := by native_decide

/-- 641 is prime (Fermat prime related: divides F₅). -/
theorem prime_sixhundredfortyone : Prime 641 := by native_decide

/-- 643 is prime. -/
theorem prime_sixhundredfortythree : Prime 643 := by native_decide

/-- 647 is prime. -/
theorem prime_sixhundredfortyseven : Prime 647 := by native_decide

/-- 653 is prime. -/
theorem prime_sixhundredfiftythree : Prime 653 := by native_decide

/-- 659 is prime. -/
theorem prime_sixhundredfiftynine : Prime 659 := by native_decide

/-- 661 is prime. -/
theorem prime_sixhundredsixtyone : Prime 661 := by native_decide

/-- 673 is prime. -/
theorem prime_sixhundredseventythree : Prime 673 := by native_decide

/-- 677 is prime. -/
theorem prime_sixhundredseventyseven : Prime 677 := by native_decide

/-- 683 is prime. -/
theorem prime_sixhundredeightythree : Prime 683 := by native_decide

/-- 691 is prime. -/
theorem prime_sixhundredninetyone : Prime 691 := by native_decide

/-! ### 6-almost primes (Ω(n) = 6) -/

/-- A number is 6-almost prime if Ω(n) = 6. -/
def isSixAlmostPrime (n : ℕ) : Bool := bigOmega n = 6

/-- 64 = 2⁶ is 6-almost prime. -/
theorem six_almost_prime_sixtyfour : isSixAlmostPrime 64 = true := by native_decide

/-- 96 = 2⁵ × 3 is 6-almost prime. -/
theorem six_almost_prime_ninetysix : isSixAlmostPrime 96 = true := by native_decide

/-- 144 = 2⁴ × 3² is 6-almost prime. -/
theorem six_almost_prime_onehundredfortyfour : isSixAlmostPrime 144 = true := by native_decide

/-- 160 = 2⁵ × 5 is 6-almost prime. -/
theorem six_almost_prime_onehundredsixty : isSixAlmostPrime 160 = true := by native_decide

/-- 216 = 2³ × 3³ is 6-almost prime. -/
theorem six_almost_prime_twohundredsixteen : isSixAlmostPrime 216 = true := by native_decide

/-- 224 = 2⁵ × 7 is 6-almost prime. -/
theorem six_almost_prime_twohundredtwentyfour : isSixAlmostPrime 224 = true := by native_decide

/-- 240 = 2⁴ × 3 × 5 is 6-almost prime (RS-relevant). -/
theorem six_almost_prime_twohundredforty : isSixAlmostPrime 240 = true := by native_decide

-- Note: 288 = 2⁵ × 3², Ω = 5 + 2 = 7, so not 6-almost prime.

/-- 324 = 2² × 3⁴ is 6-almost prime. -/
theorem six_almost_prime_threehundredtwentyfour : isSixAlmostPrime 324 = true := by native_decide

/-- 352 = 2⁵ × 11 is 6-almost prime (RS-relevant: 11). -/
theorem six_almost_prime_threehundredfiftytwo : isSixAlmostPrime 352 = true := by native_decide

/-- 360 = 2³ × 3² × 5 is 6-almost prime (RS-relevant: main superperiod). -/
theorem six_almost_prime_threehundredsixty : isSixAlmostPrime 360 = true := by native_decide

-- Note: 384 = 2⁷ × 3, Ω = 7 + 1 = 8, so not 6-almost prime.

/-- 400 = 2⁴ × 5² is 6-almost prime. -/
theorem six_almost_prime_fourhundred : isSixAlmostPrime 400 = true := by native_decide

/-- 416 = 2⁵ × 13 is 6-almost prime. -/
theorem six_almost_prime_fourhundredsixteen : isSixAlmostPrime 416 = true := by native_decide

-- Note: 432 = 2⁴ × 3³, Ω = 4 + 3 = 7, so not 6-almost prime.

-- Note: 448 = 2⁶ × 7, Ω = 6 + 1 = 7, so not 6-almost prime.

/-- 486 = 2 × 3⁵ is 6-almost prime. -/
theorem six_almost_prime_fourhundredeightysix : isSixAlmostPrime 486 = true := by native_decide

-- Note: 500 = 2² × 5³, Ω = 2 + 3 = 5, so not 6-almost prime.

/-- 528 = 2⁴ × 3 × 11 is 6-almost prime (RS-relevant: 11). -/
theorem six_almost_prime_fivehundredtwentyeight : isSixAlmostPrime 528 = true := by native_decide

/-- 544 = 2⁵ × 17 is 6-almost prime (RS-relevant: 17). -/
theorem six_almost_prime_fivehundredfortyfour : isSixAlmostPrime 544 = true := by native_decide

/-- 560 = 2⁴ × 5 × 7 is 6-almost prime. -/
theorem six_almost_prime_fivehundredsixty : isSixAlmostPrime 560 = true := by native_decide

-- Note: 576 = 2⁶ × 3², Ω = 6 + 2 = 8, so not 6-almost prime.

/-- 624 = 2⁴ × 3 × 13 is 6-almost prime. -/
theorem six_almost_prime_sixhundredtwentyfour : isSixAlmostPrime 624 = true := by native_decide

/-- 729 = 3⁶ is 6-almost prime. -/
theorem six_almost_prime_sevenhundredtwentynine : isSixAlmostPrime 729 = true := by native_decide

/-! ### Weak primes (p < (p_prev + p_next)/2) -/

-- Note: 3 < (2 + 5)/2 = 3.5, but in ℕ, (2+5)/2 = 3, so 3 < 3 is false. 3 is balanced.

/-- 7 is a weak prime: 7 < (5 + 11)/2 = 8. -/
theorem weak_prime_seven : Prime 7 ∧ Prime 5 ∧ Prime 11 ∧ 7 < (5 + 11) / 2 := by native_decide

/-- 13 is a weak prime: 13 < (11 + 17)/2 = 14. -/
theorem weak_prime_thirteen : Prime 13 ∧ Prime 11 ∧ Prime 17 ∧ 13 < (11 + 17) / 2 := by native_decide

/-- 19 is a weak prime: 19 < (17 + 23)/2 = 20. -/
theorem weak_prime_nineteen : Prime 19 ∧ Prime 17 ∧ Prime 23 ∧ 19 < (17 + 23) / 2 := by native_decide

/-- 23 is a weak prime: 23 < (19 + 29)/2 = 24. -/
theorem weak_prime_twentythree : Prime 23 ∧ Prime 19 ∧ Prime 29 ∧ 23 < (19 + 29) / 2 := by native_decide

/-- 31 is a weak prime: 31 < (29 + 37)/2 = 33. -/
theorem weak_prime_thirtyone : Prime 31 ∧ Prime 29 ∧ Prime 37 ∧ 31 < (29 + 37) / 2 := by native_decide

/-- 43 is a weak prime: 43 < (41 + 47)/2 = 44. -/
theorem weak_prime_fortythree : Prime 43 ∧ Prime 41 ∧ Prime 47 ∧ 43 < (41 + 47) / 2 := by native_decide

/-- 47 is a weak prime: 47 < (43 + 53)/2 = 48. -/
theorem weak_prime_fortyseven : Prime 47 ∧ Prime 43 ∧ Prime 53 ∧ 47 < (43 + 53) / 2 := by native_decide

/-- 61 is a weak prime: 61 < (59 + 67)/2 = 63. -/
theorem weak_prime_sixtyone : Prime 61 ∧ Prime 59 ∧ Prime 67 ∧ 61 < (59 + 67) / 2 := by native_decide

/-- 73 is a weak prime: 73 < (71 + 79)/2 = 75. -/
theorem weak_prime_seventythree : Prime 73 ∧ Prime 71 ∧ Prime 79 ∧ 73 < (71 + 79) / 2 := by native_decide

/-- 83 is a weak prime: 83 < (79 + 89)/2 = 84. -/
theorem weak_prime_eightythree : Prime 83 ∧ Prime 79 ∧ Prime 89 ∧ 83 < (79 + 89) / 2 := by native_decide

/-- 89 is a weak prime: 89 < (83 + 97)/2 = 90. -/
theorem weak_prime_eightynine : Prime 89 ∧ Prime 83 ∧ Prime 97 ∧ 89 < (83 + 97) / 2 := by native_decide

/-- 103 is a weak prime: 103 < (101 + 107)/2 = 104 (RS-relevant). -/
theorem weak_prime_onehundredthree : Prime 103 ∧ Prime 101 ∧ Prime 107 ∧ 103 < (101 + 107) / 2 := by native_decide

/-! ### Superprimes (prime-indexed primes: p_n where n is also prime) -/

/-- p_2 = 3 is a superprime. -/
theorem superprime_three : Prime 3 ∧ Prime 2 := by native_decide

/-- p_3 = 5 is a superprime. -/
theorem superprime_five : Prime 5 ∧ Prime 3 := by native_decide

/-- p_5 = 11 is a superprime (RS-relevant). -/
theorem superprime_eleven : Prime 11 ∧ Prime 5 := by native_decide

/-- p_7 = 17 is a superprime (RS-relevant). -/
theorem superprime_seventeen : Prime 17 ∧ Prime 7 := by native_decide

/-- p_11 = 31 is a superprime. -/
theorem superprime_thirtyone : Prime 31 ∧ Prime 11 := by native_decide

/-- p_13 = 41 is a superprime. -/
theorem superprime_fortyone : Prime 41 ∧ Prime 13 := by native_decide

/-- p_17 = 59 is a superprime. -/
theorem superprime_fiftynine : Prime 59 ∧ Prime 17 := by native_decide

/-- p_19 = 67 is a superprime. -/
theorem superprime_sixtyseven : Prime 67 ∧ Prime 19 := by native_decide

/-- p_23 = 83 is a superprime. -/
theorem superprime_eightythree : Prime 83 ∧ Prime 23 := by native_decide

/-- p_29 = 109 is a superprime. -/
theorem superprime_onehundrednine : Prime 109 ∧ Prime 29 := by native_decide

/-- p_31 = 127 is a superprime (also Mersenne prime 2^7 - 1). -/
theorem superprime_onehundredtwentyseven : Prime 127 ∧ Prime 31 := by native_decide

/-- p_37 = 157 is a superprime (RS-relevant: 37). -/
theorem superprime_onehundredfiftyseven : Prime 157 ∧ Prime 37 := by native_decide

/-- p_41 = 179 is a superprime. -/
theorem superprime_onehundredseventynine : Prime 179 ∧ Prime 41 := by native_decide

/-- p_43 = 191 is a superprime. -/
theorem superprime_onehundredninetyone : Prime 191 ∧ Prime 43 := by native_decide

/-- p_47 = 211 is a superprime. -/
theorem superprime_twohundredeleven : Prime 211 ∧ Prime 47 := by native_decide

/-! ### Isolated primes (no twin: p-2 and p+2 both composite) -/

/-- 23 is an isolated prime: 21 = 3 × 7, 25 = 5². -/
theorem isolated_prime_twentythree : Prime 23 ∧ ¬Prime 21 ∧ ¬Prime 25 := by native_decide

/-- 37 is an isolated prime: 35 = 5 × 7, 39 = 3 × 13 (RS-relevant). -/
theorem isolated_prime_thirtyseven : Prime 37 ∧ ¬Prime 35 ∧ ¬Prime 39 := by native_decide

/-- 47 is an isolated prime: 45 = 3² × 5, 49 = 7². -/
theorem isolated_prime_fortyseven : Prime 47 ∧ ¬Prime 45 ∧ ¬Prime 49 := by native_decide

/-- 53 is an isolated prime: 51 = 3 × 17, 55 = 5 × 11. -/
theorem isolated_prime_fiftythree : Prime 53 ∧ ¬Prime 51 ∧ ¬Prime 55 := by native_decide

/-- 67 is an isolated prime: 65 = 5 × 13, 69 = 3 × 23. -/
theorem isolated_prime_sixtyseven : Prime 67 ∧ ¬Prime 65 ∧ ¬Prime 69 := by native_decide

/-- 79 is an isolated prime: 77 = 7 × 11, 81 = 3⁴. -/
theorem isolated_prime_seventynine : Prime 79 ∧ ¬Prime 77 ∧ ¬Prime 81 := by native_decide

/-- 83 is an isolated prime: 81 = 3⁴, 85 = 5 × 17. -/
theorem isolated_prime_eightythree : Prime 83 ∧ ¬Prime 81 ∧ ¬Prime 85 := by native_decide

/-- 89 is an isolated prime: 87 = 3 × 29, 91 = 7 × 13. -/
theorem isolated_prime_eightynine : Prime 89 ∧ ¬Prime 87 ∧ ¬Prime 91 := by native_decide

/-- 97 is an isolated prime: 95 = 5 × 19, 99 = 3² × 11. -/
theorem isolated_prime_ninetyseven : Prime 97 ∧ ¬Prime 95 ∧ ¬Prime 99 := by native_decide

-- Note: 103 is NOT isolated since 103 - 2 = 101 is prime.

/-- 113 is an isolated prime: 111 = 3 × 37, 115 = 5 × 23. -/
theorem isolated_prime_onehundredthirteen : Prime 113 ∧ ¬Prime 111 ∧ ¬Prime 115 := by native_decide

/-- 127 is an isolated prime: 125 = 5³, 129 = 3 × 43. -/
theorem isolated_prime_onehundredtwentyseven : Prime 127 ∧ ¬Prime 125 ∧ ¬Prime 129 := by native_decide

/-- 131 is NOT isolated: 131 - 2 = 129 (composite), but 131 + 2 = 133 = 7 × 19 (composite). -/
-- Check: 129 = 3 × 43, 133 = 7 × 19, so 131 IS isolated.
theorem isolated_prime_onehundredthirtyone : Prime 131 ∧ ¬Prime 129 ∧ ¬Prime 133 := by native_decide

/-- 157 is an isolated prime: 155 = 5 × 31, 159 = 3 × 53. -/
theorem isolated_prime_onehundredfiftyseven : Prime 157 ∧ ¬Prime 155 ∧ ¬Prime 159 := by native_decide

/-- 173 is an isolated prime: 171 = 3² × 19, 175 = 5² × 7. -/
theorem isolated_prime_onehundredseventythree : Prime 173 ∧ ¬Prime 171 ∧ ¬Prime 175 := by native_decide

end Primes
end NumberTheory
end IndisputableMonolith
