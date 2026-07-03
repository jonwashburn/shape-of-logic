/-
  PrimitiveRecognitionCalculus/PrimeAxisCoherence.lean

  Phase 5 of the Delta-Native Analysis frontier: the Prime-Axis Coherence Theorem.

  On the positive rationals the multiplicative group is free abelian on the
  primes. Before any continuity or order condition enters, a multiplicative
  character may be assigned an independent weight on every prime axis: the prime
  directions are independent. A log-character is exactly a choice of one real
  weight per prime, extended additively through prime factorization.

  The coherence move is the collapse of that freedom. A character obeys a single
  global power law `χ(n) = exp(c · W(n))` (one exponent `c` against a fixed
  reference scale `W`) if and only if its prime weights are all aligned to that
  same reference, `a(p) = c · w(p)`. Independent prime axes are synchronized into
  one scale exactly when the global power law holds.

  What is proved here:

  * `logChar_one`, `logChar_mul`  : log-characters are additive (freedom: every
                                    weight assignment is a multiplicative character);
  * `logChar_prime`               : a log-character reads back its weight at a prime;
  * `faithful`                    : characters agreeing everywhere agree on every
                                    prime weight (the axes are independent coordinates);
  * `powerLaw_iff_aligned`        : THE collapse. Global power law ⟺ aligned prime
                                    weights, against any fixed reference scale `w`;
  * `logChar_log`                 : the canonical reference scale `w(p) = log p`
                                    gives `logChar log = log`;
  * `character_is_rpow`           : under the log reference, an aligned character is
                                    exactly `n ↦ n^c`.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PrimeAxisCoherence

open scoped BigOperators

/-- The log-character with prime weights `a`: the additive extension of `a`
through prime factorization. `a p` is the log-value the character assigns to the
prime axis `p`. -/
noncomputable def logChar (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  n.factorization.sum (fun p k => (k : ℝ) * a p)

@[simp] theorem logChar_one (a : ℕ → ℝ) : logChar a 1 = 0 := by
  unfold logChar
  simp

/-- **Freedom.** Every weight assignment extends to a multiplicative character:
the log-character is additive on products of nonzero naturals. The prime axes
are independent; no relation among them is forced before coherence enters. -/
theorem logChar_mul (a : ℕ → ℝ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    logChar a (m * n) = logChar a m + logChar a n := by
  unfold logChar
  rw [Nat.factorization_mul hm hn]
  rw [Finsupp.sum_add_index']
  · intro p; simp
  · intro p k1 k2; push_cast; ring

/-- A log-character reads back exactly its weight at a prime. -/
theorem logChar_prime (a : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : logChar a p = a p := by
  unfold logChar
  rw [hp.factorization]
  rw [Finsupp.sum_single_index (by simp)]
  simp

/-- **Independence of the axes.** Two log-characters that agree on all naturals
agree on every prime weight. The prime weights are genuine independent
coordinates of the character. -/
theorem faithful {a b : ℕ → ℝ} (h : ∀ n, logChar a n = logChar b n)
    {p : ℕ} (hp : p.Prime) : a p = b p := by
  have := h p
  rwa [logChar_prime a hp, logChar_prime b hp] at this

/-- A character is a power law against the reference scale `w` if there is a
single exponent `c` with `logChar a n = c · logChar w n` for every nonzero `n`. -/
def IsPowerLaw (a w : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ n : ℕ, n ≠ 0 → logChar a n = c * logChar w n

/-- The prime weights of `a` are aligned to the reference `w` if a single
exponent `c` has `a p = c · w p` on every prime. -/
def WeightsAligned (a w : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ p : ℕ, p.Prime → a p = c * w p

/-- **Prime-Axis Coherence Theorem.** A character obeys a single global power law
against the reference scale `w` if and only if its prime weights are all aligned
to `w`. The continuum/order condition that forces a global power law is exactly
the condition that synchronizes the independent prime axes into one common scale. -/
theorem powerLaw_iff_aligned (a w : ℕ → ℝ) : IsPowerLaw a w ↔ WeightsAligned a w := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro p hp
    have h := hc p hp.ne_zero
    rwa [logChar_prime a hp, logChar_prime w hp] at h
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro n hn
    unfold logChar
    rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := by
      rw [Nat.support_factorization] at hp
      exact Nat.prime_of_mem_primeFactors hp
    rw [hc p hpp]
    ring

/-! ### The canonical reference scale `w(p) = log p` -/

/-- With the reference weights `w(p) = log p`, the log-character is exactly the
real logarithm. This is the scale that the order/continuum condition selects. -/
theorem logChar_log (n : ℕ) (hn : n ≠ 0) :
    logChar (fun p => Real.log p) n = Real.log n := by
  unfold logChar
  rw [Finsupp.sum]
  have hself : n.factorization.prod (fun p k => p ^ k) = n :=
    Nat.factorization_prod_pow_eq_self hn
  have hcast : (n : ℝ) = ∏ p ∈ n.factorization.support, ((p : ℝ) ^ (n.factorization p)) := by
    conv_lhs => rw [← hself, Finsupp.prod]
    push_cast
    rfl
  rw [hcast, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_pow]
  · intro p hp
    have hpp : p.Prime := by
      rw [Nat.support_factorization] at hp
      exact Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) < (p : ℝ) ^ (n.factorization p) := by
      apply pow_pos
      exact_mod_cast hpp.pos
    exact ne_of_gt this

/-- **The synchronized character is a power map.** Under the log reference scale,
an aligned character with exponent `c` is exactly `n ↦ n^c`. The independent
prime axes, once locked to one scale, produce a single global power law on the
positive rationals. -/
theorem character_is_rpow {a : ℕ → ℝ} {c : ℝ}
    (haligned : ∀ p : ℕ, p.Prime → a p = c * Real.log p)
    (n : ℕ) (hn : n ≠ 0) :
    Real.exp (logChar a n) = (n : ℝ) ^ c := by
  have hpl : logChar a n = c * Real.log n := by
    have hdirect : logChar a n = c * logChar (fun p => Real.log p) n := by
      unfold logChar
      rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpp : p.Prime := by
        rw [Nat.support_factorization] at hp
        exact Nat.prime_of_mem_primeFactors hp
      rw [haligned p hpp]; ring
    rw [hdirect, logChar_log n hn]
  rw [hpl]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.rpow_def_of_pos hnpos]
  congr 1
  ring

/-- **Phase 5 headline.** Freedom then collapse, in one statement. Independent
prime weights always define a multiplicative character (`logChar_mul`), distinct
weights give distinct characters (`faithful`), and a global power law against any
fixed reference scale holds iff the prime weights are aligned to it
(`powerLaw_iff_aligned`). Coherence is the synchronization of independent prime
axes into one scale. -/
theorem prime_axis_coherence :
    (∀ (a : ℕ → ℝ) (m n : ℕ), m ≠ 0 → n ≠ 0 →
        logChar a (m * n) = logChar a m + logChar a n)
      ∧ (∀ (a b : ℕ → ℝ), (∀ n, logChar a n = logChar b n) →
          ∀ (p : ℕ), p.Prime → a p = b p)
      ∧ (∀ a w : ℕ → ℝ, IsPowerLaw a w ↔ WeightsAligned a w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a m n hm hn; exact logChar_mul a hm hn
  · intro a b h p hp; exact faithful h hp
  · exact powerLaw_iff_aligned

end PrimeAxisCoherence
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
