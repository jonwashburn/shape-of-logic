import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# St Petersburg Paradox: Linear Utility Diverges, Log Utility Converges (Track E6)

Replaces the earlier placeholder version of this module. The earlier
file defined `marginal_utility := 1/(1+x)` and proved it was positive
and decreasing. That had nothing to do with St Petersburg.

This file builds the actual St Petersburg ensemble and proves the
divergence/convergence dichotomy directly from the partial sums.

## The St Petersburg ensemble

A fair coin is flipped until it lands heads.  If heads first appears
on flip `n ≥ 1`, the player wins `2^n`.  The probability that the
first head occurs on flip `n` is `(1/2)^n` (geometric distribution).

Equivalently: there is a sample space indexed by `n : ℕ` (the flip
on which the first head occurs), with `P(n) = (1/2)^(n+1)` for
`n = 0, 1, 2, ...` (so payout on outcome `n` is `2^(n+1)`).  We use
the 1-indexed convention here: outcomes are `n = 1, 2, ...`,
probability `(1/2)^n`, payout `2^n`.

## What we prove

**Linear utility (the classical paradox).** The expected payout
under linear utility is

\[
  E[X] = \sum_{n = 1}^{\infty} \tfrac{1}{2^n} \cdot 2^n
       = \sum_{n = 1}^{\infty} 1
       = +\infty.
\]

We prove this by showing the partial sum `∑_{n=1}^{N} (1/2)^n · 2^n
= N`, which is unbounded.

**Log utility (the J-cost-shaped resolution).** The expected utility
under log payout is

\[
  E[\log X]
  = \sum_{n = 1}^{\infty} \tfrac{1}{2^n} \cdot \log(2^n)
  = (\log 2) \sum_{n = 1}^{\infty} \tfrac{n}{2^n}
  = (\log 2) \cdot 2
  = 2 \log 2 \approx 1.386.
\]

We work directly with the unitless sum `∑ n / 2^n`; the `log 2` factor
is constant and does not affect the convergence/divergence dichotomy.
We prove the **closed-form identity**

\[
  \sum_{n = 1}^{N} \tfrac{n}{2^n}
  = 2 - \tfrac{N + 2}{2^N},
\]

from which `S_N < 2` for every `N`, so the partial sums form a
bounded monotone sequence and therefore converge.

This is the J-cost-shaped resolution because `J(x) = (x + x⁻¹)/2 - 1`
expanded near `x = 1` agrees to second order with `½(log x)²`, so
log-utility is the local J-cost penalty around the natural reference
point.

## Connection to RS

The St Petersburg paradox is not about probability theory; it is
about which utility function the player applies. RS makes a definite
prediction: utility scales as `J(x)`, the unique reciprocal-symmetric
cost. Locally that behaves like `log` (and `(log x)²`), giving a
finite expected utility on heavy-tailed payouts.

The classical "paradox" is the observation that linear utility (which
has no σ-conservation structure) gives a divergent expected value.
J-cost utility (which has σ-conservation built in) does not.

## Status

THEOREM: divergence of the linear partial sum (unbounded), convergence
of the log partial sum (bounded above by `2`), and the closed-form
identity `∑_{n=1}^{N} n/2^n = 2 - (N+2)/2^N`.

No HYPOTHESIS, no axiom, no `sorry`.

The fact that `J(x)` agrees to leading order with `½(log x)²` near
`x = 1` is recorded in a separate module (`Cost.JcostExpansion`) and
not repeated here.
-/

namespace IndisputableMonolith
namespace Decision
namespace StPetersburg

open Constants Cost
open scoped BigOperators

noncomputable section

/-! ## §1. Payout, probability, and the two utility functionals -/

/-- The payout on outcome `n` (heads first on flip `n`): `2^n`.
We work with `n ≥ 1`, but allow `n = 0` for sum-indexing convenience
(the `n = 0` term contributes nothing to either partial sum). -/
def payout (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- The probability of outcome `n`: `(1/2)^n`.  -/
def prob (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- The probability of outcome 0 in our 1-indexed convention is
just `1`, the empty product; we use the partial-sum range
`Finset.Ico 1 (N+1)` to sum over `n = 1, ..., N`. -/
theorem prob_zero : prob 0 = 1 := by
  unfold prob; simp

/-- Probability is positive. -/
theorem prob_pos (n : ℕ) : 0 < prob n := by
  unfold prob; positivity

/-! ## §2. Linear utility: the partial sum equals `N` -/

/-- The per-outcome contribution to the linear-utility expected
payout: `prob n · payout n = (1/2)^n · 2^n = 1`. -/
theorem linear_term (n : ℕ) : prob n * payout n = 1 := by
  unfold prob payout
  rw [← mul_pow]
  norm_num

/-- The partial sum of the linear-utility expected payout from
`n = 1` to `n = N` (inclusive). -/
def linearUtilityPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (N + 1), prob n * payout n

/-- **CLOSED FORM (linear utility).** The partial sum is exactly `N`. -/
theorem linearUtilityPartial_eq (N : ℕ) :
    linearUtilityPartial N = N := by
  unfold linearUtilityPartial
  -- Each term equals 1, so the sum equals the cardinality of the index set.
  rw [Finset.sum_congr rfl (fun n _ => linear_term n)]
  rw [Finset.sum_const]
  rw [Nat.card_Ico]
  simp

/-- **DIVERGENCE OF LINEAR UTILITY.** The linear expected payout is
unbounded: for every `M`, there is an `N` such that the partial sum
exceeds `M`. -/
theorem linearUtility_diverges :
    ∀ M : ℝ, ∃ N : ℕ, M < linearUtilityPartial N := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  exact ⟨N, by rw [linearUtilityPartial_eq]; exact hN⟩

/-- The linear partial sum is non-decreasing. -/
theorem linearUtilityPartial_mono : Monotone linearUtilityPartial := by
  intro N₁ N₂ h
  rw [linearUtilityPartial_eq, linearUtilityPartial_eq]
  exact_mod_cast h

/-! ## §3. Log utility: the closed-form identity `S_N = 2 - (N+2)/2^N`

The fundamental identity:

  `∑_{n = 1}^{N} n / 2^n = 2 - (N + 2) / 2^N`.

Proof by induction on `N`.

The per-outcome contribution to the log-utility expected payout is
`prob n · n = n / 2^n` (we are working with the unitless sum;
multiply by `log 2` at the end if you want the actual expected log
payout).
-/

/-- The per-outcome contribution to the log-utility expected payout
(unitless: `n / 2^n`). -/
def logTerm (n : ℕ) : ℝ := (n : ℝ) / (2 : ℝ) ^ n

/-- The unitless log-utility partial sum from `n = 1` to `n = N`. -/
def logUtilityPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (N + 1), logTerm n

/-- The empty partial sum is zero. -/
theorem logUtilityPartial_zero : logUtilityPartial 0 = 0 := by
  unfold logUtilityPartial
  simp

/-- The recursion: `logUtilityPartial (N+1) = logUtilityPartial N
  + (N+1) / 2^(N+1)`. -/
theorem logUtilityPartial_succ (N : ℕ) :
    logUtilityPartial (N + 1) =
      logUtilityPartial N + ((N + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (N + 1) := by
  unfold logUtilityPartial logTerm
  -- Finset.Ico 1 (N+2) = Finset.Ico 1 (N+1) ∪ {N+1}.
  rw [show N + 1 + 1 = (N + 1) + 1 from rfl]
  rw [Finset.sum_Ico_succ_top (Nat.succ_le_succ (Nat.zero_le N))]

/-- **CLOSED FORM (log utility).** The unitless partial sum equals
`2 - (N + 2) / 2^N` for every `N : ℕ`. -/
theorem logUtilityPartial_closed_form (N : ℕ) :
    logUtilityPartial N = 2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
  induction N with
  | zero =>
      simp [logUtilityPartial_zero]
  | succ N ih =>
      rw [logUtilityPartial_succ N, ih]
      -- Goal: 2 - (N+2)/2^N + (N+1)/2^(N+1) = 2 - (N+3)/2^(N+1).
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (N + 1) := pow_pos (by norm_num : (0 : ℝ) < 2) _
      have h2pow : (2 : ℝ) ^ (N + 1) = 2 * (2 : ℝ) ^ N := by
        rw [pow_succ]; ring
      push_cast
      field_simp
      ring

/-- **BOUNDEDNESS OF THE LOG PARTIAL SUM.** For every `N`,
`logUtilityPartial N < 2`. -/
theorem logUtilityPartial_lt_two (N : ℕ) :
    logUtilityPartial N < 2 := by
  rw [logUtilityPartial_closed_form]
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos (by norm_num : (0 : ℝ) < 2) _
  have h_num_pos : (0 : ℝ) < (N : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have h_quot_pos : (0 : ℝ) < ((N : ℝ) + 2) / (2 : ℝ) ^ N := div_pos h_num_pos h_pow_pos
  linarith

/-- The log partial sum is non-negative. -/
theorem logUtilityPartial_nonneg (N : ℕ) :
    0 ≤ logUtilityPartial N := by
  unfold logUtilityPartial logTerm
  apply Finset.sum_nonneg
  intro n _
  apply div_nonneg
  · exact Nat.cast_nonneg n
  · exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) _)

/-- The log partial sum is monotone in `N`. -/
theorem logUtilityPartial_mono : Monotone logUtilityPartial := by
  intro N₁ N₂ h
  unfold logUtilityPartial logTerm
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Ico] at hn ⊢
    exact ⟨hn.1, lt_of_lt_of_le hn.2 (Nat.succ_le_succ h)⟩
  · intro n _ _
    apply div_nonneg
    · exact Nat.cast_nonneg n
    · exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) _)

/-! ## §4. Convergence of the log expected utility

A bounded monotone sequence converges. We don't need to compute the
limit (`= 2`); we just need the existence of the limit. -/

/-- The auxiliary limit `(N + 2) / 2^N → 0` as `N → ∞`. -/
private theorem aux_limit_N_plus_two_div_pow :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 2) / (2 : ℝ) ^ N)
      Filter.atTop (nhds 0) := by
  -- Split as N/2^N + 2/2^N; both pieces tend to 0.
  -- Piece 1: N / 2^N from `tendsto_pow_const_div_const_pow_of_one_lt 1`.
  have h_lim_n : Filter.Tendsto (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ N)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 1
      (show (1 : ℝ) < 2 by norm_num)
    simpa [pow_one] using h
  -- Piece 2: 2 / 2^N = 2 · (1/2)^N → 2 · 0 = 0.
  have h_lim_const : Filter.Tendsto (fun N : ℕ => (2 : ℝ) / (2 : ℝ) ^ N)
      Filter.atTop (nhds 0) := by
    have h_half : Filter.Tendsto (fun N : ℕ => ((1 / 2 : ℝ)) ^ N)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h_mul := h_half.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    -- 2 · (1/2)^N = 2 / 2^N, after rewriting (1/2)^N = 1/2^N.
    have h_eq : (fun N : ℕ => (2 : ℝ) * ((1 / 2 : ℝ)) ^ N)
        = (fun N : ℕ => (2 : ℝ) / (2 : ℝ) ^ N) := by
      funext N
      rw [div_pow, one_pow]
      field_simp
    rw [h_eq] at h_mul
    exact h_mul
  -- Combine.
  have h_sum := h_lim_n.add h_lim_const
  simp only [zero_add] at h_sum
  have h_split : (fun N : ℕ => ((N : ℝ) + 2) / (2 : ℝ) ^ N)
      = (fun N : ℕ => (N : ℝ) / (2 : ℝ) ^ N + (2 : ℝ) / (2 : ℝ) ^ N) := by
    funext N
    have : (2 : ℝ) ^ N ≠ 0 := pow_ne_zero N (by norm_num : (2 : ℝ) ≠ 0)
    field_simp
  rw [h_split]
  exact h_sum

/-- **THE LOG EXPECTED UTILITY EQUALS `2`** (in unitless form).
The full expected log payout is `2 · log 2 = log 4`. -/
theorem logUtility_limit_eq_two :
    Filter.Tendsto (fun N => logUtilityPartial N)
      Filter.atTop (nhds (2 : ℝ)) := by
  -- logUtilityPartial N = 2 - (N+2)/2^N, and (N+2)/2^N → 0.
  have h_diff : (fun N : ℕ => logUtilityPartial N)
      = (fun N : ℕ => (2 : ℝ) - ((N : ℝ) + 2) / (2 : ℝ) ^ N) := by
    funext N
    exact logUtilityPartial_closed_form N
  rw [h_diff]
  -- 2 - f(N) → 2 - 0 = 2.
  have h_const : Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop (nhds 2) :=
    tendsto_const_nhds
  have h_sub := h_const.sub aux_limit_N_plus_two_div_pow
  simp only [sub_zero] at h_sub
  exact h_sub

/-- **CONVERGENCE OF LOG UTILITY.** The log partial sums converge. -/
theorem logUtility_converges :
    ∃ L : ℝ, Filter.Tendsto (fun N => logUtilityPartial N)
      Filter.atTop (nhds L) :=
  ⟨2, logUtility_limit_eq_two⟩

/-! ## §5. The dichotomy: linear diverges, log converges -/

/-- **DICHOTOMY.** Under the St Petersburg ensemble, linear utility
gives a divergent expected payout while the log-shaped (J-cost-shaped)
utility gives a finite expected payout. -/
theorem stPetersburg_dichotomy :
    -- (1) Linear utility: unbounded.
    (∀ M : ℝ, ∃ N : ℕ, M < linearUtilityPartial N) ∧
    -- (2) Log utility: bounded above by 2.
    (∀ N : ℕ, logUtilityPartial N < 2) ∧
    -- (3) Log utility: converges to 2.
    Filter.Tendsto (fun N => logUtilityPartial N)
      Filter.atTop (nhds (2 : ℝ)) := by
  exact ⟨linearUtility_diverges, logUtilityPartial_lt_two, logUtility_limit_eq_two⟩

/-! ## §6. Master certificate -/

/-- **ST PETERSBURG MASTER CERTIFICATE.**

Eight clauses, all derived from explicit summation on `Finset.Ico`:

1. The per-outcome term `prob n · payout n` equals `1`.
2. The linear-utility partial sum equals `N` (closed form).
3. The linear-utility partial sums are unbounded.
4. The log-utility partial sum has closed form `2 - (N+2)/2^N`.
5. The log-utility partial sums are bounded above by `2`.
6. The log-utility partial sums are non-negative and monotone.
7. The log-utility partial sums converge to `2`.
8. The dichotomy holds: linear diverges, log converges.

This is not a label-and-arithmetic statement; the closed-form
identities and the convergence statement are derived from
Mathlib's `Filter.Tendsto` and `Finset.sum`. -/
structure StPetersburgCert where
  linear_term_eq_one : ∀ n, prob n * payout n = 1
  linear_partial_eq_N : ∀ N, linearUtilityPartial N = N
  linear_unbounded : ∀ M : ℝ, ∃ N, M < linearUtilityPartial N
  log_partial_closed : ∀ N, logUtilityPartial N = 2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N
  log_partial_lt_two : ∀ N, logUtilityPartial N < 2
  log_partial_nonneg : ∀ N, 0 ≤ logUtilityPartial N
  log_partial_mono : Monotone logUtilityPartial
  log_converges_to_two :
    Filter.Tendsto (fun N => logUtilityPartial N) Filter.atTop (nhds (2 : ℝ))

/-- The master certificate is inhabited. -/
def stPetersburgCert : StPetersburgCert where
  linear_term_eq_one := linear_term
  linear_partial_eq_N := linearUtilityPartial_eq
  linear_unbounded := linearUtility_diverges
  log_partial_closed := logUtilityPartial_closed_form
  log_partial_lt_two := logUtilityPartial_lt_two
  log_partial_nonneg := logUtilityPartial_nonneg
  log_partial_mono := logUtilityPartial_mono
  log_converges_to_two := logUtility_limit_eq_two

/-! ## §7. One-statement summary -/

/-- **ST PETERSBURG ONE-STATEMENT THEOREM.**

For the St Petersburg ensemble (heads first on flip `n` with
probability `(1/2)^n`, payout `2^n`):

(1) Linear utility: `∑_{n=1}^{N} (1/2)^n · 2^n = N`, unbounded.
(2) Log utility (unitless): `∑_{n=1}^{N} n / 2^n = 2 - (N+2)/2^N`,
    bounded above by `2`, converging to `2`.
(3) Therefore linear utility predicts an infinite price for the
    game, while log-utility (the J-cost-shaped resolution) predicts
    a finite price `≈ 2 log 2 ≈ 1.386` (in log units of payout). -/
theorem st_petersburg_one_statement :
    -- (1) Linear partial sum = N.
    (∀ N, linearUtilityPartial N = N) ∧
    -- (2) Log partial sum has the closed form.
    (∀ N, logUtilityPartial N = 2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N) ∧
    -- (3) Log partial sum is strictly less than 2.
    (∀ N, logUtilityPartial N < 2) ∧
    -- (4) Log partial sum converges to 2.
    Filter.Tendsto (fun N => logUtilityPartial N) Filter.atTop (nhds (2 : ℝ)) :=
  ⟨linearUtilityPartial_eq, logUtilityPartial_closed_form,
   logUtilityPartial_lt_two, logUtility_limit_eq_two⟩

end

end StPetersburg
end Decision
end IndisputableMonolith
