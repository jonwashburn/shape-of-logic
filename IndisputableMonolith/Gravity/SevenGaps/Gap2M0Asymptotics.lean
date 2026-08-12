import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusProductForm
import IndisputableMonolith.Gravity.SevenGaps.Gap2AnomalyAsymptotics

/-!
# Gap 2 / C11 / A45: saddle asymptotics of M0 and the anomaly rate

The A36 campaign closed the C11 fork on paper: the anomaly fraction
`q(c) = ‖r(h)‖²/‖h‖²` of the incidence history against the count span is
bounded by the mechanism bound `B(c) = E_μ[n_loop²] / E_μ[n_proper²]`, and the
product-form census law makes both moments explicit finite sums.  The
kernel-checked content before this module: the mechanism identity and the
inequality `q ≤ ‖n_loop‖²/‖n_proper‖²` (`Gap2AnomalyAsymptotics.lean`), and the
census product form itself (`Gap2CensusProductForm.lean`).  What remained
DERIVED-UNFORMALIZED was the asymptotic evaluation of the two moments: the
saddle computation of A36 section 4.  This module formalizes that saddle
computation at kernel strength, as far as the library allows.

## What is proved here (kernel strength, no new axioms, no sorry)

Combinatorial layer (exact identities, no asymptotics):

* `sum_choose_sq_weighted`: the second factorial moment of the binomial,
  `Σ_j j²·C(k,j)·a^j·b^(k−j) = k(k−1)a²(a+b)^(k−2) + ka(a+b)^(k−1)`.
* `loopSqSum_eq`, `properSqSum_eq`: the exact cell second moments.
* `conditional_loop_sq_mean`: `E[n_loop² | n,k] = (k/n)² + (k/n)(1 − 1/n)`.
* `conditional_proper_sq_mean`:
  `E[n_proper² | n,k] = k²(1 − 1/n)² + (k/n)(1 − 1/n)`.
* `loopSqSum_le_properSqSum`: the per-cell mechanism comparison,
  `loopSqSum·(n−1) ≤ properSqSum` for `n ≥ 2`.  This is the microscopic
  content of the rate: a cell at `(n, k)` suppresses the loop anomaly by a
  factor `1/(n−1)`, so the ensemble rate is governed by where the census mass
  sits in `n`.

Analytic layer (elementary saddle bounds):

* `wrow_le_exp`, `wrow_le_two_wterm`: the truncated exponential row bounds
  (`wrow c n ≤ exp(n²)`, and `wrow c n ≤ 2·n^(2c)/(n!·c!)` for `2c ≤ n²`).
* `factorial_upper`, from Mathlib's Stirling sequence: `n! ≤ e·√n·(n/e)^n`;
  `factorial_lower`: `√(2πn)·(n/e)^n ≤ n!`.
* `m0_lower`: the saddle-row lower bound on the census mass at the split
  scale `saddleN c = ⌈2√(c·log c)⌉`.
* `smallMass_le`: the small-region mass bound, `smallMass c ≤
  (c+1)·(exp(2c) + 2·(c·log c)^c/c!)`.

## A47: reduction lemmas and the concentration envelope

Banked here (kernel strength):

* Cell bounds `properSqSum_le_sq_pow`, `loopSqSum_le_sq_pow`, and the
  `n = 1` identities `loopSqSum_one` / `properSqSum_one` (pure-numerator
  cells; the mechanism comparison needs `n ≥ 2`).
* Moment-to-mass reductions `dsumSmall_le_c_sq_smallMass` and
  `nsumSmall_le_c_sq_smallMass`.
* The `c ≥ 9` regime for the joint `m0_lower` hypotheses
  (`saddleN_hypotheses_of_nine`), and the finite-`c` envelope
  `smallMass_div_m0sum_le_envelope` composing `smallMass_le` with
  `m0_lower`.  The split scale `saddleN` is a concentration cutoff, not
  the true Laplace saddle `n*` with `n* log n* = 2c`.

## What remains open (updated 2026-08-01, A48)

Both steps formerly listed here are CLOSED at kernel strength by the A48
arc (this module): `tendsto_smallMass_div_m0sum_zero` (the concentration
limit, via the explicit envelope `smallMass_div_m0sum_le_half_pow`) and
`tendsto_mechanismBound_zero` (the fork closure for the mechanism bound,
through `mechanismBound_le` with the bulk lower bound `bulk_dsum_lower`
discharging `MechanismBoundClosureGap`). What remains open:

* The ensemble reading `q(c) → 0`: the banked Pythagoras algebra gives
  `q ≤ B`, and `B → 0` is now THEOREM, but instantiating that algebra at
  the census measure needs the product-form census law (A36 check A5, the
  orbit-stabilizer identity). DERIVED-UNFORMALIZED; the A49 arc owns it.
* The sharp rate `q ∼ (log c)/(2c²)`: a further residual-variance step on
  top of the census law, plus two-sided saddle concentration at the true
  saddle `n*`. DERIVED-UNFORMALIZED. The proved envelope is
  `O(1/√(c·log c))`; no theorem here claims the sharp rate.
-/

namespace Gap2M0Asymptotics

open Gap2CensusProductForm Finset
open scoped Topology Nat

/-- Factorial positivity at `ℝ`, for the denominators below. -/
theorem ffact_pos (n : ℕ) : (0 : ℝ) < (n ! : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos n)

/-- Factorial nonnegativity at `ℝ`. -/
theorem ffact_nonneg (n : ℕ) : (0 : ℝ) ≤ (n ! : ℝ) := (ffact_pos n).le

/-!
## Section 1: second-moment combinatorial identities
-/

/-- Second weighted binomial sum: `Σ_j j²·C(k,j)·a^j·b^(k−j)` equals
`k(k−1)a²(a+b)^(k−2) + ka(a+b)^(k−1)`.  The second factorial moment of the
binomial; the absorption identity `(j+1)·C(m+1,j+1) = (m+1)·C(m,j)` applied
once reduces it to the first moment `sum_choose_weighted`. -/
theorem sum_choose_sq_weighted (a b k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), j ^ 2 * Nat.choose k j * a ^ j * b ^ (k - j))
      = k * (k - 1) * a ^ 2 * (a + b) ^ (k - 2) + k * a * (a + b) ^ (k - 1) := by
  cases k with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    have hz : (0 : ℕ) ^ 2 * Nat.choose (m + 1) 0 * a ^ 0 * b ^ (m + 1 - 0) = 0 := by simp
    rw [hz, add_zero]
    have hterm : ∀ j ∈ Finset.range (m + 1),
        (j + 1) ^ 2 * Nat.choose (m + 1) (j + 1) * a ^ (j + 1) * b ^ (m + 1 - (j + 1))
          = (m + 1) * a * ((j + 1) * Nat.choose m j * a ^ j * b ^ (m - j)) := by
      intro j _
      have hch : (j + 1) * Nat.choose (m + 1) (j + 1) = (m + 1) * Nat.choose m j := by
        have h := Nat.add_one_mul_choose_eq m j
        exact (mul_comm _ _).trans h.symm
      rw [Nat.add_sub_add_right, pow_succ a j]
      have hsq : (j + 1) ^ 2 * Nat.choose (m + 1) (j + 1)
          = (j + 1) * ((m + 1) * Nat.choose m j) := by
        rw [pow_two, mul_assoc, hch]
      rw [hsq]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsplit : ∀ j ∈ Finset.range (m + 1),
        (j + 1) * Nat.choose m j * a ^ j * b ^ (m - j)
          = j * Nat.choose m j * a ^ j * b ^ (m - j)
            + Nat.choose m j * a ^ j * b ^ (m - j) := fun j _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      Gap2CensusProductForm.sum_choose_weighted a b m]
    have hpow : (∑ j ∈ Finset.range (m + 1), Nat.choose m j * a ^ j * b ^ (m - j))
        = (a + b) ^ m := by
      rw [(Commute.all a b).add_pow m]
      exact Finset.sum_congr rfl fun j _ => by rw [Nat.cast_id]; ring
    rw [hpow, Nat.add_sub_cancel, show m + 1 - 2 = m - 1 from by omega]
    ring

/-- The loop second moment of the `(n, k)` cell, summed over the loop count. -/
def loopSqSum (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), j ^ 2 * cellCount n k j

/-- The proper-edge second moment of the `(n, k)` cell, summed over the loop
count (the proper-edge count of a word with `j` loops is `k − j`). -/
def properSqSum (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k - j) ^ 2 * cellCount n k j

/-- The cell count vanishes at `n = 0` for `k ≥ 1`: a word of positive length
needs at least one generator. -/
theorem cellCount_zero_left {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : cellCount 0 k j = 0 := by
  rw [cellCount]
  rcases le_or_gt j k with hjk | hjk
  · have e : (0 : ℕ) ^ 2 - 0 = 0 := by norm_num
    rw [e, ← pow_add, Nat.add_sub_cancel' hjk, zero_pow (by omega : k ≠ 0), mul_zero]
  · rw [Nat.choose_eq_zero_of_lt hjk, zero_mul]

theorem loopSqSum_zero_left (k : ℕ) : loopSqSum 0 k = 0 := by
  rcases k with _ | m
  · simp [loopSqSum]
  · exact Finset.sum_eq_zero fun j _ => by
      rw [cellCount_zero_left (by omega : 1 ≤ m + 1) j]; simp

/-- Exact closed form of the loop second moment: the binomial second factorial
moment at `p = 1/n`, multiplied through by the cell mass `n^(2k)`. -/
theorem loopSqSum_eq (n k : ℕ) :
    loopSqSum n k = k * (k - 1) * n ^ 2 * (n ^ 2) ^ (k - 2) + k * n * (n ^ 2) ^ (k - 1) := by
  rw [loopSqSum]
  have hcell : ∀ j ∈ Finset.range (k + 1),
      j ^ 2 * cellCount n k j = j ^ 2 * Nat.choose k j * n ^ j * (n ^ 2 - n) ^ (k - j) :=
    fun j _ => by rw [cellCount]; ring
  rw [Finset.sum_congr rfl hcell, sum_choose_sq_weighted n (n ^ 2 - n) k, add_sq_sub n]

/-- Reversal of the proper-edge sum: substituting `j ↦ k − j` turns the
proper-edge count `k − j` into the loop count `j`. -/
theorem properSqSum_rev (n k : ℕ) :
    properSqSum n k = ∑ j ∈ Finset.range (k + 1), j ^ 2 * cellCount n k (k - j) := by
  rw [properSqSum,
    ← Finset.sum_range_reflect (fun j => (k - j) ^ 2 * cellCount n k j) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
  have e : k + 1 - 1 - j = k - j := by omega
  show (k - (k + 1 - 1 - j)) ^ 2 * cellCount n k (k + 1 - 1 - j) = _
  rw [e, Nat.sub_sub_self hjk]

/-- Exact closed form of the proper-edge second moment: reverse the sum
(`j ↦ k − j`) to turn proper counts into loop counts, then apply the loop
identity with the roles of `n` and `n² − n` exchanged. -/
theorem properSqSum_eq (n k : ℕ) :
    properSqSum n k
      = k * (k - 1) * (n ^ 2 - n) ^ 2 * (n ^ 2) ^ (k - 2)
        + k * (n ^ 2 - n) * (n ^ 2) ^ (k - 1) := by
  rw [properSqSum_rev]
  have h : ∀ j ∈ Finset.range (k + 1),
      j ^ 2 * cellCount n k (k - j)
        = j ^ 2 * Nat.choose k j * (n ^ 2 - n) ^ j * n ^ (k - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    rw [cellCount, Nat.choose_symm hjk, Nat.sub_sub_self hjk]
    ring
  rw [Finset.sum_congr rfl h, sum_choose_sq_weighted (n ^ 2 - n) n k,
    show n ^ 2 - n + n = n ^ 2 from Nat.sub_add_cancel (by
      rcases n with _ | m
      · simp
      · exact le_self_pow (by omega : (1 : ℕ) ≤ m + 1) (by decide : (2 : ℕ) ≠ 0))]

/-- `loopSqSum_eq` at `k = m + 1`, with the truncated subtractions resolved. -/
theorem loopSqSum_eq_one_add (n m : ℕ) :
    loopSqSum n (m + 1)
      = (m + 1) * m * n ^ 2 * (n ^ 2) ^ (m - 1) + (m + 1) * n * (n ^ 2) ^ m := by
  rw [loopSqSum_eq, Nat.add_sub_cancel, show m + 1 - 2 = m - 1 from by omega]

/-- `loopSqSum_eq` at `k = m + 2`, with the truncated subtractions resolved. -/
theorem loopSqSum_eq_two_add (n m : ℕ) :
    loopSqSum n (m + 2)
      = (m + 2) * (m + 1) * n ^ 2 * (n ^ 2) ^ m + (m + 2) * n * (n ^ 2) ^ (m + 1) := by
  rw [loopSqSum_eq, show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]

/-- `properSqSum_eq` at `k = m + 2`, with the truncated subtractions resolved. -/
theorem properSqSum_eq_two_add (n m : ℕ) :
    properSqSum n (m + 2)
      = (m + 2) * (m + 1) * (n ^ 2 - n) ^ 2 * (n ^ 2) ^ m
        + (m + 2) * (n ^ 2 - n) * (n ^ 2) ^ (m + 1) := by
  rw [properSqSum_eq, show m + 2 - 2 = m from by omega, show m + 2 - 1 = m + 1 from by omega]

/-- Real-valued form of `loopSqSum_eq` with no truncated subtraction:
`loopSqSum·n² = k(k−1)·n^(2k) + k·n^(2k+1)`. -/
theorem loopSqSum_mul_sq (n k : ℕ) :
    (loopSqSum n k : ℝ) * (n : ℝ) ^ 2
      = (k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1) := by
  rcases k with _ | m
  · simp [loopSqSum]
  · rcases m with _ | m'
    · have h1 : loopSqSum n 1 = n := by rw [loopSqSum_eq]; simp
      rw [h1]
      push_cast
      ring
    · have h2 := loopSqSum_eq_two_add n m'
      rw [show m' + 1 + 1 = m' + 2 from rfl]
      rw [h2]
      push_cast
      ring_nf

/-- Real-valued form of `properSqSum_eq` with no truncated subtraction:
`properSqSum·n⁴ = k(k−1)(n−1)²·n^(2k+2) + k(n−1)·n^(2k+3)`. -/
theorem properSqSum_mul_pow4 (n k : ℕ) :
    (properSqSum n k : ℝ) * (n : ℝ) ^ 4
      = (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
        + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3) := by
  rcases k with _ | m
  · simp [properSqSum]
  · rcases m with _ | m'
    · have h1 : properSqSum n 1 = n ^ 2 - n := by rw [properSqSum_eq]; simp
      rw [h1]
      have hn2 : n ≤ n ^ 2 := by
        rcases n with _ | m''
        · simp
        · exact le_self_pow (by omega : (1 : ℕ) ≤ m'' + 1) (by decide : (2 : ℕ) ≠ 0)
      push_cast [Nat.cast_sub hn2]
      ring
    · have h2 := properSqSum_eq_two_add n m'
      rw [show m' + 1 + 1 = m' + 2 from rfl]
      rw [h2]
      have hn2 : n ≤ n ^ 2 := by
        rcases n with _ | m''
        · simp
        · exact le_self_pow (by omega : (1 : ℕ) ≤ m'' + 1) (by decide : (2 : ℕ) ≠ 0)
      push_cast [Nat.cast_sub hn2]
      have hsub : (n : ℝ) ^ 2 - n = (n : ℝ) * ((n : ℝ) - 1) := by ring
      rw [hsub]
      ring_nf

/-- Conditional second moment of the loop count: under the uniform law on the
`(n, k)` cell, `n_loop ~ Binomial(k, 1/n)`, so
`E[n_loop²] = (k/n)² + (k/n)(1 − 1/n)`. -/
theorem conditional_loop_sq_mean (n k : ℕ) (hn : n ≠ 0) :
    (loopSqSum n k : ℝ) / (n : ℝ) ^ (2 * k)
      = (k / (n : ℝ)) ^ 2 + (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := loopSqSum_mul_sq n k
  have h2 : (loopSqSum n k : ℝ)
      = ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
        / (n : ℝ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hn')]
    exact h
  rw [div_eq_iff (pow_ne_zero _ hn'), h2]
  field_simp
  ring

/-- Conditional second moment of the proper-edge count:
`E[n_proper²] = k²(1 − 1/n)² + (k/n)(1 − 1/n)`. -/
theorem conditional_proper_sq_mean (n k : ℕ) (hn : n ≠ 0) :
    (properSqSum n k : ℝ) / (n : ℝ) ^ (2 * k)
      = ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 + (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := properSqSum_mul_pow4 n k
  have h2 : (properSqSum n k : ℝ)
      = ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
          + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3)) / (n : ℝ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hn')]
    exact h
  rw [div_eq_iff (pow_ne_zero _ hn'), h2]
  field_simp
  ring

/-- The microscopic mechanism bound: in any cell with `n ≥ 2`, the loop second
moment is at most `1/(n−1)` times the proper-edge second moment,
`loopSqSum·(n−1) ≤ properSqSum`.  This is the per-cell content behind the rate
`B(c) ≈ 1/n*²`: cells at large `n` suppress the loop anomaly, and the saddle
`n* → ∞` is what drives `B(c) → 0`. -/
theorem loopSqSum_le_properSqSum (n k : ℕ) (hn : 2 ≤ n) :
    (loopSqSum n k : ℝ) * ((n : ℝ) - 1) ≤ (properSqSum n k : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hL := loopSqSum_mul_sq n k
  have hP := properSqSum_mul_pow4 n k
  have hL' : (loopSqSum n k : ℝ)
      = ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
        / (n : ℝ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hn0)]
    exact hL
  have hP' : (properSqSum n k : ℝ)
      = ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
          + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3)) / (n : ℝ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero 4 hn0)]
    exact hP
  rw [hL', hP', div_mul_eq_mul_div,
    div_le_div_iff₀ (pow_pos (by linarith) 2) (pow_pos (by linarith) 4)]
  have hk2 : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    rcases k with _ | k'
    · simp
    · have e : ((k' : ℝ) + 1) - 1 = k' := by ring
      push_cast
      rw [e]
      positivity
  have hdiff : (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
        + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3)
      - ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
        * ((n : ℝ) - 1) * (n : ℝ) ^ 2
      = (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) * ((n : ℝ) - 2) * (n : ℝ) ^ (2 * k + 2) := by
    ring
  have hpos : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) * ((n : ℝ) - 2)
      * (n : ℝ) ^ (2 * k + 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hk2 (by linarith)) (by linarith))
      (pow_nonneg (Nat.cast_nonneg _) _)
  have hscale : ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
        * ((n : ℝ) - 1) * (n : ℝ) ^ 4
      ≤ ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
          + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3)) * (n : ℝ) ^ 2 := by
    have h1 : ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
          * ((n : ℝ) - 1) * (n : ℝ) ^ 2
        ≤ (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
          + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3) := by
      have h2 := hdiff
      linarith [hpos]
    have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by linarith) 2
    calc ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
          * ((n : ℝ) - 1) * (n : ℝ) ^ 4
        = (((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
            * ((n : ℝ) - 1) * (n : ℝ) ^ 2) * (n : ℝ) ^ 2 := by ring
      _ ≤ ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
            + (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hn2pos.le
  exact hscale

/-!
## Section 2: the ensemble sums and the mechanism bound
-/

/-- One row of the census mass: `Σ_k n^(2k)/(n!·k!)`, the truncated exponential
`e_{c}(n²)/n!`. -/
noncomputable def wrow (c n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (c + 1), (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The census mass without the `(c+1)` prefactor: `M0 = (c+1)·m0sum c`. -/
noncomputable def m0sum (c : ℕ) : ℝ := ∑ n ∈ Finset.range (c + 1), wrow c n

/-- The loop second-moment sum `N(c) = Σ_{n,k} loopSqSum(n,k)/(n!·k!)`. -/
noncomputable def nsum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

/-- The proper second-moment sum `D(c) = Σ_{n,k} properSqSum(n,k)/(n!·k!)`. -/
noncomputable def dsum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

/-- The mechanism bound `B(c) = N(c)/D(c)`: the loop-to-proper second-moment
ratio, the quantity the A36 mechanism inequality bounds `q(c)` by. -/
noncomputable def mechanismBound (c : ℕ) : ℝ := nsum c / dsum c

theorem wrow_nonneg (c n : ℕ) : 0 ≤ wrow c n :=
  Finset.sum_nonneg fun _k _ =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

theorem wrow_pos (c n : ℕ) : 0 < wrow c n := by
  apply Finset.sum_pos' (fun k _ =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _)))
  refine ⟨0, Finset.mem_range.2 (Nat.succ_pos c), ?_⟩
  have h0 : (0 : ℝ) < (n : ℝ) ^ (2 * 0) / ((n ! : ℝ) * (0 ! : ℝ)) := by
    rw [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    exact div_pos one_pos (ffact_pos n)
  exact h0

theorem m0sum_pos (c : ℕ) : 0 < m0sum c :=
  Finset.sum_pos' (fun n _ => wrow_nonneg c n)
    ⟨0, Finset.mem_range.2 (Nat.succ_pos c), wrow_pos c 0⟩

theorem dsum_pos (c : ℕ) (hc : 2 ≤ c) : 0 < dsum c := by
  apply Finset.sum_pos' (fun n _ => Finset.sum_nonneg fun k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _)))
  refine ⟨2, Finset.mem_range.2 (by omega), ?_⟩
  apply Finset.sum_pos' (fun k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _)))
  refine ⟨1, Finset.mem_range.2 (by omega), ?_⟩
  have h : properSqSum 2 1 = 2 := by decide
  rw [h]
  exact div_pos (by norm_num) (mul_pos (ffact_pos 2) (ffact_pos 1))

/-!
## Section 3a: elementary row bounds
-/

/-- The row sum is bounded by the full exponential: `wrow c n ≤ exp(n²)`. -/
theorem wrow_le_exp (c n : ℕ) : wrow c n ≤ Real.exp ((n : ℝ) ^ 2) := by
  have h1 : wrow c n
      = (1 / (n ! : ℝ)) * ∑ k ∈ Finset.range (c + 1), ((n : ℝ) ^ 2) ^ k / (k ! : ℝ) := by
    rw [wrow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [pow_mul]
      field_simp [(ffact_pos n).ne', (ffact_pos k).ne']
  rw [h1]
  have h2 : (∑ k ∈ Finset.range (c + 1), ((n : ℝ) ^ 2) ^ k / (k ! : ℝ))
      ≤ Real.exp ((n : ℝ) ^ 2) := by
    have hsum : Summable (fun k : ℕ => ((n : ℝ) ^ 2) ^ k / (k ! : ℝ)) :=
      Real.summable_pow_div_factorial _
    have hexp : Real.exp ((n : ℝ) ^ 2) = ∑' k : ℕ, ((n : ℝ) ^ 2) ^ k / (k ! : ℝ) := by
      simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp]
    exact hsum.sum_le_tsum (Finset.range (c + 1)) (fun k _ =>
      div_nonneg (pow_nonneg (sq_nonneg _) _) (ffact_nonneg _))
  have h3 : (1 / (n ! : ℝ)) ≤ 1 := by
    rw [div_le_one (ffact_pos n)]
    exact Nat.one_le_cast.2 (Nat.factorial_pos n)
  calc (1 / (n ! : ℝ)) * ∑ k ∈ Finset.range (c + 1), ((n : ℝ) ^ 2) ^ k / (k ! : ℝ)
      ≤ 1 * Real.exp ((n : ℝ) ^ 2) :=
        mul_le_mul h3 h2
          (Finset.sum_nonneg fun k _ =>
            div_nonneg (pow_nonneg (sq_nonneg _) _) (ffact_nonneg _))
          zero_le_one
    _ = Real.exp ((n : ℝ) ^ 2) := one_mul _

/-- `c!/k!` as a product over `Ioc k c`, for the geometric term-ratio bound. -/
theorem factorial_div_eq_prod (k c : ℕ) (h : k ≤ c) :
    (c ! : ℝ) / k ! = ∏ j ∈ Finset.Ioc k c, (j : ℝ) := by
  induction c with
  | zero =>
    rw [Nat.eq_zero_of_le_zero h, Finset.Ioc_self, Finset.prod_empty]
    exact div_self (ffact_pos 0).ne'
  | succ c ih =>
    by_cases hkc : k ≤ c
    · rw [Finset.prod_Ioc_succ_top hkc, ← ih hkc, Nat.factorial_succ]
      push_cast
      ring
    · have hk2 : k = c + 1 := by omega
      rw [hk2, Finset.Ioc_self, Finset.prod_empty]
      exact div_self (ffact_pos _).ne'

/-- The factorial ratio bound: `c!/k! ≤ (n²/2)^(c−k)` when `2c ≤ n²`.  Each
factor `j ≤ c` of the product is at most `n²/2`. -/
theorem factorial_div_le (n k c : ℕ) (hkc : k ≤ c) (hn : (2 : ℝ) * c ≤ (n : ℝ) ^ 2) :
    (c ! : ℝ) / k ! ≤ ((n : ℝ) ^ 2 / 2) ^ (c - k) := by
  rw [factorial_div_eq_prod k c hkc]
  have hbound : ∀ j ∈ Finset.Ioc k c, (j : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hjc : (j : ℝ) ≤ c := by exact_mod_cast hj.2
    linarith
  calc ∏ j ∈ Finset.Ioc k c, (j : ℝ)
      ≤ ∏ _j ∈ Finset.Ioc k c, ((n : ℝ) ^ 2 / 2) :=
        Finset.prod_le_prod (fun j _ => Nat.cast_nonneg j) hbound
    _ = ((n : ℝ) ^ 2 / 2) ^ (c - k) := by rw [Finset.prod_const, Nat.card_Ioc]

/-- Termwise geometric decay below the top of the row: for `2c ≤ n²`,
`n^(2k)/(n!·k!) ≤ (1/2)^(c−k) · n^(2c)/(n!·c!)`. -/
theorem wrow_term_le (c n k : ℕ) (hkc : k ≤ c) (hn : (2 : ℝ) * c ≤ (n : ℝ) ^ 2) :
    (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ (1 / 2) ^ (c - k) * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have hc0 : c = 0 := by
      have h2 := hn
      norm_num at h2
      have h3 : (c : ℝ) = 0 := by linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
      exact Nat.cast_eq_zero.1 h3
    subst hc0
    rw [Nat.le_zero.1 hkc]
    have e : ((0 : ℕ) : ℝ) ^ (2 * 0) / (((0 : ℕ) ! : ℝ) * ((0 : ℕ) ! : ℝ)) = 1 := by
      rw [mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    have e2 : (1 / 2 : ℝ) ^ (0 - 0) = 1 := by rw [Nat.sub_zero, pow_zero]
    rw [e, e2, one_mul]
  · have h1 := factorial_div_le n k c hkc hn
    have h2 : ((n : ℝ) ^ 2 / 2) ^ (c - k)
        = (1 / 2) ^ (c - k) * (n : ℝ) ^ (2 * (c - k)) := by
      rw [div_pow, pow_mul, div_pow, one_pow]
      ring
    rw [h2, div_le_iff₀ (ffact_pos k)] at h1
    have hpow : (n : ℝ) ^ (2 * c) = (n : ℝ) ^ (2 * k) * (n : ℝ) ^ (2 * (c - k)) := by
      rw [← pow_add]
      congr 1
      omega
    have hnn1 : (0 : ℝ) ≤ (n : ℝ) ^ (2 * k) * (n ! : ℝ) :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (ffact_nonneg n)
    have h3 := mul_le_mul_of_nonneg_left h1 hnn1
    rw [← mul_div_assoc ((1 / 2 : ℝ) ^ (c - k)) ((n : ℝ) ^ (2 * c)),
      div_le_div_iff₀ (mul_pos (ffact_pos n) (ffact_pos k)) (mul_pos (ffact_pos n) (ffact_pos c)),
      hpow]
    calc (n : ℝ) ^ (2 * k) * ((n ! : ℝ) * (c ! : ℝ))
        = (n : ℝ) ^ (2 * k) * (n ! : ℝ) * (c ! : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (2 * k) * (n ! : ℝ)
            * ((1 / 2) ^ (c - k) * (n : ℝ) ^ (2 * (c - k)) * (k ! : ℝ)) := h3
      _ = (1 / 2) ^ (c - k) * ((n : ℝ) ^ (2 * k) * (n : ℝ) ^ (2 * (c - k)))
            * ((n ! : ℝ) * (k ! : ℝ)) := by ring

/-- The reversed geometric sum: `Σ_{k≤c} (1/2)^(c−k) = 2 − (1/2)^c`. -/
theorem geom_half_sum (c : ℕ) :
    ∑ k ∈ Finset.range (c + 1), (1 / 2 : ℝ) ^ (c - k) = 2 - (1 / 2) ^ c := by
  induction c with
  | zero => rw [Finset.sum_range_one]; norm_num
  | succ c ih =>
    rw [Finset.sum_range_succ', Nat.sub_zero]
    have h1 : ∀ k ∈ Finset.range (c + 1),
        (1 / 2 : ℝ) ^ (c + 1 - (k + 1)) = (1 / 2) ^ (c - k) := fun k _ => by
      rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl h1, ih, pow_succ]
    ring

/-- Above the `n² ≥ 2c` scale the row is dominated by its top term:
`wrow c n ≤ 2 · n^(2c)/(n!·c!)`. -/
theorem wrow_le_two_wterm (c n : ℕ) (hn : (2 : ℝ) * c ≤ (n : ℝ) ^ 2) :
    wrow c n ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
  rw [wrow]
  have hterm : ∀ k ∈ Finset.range (c + 1),
      (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (1 / 2) ^ (c - k) * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
    fun k hk => wrow_term_le c n k (Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)) hn
  calc ∑ k ∈ Finset.range (c + 1), (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ ∑ k ∈ Finset.range (c + 1),
          (1 / 2) ^ (c - k) * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (c + 1), (1 / 2) ^ (c - k))
          * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _
          (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
            (mul_nonneg (ffact_nonneg _) (ffact_nonneg _)))
        rw [geom_half_sum]
        have h3 : (0 : ℝ) ≤ (1 / 2) ^ c := by positivity
        linarith

/-- The Stirling upper bound on the factorial, from Mathlib's Stirling
sequence: `n! ≤ e·√n·(n/e)^n`.  This is the one analytic input to the saddle
argument beyond the exponential series; it is a proved Mathlib theorem, not a
hypothesis. -/
theorem factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
  have h0 : 0 < n := hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 h0
  have h : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
    have hanti := Stirling.stirlingSeq'_antitone (show 0 ≤ n - 1 from by omega)
    simp only [Function.comp_apply] at hanti
    rwa [Nat.sub_one, Nat.succ_pred_eq_of_pos h0] at hanti
  rw [Stirling.stirlingSeq_one] at h
  have hdef : Stirling.stirlingSeq n
      = (n ! : ℝ) / (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    unfold Stirling.stirlingSeq
    ring
  rw [hdef] at h
  have hpos : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n :=
    mul_pos (Real.sqrt_pos.2 (mul_pos two_pos hnR))
      (pow_pos (div_pos hnR (Real.exp_pos 1)) n)
  rw [div_le_iff₀ hpos] at h
  calc (n ! : ℝ)
      ≤ (Real.exp 1 / Real.sqrt 2)
          * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := h
    _ = Real.exp 1 * Real.sqrt n * ((n : ℝ) / Real.exp 1) ^ n := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (n : ℝ)]
        field_simp [Real.sqrt_ne_zero'.2 (two_pos (α := ℝ))]

/-- The Stirling lower bound on the factorial (Mathlib):
`√(2πn)·(n/e)^n ≤ n!`, effective for all `n`. -/
theorem factorial_lower (n : ℕ) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n ! : ℝ) :=
  Stirling.le_factorial_stirling n

/-!
## Section 3b: the saddle split and the mass bounds
-/

/-- The split scale: `n₂(c) = ⌈2√(c·log c)⌉`.  Rows with `n² ≤ c·log c` carry
negligible mass; rows above the `2c` scale are dominated by their top term. -/
noncomputable def saddleN (c : ℕ) : ℕ := ⌈2 * Real.sqrt ((c : ℝ) * Real.log c)⌉₊

/-- The small region: rows whose square is at most `c·log c`. -/
noncomputable def smallSet (c : ℕ) : Finset ℕ :=
  (Finset.range (c + 1)).filter fun n => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c

/-- The mass in the small region. -/
noncomputable def smallMass (c : ℕ) : ℝ := ∑ n ∈ smallSet c, wrow c n

theorem smallMass_nonneg (c : ℕ) : 0 ≤ smallMass c :=
  Finset.sum_nonneg fun n _ => wrow_nonneg c n

/-- The saddle-row lower bound on the census mass: the `n = n₂`, `k = c` term
alone, with both factorials bounded above by the Stirling sequence. -/
theorem m0_lower (c : ℕ) (hc : 1 ≤ c) (h2 : 1 ≤ saddleN c) (h2c : saddleN c ≤ c) :
    (saddleN c : ℝ) ^ (2 * c)
      / (Real.exp 1 * Real.sqrt (saddleN c) * ((saddleN c : ℝ) / Real.exp 1) ^ saddleN c
        * (Real.exp 1 * Real.sqrt c * ((c : ℝ) / Real.exp 1) ^ c))
    ≤ m0sum c := by
  have hn2R : (1 : ℝ) ≤ saddleN c := by exact_mod_cast h2
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hU1 := factorial_upper (saddleN c) h2
  have hU2 := factorial_upper c hc
  have hmem1 : saddleN c ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
  have h1 : wrow c (saddleN c) ≤ m0sum c :=
    Finset.single_le_sum (fun n _ => wrow_nonneg c n) hmem1
  have hmem2 : c ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
  have h2' : (saddleN c : ℝ) ^ (2 * c) / (((saddleN c) ! : ℝ) * (c ! : ℝ))
      ≤ wrow c (saddleN c) := by
    rw [wrow]
    exact Finset.single_le_sum
      (f := fun k => (saddleN c : ℝ) ^ (2 * k) / (((saddleN c) ! : ℝ) * (k ! : ℝ)))
      (fun k _ => div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))) hmem2
  have hpos1 : (0 : ℝ) < Real.exp 1 * Real.sqrt (saddleN c)
      * ((saddleN c : ℝ) / Real.exp 1) ^ saddleN c :=
    mul_pos (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.2 (by linarith)))
      (pow_pos (div_pos (by linarith) (Real.exp_pos 1)) _)
  have hpos2 : (0 : ℝ) < Real.exp 1 * Real.sqrt c * ((c : ℝ) / Real.exp 1) ^ c :=
    mul_pos (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.2 (by linarith)))
      (pow_pos (div_pos (by linarith) (Real.exp_pos 1)) _)
  have hposF : (0 : ℝ) < ((saddleN c) ! : ℝ) * (c ! : ℝ) := mul_pos (ffact_pos _) (ffact_pos _)
  have hpow : (0 : ℝ) < (saddleN c : ℝ) ^ (2 * c) := pow_pos (by linarith) _
  calc (saddleN c : ℝ) ^ (2 * c)
        / (Real.exp 1 * Real.sqrt (saddleN c) * ((saddleN c : ℝ) / Real.exp 1) ^ saddleN c
          * (Real.exp 1 * Real.sqrt c * ((c : ℝ) / Real.exp 1) ^ c))
      ≤ (saddleN c : ℝ) ^ (2 * c) / (((saddleN c) ! : ℝ) * (c ! : ℝ)) :=
        (div_le_div_iff_of_pos_left hpow (mul_pos hpos1 hpos2) hposF).2
          (mul_le_mul hU1 hU2 (ffact_nonneg c) hpos1.le)
    _ ≤ wrow c (saddleN c) := h2'
    _ ≤ m0sum c := h1

/-- The small-region mass bound: below the `2c` scale the row is at most
`exp(2c)`; between `2c` and `c·log c` the geometric decay bounds the row by
twice its top term, and the top term by `(c·log c)^c/c!`. -/
theorem smallMass_le (c : ℕ) :
    smallMass c
      ≤ ((c : ℝ) + 1) * (Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !)) := by
  have hcl : (0 : ℝ) ≤ (c : ℝ) * Real.log c := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hc0))
  rw [smallMass]
  have hterm : ∀ n ∈ smallSet c,
      wrow c n ≤ Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !) := by
    intro n hn
    rw [smallSet, Finset.mem_filter] at hn
    obtain ⟨_, hn2⟩ := hn
    rcases le_or_gt ((n : ℝ) ^ 2) (2 * c) with h | h
    · have h1 : wrow c n ≤ Real.exp ((n : ℝ) ^ 2) := wrow_le_exp c n
      have h2 : Real.exp ((n : ℝ) ^ 2) ≤ Real.exp (2 * c) := Real.exp_le_exp.2 h
      have h3 : (0 : ℝ) ≤ 2 * (((c : ℝ) * Real.log c) ^ c / c !) :=
        mul_nonneg (by norm_num) (div_nonneg (pow_nonneg hcl _) (ffact_nonneg c))
      linarith [h1, h2, h3]
    · have h3 : wrow c n ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
        wrow_le_two_wterm c n (le_of_lt h)
      have h4 : (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))
          ≤ ((c : ℝ) * Real.log c) ^ c / c ! := by
        have h5 : (n : ℝ) ^ (2 * c) ≤ ((c : ℝ) * Real.log c) ^ c * (n ! : ℝ) := by
          have h6 : (n : ℝ) ^ (2 * c) = ((n : ℝ) ^ 2) ^ c := by rw [pow_mul]
          rw [h6]
          have h7 : ((n : ℝ) ^ 2) ^ c ≤ ((c : ℝ) * Real.log c) ^ c :=
            pow_le_pow_left₀ (sq_nonneg _) hn2 c
          have h8 : (1 : ℝ) ≤ (n ! : ℝ) := Nat.one_le_cast.2 (Nat.factorial_pos n)
          calc ((n : ℝ) ^ 2) ^ c ≤ ((c : ℝ) * Real.log c) ^ c := h7
            _ ≤ ((c : ℝ) * Real.log c) ^ c * (n ! : ℝ) :=
                le_mul_of_one_le_right (pow_nonneg hcl _) h8
        rw [div_le_div_iff₀ (mul_pos (ffact_pos n) (ffact_pos c)) (ffact_pos c)]
        have h9 := mul_le_mul_of_nonneg_right h5 (ffact_nonneg c)
        convert h9 using 1
        ring
      have h5 : (0 : ℝ) ≤ Real.exp (2 * c) := Real.exp_nonneg _
      calc wrow c n ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := h3
        _ ≤ 2 * (((c : ℝ) * Real.log c) ^ c / c !) :=
            mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ ≤ Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !) := by
            linarith [h5]
  calc smallMass c
        ≤ ∑ _n ∈ smallSet c, (Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !)) :=
        Finset.sum_le_sum hterm
    _ = ((smallSet c).card : ℝ)
          * (Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((c : ℝ) + 1) * (Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !)) := by
        have hpos : (0 : ℝ) ≤ Real.exp (2 * c) + 2 * (((c : ℝ) * Real.log c) ^ c / c !) :=
          add_nonneg (Real.exp_nonneg _)
            (mul_nonneg (by norm_num) (div_nonneg (pow_nonneg hcl _) (ffact_nonneg c)))
        apply mul_le_mul_of_nonneg_right _ hpos
        have hcard : (smallSet c).card ≤ c + 1 := by
          rw [smallSet]
          exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])
        exact_mod_cast hcard

/-!
## Section 4: A47 reduction lemmas and the c ≥ 9 envelope
-/

open Filter

/-- Stirling envelope `U(m) = e·√m·(m/e)^m` from `m0_lower`. -/
noncomputable def stirlingU (m : ℕ) : ℝ :=
  Real.exp 1 * Real.sqrt m * ((m : ℝ) / Real.exp 1) ^ m

theorem stirlingU_pos (m : ℕ) (hm : 1 ≤ m) : 0 < stirlingU m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  exact mul_pos (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.2 hmR))
    (pow_pos (div_pos hmR (Real.exp_pos 1)) m)

theorem le_saddleN (c : ℕ) :
    2 * Real.sqrt ((c : ℝ) * Real.log c) ≤ (saddleN c : ℝ) := by
  simpa [saddleN] using Nat.le_ceil (2 * Real.sqrt ((c : ℝ) * Real.log c))

theorem saddleN_lt_add_one (c : ℕ) :
    (saddleN c : ℝ) < 2 * Real.sqrt ((c : ℝ) * Real.log c) + 1 := by
  have h : (0 : ℝ) ≤ 2 * Real.sqrt ((c : ℝ) * Real.log c) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  simpa [saddleN] using Nat.ceil_lt_add_one h

theorem log_c_pos {c : ℕ} (hc : 3 ≤ c) : 0 < Real.log (c : ℝ) :=
  Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < c))

/-- `9 < exp(9/4)` via the degree-5 Taylor partial sum of `exp`. -/
theorem nine_lt_exp_nine_div_four : (9 : ℝ) < Real.exp (9 / 4) := by
  have hsum : (∑ k ∈ Finset.range 6, (9 / 4 : ℝ) ^ k / (k ! : ℝ)) ≤ Real.exp (9 / 4) := by
    have hs : Summable fun k : ℕ => (9 / 4 : ℝ) ^ k / (k ! : ℝ) :=
      Real.summable_pow_div_factorial _
    have hexp : Real.exp (9 / 4) = ∑' k : ℕ, (9 / 4 : ℝ) ^ k / (k ! : ℝ) := by
      simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [hexp]
    exact hs.sum_le_tsum (Finset.range 6) (fun _ _ => by positivity)
  have hcalc : (9 : ℝ) < ∑ k ∈ Finset.range 6, (9 / 4 : ℝ) ^ k / (k ! : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- `4 · log c ≤ c` for every natural `c ≥ 9`. -/
theorem four_log_le_self {c : ℕ} (hc : 9 ≤ c) : 4 * Real.log (c : ℝ) ≤ (c : ℝ) := by
  have hcR : (9 : ℝ) ≤ c := by exact_mod_cast hc
  have h9 : 4 * Real.log (9 : ℝ) ≤ (9 : ℝ) := by
    have : Real.log (9 : ℝ) ≤ 9 / 4 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      exact nine_lt_exp_nine_div_four.le
    linarith
  have hmono : 4 * Real.log (c : ℝ) - 4 * Real.log 9 ≤ (c : ℝ) - 9 := by
    have hlog : Real.log (c : ℝ) - Real.log 9 ≤ (c - 9) / 9 := by
      have : Real.log ((c : ℝ) / 9) ≤ (c : ℝ) / 9 - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le (by norm_num) hcR) (by norm_num))
      have heq : Real.log ((c : ℝ) / 9) = Real.log (c : ℝ) - Real.log 9 :=
        Real.log_div (by linarith) (by norm_num)
      have : (c : ℝ) / 9 - 1 = (c - 9) / 9 := by ring
      linarith
    have hdiv : (c - 9 : ℝ) / 9 ≤ c - 9 :=
      div_le_self (by linarith) (by norm_num)
    linarith
  linarith

/-- For `c ≥ 9`, `saddleN c ≤ c`. (Fails for `c = 2..8`.) -/
theorem saddleN_le_c_of_nine {c : ℕ} (hc : 9 ≤ c) : saddleN c ≤ c := by
  have hlog := log_c_pos (by omega : 3 ≤ c)
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (by omega)
  rw [saddleN, Nat.ceil_le]
  set x := 2 * Real.sqrt ((c : ℝ) * Real.log c) with hx
  have hx0 : (0 : ℝ) ≤ x := by
    rw [hx]; exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hsq : x ^ 2 ≤ (c : ℝ) ^ 2 := by
    have h1 : 4 * ((c : ℝ) * Real.log c) ≤ (c : ℝ) ^ 2 := by
      have := four_log_le_self hc
      nlinarith [this, hlog.le, sq_nonneg (c : ℝ)]
    calc x ^ 2 = 4 * ((c : ℝ) * Real.log c) := by
          rw [hx, mul_pow, Real.sq_sqrt (mul_nonneg hcR.le hlog.le)]; ring
      _ ≤ (c : ℝ) ^ 2 := h1
  exact (sq_le_sq₀ hx0 hcR.le).1 hsq

/-- For `c ≥ 3`, `1 ≤ saddleN c`. -/
theorem one_le_saddleN_of_three {c : ℕ} (hc : 3 ≤ c) : 1 ≤ saddleN c := by
  have hlog := log_c_pos hc
  have hcl : (0 : ℝ) < (c : ℝ) * Real.log c :=
    mul_pos (Nat.cast_pos.2 (by omega)) hlog
  have h2 : (1 : ℝ) ≤ 2 * Real.sqrt ((c : ℝ) * Real.log c) := by
    have : (1 / 4 : ℝ) ≤ (c : ℝ) * Real.log c := by
      have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
      have hlog3 : (1 : ℝ) < Real.log 3 := by
        have hexp : Real.exp 1 < 3 :=
          Real.exp_one_lt_d9.trans_le (by norm_num)
        have h := Real.log_lt_log (Real.exp_pos 1) hexp
        rwa [Real.log_exp] at h
      have hprod : (3 : ℝ) * (1 : ℝ) ≤ (c : ℝ) * Real.log c :=
        mul_le_mul hcR (le_of_lt (lt_of_lt_of_le hlog3
          (Real.log_le_log (by norm_num) hcR))) (by norm_num) (Nat.cast_nonneg _)
      linarith
    have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c) := by
      rw [Real.le_sqrt (by norm_num) hcl.le]
      convert this using 1; ring
    linarith
  exact_mod_cast (le_trans h2 (le_saddleN c))

/-- Joint `m0_lower` hypotheses for every `c ≥ 9`. -/
theorem saddleN_hypotheses_of_nine {c : ℕ} (hc : 9 ≤ c) :
    1 ≤ c ∧ 1 ≤ saddleN c ∧ saddleN c ≤ c :=
  ⟨by omega, one_le_saddleN_of_three (by omega), saddleN_le_c_of_nine hc⟩

/-- `properSqSum ≤ k² · n^(2k)`. -/
theorem properSqSum_le_sq_pow (n k : ℕ) :
    (properSqSum n k : ℝ) ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ (2 * k) := by
  have hcell : properSqSum n k ≤ k ^ 2 * n ^ (2 * k) := by
    rw [properSqSum]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (k - j) ^ 2 * cellCount n k j ≤ k ^ 2 * cellCount n k j := fun j _ =>
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le _ _) 2)
    calc ∑ j ∈ Finset.range (k + 1), (k - j) ^ 2 * cellCount n k j
        ≤ ∑ j ∈ Finset.range (k + 1), k ^ 2 * cellCount n k j := Finset.sum_le_sum hterm
      _ = k ^ 2 * ∑ j ∈ Finset.range (k + 1), cellCount n k j := by rw [Finset.mul_sum]
      _ = k ^ 2 * n ^ (2 * k) := by rw [margin_count]
  exact_mod_cast hcell

/-- `loopSqSum ≤ k² · n^(2k)`. -/
theorem loopSqSum_le_sq_pow (n k : ℕ) :
    (loopSqSum n k : ℝ) ≤ (k : ℝ) ^ 2 * (n : ℝ) ^ (2 * k) := by
  have hcell : loopSqSum n k ≤ k ^ 2 * n ^ (2 * k) := by
    rw [loopSqSum]
    have hterm : ∀ j ∈ Finset.range (k + 1),
        j ^ 2 * cellCount n k j ≤ k ^ 2 * cellCount n k j := fun j hj =>
      Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)) 2)
    calc ∑ j ∈ Finset.range (k + 1), j ^ 2 * cellCount n k j
        ≤ ∑ j ∈ Finset.range (k + 1), k ^ 2 * cellCount n k j := Finset.sum_le_sum hterm
      _ = k ^ 2 * ∑ j ∈ Finset.range (k + 1), cellCount n k j := by rw [Finset.mul_sum]
      _ = k ^ 2 * n ^ (2 * k) := by rw [margin_count]
  exact_mod_cast hcell

/-- At `n = 1`, `loopSqSum = k²` (pure-numerator cell). -/
theorem loopSqSum_one (k : ℕ) : loopSqSum 1 k = k ^ 2 := by
  rw [loopSqSum_eq]
  simp [pow_two, one_pow]
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    ring

/-- At `n = 1`, `properSqSum = 0` (pure-numerator cell; mechanism comparison
needs `n ≥ 2`). -/
theorem properSqSum_one (k : ℕ) : properSqSum 1 k = 0 := by
  rw [properSqSum_eq]
  simp [pow_two]

/-- Small-region proper-second-moment mass. -/
noncomputable def dsumSmall (c : ℕ) : ℝ :=
  ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
    (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

/-- Small-region loop-second-moment mass (includes the `n = 1` row). -/
noncomputable def nsumSmall (c : ℕ) : ℝ :=
  ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
    (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

theorem dsumSmall_le_c_sq_smallMass (c : ℕ) :
    dsumSmall c ≤ (c : ℝ) ^ 2 * smallMass c := by
  have hterm : ∀ n ∈ smallSet c, ∀ k ∈ Finset.range (c + 1),
      (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n _ k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    have hk2 : (k : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hkc 2
    have hle : (properSqSum n k : ℝ) ≤ (c : ℝ) ^ 2 * (n : ℝ) ^ (2 * k) :=
      le_trans (properSqSum_le_sq_pow n k)
        (mul_le_mul_of_nonneg_right hk2 (pow_nonneg (Nat.cast_nonneg _) _))
    have hden : (0 : ℝ) ≤ (n ! : ℝ) * (k ! : ℝ) :=
      mul_nonneg (ffact_nonneg _) (ffact_nonneg _)
    calc (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ ((c : ℝ) ^ 2 * (n : ℝ) ^ (2 * k)) / ((n ! : ℝ) * (k ! : ℝ)) :=
          div_le_div_of_nonneg_right hle hden
      _ = (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
  calc dsumSmall c
      ≤ ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
          (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = (c : ℝ) ^ 2 * ∑ n ∈ smallSet c,
          ∑ k ∈ Finset.range (c + 1), (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := by
        simp_rw [← Finset.mul_sum]
    _ = (c : ℝ) ^ 2 * smallMass c := by rfl

theorem nsumSmall_le_c_sq_smallMass (c : ℕ) :
    nsumSmall c ≤ (c : ℝ) ^ 2 * smallMass c := by
  have hterm : ∀ n ∈ smallSet c, ∀ k ∈ Finset.range (c + 1),
      (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n _ k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    have hk2 : (k : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hkc 2
    have hle : (loopSqSum n k : ℝ) ≤ (c : ℝ) ^ 2 * (n : ℝ) ^ (2 * k) :=
      le_trans (loopSqSum_le_sq_pow n k)
        (mul_le_mul_of_nonneg_right hk2 (pow_nonneg (Nat.cast_nonneg _) _))
    have hden : (0 : ℝ) ≤ (n ! : ℝ) * (k ! : ℝ) :=
      mul_nonneg (ffact_nonneg _) (ffact_nonneg _)
    calc (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ ((c : ℝ) ^ 2 * (n : ℝ) ^ (2 * k)) / ((n ! : ℝ) * (k ! : ℝ)) :=
          div_le_div_of_nonneg_right hle hden
      _ = (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
  calc nsumSmall c
      ≤ ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
          (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = (c : ℝ) ^ 2 * ∑ n ∈ smallSet c,
          ∑ k ∈ Finset.range (c + 1), (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := by
        simp_rw [← Finset.mul_sum]
    _ = (c : ℝ) ^ 2 * smallMass c := by rfl

/-- Concentration envelope for `c ≥ 9`: the ratio is at most the explicit
A45 combination of `smallMass_le` and `m0_lower`. -/
theorem smallMass_div_m0sum_le_envelope {c : ℕ} (hc : 9 ≤ c) :
    smallMass c / m0sum c
      ≤ ((c : ℝ) + 1) * (Real.exp (2 * (c : ℝ)) + 2 * (((c : ℝ) * Real.log c) ^ c / c !))
          * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c) := by
  obtain ⟨hc1, hs1, hsc⟩ := saddleN_hypotheses_of_nine hc
  have hsR : (0 : ℝ) < saddleN c := Nat.cast_pos.2 (by omega)
  have hU1 := stirlingU_pos (saddleN c) hs1
  have hU2 := stirlingU_pos c hc1
  have hm0 := m0_lower c hc1 hs1 hsc
  have hm0' :
      (saddleN c : ℝ) ^ (2 * c) / (stirlingU (saddleN c) * stirlingU c) ≤ m0sum c := by
    simpa [stirlingU] using hm0
  have hm0pos := m0sum_pos c
  have hpow := pow_pos hsR (2 * c)
  have hdenU := mul_pos hU1 hU2
  have hinv : 1 / m0sum c
      ≤ (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c) := by
    have h := (div_le_iff₀ hdenU).1 hm0'
    rw [div_le_div_iff₀ hm0pos hpow]
    linarith
  have hsmU : smallMass c * (stirlingU (saddleN c) * stirlingU c)
      ≤ ((c : ℝ) + 1) * (Real.exp (2 * (c : ℝ)) + 2 * (((c : ℝ) * Real.log c) ^ c / c !))
          * (stirlingU (saddleN c) * stirlingU c) :=
    mul_le_mul_of_nonneg_right (smallMass_le c) (mul_nonneg hU1.le hU2.le)
  calc smallMass c / m0sum c
      = smallMass c * (1 / m0sum c) := by ring
    _ ≤ smallMass c * ((stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c)) :=
        mul_le_mul_of_nonneg_left hinv (smallMass_nonneg c)
    _ = (smallMass c * (stirlingU (saddleN c) * stirlingU c)) / (saddleN c : ℝ) ^ (2 * c) := by
        ring
    _ ≤ ((c : ℝ) + 1) * (Real.exp (2 * (c : ℝ)) + 2 * (((c : ℝ) * Real.log c) ^ c / c !))
          * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c) :=
        div_le_div_of_nonneg_right hsmU hpow.le

/-!
## A48 section 5: saddle concentration `smallMass / m0sum → 0`

The A47 envelope bounds `smallMass/m0sum` by a Stirling product form; this
section closes the limit.  The route, with each step kernel-checked below:

* (a) `(c·log c)^c / s^(2c) ≤ (1/4)^c`, from `2√(c·log c) ≤ s`.
* (b) `stirlingU c / c! ≤ e/√(2π)`, the two Stirling bounds divided.
* (c) `log stirlingU s ≤ s·log s − s + (3/2)·log s + 1 ≤ 4√(c·log c)·log c`
  for `c ≥ 27`.
* (d) `4√(c·log c)·log c ≤ ε·c` eventually, since `(log c)³ = o(c)`.

Combining: `smallMass/m0sum ≤ K·(c+1)·√c·(1/2)^c → 0`.
-/

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
  have h := Real.log_lt_log (Real.exp_pos 1) hexp
  rwa [Real.log_exp] at h

theorem two_lt_log_nine : (2 : ℝ) < Real.log 9 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 9)]
  have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [he2]
  calc (Real.exp 1) ^ 2 < (2.7182818286 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : (2 : ℕ) ≠ 0)
    _ < 9 := by norm_num

/-- `1 < c·log c` for `c ≥ 3`. -/
theorem one_lt_clogc {c : ℕ} (hc : 3 ≤ c) : (1 : ℝ) < (c : ℝ) * Real.log c := by
  have hle : Real.log 3 ≤ Real.log (c : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hc)
  have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
  calc (1 : ℝ) < 3 * Real.log 3 := by linarith [one_lt_log_three]
    _ ≤ (c : ℝ) * Real.log (c : ℝ) :=
        mul_le_mul hcR hle (by linarith [one_lt_log_three] : (0 : ℝ) ≤ Real.log 3)
          (by linarith)

/-- The large region: rows whose square exceeds `c·log c`. -/
noncomputable def largeSet (c : ℕ) : Finset ℕ :=
  (Finset.range (c + 1)).filter fun n => (c : ℝ) * Real.log c < (n : ℝ) ^ 2

theorem mem_largeSet {c n : ℕ} :
    n ∈ largeSet c ↔ n ∈ Finset.range (c + 1) ∧ (c : ℝ) * Real.log c < (n : ℝ) ^ 2 :=
  Finset.mem_filter

/-- Cells of the large region satisfy `n ≥ 2` for `c ≥ 3`. -/
theorem largeSet_n_ge_two {c : ℕ} (hc : 3 ≤ c) {n : ℕ} (hn : n ∈ largeSet c) :
    2 ≤ n := by
  rw [mem_largeSet] at hn
  by_contra hlt
  push_neg at hlt
  have hn1 : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
  have h : (n : ℝ) ^ 2 ≤ 1 := by
    calc (n : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn1 2
      _ = 1 := by norm_num
  have hc := one_lt_clogc hc
  linarith [hn.2]

/-- Cells of the large region satisfy `n ≥ 5` for `c ≥ 9`, since
`c·log c ≥ 9·log 9 > 16`. -/
theorem largeSet_n_ge_five {c : ℕ} (hc : 9 ≤ c) {n : ℕ} (hn : n ∈ largeSet c) :
    5 ≤ n := by
  rw [mem_largeSet] at hn
  by_contra hlt
  push_neg at hlt
  have hnR : (n : ℝ) ≤ 4 := by exact_mod_cast (by omega : n ≤ 4)
  have h16 : (n : ℝ) ^ 2 ≤ 16 := by
    calc (n : ℝ) ^ 2 ≤ (4 : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR 2
      _ = 16 := by norm_num
  have hle : Real.log 9 ≤ Real.log (c : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hc)
  have hc9 : (9 : ℝ) ≤ c := by exact_mod_cast hc
  have hclog : (16 : ℝ) < (c : ℝ) * Real.log (c : ℝ) := by
    calc (16 : ℝ) < 9 * Real.log 9 := by linarith [two_lt_log_nine]
      _ ≤ (c : ℝ) * Real.log (c : ℝ) :=
          mul_le_mul hc9 hle (by linarith [two_lt_log_nine]) (by linarith)
  linarith [hn.2]

/-- `(4·c·log c)^c ≤ s^(2c)` for `c ≥ 1`, from `2√(c·log c) ≤ s`. -/
theorem four_clogc_pow_le_saddlen_pow {c : ℕ} (hc : 1 ≤ c) :
    (4 * ((c : ℝ) * Real.log c)) ^ c ≤ (saddleN c : ℝ) ^ (2 * c) := by
  have hle := le_saddleN c
  have heq : (4 * ((c : ℝ) * Real.log c)) ^ c
      = (2 * Real.sqrt ((c : ℝ) * Real.log c)) ^ (2 * c) := by
    have h1 : (2 * Real.sqrt ((c : ℝ) * Real.log c)) ^ 2
        = 4 * ((c : ℝ) * Real.log c) := by
      rw [mul_pow, Real.sq_sqrt
        (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hc)))]
      norm_num
    rw [← h1, ← pow_mul]
  rw [heq]
  exact pow_le_pow_left₀ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hle (2 * c)

/-- Piece (a): `(c·log c)^c / s^(2c) ≤ (1/4)^c` for `c ≥ 3`. -/
theorem clogc_pow_div_saddlen_pow_le {c : ℕ} (hc : 3 ≤ c) :
    ((c : ℝ) * Real.log c) ^ c / (saddleN c : ℝ) ^ (2 * c) ≤ (1 / 4 : ℝ) ^ c := by
  have hs1n : 1 ≤ saddleN c := one_le_saddleN_of_three hc
  have hX : (0 : ℝ) ≤ (c : ℝ) * Real.log c :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c)))
  have hge := four_clogc_pow_le_saddlen_pow (by omega : 1 ≤ c)
  have h4pos : (0 : ℝ) < (4 * ((c : ℝ) * Real.log c)) ^ c :=
    pow_pos (mul_pos (by norm_num) (mul_pos (Nat.cast_pos.2 (by omega)) (log_c_pos hc))) _
  have hPpos : (0 : ℝ) < (saddleN c : ℝ) ^ (2 * c) := pow_pos (Nat.cast_pos.2 hs1n) _
  have key : ((c : ℝ) * Real.log c) ^ c
      = (1 / 4 : ℝ) ^ c * (4 * ((c : ℝ) * Real.log c)) ^ c := by
    rw [mul_pow, div_pow, one_pow]
    field_simp [(pow_pos (by norm_num : (0 : ℝ) < 4) c).ne']
    ring
  rw [div_le_iff₀ hPpos, key]
  exact mul_le_mul_of_nonneg_left hge (pow_nonneg (by norm_num) c)

/-- Piece (b): `stirlingU c / c! ≤ e/√(2π)` for `c ≥ 1`, the upper Stirling
bound divided by the lower one. -/
theorem stirlingU_div_factorial_le {c : ℕ} (hc : 1 ≤ c) :
    stirlingU c / (c ! : ℝ) ≤ Real.exp 1 / Real.sqrt (2 * Real.pi) := by
  have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 hc
  have hL := factorial_lower c
  have key : stirlingU c * Real.sqrt (2 * Real.pi)
      = Real.exp 1 * (((c : ℝ) / Real.exp 1) ^ c) * Real.sqrt (2 * Real.pi * (c : ℝ)) := by
    have e0 : stirlingU c
        = Real.exp 1 * Real.sqrt (c : ℝ) * ((c : ℝ) / Real.exp 1) ^ c := rfl
    rw [e0]
    calc Real.exp 1 * Real.sqrt (c : ℝ) * ((c : ℝ) / Real.exp 1) ^ c * Real.sqrt (2 * Real.pi)
        = Real.exp 1 * ((c : ℝ) / Real.exp 1) ^ c
          * (Real.sqrt (c : ℝ) * Real.sqrt (2 * Real.pi)) := by ring
      _ = Real.exp 1 * ((c : ℝ) / Real.exp 1) ^ c
          * Real.sqrt ((c : ℝ) * (2 * Real.pi)) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg c)]
      _ = Real.exp 1 * ((c : ℝ) / Real.exp 1) ^ c
          * Real.sqrt (2 * Real.pi * (c : ℝ)) := by
          rw [show (c : ℝ) * (2 * Real.pi) = 2 * Real.pi * (c : ℝ) from mul_comm _ _]
  rw [div_le_div_iff₀ (ffact_pos _)
    (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)), key]
  calc Real.exp 1 * (((c : ℝ) / Real.exp 1) ^ c) * Real.sqrt (2 * Real.pi * (c : ℝ))
      = Real.exp 1 * (Real.sqrt (2 * Real.pi * (c : ℝ)) * ((c : ℝ) / Real.exp 1) ^ c) := by ring
    _ ≤ Real.exp 1 * (c ! : ℝ) := mul_le_mul_of_nonneg_left hL (Real.exp_pos 1).le

/-- `log stirlingU m = 1 + (log m)/2 + m·(log m − 1)` for `m ≥ 1`. -/
theorem log_stirlingU_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (stirlingU m)
      = 1 + Real.log (m : ℝ) / 2 + (m : ℝ) * (Real.log (m : ℝ) - 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have e0 : stirlingU m
      = Real.exp 1 * Real.sqrt (m : ℝ) * ((m : ℝ) / Real.exp 1) ^ m := rfl
  have hpow : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 :=
    (pow_pos (div_pos hmR (Real.exp_pos 1)) m).ne'
  rw [e0, Real.log_mul (mul_ne_zero (Real.exp_pos 1).ne' (Real.sqrt_pos.2 hmR).ne') hpow,
    Real.log_mul (Real.exp_pos 1).ne' (Real.sqrt_pos.2 hmR).ne', Real.log_exp, Real.log_pow,
    Real.log_div hmR.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt hmR.le]

/-- `s ≤ 3√(c·log c)` once `√(c·log c) ≥ 9`, since `s < 2√(c·log c) + 1`. -/
theorem saddleN_le_three_sqrt {c : ℕ}
    (h : (9 : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c)) :
    (saddleN c : ℝ) ≤ 3 * Real.sqrt ((c : ℝ) * Real.log c) := by
  have hlt := saddleN_lt_add_one c
  linarith

theorem log_three_lt_two : Real.log 3 < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (3 : ℝ) < 2 ^ 2 := by norm_num
    _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) he2 2
    _ = Real.exp 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]

/-- `exp(12) < 163000`, via `e < 2.7182818286` and a numeral power. -/
theorem exp_twelve_lt : Real.exp 12 < 163000 := by
  have h1 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h1]
  calc (Real.exp 1) ^ 12 < (2.7182818286 : ℝ) ^ 12 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num : (12 : ℕ) ≠ 0)
    _ < 163000 := by norm_num

/-- Piece (c): `log stirlingU s ≤ 4√(c·log c)·log c` for `c ≥ 163000`
(so that `log c ≥ 12` and `√(c·log c) ≥ 9`). -/
theorem log_stirlingU_saddlen_le {c : ℕ} (hc : 163000 ≤ c) :
    Real.log (stirlingU (saddleN c))
      ≤ 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c := by
  have hs1n : 1 ≤ saddleN c := one_le_saddleN_of_three (by omega : 3 ≤ c)
  have hsR : (0 : ℝ) < (saddleN c : ℝ) := Nat.cast_pos.2 hs1n
  have hlogc : (0 : ℝ) < Real.log (c : ℝ) := log_c_pos (by omega : 3 ≤ c)
  have hcl : (0 : ℝ) < (c : ℝ) * Real.log c := mul_pos (Nat.cast_pos.2 (by omega)) hlogc
  have hXpos : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := Real.sqrt_pos.2 hcl
  -- `12 ≤ log c` from `exp(12) < 163000 ≤ c`
  have hL12 : (12 : ℝ) ≤ Real.log (c : ℝ) := by
    rw [Real.le_log_iff_exp_le (Nat.cast_pos.2 (by omega : 0 < c))]
    have hcR : (163000 : ℝ) ≤ c := by exact_mod_cast hc
    exact exp_twelve_lt.le.trans hcR
  -- scale facts about `X = √(c·log c)`
  have hX9 : (9 : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c) := by
    have e : (9 : ℝ) ^ 2 = 81 := by norm_num
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 9) hcl.le, e]
    have hcR : (163000 : ℝ) ≤ c := by exact_mod_cast hc
    calc (81 : ℝ) ≤ 163000 * 12 := by norm_num
      _ ≤ (c : ℝ) * Real.log (c : ℝ) :=
          mul_le_mul hcR hL12 (by norm_num) (by linarith)
  have hX1 : (1 : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c) := by linarith
  have hLX : Real.log (c : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.le_sqrt hlogc.le hcl.le]
    have h : Real.log (c : ℝ) ≤ (c : ℝ) :=
      (Real.log_le_sub_one_of_pos (Nat.cast_pos.2 (by omega : 0 < c))).trans (by linarith)
    calc Real.log (c : ℝ) ^ 2
        ≤ Real.log (c : ℝ) * (c : ℝ) := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left h hlogc.le
      _ = (c : ℝ) * Real.log (c : ℝ) := by ring
  -- `s ≤ 3X` and `log s ≤ 2 + log c`
  have hs : (saddleN c : ℝ) ≤ 3 * Real.sqrt ((c : ℝ) * Real.log c) :=
    saddleN_le_three_sqrt hX9
  have hlogsn : (0 : ℝ) ≤ Real.log (saddleN c) := Real.log_nonneg (by exact_mod_cast hs1n)
  have hlogs : Real.log (saddleN c) ≤ 2 + Real.log (c : ℝ) := by
    have h1 : Real.log (saddleN c)
        ≤ Real.log 3 + (Real.log c + Real.log (Real.log c)) / 2 := by
      calc Real.log (saddleN c)
          ≤ Real.log (3 * Real.sqrt ((c : ℝ) * Real.log c)) :=
            Real.log_le_log hsR hs
        _ = Real.log 3 + Real.log (Real.sqrt ((c : ℝ) * Real.log c)) := by
            rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hXpos.ne']
        _ = Real.log 3 + (Real.log c + Real.log (Real.log c)) / 2 := by
            rw [Real.log_sqrt hcl.le,
              Real.log_mul (Nat.cast_pos.2 (by omega : 0 < c)).ne' hlogc.ne']
    have h2 : Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hlogc]
    linarith [h1, h2, log_three_lt_two]
  -- assemble
  have hsplit := log_stirlingU_le (saddleN c) hs1n
  calc Real.log (stirlingU (saddleN c))
      = 1 + Real.log (saddleN c) / 2
        + ((saddleN c : ℝ) * Real.log (saddleN c) - saddleN c) := by
        rw [hsplit]
        ring
    _ ≤ 1 + (2 + Real.log (c : ℝ)) / 2
        + (3 * Real.sqrt ((c : ℝ) * Real.log c) * (2 + Real.log (c : ℝ)) - 0) := by
        apply add_le_add
        · exact add_le_add le_rfl
            (div_le_div_of_nonneg_right hlogs (by norm_num : (0 : ℝ) ≤ 2))
        · calc (saddleN c : ℝ) * Real.log (saddleN c) - saddleN c
              ≤ (saddleN c : ℝ) * Real.log (saddleN c) := sub_le_self _ hsR.le
            _ ≤ 3 * Real.sqrt ((c : ℝ) * Real.log c) * (2 + Real.log (c : ℝ)) :=
                mul_le_mul hs hlogs hlogsn (mul_nonneg (by norm_num) hXpos.le)
            _ = 3 * Real.sqrt ((c : ℝ) * Real.log c) * (2 + Real.log (c : ℝ)) - 0 := by ring
    _ = 2 + Real.log (c : ℝ) / 2
        + 6 * Real.sqrt ((c : ℝ) * Real.log c)
        + 3 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c := by ring
    _ ≤ 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c := by
        have h2 : 2 + Real.log (c : ℝ) / 2
            ≤ 6 * Real.sqrt ((c : ℝ) * Real.log c) := by
          have h1 : Real.log (c : ℝ) / 2
              ≤ Real.sqrt ((c : ℝ) * Real.log c) := by linarith [hLX, hXpos.le]
          have h2' : (2 : ℝ) ≤ 2 * Real.sqrt ((c : ℝ) * Real.log c) := by linarith [hX1]
          linarith
        have h3 : 6 * Real.sqrt ((c : ℝ) * Real.log c)
            ≤ Real.sqrt ((c : ℝ) * Real.log c) * Real.log (c : ℝ) / 2 := by
          have h := mul_le_mul_of_nonneg_left hL12 hXpos.le
          linarith
        linarith [h2, h3, hXpos.le]

/-- Piece (d): `4√(c·log c)·log c ≤ ε·c` eventually in `c`, for any `ε > 0`,
since `(log c)³ = o(c)`. -/
theorem four_sqrt_clogc_log_le_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℕ in atTop,
      4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ ε * (c : ℝ) := by
  have hN : (fun c : ℕ => Real.log (c : ℝ) ^ 3) =o[atTop] (fun c : ℕ => (c : ℝ)) := by
    have h1 := (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def, id] using h1
  have hε' : (0 : ℝ) < ε ^ 2 / 16 := by positivity
  have hN' := (hN.def' hε').bound
  filter_upwards [hN', eventually_ge_atTop 3] with c hc hc3
  have hlogc : (0 : ℝ) < Real.log (c : ℝ) := log_c_pos hc3
  have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 (by omega)
  have hc3' : (0 : ℝ) ≤ Real.log (c : ℝ) ^ 3 := by positivity
  rw [Real.norm_of_nonneg hc3', Real.norm_of_nonneg hcR.le] at hc
  have hcl : (0 : ℝ) < (c : ℝ) * Real.log c := mul_pos hcR hlogc
  have hsq : (4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c) ^ 2
      = 16 * Real.log c ^ 3 * (c : ℝ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hcl.le]
    ring
  have hsqle : (4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c) ^ 2
      ≤ (ε * (c : ℝ)) ^ 2 := by
    rw [hsq, mul_pow]
    have h16 : (16 : ℝ) * Real.log c ^ 3 * (c : ℝ) ≤ (ε ^ 2) * (c : ℝ) ^ 2 := by
      calc (16 : ℝ) * Real.log c ^ 3 * (c : ℝ)
          ≤ 16 * ((ε ^ 2 / 16) * (c : ℝ)) * (c : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hcR.le
            exact mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 16)
        _ = (ε ^ 2) * (c : ℝ) ^ 2 := by ring
    exact h16
  have hnn1 : (0 : ℝ) ≤ 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hlogc.le
  have hnn2 : (0 : ℝ) ≤ ε * (c : ℝ) := mul_nonneg hε.le hcR.le
  exact (sq_le_sq₀ hnn1 hnn2).1 hsqle

/-- `stirlingU s ≤ 2^c` once piece (c)'s log bound is below `c·log 2`. -/
theorem stirlingU_saddlen_le_two_pow {c : ℕ} (hc : 163000 ≤ c)
    (hd : 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ Real.log 2 * (c : ℝ)) :
    stirlingU (saddleN c) ≤ (2 : ℝ) ^ c := by
  have hs1n : 1 ≤ saddleN c := one_le_saddleN_of_three (by omega : 3 ≤ c)
  have hlog := le_trans (log_stirlingU_saddlen_le hc) hd
  have h := Real.exp_le_exp.2 hlog
  rwa [Real.exp_log (stirlingU_pos _ hs1n), mul_comm (Real.log 2) (c : ℝ), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h

/-- The `e^(2c)` term of the A47 envelope is at most
`e·(c+1)·√c·(1/2)^c`. -/
theorem termA_le {c : ℕ} (hc : 163000 ≤ c)
    (hd : 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ Real.log 2 * (c : ℝ))
    (he4 : Real.exp 1 / (4 * Real.log (c : ℝ)) ≤ 1 / 4) :
    ((c : ℝ) + 1) * Real.exp (2 * (c : ℝ)) * (stirlingU (saddleN c) * stirlingU c)
        / (saddleN c : ℝ) ^ (2 * c)
      ≤ Real.exp 1 * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c := by
  have hc3 : 3 ≤ c := by omega
  have hs1n : 1 ≤ saddleN c := one_le_saddleN_of_three hc3
  have hsR : (0 : ℝ) < (saddleN c : ℝ) := Nat.cast_pos.2 hs1n
  have hlogc : (0 : ℝ) < Real.log (c : ℝ) := log_c_pos hc3
  have hU_s := stirlingU_saddlen_le_two_pow hc hd
  have hcore : Real.exp (2 * (c : ℝ)) * stirlingU c / (saddleN c : ℝ) ^ (2 * c)
      ≤ Real.exp 1 * Real.sqrt (c : ℝ) * (1 / 4 : ℝ) ^ c := by
    have hge := four_clogc_pow_le_saddlen_pow (by omega : 1 ≤ c)
    have h4pos : (0 : ℝ) < (4 * ((c : ℝ) * Real.log c)) ^ c :=
      pow_pos (mul_pos (by norm_num) (mul_pos (Nat.cast_pos.2 (by omega)) hlogc)) _
    have hU_c_pos := stirlingU_pos c (by omega : 1 ≤ c)
    have hnum : (0 : ℝ) ≤ Real.exp (2 * (c : ℝ)) * stirlingU c :=
      mul_nonneg (Real.exp_nonneg _) hU_c_pos.le
    have hstep1 : Real.exp (2 * (c : ℝ)) * stirlingU c / (saddleN c : ℝ) ^ (2 * c)
        ≤ Real.exp (2 * (c : ℝ)) * stirlingU c / (4 * ((c : ℝ) * Real.log c)) ^ c :=
      div_le_div_of_nonneg_left hnum h4pos hge
    have hid : Real.exp (2 * (c : ℝ)) * stirlingU c / (4 * ((c : ℝ) * Real.log c)) ^ c
        = Real.exp 1 * Real.sqrt (c : ℝ) * (Real.exp 1 / (4 * Real.log (c : ℝ))) ^ c := by
      have e1 : Real.exp (2 * (c : ℝ)) = (Real.exp 1) ^ (2 * c) := by
        rw [show (2 : ℝ) * (c : ℝ) = ((2 * c : ℕ) : ℝ) * 1 by push_cast; ring,
          Real.exp_nat_mul]
      have e2 : (Real.exp 1) ^ (2 * c) = ((Real.exp 1) ^ c) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      have e3 : (4 * ((c : ℝ) * Real.log c)) ^ c
          = 4 ^ c * ((c : ℝ) ^ c * (Real.log (c : ℝ)) ^ c) := by
        rw [mul_pow, mul_pow]
      have e4 : (Real.exp 1 / (4 * Real.log (c : ℝ))) ^ c
          = (Real.exp 1) ^ c / (4 ^ c * (Real.log (c : ℝ)) ^ c) := by
        rw [div_pow, mul_pow]
      have e5 : stirlingU c
          = Real.exp 1 * Real.sqrt (c : ℝ) * ((c : ℝ) / Real.exp 1) ^ c := rfl
      rw [e1, e2, e3, e4, e5, div_pow]
      field_simp [(Real.exp_pos 1).ne', hlogc.ne', (Nat.cast_pos.2 (by omega : 0 < c)).ne']
        <;> ring
    have hstep3 : Real.exp 1 * Real.sqrt (c : ℝ) * (Real.exp 1 / (4 * Real.log (c : ℝ))) ^ c
        ≤ Real.exp 1 * Real.sqrt (c : ℝ) * (1 / 4 : ℝ) ^ c := by
      have hnn1 : (0 : ℝ) ≤ Real.exp 1 / (4 * Real.log (c : ℝ)) :=
        div_nonneg (Real.exp_pos 1).le (mul_nonneg (by norm_num) hlogc.le)
      have hnn2 : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (c : ℝ) :=
        mul_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn1 he4 c) hnn2
    exact hstep1.trans (hid.symm ▸ hstep3)
  have hU_s_pos := stirlingU_pos (saddleN c) hs1n
  have hfact : (0 : ℝ) ≤ Real.exp 1 * Real.sqrt (c : ℝ) * (1 / 4 : ℝ) ^ c := by positivity
  have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
  have hhalf : (2 : ℝ) ^ c * (1 / 4 : ℝ) ^ c = (1 / 2 : ℝ) ^ c := by
    rw [← mul_pow]
    norm_num
  calc ((c : ℝ) + 1) * Real.exp (2 * (c : ℝ)) * (stirlingU (saddleN c) * stirlingU c)
        / (saddleN c : ℝ) ^ (2 * c)
      = ((c : ℝ) + 1) * stirlingU (saddleN c)
          * (Real.exp (2 * (c : ℝ)) * stirlingU c / (saddleN c : ℝ) ^ (2 * c)) := by ring
    _ ≤ ((c : ℝ) + 1) * stirlingU (saddleN c)
          * (Real.exp 1 * Real.sqrt (c : ℝ) * (1 / 4 : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left hcore (mul_nonneg hc1 hU_s_pos.le)
    _ ≤ ((c : ℝ) + 1) * (2 : ℝ) ^ c
          * (Real.exp 1 * Real.sqrt (c : ℝ) * (1 / 4 : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_right (mul_le_mul le_rfl hU_s hU_s_pos.le hc1) hfact
    _ = ((c : ℝ) + 1) * Real.exp 1 * Real.sqrt (c : ℝ)
          * ((2 : ℝ) ^ c * (1 / 4 : ℝ) ^ c) := by ring
    _ = Real.exp 1 * ((c : ℝ) + 1) * Real.sqrt (c : ℝ) * (1 / 2 : ℝ) ^ c := by
        rw [hhalf]
        ring

/-- The `2·(c·log c)^c/c!` term of the A47 envelope is at most
`(2e/√(2π))·(c+1)·(1/2)^c`. -/
theorem termB_le {c : ℕ} (hc : 163000 ≤ c)
    (hd : 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ Real.log 2 * (c : ℝ)) :
    ((c : ℝ) + 1) * (2 * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (c ! : ℝ)))
        * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c)
      ≤ (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
  have hc3 : 3 ≤ c := by omega
  have hs1n : 1 ≤ saddleN c := one_le_saddleN_of_three hc3
  have hU_s_pos := stirlingU_pos (saddleN c) hs1n
  have hU_c_pos := stirlingU_pos c (by omega : 1 ≤ c)
  have hU_s := stirlingU_saddlen_le_two_pow hc hd
  have hpa := clogc_pow_div_saddlen_pow_le hc3
  have hU_c := stirlingU_div_factorial_le (by omega : 1 ≤ c)
  have hcl : (0 : ℝ) ≤ (c : ℝ) * Real.log (c : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c)))
  have ha_nn : (0 : ℝ) ≤ ((c : ℝ) * Real.log (c : ℝ)) ^ c / (saddleN c : ℝ) ^ (2 * c) :=
    div_nonneg (pow_nonneg hcl _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hUcCf_nn : (0 : ℝ) ≤ stirlingU c / (c ! : ℝ) :=
    div_nonneg hU_c_pos.le (ffact_nonneg _)
  have hc1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
  have hcf : (0 : ℝ) ≤ ((c : ℝ) + 1) * 2 := by positivity
  have hhalf : (2 : ℝ) ^ c * (1 / 4 : ℝ) ^ c = (1 / 2 : ℝ) ^ c := by
    rw [← mul_pow]
    norm_num
  calc ((c : ℝ) + 1) * (2 * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (c ! : ℝ)))
        * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c)
      = ((c : ℝ) + 1) * 2
        * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (saddleN c : ℝ) ^ (2 * c))
        * (stirlingU c / (c ! : ℝ)) * stirlingU (saddleN c) := by ring
    _ ≤ ((c : ℝ) + 1) * 2 * ((1 / 4 : ℝ) ^ c) * (Real.exp 1 / Real.sqrt (2 * Real.pi))
        * (2 : ℝ) ^ c := by
        apply mul_le_mul _ hU_s hU_s_pos.le _
        · apply mul_le_mul _ hU_c hUcCf_nn _
          · exact mul_le_mul le_rfl hpa ha_nn hcf
          · exact mul_nonneg (mul_nonneg hc1 (by norm_num)) (pow_nonneg (by norm_num) _)
        · exact mul_nonneg (mul_nonneg (mul_nonneg hc1 (by norm_num))
            (pow_nonneg (by norm_num) _))
            (div_nonneg (Real.exp_pos 1).le (Real.sqrt_nonneg _))
    _ = (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ c := by
        rw [← hhalf]
        ring

/-- The concentration bound: `smallMass/m0sum ≤ K·(c+1)·√c·(1/2)^c` with
`K = e + 2e/√(2π)`, for every `c` where pieces (c,d) and the `e/(4 log c)`
threshold hold. -/
theorem smallMass_div_m0sum_le_half_pow {c : ℕ} (hc : 163000 ≤ c)
    (hd : 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ Real.log 2 * (c : ℝ))
    (he4 : Real.exp 1 / (4 * Real.log (c : ℝ)) ≤ 1 / 4) :
    smallMass c / m0sum c
      ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
          * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c := by
  have henv := smallMass_div_m0sum_le_envelope (by omega : 9 ≤ c)
  have hA := termA_le hc hd he4
  have hB := termB_le hc hd
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (c : ℝ) := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg c), one_pow]
    exact_mod_cast (by omega : 1 ≤ c)
  have hB' : ((c : ℝ) + 1) * (2 * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (c ! : ℝ)))
        * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c)
      ≤ (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1) * Real.sqrt c
        * (1 / 2 : ℝ) ^ c := by
    calc ((c : ℝ) + 1) * (2 * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (c ! : ℝ)))
          * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c)
        ≤ (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1) * (1 / 2 : ℝ) ^ c := hB
      _ = (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
          * (1 * (1 / 2 : ℝ) ^ c) := by ring
      _ ≤ (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
          * (Real.sqrt c * (1 / 2 : ℝ) ^ c) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrt1 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _))
          (mul_nonneg
            (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le)
              (Real.sqrt_nonneg _))
            (by positivity : (0 : ℝ) ≤ (c : ℝ) + 1))
      _ = (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
          * Real.sqrt c * (1 / 2 : ℝ) ^ c := by ring
  calc smallMass c / m0sum c
      ≤ ((c : ℝ) + 1) * (Real.exp (2 * (c : ℝ)) + 2 * (((c : ℝ) * Real.log c) ^ c / c !))
          * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c) := henv
    _ = ((c : ℝ) + 1) * Real.exp (2 * (c : ℝ)) * (stirlingU (saddleN c) * stirlingU c)
          / (saddleN c : ℝ) ^ (2 * c)
        + ((c : ℝ) + 1) * (2 * (((c : ℝ) * Real.log (c : ℝ)) ^ c / (c ! : ℝ)))
          * (stirlingU (saddleN c) * stirlingU c) / (saddleN c : ℝ) ^ (2 * c) := by ring
    _ ≤ Real.exp 1 * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c
        + (2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1) * Real.sqrt c
          * (1 / 2 : ℝ) ^ c := add_le_add hA hB'
    _ = (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
        * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c := by ring

/-- **Target 1 (A48)**: the saddle concentrates, `smallMass / m0sum → 0`. -/
theorem tendsto_smallMass_div_m0sum_zero :
    Filter.Tendsto (fun c : ℕ => smallMass c / m0sum c) Filter.atTop (nhds 0) := by
  have he4 : ∀ᶠ c : ℕ in atTop, Real.exp 1 / (4 * Real.log (c : ℝ)) ≤ 1 / 4 := by
    have hlog : Filter.Tendsto (fun c : ℕ => Real.log (c : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h1 : Filter.Tendsto (fun c : ℕ => (4 * Real.log (c : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
    have h2 := h1.const_mul (Real.exp 1)
    have h3 : Filter.Tendsto (fun c : ℕ => Real.exp 1 / (4 * Real.log (c : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_zero] using h2
    exact h3.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hmain : ∀ᶠ c : ℕ in atTop,
      smallMass c / m0sum c
        ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c := by
    filter_upwards [eventually_ge_atTop 163000,
      four_sqrt_clogc_log_le_eventually (ε := Real.log 2)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)),
      he4] with c hc163 hd he4c
    exact smallMass_div_m0sum_le_half_pow hc163 hd he4c
  have hzero : Filter.Tendsto
      (fun c : ℕ => (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
        * ((c : ℝ) + 1) * Real.sqrt (c : ℝ) * (1 / 2 : ℝ) ^ c) Filter.atTop (nhds 0) := by
    have hKnn : (0 : ℝ) ≤ Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi) := by positivity
    have hlim : Filter.Tendsto
        (fun c : ℕ => (2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)))
          * ((c : ℝ) ^ 2 * (1 / 2 : ℝ) ^ c)) Filter.atTop (nhds 0) := by
      have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2
        (show |(1 / 2 : ℝ)| < 1 by norm_num)
      have h2 := h.const_mul (2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)))
      simpa [mul_zero] using h2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · filter_upwards with c
      have h1 : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hKnn h1) (Real.sqrt_nonneg _))
        (pow_nonneg (by norm_num) _)
    · filter_upwards [eventually_ge_atTop 1] with c hc
      have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (c : ℝ) := by
        rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg c), one_pow]
        exact hcR
      have hsqrt_le : Real.sqrt (c : ℝ) ≤ c := by
        calc Real.sqrt (c : ℝ) = Real.sqrt (c : ℝ) * 1 := by ring
          _ ≤ Real.sqrt (c : ℝ) * Real.sqrt (c : ℝ) :=
              mul_le_mul_of_nonneg_left hsqrt1 (Real.sqrt_nonneg _)
          _ = c := Real.mul_self_sqrt (Nat.cast_nonneg _)
      have h1 : ((c : ℝ) + 1) ≤ 2 * (c : ℝ) := by linarith
      calc (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) + 1) * Real.sqrt (c : ℝ) * (1 / 2 : ℝ) ^ c
          ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * (2 * (c : ℝ)) * (c : ℝ) * (1 / 2 : ℝ) ^ c := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) c)
            apply mul_le_mul _ hsqrt_le (Real.sqrt_nonneg _) _
            · exact mul_le_mul_of_nonneg_left h1 hKnn
            · exact mul_nonneg hKnn (by linarith : (0 : ℝ) ≤ 2 * (c : ℝ))
        _ = (2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)))
            * ((c : ℝ) ^ 2 * (1 / 2 : ℝ) ^ c) := by ring
  exact squeeze_zero'
    (Eventually.of_forall fun c => div_nonneg (smallMass_nonneg c) (m0sum_pos c).le)
    hmain hzero

/-!
## A48 section 6: the bulk-D lower bound

The denominator mass on the large region dominates `(c²/4)(m0sum − smallMass)`
eventually: each large row's proper-edge second moment carries a factor
`c(c−1)·((n−1)/n)² ≥ (9/16)c(c−1)` relative to the row's last census term, and
the last census term is at least half the row mass when `n² ≥ 2c`.
-/

/-- Per-cell lower bound: the first term of `properSqSum_mul_pow4` alone. -/
theorem properSqSum_ge_sq_term {n k : ℕ} (hn : 1 ≤ n) :
    (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2) / (n : ℝ) ^ 4
      ≤ (properSqSum n k : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := pow_pos (by linarith) _
  have hid := properSqSum_mul_pow4 n k
  have hdrop : (0 : ℝ) ≤ (k : ℝ) * ((n : ℝ) - 1) * (n : ℝ) ^ (2 * k + 3) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (pow_nonneg (by linarith) _)
  have h1 : (k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2)
      ≤ (properSqSum n k : ℝ) * (n : ℝ) ^ 4 := by
    rw [hid]
    linarith [hdrop]
  exact (div_le_iff₀ hn4).2 h1

/-- Per-row lower bound: a large row's proper second moment is at least
`(9/16)·c(c−1)` times the row's last census term. -/
theorem properRow_ge {c n : ℕ} (hn : 4 ≤ n) (hc : 2 ≤ c) :
    (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1) * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
      ≤ ∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hsum : (∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2) / (n : ℝ) ^ 4)
        / ((n ! : ℝ) * (k ! : ℝ)))
      ≤ ∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
    Finset.sum_le_sum fun k _ =>
      div_le_div_of_nonneg_right (properSqSum_ge_sq_term (by omega : 1 ≤ n))
        (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  have hterm : ((c : ℝ) * ((c : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * c + 2)
        / (n : ℝ) ^ 4) / ((n ! : ℝ) * (c ! : ℝ))
      ≤ ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2) / (n : ℝ) ^ 4)
          / ((n ! : ℝ) * (k ! : ℝ)) := by
    have hmem : c ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
    have hf : ∀ i ∈ Finset.range (c + 1), (0 : ℝ) ≤
        ((i : ℝ) * ((i : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * i + 2) / (n : ℝ) ^ 4)
          / ((n ! : ℝ) * (i ! : ℝ)) := by
      intro i _
      rcases i with _ | m
      · simp
      · have hnm1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        have hkm1 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) - 1 := by
          have h1m : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
          linarith
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by linarith
        have h : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1)
            * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * (m + 1) + 2) :=
          mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hkm1)
            (pow_nonneg hnm1 _)) (pow_nonneg hnn _)
        exact div_nonneg (div_nonneg h (pow_nonneg hnn _))
          (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
    exact Finset.single_le_sum hf hmem
  have halg : ((c : ℝ) * ((c : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * c + 2)
        / (n : ℝ) ^ 4) / ((n ! : ℝ) * (c ! : ℝ))
      = ((n : ℝ) - 1) ^ 2 / (n : ℝ) ^ 2 * ((c : ℝ) * ((c : ℝ) - 1))
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    have hpow : (n : ℝ) ^ (2 * c + 2) = (n : ℝ) ^ (2 * c) * (n : ℝ) ^ 2 := by rw [← pow_add]
    rw [hpow]
    field_simp [(pow_pos (by linarith : (0 : ℝ) < n) 2).ne',
      (pow_pos (by linarith : (0 : ℝ) < n) 4).ne', (ffact_pos _).ne'] <;> ring
  have h34 : (9 / 16 : ℝ) ≤ ((n : ℝ) - 1) ^ 2 / (n : ℝ) ^ 2 := by
    have h1 : (3 / 4 : ℝ) ≤ ((n : ℝ) - 1) / n := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < n)]
      linarith
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) h1 2
    have e : ((n : ℝ) - 1) ^ 2 / (n : ℝ) ^ 2 = (((n : ℝ) - 1) / n) ^ 2 := (div_pow _ _ _).symm
    have h3 : (9 / 16 : ℝ) = (3 / 4) ^ 2 := by norm_num
    rw [e, h3]
    exact h2
  have hc1 : (0 : ℝ) ≤ (c : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
    linarith
  have hcoef : (0 : ℝ) ≤ (c : ℝ) * ((c : ℝ) - 1) := mul_nonneg (Nat.cast_nonneg _) hc1
  have hX : (0 : ℝ) ≤ (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)) := by positivity
  calc (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
      = (9 / 16 : ℝ) * ((c : ℝ) * ((c : ℝ) - 1))
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by ring
    _ ≤ (((n : ℝ) - 1) ^ 2 / (n : ℝ) ^ 2) * ((c : ℝ) * ((c : ℝ) - 1))
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h34 hcoef) hX
    _ = ((c : ℝ) * ((c : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * c + 2)
        / (n : ℝ) ^ 4) / ((n ! : ℝ) * (c ! : ℝ)) := halg.symm
    _ ≤ ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) * ((k : ℝ) - 1) * ((n : ℝ) - 1) ^ 2 * (n : ℝ) ^ (2 * k + 2) / (n : ℝ) ^ 4)
          / ((n ! : ℝ) * (k ! : ℝ)) := hterm
    _ ≤ ∑ k ∈ Finset.range (c + 1),
        (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := hsum

/-- **Bulk-D (A48)**: `(c²/4)·(m0sum − smallMass) ≤ dsum` for `c ≥ 9`.
The factor `(9/32)·c(c−1)` from the row comparison beats `c²/4` once `c ≥ 9`. -/
theorem bulk_dsum_lower {c : ℕ} (hc : 9 ≤ c) :
    (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) ≤ dsum c := by
  have hrow : ∀ n ∈ largeSet c,
      (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
        ≤ ∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
    fun n hn => properRow_ge (by have := largeSet_n_ge_five hc hn; omega) (by omega)
  have hlog2 : (2 : ℝ) ≤ Real.log (c : ℝ) := by
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by exact_mod_cast hc : (9 : ℝ) ≤ (c : ℝ))
    linarith [two_lt_log_nine]
  have hw : ∀ n ∈ largeSet c,
      wrow c n ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    intro n hn
    apply wrow_le_two_wterm
    rw [mem_largeSet] at hn
    have hlt : (2 : ℝ) * c < (n : ℝ) ^ 2 := calc
      (2 : ℝ) * c = (c : ℝ) * 2 := by ring
      _ ≤ (c : ℝ) * Real.log (c : ℝ) := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ < (n : ℝ) ^ 2 := hn.2
    exact hlt.le
  have hsplit : m0sum c - smallMass c = ∑ n ∈ largeSet c, wrow c n := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c) (wrow c)
    have hsm : (∑ n ∈ (Finset.range (c + 1)).filter
        (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c), wrow c n) = smallMass c := rfl
    have hlg : (∑ n ∈ (Finset.range (c + 1)).filter
        (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c), wrow c n)
        = ∑ n ∈ largeSet c, wrow c n := by
      apply Finset.sum_congr _ (fun _ _ => rfl)
      show (Finset.range (c + 1)).filter (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
          = (Finset.range (c + 1)).filter (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2)
      apply Finset.filter_congr
      intro n _
      exact not_le
    rw [hsm, hlg] at h
    have hm0 : m0sum c = smallMass c + ∑ n ∈ largeSet c, wrow c n := h.symm
    rw [hm0]
    ring
  have h1 : (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
      ≤ dsum c := by
    calc (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
          * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
        = ∑ n ∈ largeSet c, (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
          * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := Finset.sum_le_sum hrow
      _ ≤ ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx)
          fun n _ _ => Finset.sum_nonneg fun k _ => div_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
      _ = dsum c := rfl
  have h2 : m0sum c - smallMass c
      ≤ 2 * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    rw [hsplit]
    calc (∑ n ∈ largeSet c, wrow c n)
        ≤ ∑ n ∈ largeSet c, 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
          Finset.sum_le_sum hw
      _ = 2 * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
          rw [Finset.mul_sum]
  have hXnn : (0 : ℝ) ≤ ∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hcoef : (9 / 32 : ℝ) * ((c : ℝ) * ((c : ℝ) - 1)) ≥ (c : ℝ) ^ 2 / 4 := by
    have hcR : (9 : ℝ) ≤ c := by exact_mod_cast hc
    have hcpos : (0 : ℝ) < c := by linarith
    rw [ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hcR, hcpos]
  calc (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)
      ≤ (9 / 32 : ℝ) * ((c : ℝ) * ((c : ℝ) - 1)) * (m0sum c - smallMass c) := by
        apply mul_le_mul_of_nonneg_right hcoef
        rw [hsplit]
        exact Finset.sum_nonneg fun n _ => wrow_nonneg c n
    _ = (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * ((m0sum c - smallMass c) / 2) := by ring
    _ ≤ (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (sub_nonneg.2 (by exact_mod_cast (by omega : 1 ≤ c) : (1 : ℝ) ≤ (c : ℝ))))
        rw [ge_iff_le] at *
        linarith [h2]
    _ ≤ dsum c := h1

/-- Large-cell comparison: a large row's loop second moment is at most its
proper second moment scaled by `1/(√(c·log c) − 1)`. -/
theorem loopRow_le_properRow_div {c n : ℕ} (hn : 2 ≤ n) (hc : 3 ≤ c)
    (hlarge : (c : ℝ) * Real.log c < (n : ℝ) ^ 2) :
    (∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
      ≤ (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcl : (0 : ℝ) ≤ (c : ℝ) * Real.log c :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c)))
  have hsqrt1 : (1 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1), one_pow]
    exact one_lt_clogc hc
  have hterm : ∀ k ∈ Finset.range (c + 1),
      (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (properSqSum n k : ℝ) / (((n ! : ℝ) * (k ! : ℝ)) * ((n : ℝ) - 1)) := by
    intro k _
    have h := loopSqSum_le_properSqSum n k hn
    have hD : (0 : ℝ) < (n ! : ℝ) * (k ! : ℝ) := mul_pos (ffact_pos _) (ffact_pos _)
    rw [div_le_div_iff₀ hD (mul_pos hD hn1)]
    calc (loopSqSum n k : ℝ) * (((n ! : ℝ) * (k ! : ℝ)) * ((n : ℝ) - 1))
        = (loopSqSum n k * ((n : ℝ) - 1)) * ((n ! : ℝ) * (k ! : ℝ)) := by ring
      _ ≤ (properSqSum n k : ℝ) * ((n ! : ℝ) * (k ! : ℝ)) :=
          mul_le_mul_of_nonneg_right h hD.le
  have hsum1 : (∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
      ≤ (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        / ((n : ℝ) - 1) := by
    have e : (∑ k ∈ Finset.range (c + 1),
        (properSqSum n k : ℝ) / (((n ! : ℝ) * (k ! : ℝ)) * ((n : ℝ) - 1)))
        = (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
          / ((n : ℝ) - 1) := by
      have hterm2 : ∀ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / (((n ! : ℝ) * (k ! : ℝ)) * ((n : ℝ) - 1))
            = (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) / ((n : ℝ) - 1) := by
        intro k _
        rw [div_div]
      rw [Finset.sum_congr rfl hterm2,
        show (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            / ((n : ℝ) - 1)
          = (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            * ((n : ℝ) - 1)⁻¹ from div_eq_mul_inv _ _,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      exact div_eq_mul_inv _ _
    rw [← e]
    exact Finset.sum_le_sum hterm
  have hproper_nn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (c + 1),
      (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
    Finset.sum_nonneg fun k _ => div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  have hsqrtn : Real.sqrt ((c : ℝ) * Real.log c) < (n : ℝ) :=
    (Real.sqrt_lt hcl (Nat.cast_nonneg _)).2 hlarge
  have hle : (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        / ((n : ℝ) - 1)
      ≤ (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
    div_le_div_of_nonneg_left hproper_nn (sub_pos.2 hsqrt1)
      (by linarith : Real.sqrt ((c : ℝ) * Real.log c) - 1 ≤ (n : ℝ) - 1)
  exact hsum1.trans hle

/-- Named remaining gap for `mechanismBound → 0`: bulk `dsum` lower bound on
the large region, and large-cell comparison.  Concentration alone is not
sufficient. -/
def MechanismBoundClosureGap : Prop :=
  (∀ᶠ c : ℕ in atTop,
      (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) ≤ dsum c) ∧
    (∀ᶠ c : ℕ in atTop,
      ∀ n ∈ Finset.range (c + 1),
        (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
          (∑ k ∈ Finset.range (c + 1),
              (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            ≤ (∑ k ∈ Finset.range (c + 1),
                (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
              / (Real.sqrt ((c : ℝ) * Real.log c) - 1))

/-- **Target 2 (A48)**: the named closure gap holds. -/
theorem mechanismBoundClosureGap_holds : MechanismBoundClosureGap := by
  unfold MechanismBoundClosureGap
  constructor
  · filter_upwards [eventually_ge_atTop 9] with c hc
    exact bulk_dsum_lower hc
  · filter_upwards [eventually_ge_atTop 3] with c hc n _ hlarge hn2
    exact loopRow_le_properRow_div hn2 hc hlarge

/-!
## A48 section 7: assembly `mechanismBound → 0`

With concentration (target 1) and the two large-region facts (target 2), the
mechanism bound splits as `nsum = nsumSmall + nsumLarge`, the small part is
`≤ c²·smallMass`, the large part is `≤ dsum/(√(c·log c) − 1)`, and the bulk-D
bound turns `c²·smallMass/dsum` into `8·smallMass/m0sum`.
-/

theorem one_mem_smallSet {c : ℕ} (hc : 3 ≤ c) : 1 ∈ smallSet c := by
  have h1 : (1 : ℝ) ≤ (c : ℝ) * Real.log c := (one_lt_clogc hc).le
  show 1 ∈ (Finset.range (c + 1)).filter (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.2 (by omega), by simpa using h1⟩

theorem nsum_nonneg (c : ℕ) : 0 ≤ nsum c :=
  Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

theorem dsum_nonneg (c : ℕ) : 0 ≤ dsum c :=
  Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-- Large-region loop-second-moment mass. -/
noncomputable def nsumLarge (c : ℕ) : ℝ :=
  ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
    (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

theorem nsum_eq_small_add_large (c : ℕ) :
    nsum c = nsumSmall c + nsumLarge c := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
    (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
    (fun n => ∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
  have hsm : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
      = nsumSmall c := rfl
  have hlg : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
      = nsumLarge c := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    show (Finset.range (c + 1)).filter (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
        = (Finset.range (c + 1)).filter (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2)
    apply Finset.filter_congr
    intro n _
    exact not_le
  rw [hsm, hlg] at h
  exact h.symm

/-- The large-region loop mass is at most `dsum/(√(c·log c) − 1)`. -/
theorem nsumLarge_le_dsum_div {c : ℕ} (hc : 9 ≤ c) :
    nsumLarge c ≤ dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  have hsqrt1 : (1 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1), one_pow]
    exact one_lt_clogc (by omega : 3 ≤ c)
  have hper : ∀ n ∈ largeSet c,
      (∑ k ∈ Finset.range (c + 1), (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        ≤ (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
          / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
    intro n hn
    rw [mem_largeSet] at hn
    exact loopRow_le_properRow_div (largeSet_n_ge_two (by omega : 3 ≤ c)
      (mem_largeSet.2 hn)) (by omega : 3 ≤ c) hn.2
  have hsum : nsumLarge c
      ≤ (∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
    have e : (∑ n ∈ largeSet c,
        (∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
          / (Real.sqrt ((c : ℝ) * Real.log c) - 1))
        = (∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
            (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
          / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
      rw [show (∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
            (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            / (Real.sqrt ((c : ℝ) * Real.log c) - 1)
          = (∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
            (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            * (Real.sqrt ((c : ℝ) * Real.log c) - 1)⁻¹ from div_eq_mul_inv _ _,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      exact div_eq_mul_inv _ _
    rw [nsumLarge, ← e]
    exact Finset.sum_le_sum hper
  have hle : (∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
      (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))) ≤ dsum c :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_of_mem_filter x hx)
      fun n _ _ => Finset.sum_nonneg fun k _ => div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  exact hsum.trans (div_le_div_of_nonneg_right hle (sub_pos.2 hsqrt1).le)

/-- The assembled finite-c bound: once `smallMass/m0sum ≤ 1/2` and `c ≥ 9`,
`mechanismBound c ≤ 8·(smallMass/m0sum) + 1/(√(c·log c) − 1)`. -/
theorem mechanismBound_le {c : ℕ} (hc : 9 ≤ c) (hs : smallMass c / m0sum c ≤ 1 / 2) :
    mechanismBound c
      ≤ 8 * (smallMass c / m0sum c) + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  have hm0 := m0sum_pos c
  have hd := dsum_pos c (by omega : 2 ≤ c)
  have hsplit := nsum_eq_small_add_large c
  have hS : nsumSmall c ≤ (c : ℝ) ^ 2 * smallMass c := nsumSmall_le_c_sq_smallMass c
  have hL : nsumLarge c ≤ dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
    nsumLarge_le_dsum_div hc
  have hsm : smallMass c ≤ m0sum c / 2 := by
    rw [div_le_iff₀ hm0] at hs
    linarith
  have hsqrt1 : (1 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1), one_pow]
    exact one_lt_clogc (by omega : 3 ≤ c)
  have hbulk := bulk_dsum_lower hc
  have h8 : (c : ℝ) ^ 2 * m0sum c ≤ 8 * dsum c := by
    have h1 : (c : ℝ) ^ 2 / 4 * m0sum c - (c : ℝ) ^ 2 / 4 * smallMass c ≤ dsum c := by
      have h2 : (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)
          = (c : ℝ) ^ 2 / 4 * m0sum c - (c : ℝ) ^ 2 / 4 * smallMass c := by ring
      rw [h2] at hbulk
      exact hbulk
    have h3 : (c : ℝ) ^ 2 / 4 * smallMass c ≤ (c : ℝ) ^ 2 / 8 * m0sum c := by
      calc (c : ℝ) ^ 2 / 4 * smallMass c
          ≤ (c : ℝ) ^ 2 / 4 * (m0sum c / 2) :=
            mul_le_mul_of_nonneg_left hsm (by positivity)
        _ = (c : ℝ) ^ 2 / 8 * m0sum c := by ring
    have h4 : (c : ℝ) ^ 2 / 8 * m0sum c ≤ dsum c := by linarith
    calc (c : ℝ) ^ 2 * m0sum c = 8 * ((c : ℝ) ^ 2 / 8 * m0sum c) := by ring
      _ ≤ 8 * dsum c := by linarith
  have hds : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) - 1 := sub_pos.2 hsqrt1
  calc mechanismBound c = (nsumSmall c + nsumLarge c) / dsum c := by
        unfold mechanismBound
        rw [hsplit]
    _ = nsumSmall c / dsum c + nsumLarge c / dsum c := add_div _ _ _
    _ ≤ (c : ℝ) ^ 2 * smallMass c / dsum c
        + (dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) / dsum c :=
        add_le_add (div_le_div_of_nonneg_right hS hd.le)
          (div_le_div_of_nonneg_right hL hd.le)
    _ ≤ 8 * smallMass c / m0sum c + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
        apply add_le_add
        · rcases eq_or_lt_of_le (smallMass_nonneg c) with hsm0 | hsmpos
          · rw [← hsm0]
            simp
          · rw [div_le_div_iff₀ hd hm0]
            calc (c : ℝ) ^ 2 * smallMass c * m0sum c
                = smallMass c * ((c : ℝ) ^ 2 * m0sum c) := by ring
              _ ≤ smallMass c * (8 * dsum c) := mul_le_mul_of_nonneg_left h8 hsmpos.le
              _ = 8 * smallMass c * dsum c := by ring
        · have e : (dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) / dsum c
              = 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
            rw [div_div, mul_comm _ (dsum c), ← div_div, div_self hd.ne']
          rw [e]
    _ = 8 * (smallMass c / m0sum c) + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by ring

/-- **Target 3 (A48)**: the mechanism bound vanishes, `B(c) → 0`. -/
theorem tendsto_mechanismBound_zero :
    Filter.Tendsto (fun c : ℕ => mechanismBound c) Filter.atTop (nhds 0) := by
  have h1 := tendsto_smallMass_div_m0sum_zero
  have hs : ∀ᶠ c : ℕ in atTop, smallMass c / m0sum c ≤ 1 / 2 :=
    h1.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hmain : ∀ᶠ c : ℕ in atTop,
      mechanismBound c
        ≤ 8 * (smallMass c / m0sum c) + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
    filter_upwards [hs, eventually_ge_atTop 9] with c hsc hc
    exact mechanismBound_le hc hsc
  have hzero : Filter.Tendsto
      (fun c : ℕ => 8 * (smallMass c / m0sum c)
        + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) Filter.atTop (nhds 0) := by
    have h8 : Filter.Tendsto (fun c : ℕ => 8 * (smallMass c / m0sum c))
        Filter.atTop (nhds 0) := by
      have := h1.const_mul 8
      simpa using this
    have hclog : Filter.Tendsto (fun c : ℕ => (c : ℝ) * Real.log c)
        Filter.atTop Filter.atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      refine ⟨max 3 (Nat.ceil M), fun a ha => ?_⟩
      have h3 : 3 ≤ a := le_trans (le_max_left _ _) ha
      have hM : M ≤ (a : ℝ) := by
        have h := le_trans (le_max_right _ _) ha
        exact (Nat.le_ceil M).trans (by exact_mod_cast h)
      have hloga : (1 : ℝ) ≤ Real.log (a : ℝ) := by
        have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
          (by exact_mod_cast h3 : (3 : ℝ) ≤ a)
        linarith [one_lt_log_three]
      calc M ≤ (a : ℝ) * 1 := by rw [mul_one]; exact hM
        _ ≤ (a : ℝ) * Real.log (a : ℝ) :=
            mul_le_mul_of_nonneg_left hloga (Nat.cast_nonneg a)
    have hsqrtT : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c))
        Filter.atTop Filter.atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      by_cases hM : M ≤ 0
      · exact ⟨0, fun a _ => hM.trans (Real.sqrt_nonneg _)⟩
      · push_neg at hM
        obtain ⟨i, hi⟩ := (tendsto_atTop_atTop).1 hclog ((M + 1) ^ 2)
        exact ⟨max i 3, fun a ha => by
          have h1a : 1 ≤ a := le_trans (by omega : 1 ≤ 3) (le_trans (le_max_right _ _) ha)
          have h := hi a (le_trans (le_max_left _ _) ha)
          have hle : M + 1 ≤ Real.sqrt ((a : ℝ) * Real.log (a : ℝ)) :=
            (Real.le_sqrt (by linarith : (0 : ℝ) ≤ M + 1)
              (mul_nonneg (Nat.cast_nonneg _)
                (Real.log_nonneg (by exact_mod_cast h1a)))).2 h
          linarith⟩
    have h2 : Filter.Tendsto (fun c : ℕ => 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1))
        Filter.atTop (nhds 0) := by
      have hsub : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c) - 1)
          Filter.atTop Filter.atTop := by
        have := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) hsqrtT
        simpa [sub_eq_add_neg] using this
      have hinv := tendsto_inv_atTop_zero.comp hsub
      simpa [one_div] using hinv
    have := h8.add h2
    simpa using this
  exact squeeze_zero'
    (Eventually.of_forall fun c => div_nonneg (nsum_nonneg c) (dsum_nonneg c))
    hmain hzero

#print axioms sum_choose_sq_weighted
#print axioms loopSqSum_eq
#print axioms properSqSum_eq
#print axioms conditional_loop_sq_mean
#print axioms conditional_proper_sq_mean
#print axioms loopSqSum_le_properSqSum
#print axioms wrow_le_exp
#print axioms wrow_le_two_wterm
#print axioms factorial_upper
#print axioms factorial_lower
#print axioms m0_lower
#print axioms smallMass_le
#print axioms properSqSum_le_sq_pow
#print axioms loopSqSum_le_sq_pow
#print axioms loopSqSum_one
#print axioms properSqSum_one
#print axioms dsumSmall_le_c_sq_smallMass
#print axioms nsumSmall_le_c_sq_smallMass
#print axioms saddleN_le_c_of_nine
#print axioms four_log_le_self
#print axioms smallMass_div_m0sum_le_envelope
#print axioms clogc_pow_div_saddlen_pow_le
#print axioms stirlingU_div_factorial_le
#print axioms log_stirlingU_le
#print axioms log_stirlingU_saddlen_le
#print axioms four_sqrt_clogc_log_le_eventually
#print axioms stirlingU_saddlen_le_two_pow
#print axioms termA_le
#print axioms termB_le
#print axioms smallMass_div_m0sum_le_half_pow
#print axioms tendsto_smallMass_div_m0sum_zero
#print axioms properSqSum_ge_sq_term
#print axioms properRow_ge
#print axioms bulk_dsum_lower
#print axioms loopRow_le_properRow_div
#print axioms mechanismBoundClosureGap_holds
#print axioms nsumLarge_le_dsum_div
#print axioms mechanismBound_le
#print axioms tendsto_mechanismBound_zero

end Gap2M0Asymptotics

