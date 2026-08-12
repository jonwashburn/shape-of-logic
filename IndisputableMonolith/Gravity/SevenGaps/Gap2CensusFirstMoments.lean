import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusMeasure

/-!
# Gap 2 / C11 / A50: census first moments

The A49 arc proved the product-form census law and evaluated the two second
moments `E_μ[n_loop²] = nsum c / m0sum c` and `E_μ[n_proper²] = dsum c / m0sum c`
(`Gap2CensusMeasure.lean`).  The sharp rate `q(c) = (log c)/(2c²)·(1+o(1))`
needs the first moments as well: the residual of the loop count against the
count span is a *variance* object, and the variance separation
(`E[Var(n_loop ∣ n,k)] = E[n_loop²] − E[(k/n)²]`) is built from first and
second moments together.  This module supplies the first moments at kernel
strength, following the `expect_nloop_sq` pattern line by line:

* `sum_j_cellCount`: **the first-moment cell identity** (TARGET 1),
  `Σ_{j≤k} j·cellCount n k j = k·n^(2k−1)`, the binomial mean at loop
  probability `1/n`, multiplied through by the cell mass `n^(2k)`.  The
  identity holds at every `n k : ℕ`: at `n = 0, k ≥ 1` the cell is empty and
  both sides vanish; at `k = 0` both sides are `0`.
* `loopMeanSum`, `properMeanSum`: the cell first moments, with closed forms
  `k·n^(2k−1)` and `k·(n²−n)·(n²)^(k−1)` (the proper count `k − j` reversed to
  the loop count `j`, exchanging the roles of `n` and `n² − n`).
* `nmeanSum`, `dmeanSum`: the census first-moment sums, siblings of
  `nsum`, `dsum` at first order.
* `expect_nloop`, `expect_nproper`: **the census first moments**,
  `E_μ[n_loop] = nmeanSum c / m0sum c` and `E_μ[n_proper] = dmeanSum c / m0sum c`.

All results audit to the base triple `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file).  Classical choice enters only
through the enumeration of the finite orbit space; the counts are
constructive.
-/

namespace Gap2CensusFirstMoments

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Finset
open scoped Gap2CensusProductForm Nat

/-!
## Section 1: the first-moment cell identity
-/

/-- **The first-moment cell identity.**  The loop count summed against the
cell count is the binomial mean at loop probability `1/n`, multiplied through
by the cell mass:
`Σ_{j=0}^{k} j·C(k,j)·n^j·(n²−n)^(k−j) = k·n·(n + (n²−n))^(k−1) = k·n^(2k−1)`.
This is `sum_choose_weighted` at `a = n`, `b = n² − n` with
`add_sq_sub : n + (n² − n) = n²`, and it holds at every `n k : ℕ` (the
`n = 0, k ≥ 1` cell is empty: `cellCount 0 k j = 0`, and `0^(2k−1) = 0`). -/
theorem sum_j_cellCount (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), j * cellCount n k j) = k * n ^ (2 * k - 1) := by
  have hcell : ∀ j ∈ Finset.range (k + 1),
      j * cellCount n k j = j * Nat.choose k j * n ^ j * (n ^ 2 - n) ^ (k - j) :=
    fun j _ => by rw [cellCount]; ring
  rw [Finset.sum_congr rfl hcell, sum_choose_weighted n (n ^ 2 - n) k, add_sq_sub n]
  cases k with
  | zero => simp
  | succ m =>
    rw [Nat.add_one_sub_one, show 2 * (m + 1) - 1 = 2 * m + 1 from by omega,
      ← pow_mul, pow_succ]
    ring

/-- The loop first moment of the `(n, k)` cell, summed over the loop count:
the sibling of `loopSqSum` at first order. -/
def loopMeanSum (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), j * cellCount n k j

/-- Exact closed form of the loop first moment. -/
theorem loopMeanSum_eq (n k : ℕ) : loopMeanSum n k = k * n ^ (2 * k - 1) :=
  sum_j_cellCount n k

/-- The proper-edge first moment of the `(n, k)` cell, summed over the loop
count (the proper-edge count of a word with `j` loops is `k − j`). -/
def properMeanSum (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), (k - j) * cellCount n k j

/-- Reversal of the proper-edge first-moment sum: substituting `j ↦ k − j`
turns the proper-edge count `k − j` into the loop count `j`. -/
theorem properMeanSum_rev (n k : ℕ) :
    properMeanSum n k = ∑ j ∈ Finset.range (k + 1), j * cellCount n k (k - j) := by
  rw [properMeanSum,
    ← Finset.sum_range_reflect (fun j => (k - j) * cellCount n k j) (k + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
  have e : k + 1 - 1 - j = k - j := by omega
  show (k - (k + 1 - 1 - j)) * cellCount n k (k + 1 - 1 - j) = _
  rw [e, Nat.sub_sub_self hjk]

/-- Exact closed form of the proper-edge first moment: reverse the sum to
turn proper counts into loop counts, then apply `sum_choose_weighted` with
the roles of `n` and `n² − n` exchanged. -/
theorem properMeanSum_eq (n k : ℕ) :
    properMeanSum n k = k * (n ^ 2 - n) * (n ^ 2) ^ (k - 1) := by
  rw [properMeanSum_rev]
  have h : ∀ j ∈ Finset.range (k + 1),
      j * cellCount n k (k - j)
        = j * Nat.choose k j * (n ^ 2 - n) ^ j * n ^ (k - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    rw [cellCount, Nat.choose_symm hjk, Nat.sub_sub_self hjk]
    ring
  rw [Finset.sum_congr rfl h, sum_choose_weighted (n ^ 2 - n) n k,
    show n ^ 2 - n + n = n ^ 2 from Nat.sub_add_cancel (by
      rcases n with _ | m
      · simp
      · exact le_self_pow (by omega : (1 : ℕ) ≤ m + 1) (by decide : (2 : ℕ) ≠ 0))]

/-!
## Section 2: the census first-moment sums
-/

/-- The loop first-moment sum `NM(c) = Σ_{n,k} loopMeanSum(n,k)/(n!·k!)`: the
sibling of `nsum` at first order. -/
noncomputable def nmeanSum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    (loopMeanSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

/-- The proper first-moment sum `DM(c) = Σ_{n,k} properMeanSum(n,k)/(n!·k!)`:
the sibling of `dsum` at first order. -/
noncomputable def dmeanSum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    (properMeanSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

theorem nmeanSum_nonneg (c : ℕ) : 0 ≤ nmeanSum c :=
  Finset.sum_nonneg fun _n _ => Finset.sum_nonneg fun _k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

theorem dmeanSum_nonneg (c : ℕ) : 0 ≤ dmeanSum c :=
  Finset.sum_nonneg fun _n _ => Finset.sum_nonneg fun _k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-- The loop first-moment cell sum: the product-form weight times `j` summed
over the loop count is the `loopMeanSum` count over the factorial weight. -/
theorem sum_loop_mean_cell (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (j : ℝ))
    = (loopMeanSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hcast : ∀ j : ℕ, (cellCount n k j : ℝ) * (j : ℝ)
      = ((j * cellCount n k j : ℕ) : ℝ) := fun j => by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Nat.cast_sum]
  simp only [loopMeanSum]

/-- The proper first-moment cell sum: the product-form weight times `k − j`
summed over the loop count is the `properMeanSum` count over the factorial
weight. -/
theorem sum_proper_mean_cell (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (((k - j : ℕ) : ℝ)))
    = (properMeanSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hcast : ∀ j : ℕ, (cellCount n k j : ℝ) * (((k - j : ℕ) : ℝ))
      = (((k - j) * cellCount n k j : ℕ) : ℝ) := fun j => by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Nat.cast_sum]
  simp only [properMeanSum]

/-- **The loop first moment under the census law (TARGET 1):**
`E_μ[n_loop] = nmeanSum c / m0sum c`.  The shared normalization
`(c+1)·m0sum c` is what cancels in ratios. -/
theorem expect_nloop (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * nloop x) = nmeanSum c / m0sum c := by
  refine (expect_eq_product_sum c (fun _n _k j _t => (j : ℝ))).trans ?_
  simp_rw [sum_jt, sum_loop_mean_cell]
  simp_rw [← Finset.mul_sum]
  rw [← nmeanSum.eq_def]
  rw [censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-- **The proper-edge first moment under the census law (TARGET 1):**
`E_μ[n_proper] = dmeanSum c / m0sum c`. -/
theorem expect_nproper (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * nproper x) = dmeanSum c / m0sum c := by
  refine (expect_eq_product_sum c (fun _n k j _t => ((k - j : ℕ) : ℝ))).trans ?_
  simp_rw [sum_jt, sum_proper_mean_cell]
  simp_rw [← Finset.mul_sum]
  rw [← dmeanSum.eq_def]
  rw [censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

#print axioms sum_j_cellCount
#print axioms loopMeanSum_eq
#print axioms properMeanSum_eq
#print axioms expect_nloop
#print axioms expect_nproper

end Gap2CensusFirstMoments
