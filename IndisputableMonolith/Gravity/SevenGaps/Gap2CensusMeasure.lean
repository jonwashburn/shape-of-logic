import IndisputableMonolith.Gravity.SevenGaps.Gap2M0Asymptotics

/-!
# Gap 2 / C11 / A49: the census measure and the product-form expectation law

The A48 arc closed `mechanismBound c → 0` at kernel strength.  What kept the
ensemble statement `q(c) → 0` at DERIVED-UNFORMALIZED was the missing link
between the enumerated iso-class ensemble and the product-form weights: the
law saying that expectations under the census measure `μ_c` (isomorphism
classes weighted by `1/|Aut|`, normalized) are exactly the product-form
weighted sums behind `nsum`, `dsum` and `m0sum`.  A36 check A5 verifies this
numerically at caps 1 to 6, and the orbit-stabilizer identity it rests on is
kernel-checked per cell in `Gap2CensusProductForm.census_identity`.  This
module packages the ensemble as a finite probability space and proves the law
itself (A36 check A5, upgraded to THEOREM), then evaluates the two second
moments that the anomaly bound is made of:

  `E_μ[n_loop²]   = nsum c / m0sum c`
  `E_μ[n_proper²] = dsum c / m0sum c`.

The three sums share one normalization (`censusM0 c = (c+1)·m0sum c`, the
free tet label contributing the factor `c+1`), which cancels in the ratio:

  `E_μ[n_loop²] / E_μ[n_proper²] = nsum c / dsum c = mechanismBound c`.

## What is proved here

* `Ensemble c`: the cap-`c` ensemble type.  An element is an isomorphism
  class of the `(n, k, j)` cell (an orbit of `S_n × S_k` on ordered edge
  sequences with exactly `j` loops) together with the free tet label `t`.
* `classMass`, `μprob`: the `1/|Aut|` weight of a class and its
  normalization to a probability law; `classMass_pos`, `μprob_pos`,
  `censusM0_pos`, `sum_μprob` (the law is normalized: `Σ μprob = 1`).
* `total_mass`: the total ensemble mass is `censusM0 c`, the closed form of
  A36's `M0`.
* `expect_eq_product_sum` (**the law, A36 check A5**): for every observable
  `g` of the cell data `(nV, nE, n_loop, nT)`,
  `E_μ[g] = (1/M0)·Σ_{n,k,j,t} (cellCount n k j)/(n!·k!)·g n k j t`.
* `expect_nloop_sq`, `expect_nproper_sq`: the two second moments as the
  product-form sums `nsum c / m0sum c` and `dsum c / m0sum c`.
* `moment_ratio`: the ratio identity with the normalization cancelled,
  `E_μ[n_loop²]/E_μ[n_proper²] = mechanismBound c`.

All results audit to the base triple `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file).  Classical choice enters only
through the enumeration of the finite orbit space and the choice of orbit
representatives (`Quotient.out`); the counts themselves are constructive.
-/

namespace Gap2CensusMeasure

open Gap2CensusProductForm Gap2M0Asymptotics Finset
open scoped Gap2CensusProductForm Nat

/-- The cap-`c` census ensemble: an isomorphism class of the `(n, k, j)` cell
(an orbit of the census group `S_n × S_k` on ordered edge sequences with
exactly `j` loops) carrying the free tet-count label `t`.  This is the A36
ensemble: the `(nV, edge multiset, nT)` isomorphism classes of the frozen
C11 receipts, with `j` the loop count. -/
abbrev Ensemble (c : ℕ) :=
  Σ (n : Fin (c + 1)) (k : Fin (c + 1)) (j : Fin (k.1 + 1)) (_t : Fin (c + 1)),
    Quotient (MulAction.orbitRel (CensusGroup n.1 k.1) (Cell n.1 k.1 j.1))

/-- The un-normalized census mass of an ensemble element: `1/|Aut|` of the
class, the C11 weight.  The stabilizer cardinality is independent of the
chosen representative (`Quotient.out` picks one; any two choices are
conjugate, so the cardinality agrees). -/
noncomputable def classMass {c : ℕ} (x : Ensemble c) : ℚ :=
  1 / (Fintype.card (MulAction.stabilizer (CensusGroup x.1.1 x.2.1.1) x.2.2.2.2.out) : ℚ)

/-- The stabilizer is nonempty (it contains the identity), so every class
carries positive mass. -/
theorem classMass_pos {c : ℕ} (x : Ensemble c) : 0 < classMass x := by
  simp only [classMass]
  have hne : Nonempty (MulAction.stabilizer (CensusGroup x.1.1 x.2.1.1) x.2.2.2.2.out) :=
    ⟨1, Subgroup.one_mem _⟩
  have hcard : (0 : ℚ) <
      (Fintype.card (MulAction.stabilizer (CensusGroup x.1.1 x.2.1.1) x.2.2.2.2.out) : ℚ) :=
    Nat.cast_pos.2 Fintype.card_pos
  exact div_pos zero_lt_one hcard

/-- The normalization `M0` of the census law is positive at every cap: the
`(n, k) = (0, 0)` summand alone contributes `1`. -/
theorem censusM0_pos (c : ℕ) : 0 < censusM0 c := by
  simp only [censusM0]
  apply mul_pos (by positivity : (0 : ℚ) < (c + 1 : ℚ))
  apply Finset.sum_pos' (fun n _ => Finset.sum_nonneg fun k _ => by positivity)
  refine ⟨0, Finset.mem_range.2 (Nat.succ_pos c), ?_⟩
  apply Finset.sum_pos' (fun k _ => by positivity)
  refine ⟨0, Finset.mem_range.2 (Nat.succ_pos c), ?_⟩
  simp [Nat.factorial_zero]

/-- The per-cell orbit mass at `ℝ`: the real cast of
`Gap2CensusProductForm.census_identity`.  This is the orbit-stabilizer
identity behind A36 check A5, cell by cell. -/
theorem sum_inv_stab_cell (n k j : ℕ) :
    (∑ q : Quotient (MulAction.orbitRel (CensusGroup n k) (Cell n k j)),
      (1 : ℝ) / (Fintype.card (MulAction.stabilizer (CensusGroup n k) q.out) : ℝ))
    = (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (census_identity n k j)
  push_cast at h
  exact h

/-- A single `Fin`-indexed sum equals the corresponding range sum.  This is
`Fin.sum_univ_eq_sum_range` with the body given as an explicit function
application, the form in which the rewrite matches first-order. -/
theorem sum_fin_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    (∑ i : Fin m, F i.1) = ∑ i ∈ Finset.range m, F i :=
  Fin.sum_univ_eq_sum_range F m

/-- Four-level `Fin`-nested sums convert to range-nested sums.  Iterated
`Fin.sum_univ_eq_sum_range`, applied at term level with the body of each
level given explicitly (the rewrite form `?F ↑i` does not match nested sum
bodies syntactically, but `exact`/`.trans` checks the same equation up to
definitional equality, which handles the beta-redexes). -/
theorem sum_fin4 {M : Type*} [AddCommMonoid M] (c : ℕ) (F : ℕ → ℕ → ℕ → ℕ → M) :
    (∑ n : Fin (c + 1), ∑ k : Fin (c + 1), ∑ j : Fin (k.1 + 1), ∑ t : Fin (c + 1),
        F n.1 k.1 j.1 t.1)
      = ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1), F n k j t := by
  refine (Fin.sum_univ_eq_sum_range (fun a => ∑ k : Fin (c + 1), ∑ j : Fin (k.1 + 1),
      ∑ t : Fin (c + 1), F a k.1 j.1 t.1) (c + 1)).trans ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  refine (Fin.sum_univ_eq_sum_range (fun b => ∑ j : Fin (b + 1), ∑ t : Fin (c + 1),
      F n b j.1 t.1) (c + 1)).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (Fin.sum_univ_eq_sum_range (fun d => ∑ t : Fin (c + 1), F n k d t.1) (k + 1)).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Fin.sum_univ_eq_sum_range (F n k j) (c + 1)

/-- **Total mass.**  The un-normalized mass of the whole cap-`c` ensemble is
`M0 = (c+1)·Σ_{n,k} n^(2k)/(n!·k!)`: the per-cell census identity summed
over cells, the marginal `Σ_j cellCount = n^(2k)` (the binomial theorem at
`n + (n² − n) = n²`), and the free tet label contributing `c+1`. -/
theorem total_mass (c : ℕ) : (∑ x : Ensemble c, classMass x) = censusM0 c := by
  simp_rw [Fintype.sum_sigma]
  simp only [classMass]
  simp_rw [census_identity]
  rw [show (∑ n : Fin (c + 1), ∑ k : Fin (c + 1), ∑ j : Fin (k.1 + 1), ∑ _t : Fin (c + 1),
        (cellCount n.1 k.1 j.1 : ℚ) / ((n.1 ! : ℚ) * (k.1 ! : ℚ)))
      = ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          ∑ j ∈ Finset.range (k + 1), ∑ _t ∈ Finset.range (c + 1),
            (cellCount n k j : ℚ) / ((n ! : ℚ) * (k ! : ℚ))
      from sum_fin4 c (fun a b d _e => (cellCount a b d : ℚ) / ((a ! : ℚ) * (b ! : ℚ)))]
  have ht : ∀ n k j : ℕ, (∑ _t ∈ Finset.range (c + 1),
      (cellCount n k j : ℚ) / ((n ! : ℚ) * (k ! : ℚ)))
      = (c + 1 : ℚ) * ((cellCount n k j : ℚ) / ((n ! : ℚ) * (k ! : ℚ))) := by
    intro n k j
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  simp_rw [ht]
  simp_rw [← Finset.mul_sum]
  rw [censusM0]
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_div, ← Nat.cast_sum, margin_count]

/-- The census probability law `μ_c` on the cap-`c` ensemble: the A36 `μ`,
iso classes weighted by `1/|Aut|` and normalized by `M0`. -/
noncomputable def μprob (c : ℕ) (x : Ensemble c) : ℝ :=
  (classMass x : ℝ) / (censusM0 c : ℝ)

/-- Every class carries positive probability: the ensemble has no invisible
classes (this is what makes the `L²(μ_c)` inner product definite). -/
theorem μprob_pos (c : ℕ) (x : Ensemble c) : 0 < μprob c x := by
  simp only [μprob]
  exact div_pos (by exact_mod_cast classMass_pos x) (by exact_mod_cast censusM0_pos c)

/-- The law is normalized: `Σ_x μ_c(x) = 1`. -/
theorem sum_μprob (c : ℕ) : (∑ x : Ensemble c, μprob c x) = 1 := by
  have hnum : (∑ x : Ensemble c, (classMass x : ℝ)) = (censusM0 c : ℝ) := by
    exact_mod_cast total_mass c
  have hM : (0 : ℝ) < (censusM0 c : ℝ) := by exact_mod_cast censusM0_pos c
  simp only [μprob]
  rw [← Finset.sum_div, hnum, div_self hM.ne']

/-- The closed form of the normalization at `ℝ`:
`M0 = (c+1)·m0sum c`. -/
theorem censusM0_cast (c : ℕ) : (censusM0 c : ℝ) = ((c + 1 : ℕ) : ℝ) * m0sum c := by
  simp only [censusM0, m0sum, wrow]
  push_cast
  ring

/-- The `μprob`-weighted sum factors the normalization out of the sum, before
any rewriting of the summand (the factoring step alone, kept separate so the
product-sum normal form is not itself reshaped). -/
theorem sum_μprob_mul (c : ℕ) (F : Ensemble c → ℝ) :
    (∑ x : Ensemble c, μprob c x * F x)
      = (∑ x : Ensemble c, (classMass x : ℝ) * F x) / (censusM0 c : ℝ) := by
  simp only [μprob]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

/-- **The product-form census law (THEOREM, A36 check A5).**  The expectation
under the census measure `μ_c` of any observable `g` of the cell data
`(nV, nE, n_loop, nT)` is the product-form weighted sum: the orbit mass
`cellCount n k j / (n!·k!)` times the value, normalized by `M0`.  This is
exactly the statement check A5 verifies numerically at caps 1 to 6:
`w(n, k, j, t) = C(k,j)·n^j·(n²−n)^(k−j)/(n!·k!·M0)`. -/
theorem expect_eq_product_sum (c : ℕ) (g : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ x : Ensemble c, μprob c x * g x.1.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)
      = (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
            (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * g n k j t)
        / (censusM0 c : ℝ) := by
  rw [sum_μprob_mul c (fun x => g x.1.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)]
  congr 1
  simp_rw [Fintype.sum_sigma]
  simp only [classMass]
  push_cast
  simp_rw [← Finset.sum_mul]
  simp_rw [sum_inv_stab_cell]
  exact sum_fin4 c (fun a b d e => ((cellCount a b d : ℝ) / ((a ! : ℝ) * (b ! : ℝ))) * g a b d e)

/-- The vertex-count observable. -/
def nV {c : ℕ} (x : Ensemble c) : ℝ := x.1.1

/-- The edge-count observable. -/
def nE {c : ℕ} (x : Ensemble c) : ℝ := x.2.1.1

/-- The loop-count observable (the number of diagonal edges). -/
def nloop {c : ℕ} (x : Ensemble c) : ℝ := x.2.2.1.1

/-- The tet-count observable (the free label). -/
def nT {c : ℕ} (x : Ensemble c) : ℝ := x.2.2.2.1.1

/-- The proper-edge count `nE − n_loop` (natural subtraction; `j ≤ k` on the
ensemble, so no truncation occurs). -/
def nproper {c : ℕ} (x : Ensemble c) : ℝ := ((x.2.1.1 - x.2.2.1.1 : ℕ) : ℝ)

/-- The `(j, t)`-marginal of the product-form weight: the free tet label is
constant across each cell, so summing over it contributes the factor `c + 1`. -/
theorem sum_jt (c n k : ℕ) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), ∑ _t ∈ Finset.range (c + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * F j)
    = ((c + 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range (k + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * F j) := by
  simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- The loop second-moment cell sum: the product-form weight times `j²`
summed over the loop count is the `loopSqSum` count over the factorial weight. -/
theorem sum_loop_cell (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (j : ℝ) ^ 2)
    = (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hcast : ∀ j : ℕ, (cellCount n k j : ℝ) * (j : ℝ) ^ 2
      = ((j ^ 2 * cellCount n k j : ℕ) : ℝ) := fun j => by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Nat.cast_sum]
  simp only [loopSqSum]

/-- The proper second-moment cell sum: the product-form weight times `(k−j)²`
summed over the loop count is the `properSqSum` count over the factorial
weight. -/
theorem sum_proper_cell (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (((k - j : ℕ) : ℝ) ^ 2))
    = (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hcast : ∀ j : ℕ, (cellCount n k j : ℝ) * (((k - j : ℕ) : ℝ) ^ 2)
      = (((k - j) ^ 2 * cellCount n k j : ℕ) : ℝ) := fun j => by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Nat.cast_sum]
  simp only [properSqSum]

/-- The loop second moment under the census law is the product-form sum:
`E_μ[n_loop²] = nsum c / m0sum c`.  The shared normalization
`(c+1)·m0sum c` is what cancels in ratios. -/
theorem expect_nloop_sq (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nloop x) ^ 2) = nsum c / m0sum c := by
  refine (expect_eq_product_sum c (fun _n _k j _t => (j : ℝ) ^ 2)).trans ?_
  simp_rw [sum_jt, sum_loop_cell]
  simp_rw [← Finset.mul_sum]
  rw [← nsum.eq_def]
  rw [censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-- The proper-edge second moment under the census law:
`E_μ[n_proper²] = dsum c / m0sum c`. -/
theorem expect_nproper_sq (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nproper x) ^ 2) = dsum c / m0sum c := by
  refine (expect_eq_product_sum c (fun _n k j _t => ((k - j : ℕ) : ℝ) ^ 2)).trans ?_
  simp_rw [sum_jt, sum_proper_cell]
  simp_rw [← Finset.mul_sum]
  rw [← dsum.eq_def]
  rw [censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-- **The ratio identity.**  The ratio of the two census second moments is
the mechanism bound: the shared normalization `m0sum c` cancels.
`E_μ[n_loop²] / E_μ[n_proper²] = nsum c / dsum c = mechanismBound c`. -/
theorem moment_ratio (c : ℕ) (hc : 2 ≤ c) :
    (∑ x : Ensemble c, μprob c x * (nloop x) ^ 2)
      / (∑ x : Ensemble c, μprob c x * (nproper x) ^ 2)
      = mechanismBound c := by
  rw [expect_nloop_sq, expect_nproper_sq]
  simp only [mechanismBound]
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hd : (0 : ℝ) < dsum c := dsum_pos c hc
  field_simp [hm0.ne', hd.ne']

#print axioms total_mass
#print axioms expect_eq_product_sum
#print axioms expect_nloop_sq
#print axioms expect_nproper_sq
#print axioms moment_ratio
#print axioms sum_μprob
#print axioms sum_inv_stab_cell
#print axioms sum_jt
#print axioms sum_loop_cell
#print axioms sum_proper_cell
#print axioms censusM0_cast
#print axioms μprob_pos
#print axioms classMass_pos
#print axioms censusM0_pos

end Gap2CensusMeasure
