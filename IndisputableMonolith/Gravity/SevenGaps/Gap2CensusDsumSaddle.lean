import IndisputableMonolith.Gravity.SevenGaps.Gap2SharpRateGap

/-!
# Gap 2 / C11 / A51: the proper second moment's saddle first order (`dsum_saddle`)

This module proves the third field of `Gap2SharpRateGap.SharpRateGap` at kernel
strength:

  `dsum_saddle : Tendsto (fun c => dsum c / (c^2 * m0sum c)) atTop (nhds 1)`,

i.e. the proper second moment concentrates at its maximal scale,
`dsum c ~ c²·m0sum c`.  This is the two-sided concentration certificate for the
census mass itself: since `n_proper ≤ k ≤ c` per cell, `E_μ[n_proper²] ≤ c²`
always, and the theorem says the ratio approaches `1`.

## The argument (squeeze)

Per cell `(n,k)` with `n ≥ 1`, the conditional proper second moment is
`properSqSum n k / n^{2k} = (k(1−1/n))² + (k/n)(1−1/n)` (`conditional_proper_sq_mean`).
Write `ρ(n,k)` for this ratio; then `dsum c = Σ ρ·w` and `m0sum c = Σ w` against
the product-form weight `w = n^{2k}/(n!·k!)`.

* **Upper bound.**  `ρ(n,k) ≤ k² + k/n ≤ c² + c`, so `dsum c ≤ (c²+c)·m0sum c`
  and `dsum/(c²·m0sum) ≤ 1 + 1/c → 1`.
* **Lower bound.**  The deficit `c²·m0sum − dsum = Σ (c² − ρ)·w` splits at the
  A48 saddle scale `smallSet c = {n² ≤ c·log c}`:
  - small rows: `c² − ρ ≤ c²`, contributing `≤ c²·smallMass c`;
  - large rows (`n² > c·log c`, hence `2c ≤ n²` once `log c ≥ 2`): the per-cell
    deficit `c² − ρ ≤ (c²−k²) + 2k²/n`.  The `k`-deficit sums geometrically
    (`wrow_term_le`) to `≤ 4c·wrow`, and the `n`-deficit to `≤ 2(c²/n)·wrow
    ≤ 2(c²/√(c·log c))·wrow`.
  Dividing by `c²·m0sum` leaves `smallMass/m0sum + 4/c + 2/√(c·log c) → 0` by the
  A48 concentration theorem `tendsto_smallMass_div_m0sum_zero`.

The `n = 0` row is absorbed into `smallSet` (it holds `0² = 0 ≤ c·log c`), so no
separate `m0sum → ∞` step is needed.

No new axioms, no `sorry`, no `native_decide` on reals.  All results audit to
the base triple `[propext, Classical.choice, Quot.sound]` (`#print axioms` at
the end of the file).
-/

namespace Gap2CensusDsumSaddle

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Finset Filter

open scoped Nat

/-!
## Section 1: the cell weight and unfolding lemmas
-/

/-- The product-form weight of the `(n,k)` cell: `n^{2k}/(n!·k!)`, the summand
of `wrow`.  Naming it keeps the deficit algebra readable. -/
noncomputable def cellW (c n k : ℕ) : ℝ := (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

theorem cellW_eq (c n k : ℕ) :
    cellW c n k = (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := rfl

theorem wrow_eq_sum_cellW (c n : ℕ) :
    wrow c n = ∑ k ∈ Finset.range (c + 1), cellW c n k := rfl

theorem cellW_nonneg (c n k : ℕ) : 0 ≤ cellW c n k :=
  div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-- The top term of a row is at most the row. -/
theorem cellW_top_le_wrow (c n : ℕ) : cellW c n c ≤ wrow c n := by
  rw [wrow_eq_sum_cellW]
  exact Finset.single_le_sum (fun k _ => cellW_nonneg c n k)
    (Finset.mem_range.2 (Nat.lt_succ_self c))

/-- The conditional proper second moment ratio `E[n_proper² ∣ n,k]`. -/
noncomputable def properRatio (n k : ℕ) : ℝ :=
  ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 + (k / (n : ℝ)) * (1 - 1 / (n : ℝ))

theorem properRatio_eq (n k : ℕ) :
    properRatio n k
      = ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 + (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) := rfl

/-- `properSqSum` as the cell mass times the conditional ratio (needs `n ≠ 0`). -/
theorem properSqSum_eq_pow_mul_ratio (n k : ℕ) (hn : n ≠ 0) :
    (properSqSum n k : ℝ) = (n : ℝ) ^ (2 * k) * properRatio n k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := conditional_proper_sq_mean n k hn
  rw [div_eq_iff (pow_ne_zero _ hn')] at h
  rw [h, properRatio_eq]; ring

/-- The `n = 0` cell is empty: `properSqSum 0 k = 0`. -/
theorem properSqSum_zero_left (k : ℕ) : properSqSum 0 k = 0 := by
  rcases k with _ | m
  · rw [properSqSum, Finset.sum_range_one]; simp
  · exact Finset.sum_eq_zero fun j _ => by
      rw [cellCount_zero_left (by omega : 1 ≤ m + 1) j]; simp

/-- One cell of the proper second moment, as the ratio times the weight. -/
theorem pRow_cell (c n k : ℕ) (hn : n ≠ 0) :
    (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) = properRatio n k * cellW c n k := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [properSqSum_eq_pow_mul_ratio n k hn, cellW_eq]
  field_simp [(ffact_pos n).ne', (ffact_pos k).ne']

/-- The proper second-moment row: `Σ_k properSqSum n k/(n!·k!)`. -/
noncomputable def pRow (c n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))

theorem pRow_eq (c n : ℕ) :
    pRow c n = ∑ k ∈ Finset.range (c + 1), (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := rfl

theorem dsum_eq_sum_pRow (c : ℕ) : dsum c = ∑ n ∈ Finset.range (c + 1), pRow c n := rfl

theorem m0sum_eq (c : ℕ) : m0sum c = ∑ n ∈ Finset.range (c + 1), wrow c n := rfl

theorem pRow_nonneg (c n : ℕ) : 0 ≤ pRow c n := by
  rw [pRow_eq]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-!
## Section 2: per-cell bounds on the ratio
-/

/-- Upper bound on the conditional proper second moment: `ρ(n,k) ≤ c² + c`. -/
theorem properRatio_le (n k c : ℕ) (hn : 1 ≤ n) (hk : k ≤ c) :
    properRatio n k ≤ (c : ℝ) ^ 2 + c := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkc : (k : ℝ) ≤ c := by exact_mod_cast hk
  have h1n1 : (1 : ℝ) / n ≤ 1 := (div_le_one hnpos).2 hnR
  have h1n0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hsub0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by linarith
  have hsub1 : (1 : ℝ) - 1 / n ≤ 1 := by linarith
  have hkmul : (k : ℝ) * (1 - 1 / (n : ℝ)) ≤ k := by
    have h := mul_le_mul_of_nonneg_left hsub1 hkR
    rwa [mul_one] at h
  have hkmul0 : (0 : ℝ) ≤ (k : ℝ) * (1 - 1 / (n : ℝ)) := mul_nonneg hkR hsub0
  have hsq : ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hkmul0 hkmul 2
  have hk2 : (k : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 := pow_le_pow_left₀ hkR hkc 2
  have hterm2 : (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) ≤ c := by
    have hkn : (k : ℝ) / n ≤ k := div_le_self hkR hnR
    calc (k / (n : ℝ)) * (1 - 1 / (n : ℝ))
        ≤ (k / (n : ℝ)) * 1 := mul_le_mul_of_nonneg_left hsub1 (div_nonneg hkR hnpos.le)
      _ = k / (n : ℝ) := mul_one _
      _ ≤ k := hkn
      _ ≤ c := hkc
  calc properRatio n k
      = ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 + (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) := properRatio_eq n k
    _ ≤ (c : ℝ) ^ 2 + c := add_le_add (le_trans hsq hk2) hterm2

/-- Per-cell deficit bound: `c² − ρ(n,k) ≤ (c² − k²) + 2k²/n`. -/
theorem c_sq_sub_properRatio_le (n k c : ℕ) (hn : 1 ≤ n) (hk : k ≤ c) :
    (c : ℝ) ^ 2 - properRatio n k ≤ ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) + 2 * ((k : ℝ) ^ 2 / n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1n1 : (1 : ℝ) / n ≤ 1 := (div_le_one hnpos).2 hnR
  have hsub0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by linarith
  have hterm2 : (0 : ℝ) ≤ (k / (n : ℝ)) * (1 - 1 / (n : ℝ)) :=
    mul_nonneg (div_nonneg hkR hnpos.le) hsub0
  have hsq : (1 - 2 / (n : ℝ)) ≤ (1 - 1 / (n : ℝ)) ^ 2 := by
    have he : (1 - 1 / (n : ℝ)) ^ 2 = 1 - 2 / n + (1 / n) ^ 2 := by ring
    have hpos : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ 2 := by positivity
    linarith [he, hpos]
  have hk2 : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
  have hlo : (k : ℝ) ^ 2 * (1 - 2 / (n : ℝ)) ≤ properRatio n k := by
    have h1 : (k : ℝ) ^ 2 * (1 - 2 / (n : ℝ)) ≤ (k : ℝ) ^ 2 * (1 - 1 / (n : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hk2
    have h2 : (k : ℝ) ^ 2 * (1 - 1 / (n : ℝ)) ^ 2 = ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 := by ring
    calc (k : ℝ) ^ 2 * (1 - 2 / (n : ℝ)) ≤ (k : ℝ) ^ 2 * (1 - 1 / (n : ℝ)) ^ 2 := h1
      _ = ((k : ℝ) * (1 - 1 / (n : ℝ))) ^ 2 := h2
      _ ≤ properRatio n k := by
          rw [properRatio_eq]; exact le_add_of_nonneg_right hterm2
  have hstep : (c : ℝ) ^ 2 - properRatio n k ≤ (c : ℝ) ^ 2 - (k : ℝ) ^ 2 * (1 - 2 / (n : ℝ)) := by
    linarith [hlo]
  have heq : (c : ℝ) ^ 2 - (k : ℝ) ^ 2 * (1 - 2 / (n : ℝ))
      = ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) + 2 * ((k : ℝ) ^ 2 / n) := by
    field_simp [hnpos.ne']
    ring
  rw [heq] at hstep
  exact hstep

/-!
## Section 3: the weighted geometric sum and the k-deficit
-/

/-- The weighted geometric sum: `Σ_{k≤c} k·(1/2)^k = 2 − (c+2)/2^c`. -/
theorem weighted_geom_half (c : ℕ) :
    (∑ k ∈ Finset.range (c + 1), (k : ℝ) * (1 / 2) ^ k) = 2 - ((c : ℝ) + 2) / 2 ^ c := by
  induction c with
  | zero => rw [Finset.sum_range_one]; norm_num
  | succ c ih =>
    have h2c : (2 : ℝ) ^ c ≠ 0 := by positivity
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [div_pow, one_pow, pow_succ]
    field_simp [h2c]
    ring

theorem weighted_geom_half_le (c : ℕ) :
    (∑ k ∈ Finset.range (c + 1), (k : ℝ) * (1 / 2) ^ k) ≤ 2 := by
  rw [weighted_geom_half]
  have h : (0 : ℝ) ≤ ((c : ℝ) + 2) / 2 ^ c := by positivity
  linarith

/-- Reindexing: the reversed weighted sum equals the forward one. -/
theorem weighted_geom_rev (c : ℕ) :
    (∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k))
      = ∑ k ∈ Finset.range (c + 1), (k : ℝ) * (1 / 2) ^ k :=
  Finset.sum_range_reflect (fun j => (j : ℝ) * (1 / 2) ^ j) (c + 1)

theorem weighted_geom_rev_le (c : ℕ) :
    (∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k)) ≤ 2 := by
  rw [weighted_geom_rev]
  exact weighted_geom_half_le c

/-- For `2c ≤ n²`, the k-deficit row sum is at most twice the row. -/
theorem sum_sub_cellW_le_two_wrow (c n : ℕ) (hn : (2 : ℝ) * c ≤ (n : ℝ) ^ 2) :
    ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * cellW c n k ≤ 2 * wrow c n := by
  have hterm : ∀ k ∈ Finset.range (c + 1),
      ((c - k : ℕ) : ℝ) * cellW c n k
        ≤ ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k) * cellW c n c := by
    intro k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    have h1 : cellW c n k ≤ (1 / 2) ^ (c - k) * cellW c n c := wrow_term_le c n k hkc hn
    have h2 : (0 : ℝ) ≤ ((c - k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : ((c - k : ℕ) : ℝ) * cellW c n k
        ≤ ((c - k : ℕ) : ℝ) * ((1 / 2) ^ (c - k) * cellW c n c) :=
      mul_le_mul_of_nonneg_left h1 h2
    have h4 : ((c - k : ℕ) : ℝ) * ((1 / 2) ^ (c - k) * cellW c n c)
        = ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k) * cellW c n c := (mul_assoc _ _ _).symm
    rwa [h4] at h3
  calc ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * cellW c n k
      ≤ ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k) * cellW c n c :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * (1 / 2) ^ (c - k)) * cellW c n c := by
        rw [Finset.sum_mul]
    _ ≤ 2 * cellW c n c := by
        exact mul_le_mul_of_nonneg_right (weighted_geom_rev_le c) (cellW_nonneg c n c)
    _ ≤ 2 * wrow c n := by
        exact mul_le_mul_of_nonneg_left (cellW_top_le_wrow c n) (by norm_num)

/-- The k-deficit against the squared scale: `Σ (c²−k²)·w ≤ 4c·wrow`. -/
theorem sum_sq_sub_cellW_le (c n : ℕ) (hn : (2 : ℝ) * c ≤ (n : ℝ) ^ 2) :
    ∑ k ∈ Finset.range (c + 1), ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) * cellW c n k ≤ 4 * c * wrow c n := by
  have hterm : ∀ k ∈ Finset.range (c + 1),
      ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) * cellW c n k ≤ 2 * c * (((c - k : ℕ) : ℝ) * cellW c n k) := by
    intro k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    have hle : (c : ℝ) ^ 2 - (k : ℝ) ^ 2 ≤ 2 * (c : ℝ) * ((c - k : ℕ) : ℝ) := by
      have hkR : (k : ℝ) ≤ c := by exact_mod_cast hkc
      have hck : ((c - k : ℕ) : ℝ) = (c : ℝ) - k := Nat.cast_sub hkc
      have h1 : (c : ℝ) ^ 2 - (k : ℝ) ^ 2 = ((c : ℝ) - k) * ((c : ℝ) + k) := by ring
      have h2 : (c : ℝ) + k ≤ 2 * c := by linarith
      have h3 : (0 : ℝ) ≤ (c : ℝ) - k := by linarith
      rw [h1, hck]
      calc ((c : ℝ) - k) * ((c : ℝ) + k)
          ≤ ((c : ℝ) - k) * (2 * c) := mul_le_mul_of_nonneg_left h2 h3
        _ = 2 * c * ((c : ℝ) - k) := by ring
    have h5 := mul_le_mul_of_nonneg_right hle (cellW_nonneg c n k)
    have h6 : (2 * (c : ℝ) * ((c - k : ℕ) : ℝ)) * cellW c n k
        = 2 * c * (((c - k : ℕ) : ℝ) * cellW c n k) := mul_assoc _ _ _
    rwa [h6] at h5
  calc ∑ k ∈ Finset.range (c + 1), ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) * cellW c n k
      ≤ ∑ k ∈ Finset.range (c + 1), 2 * c * (((c - k : ℕ) : ℝ) * cellW c n k) :=
        Finset.sum_le_sum hterm
    _ = 2 * c * ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * cellW c n k := by
        rw [Finset.mul_sum]
    _ ≤ 2 * c * (2 * wrow c n) := by
        exact mul_le_mul_of_nonneg_left (sum_sub_cellW_le_two_wrow c n hn) (by positivity)
    _ = 4 * c * wrow c n := by ring

/-- The n-deficit against the squared scale: `Σ 2(k²/n)·w ≤ 2(c²/n)·wrow`. -/
theorem sum_k_sq_div_cellW_le (c n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (c + 1), (2 * ((k : ℝ) ^ 2 / n)) * cellW c n k
      ≤ 2 * ((c : ℝ) ^ 2 / n) * wrow c n := by
  have hterm : ∀ k ∈ Finset.range (c + 1),
      (2 * ((k : ℝ) ^ 2 / n)) * cellW c n k ≤ (2 * ((c : ℝ) ^ 2 / n)) * cellW c n k := by
    intro k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    have hk2 : (k : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hkc) 2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hkn : (k : ℝ) ^ 2 / (n : ℝ) ≤ (c : ℝ) ^ 2 / (n : ℝ) :=
      (div_le_div_iff_of_pos_right hnpos).2 hk2
    have hle : 2 * ((k : ℝ) ^ 2 / n) ≤ 2 * ((c : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_left hkn (by norm_num)
    exact mul_le_mul_of_nonneg_right hle (cellW_nonneg c n k)
  calc ∑ k ∈ Finset.range (c + 1), (2 * ((k : ℝ) ^ 2 / n)) * cellW c n k
      ≤ ∑ k ∈ Finset.range (c + 1), (2 * ((c : ℝ) ^ 2 / n)) * cellW c n k :=
        Finset.sum_le_sum hterm
    _ = (2 * ((c : ℝ) ^ 2 / n)) * ∑ k ∈ Finset.range (c + 1), cellW c n k := by
        rw [Finset.mul_sum]
    _ = (2 * ((c : ℝ) ^ 2 / n)) * wrow c n := by rw [← wrow_eq_sum_cellW]
    _ = 2 * ((c : ℝ) ^ 2 / n) * wrow c n := by ring

/-!
## Section 4: the saddle split and the deficit bound
-/

/-- The large region: rows whose square exceeds `c·log c` (complement of
`smallSet`). -/
noncomputable def largeSet (c : ℕ) : Finset ℕ :=
  (Finset.range (c + 1)).filter fun n => ¬ ((n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)

theorem smallSet_eq (c : ℕ) :
    smallSet c
      = (Finset.range (c + 1)).filter (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c) := rfl

theorem largeSet_eq (c : ℕ) :
    largeSet c
      = (Finset.range (c + 1)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)) := rfl

theorem smallMass_eq (c : ℕ) : smallMass c = ∑ n ∈ smallSet c, wrow c n := rfl

theorem largeSet_mem_ge_one {c n : ℕ} (hc : 1 ≤ c) (hn : n ∈ largeSet c) : 1 ≤ n := by
  rw [Nat.one_le_iff_ne_zero]
  intro hn0
  rw [largeSet_eq, Finset.mem_filter] at hn
  subst hn0
  have hnonneg : (0 : ℝ) ≤ (c : ℝ) * Real.log c :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hc))
  exact hn.2 (by simpa using hnonneg)

theorem largeSet_mem_two_c_le {c n : ℕ} (hlog : (2 : ℝ) ≤ Real.log c) (hn : n ∈ largeSet c) :
    (2 : ℝ) * c ≤ (n : ℝ) ^ 2 := by
  rw [largeSet_eq, Finset.mem_filter] at hn
  obtain ⟨_, hn2⟩ := hn
  push_neg at hn2
  have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h1 : (2 : ℝ) * c ≤ (c : ℝ) * Real.log c := by
    calc (2 : ℝ) * c = c * 2 := by ring
      _ ≤ c * Real.log c := mul_le_mul_of_nonneg_left hlog hcR
  linarith [hn2, h1]

/-- The per-row deficit above the saddle scale, in `n`-form. -/
theorem large_row_deficit_le (c n : ℕ) (hc : 1 ≤ c) (hlog : (2 : ℝ) ≤ Real.log c)
    (hn : n ∈ largeSet c) :
    (c : ℝ) ^ 2 * wrow c n - pRow c n ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / n)) * wrow c n := by
  have hn1 : 1 ≤ n := largeSet_mem_ge_one hc hn
  have hn0 : n ≠ 0 := by omega
  have hn2 : (2 : ℝ) * c ≤ (n : ℝ) ^ 2 := largeSet_mem_two_c_le hlog hn
  have heq : (c : ℝ) ^ 2 * wrow c n - pRow c n
      = ∑ k ∈ Finset.range (c + 1), ((c : ℝ) ^ 2 - properRatio n k) * cellW c n k := by
    rw [wrow_eq_sum_cellW, Finset.mul_sum, pRow_eq, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pRow_cell c n k hn0]
    ring
  rw [heq]
  have hterm : ∀ k ∈ Finset.range (c + 1),
      ((c : ℝ) ^ 2 - properRatio n k) * cellW c n k
        ≤ (((c : ℝ) ^ 2 - (k : ℝ) ^ 2) + 2 * ((k : ℝ) ^ 2 / n)) * cellW c n k := by
    intro k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    exact mul_le_mul_of_nonneg_right (c_sq_sub_properRatio_le n k c hn1 hkc) (cellW_nonneg c n k)
  calc ∑ k ∈ Finset.range (c + 1), ((c : ℝ) ^ 2 - properRatio n k) * cellW c n k
      ≤ ∑ k ∈ Finset.range (c + 1),
          (((c : ℝ) ^ 2 - (k : ℝ) ^ 2) + 2 * ((k : ℝ) ^ 2 / n)) * cellW c n k :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range (c + 1), ((c : ℝ) ^ 2 - (k : ℝ) ^ 2) * cellW c n k)
          + ∑ k ∈ Finset.range (c + 1), (2 * ((k : ℝ) ^ 2 / n)) * cellW c n k := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ 4 * c * wrow c n + 2 * ((c : ℝ) ^ 2 / n) * wrow c n := by
        exact add_le_add (sum_sq_sub_cellW_le c n hn2) (sum_k_sq_div_cellW_le c n hn1)
    _ = (4 * c + 2 * ((c : ℝ) ^ 2 / n)) * wrow c n := by ring

/-- The per-row deficit above the saddle scale, in `√(c·log c)`-form. -/
theorem large_row_deficit_le' (c n : ℕ) (hc : 2 ≤ c) (hlog : (2 : ℝ) ≤ Real.log c)
    (hn : n ∈ largeSet c) :
    (c : ℝ) ^ 2 * wrow c n - pRow c n
      ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * wrow c n := by
  have hn1 : 1 ≤ n := largeSet_mem_ge_one (by omega : 1 ≤ c) hn
  have hbase := large_row_deficit_le c n (by omega : 1 ≤ c) hlog hn
  have hsqrt_le_n : Real.sqrt ((c : ℝ) * Real.log c) ≤ n := by
    have hn' : n ∈ (Finset.range (c + 1)).filter
        (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)) := by
      rw [← largeSet_eq]; exact hn
    rw [Finset.mem_filter] at hn'
    obtain ⟨_, hn2⟩ := hn'
    push_neg at hn2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ((Real.sqrt_lt' hnpos).2 hn2).le
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) :=
    Real.sqrt_pos.2 (mul_pos (by exact_mod_cast (by omega : 0 < c))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))))
  have hterm : 2 * ((c : ℝ) ^ 2 / n) ≤ 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c)) := by
    have hinv : (1 : ℝ) / n ≤ 1 / Real.sqrt ((c : ℝ) * Real.log c) :=
      one_div_le_one_div_of_le hsqrt_pos hsqrt_le_n
    have hc2 : (0 : ℝ) ≤ 2 * (c : ℝ) ^ 2 := by positivity
    calc 2 * ((c : ℝ) ^ 2 / n) = 2 * (c : ℝ) ^ 2 * (1 / n) := by ring
      _ ≤ 2 * (c : ℝ) ^ 2 * (1 / Real.sqrt ((c : ℝ) * Real.log c)) :=
        mul_le_mul_of_nonneg_left hinv hc2
      _ = 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c)) := by ring
  have hwrow : (0 : ℝ) ≤ wrow c n := wrow_nonneg c n
  calc (c : ℝ) ^ 2 * wrow c n - pRow c n
      ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / n)) * wrow c n := hbase
    _ ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * wrow c n := by
        apply mul_le_mul_of_nonneg_right _ hwrow
        linarith [hterm]

/-- The deficit term of one row. -/
noncomputable def deficitTerm (c n : ℕ) : ℝ := (c : ℝ) ^ 2 * wrow c n - pRow c n

theorem deficitTerm_eq (c n : ℕ) :
    deficitTerm c n = (c : ℝ) ^ 2 * wrow c n - pRow c n := rfl

/-- **The deficit bound:** `c²·m0sum − dsum ≤ c²·smallMass + (4c + 2c²/√(c·log c))·m0sum`. -/
theorem c_sq_m0sum_sub_dsum_le (c : ℕ) (hc : 2 ≤ c) (hlog : (2 : ℝ) ≤ Real.log c) :
    (c : ℝ) ^ 2 * m0sum c - dsum c
      ≤ (c : ℝ) ^ 2 * smallMass c
        + (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * m0sum c := by
  have hdecomp : (c : ℝ) ^ 2 * m0sum c - dsum c
      = ∑ n ∈ Finset.range (c + 1), deficitTerm c n := by
    rw [dsum_eq_sum_pRow, m0sum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [deficitTerm_eq]
  have hsplit : (∑ n ∈ Finset.range (c + 1), deficitTerm c n)
      = (∑ n ∈ smallSet c, deficitTerm c n) + (∑ n ∈ largeSet c, deficitTerm c n) := by
    rw [smallSet_eq, largeSet_eq]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
      (fun n => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c) (deficitTerm c)).symm
  rw [hdecomp, hsplit]
  have hsmall : (∑ n ∈ smallSet c, deficitTerm c n) ≤ (c : ℝ) ^ 2 * smallMass c := by
    have hterm : ∀ n ∈ smallSet c, deficitTerm c n ≤ (c : ℝ) ^ 2 * wrow c n := by
      intro n _
      have hp : 0 ≤ pRow c n := pRow_nonneg c n
      rw [deficitTerm_eq]
      linarith
    calc (∑ n ∈ smallSet c, deficitTerm c n)
        ≤ ∑ n ∈ smallSet c, (c : ℝ) ^ 2 * wrow c n := Finset.sum_le_sum hterm
      _ = (c : ℝ) ^ 2 * ∑ n ∈ smallSet c, wrow c n := by rw [Finset.mul_sum]
      _ = (c : ℝ) ^ 2 * smallMass c := by rw [smallMass_eq]
  have hlarge : (∑ n ∈ largeSet c, deficitTerm c n)
      ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * m0sum c := by
    have hterm : ∀ n ∈ largeSet c, deficitTerm c n
        ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * wrow c n := by
      intro n hn
      exact large_row_deficit_le' c n hc hlog hn
    have hcoef : (0 : ℝ) ≤ 4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c)) := by
      have hsqrt_pos : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) :=
        Real.sqrt_pos.2 (mul_pos (by exact_mod_cast (by omega : 0 < c))
          (Real.log_pos (by exact_mod_cast (by omega : 1 < c))))
      positivity
    have hsub : (∑ n ∈ largeSet c, wrow c n) ≤ m0sum c := by
      rw [m0sum_eq]
      apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => wrow_nonneg c i)
      intro x hx
      rw [largeSet_eq, Finset.mem_filter] at hx
      exact hx.1
    calc (∑ n ∈ largeSet c, deficitTerm c n)
        ≤ ∑ n ∈ largeSet c,
            (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * wrow c n :=
          Finset.sum_le_sum hterm
      _ = (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c)))
            * ∑ n ∈ largeSet c, wrow c n := by rw [Finset.mul_sum]
      _ ≤ (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * m0sum c :=
          mul_le_mul_of_nonneg_left hsub hcoef
  exact add_le_add hsmall hlarge

/-!
## Section 5: the squeeze
-/

/-- The upper bound: `dsum c ≤ (c² + c)·m0sum c`. -/
theorem dsum_le (c : ℕ) : dsum c ≤ ((c : ℝ) ^ 2 + c) * m0sum c := by
  rw [dsum_eq_sum_pRow, m0sum_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : pRow c 0 = 0 := by
      rw [pRow_eq]
      apply Finset.sum_eq_zero
      intro k _
      rw [properSqSum_zero_left]; simp
    rw [h0]; exact mul_nonneg (by positivity) (wrow_nonneg c 0)
  · rw [pRow_eq, wrow_eq_sum_cellW, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.1 hk)
    rw [pRow_cell c n k hn0]
    exact mul_le_mul_of_nonneg_right
      (properRatio_le n k c (Nat.one_le_iff_ne_zero.2 hn0) hkc) (cellW_nonneg c n k)

/-- The upper ratio bound: `dsum/(c²·m0sum) ≤ 1 + 1/c`. -/
theorem dsum_div_le (c : ℕ) (hc : 1 ≤ c) : dsum c / ((c : ℝ) ^ 2 * m0sum c) ≤ 1 + 1 / (c : ℝ) := by
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := pow_pos hcR 2
  have h := dsum_le c
  rw [div_le_iff₀ (mul_pos hc2 hm0)]
  have heq : (1 + 1 / (c : ℝ)) * ((c : ℝ) ^ 2 * m0sum c) = ((c : ℝ) ^ 2 + c) * m0sum c := by
    field_simp [hcR.ne']
  rw [heq]
  exact h

/-- The lower ratio bound: `1 − (smallMass/m0sum + 4/c + 2/√(c·log c)) ≤ dsum/(c²·m0sum)`. -/
theorem one_sub_le_dsum_div (c : ℕ) (hc : 2 ≤ c) (hlog : (2 : ℝ) ≤ Real.log c) :
    1 - (smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c))
      ≤ dsum c / ((c : ℝ) ^ 2 * m0sum c) := by
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hcR : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := pow_pos hcR 2
  have hsqrt : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) :=
    Real.sqrt_pos.2 (mul_pos hcR (Real.log_pos (by exact_mod_cast (by omega : 1 < c))))
  have hdef := c_sq_m0sum_sub_dsum_le c hc hlog
  rw [le_div_iff₀ (mul_pos hc2 hm0)]
  have heq : (1 - (smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c)))
        * ((c : ℝ) ^ 2 * m0sum c)
      = (c : ℝ) ^ 2 * m0sum c
        - ((c : ℝ) ^ 2 * smallMass c
          + (4 * c + 2 * ((c : ℝ) ^ 2 / Real.sqrt ((c : ℝ) * Real.log c))) * m0sum c) := by
    field_simp [hm0.ne', hcR.ne', hsqrt.ne']
    ring
  rw [heq]
  linarith [hdef]

/-- **The proper second moment's saddle first order (TARGET: `dsum_saddle`).**
`dsum c ~ c²·m0sum c`: the two-sided concentration certificate for the census
mass.  This is the third field of `Gap2SharpRateGap.SharpRateGap`, proved here
at kernel strength. -/
theorem dsum_saddle :
    Filter.Tendsto (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c)) Filter.atTop (nhds 1) := by
  have hnat : Filter.Tendsto (fun c : ℕ => (c : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun c : ℕ => Real.log c) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hlog2 : ∀ᶠ c : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log c :=
    hlog.eventually (eventually_ge_atTop 2)
  have h1c : Filter.Tendsto (fun c : ℕ => (c : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hmono : (fun c : ℕ => (c : ℝ)) ≤ᶠ[Filter.atTop] (fun c : ℕ => (c : ℝ) * Real.log c) := by
    filter_upwards [hlog2] with c h2c
    have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    calc (c : ℝ) = c * 1 := by ring
      _ ≤ c * 2 := mul_le_mul_of_nonneg_left (by norm_num) hcR
      _ ≤ c * Real.log c := mul_le_mul_of_nonneg_left h2c hcR
  have hclogc : Filter.Tendsto (fun c : ℕ => (c : ℝ) * Real.log c) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono' Filter.atTop hmono hnat
  have hsqrt : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop Filter.atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hclogc
    simpa [Real.sqrt_eq_rpow] using h
  have h2sqrt : Filter.Tendsto (fun c : ℕ => 2 / Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp hsqrt).const_mul 2
    simpa [div_eq_mul_inv] using h
  have h4c : Filter.Tendsto (fun c : ℕ => 4 / (c : ℝ)) Filter.atTop (nhds 0) := by
    have h := h1c.const_mul 4
    simpa [div_eq_mul_inv] using h
  have hupper : ∀ᶠ c : ℕ in Filter.atTop, dsum c / ((c : ℝ) ^ 2 * m0sum c) ≤ 1 + 1 / (c : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with c hc
    exact dsum_div_le c hc
  have hlower : ∀ᶠ c : ℕ in Filter.atTop,
      1 - (smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c))
        ≤ dsum c / ((c : ℝ) ^ 2 * m0sum c) := by
    filter_upwards [eventually_ge_atTop 2, hlog2] with c hc h2c
    exact one_sub_le_dsum_div c hc h2c
  have hhi : Filter.Tendsto (fun c : ℕ => 1 + 1 / (c : ℝ)) Filter.atTop (nhds 1) := by
    have h : Filter.Tendsto (fun c : ℕ => (1 : ℝ) + (c : ℝ)⁻¹) Filter.atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add h1c
    simpa using h
  have hlo : Filter.Tendsto
      (fun c : ℕ => 1 - (smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c)))
      Filter.atTop (nhds 1) := by
    have hsum : Filter.Tendsto
        (fun c : ℕ => smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c))
        Filter.atTop (nhds (0 + 0 + 0)) :=
      (tendsto_smallMass_div_m0sum_zero.add h4c).add h2sqrt
    have h : Filter.Tendsto
        (fun c : ℕ => (1 : ℝ) - (smallMass c / m0sum c + 4 / (c : ℝ) + 2 / Real.sqrt ((c : ℝ) * Real.log c)))
        Filter.atTop (nhds (1 - (0 + 0 + 0))) :=
      tendsto_const_nhds.sub hsum
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi hlower hupper

#print axioms dsum_saddle

end Gap2CensusDsumSaddle
