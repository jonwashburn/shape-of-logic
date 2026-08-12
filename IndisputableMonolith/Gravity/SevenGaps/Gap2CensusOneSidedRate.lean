import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusVarianceSep

/-!
# Gap 2 / C11 / A50: the one-sided rate improvement (TARGET 3, one-sided half)

The A49 ensemble limit bounded the anomaly fraction by the raw second-moment
ratio and read off the explicit envelope

  `q(c) ≤ 8·(smallMass c / m0sum c) + 1/(√(c·log c) − 1)`,

which decays like `1/√(c·log c)`.  The A50 variance separation
(`Gap2CensusVarianceSep.qfrac_eval`) turns `q` into an evaluated ratio:

  `q(c) = (nvarSum c + ‖r(m)‖²·m0sum c) / dsum c`,

with `nvarSum c = nsum c − msqSum c` the conditional-variance numerator.  Per
cell the variance weight is `(k/n)·(1−1/n)·n^(2k)/(n!·k!)` and the mean-square
weight is `(k/n)²·n^(2k)/(n!·k!)`; against the A48 bulk lower bound
`dsum ≥ (c²/4)·(m0sum − smallMass)` these give a factor-`c`-ish improvement
over the raw second moment, whose cell weight is `≈ (k/n)² + k/n`.

## What is proved here (kernel strength, no new axioms, no sorry)

* `varSum`, `varSmall`, `varLarge`, `msqSmall`, `msqLarge`: the variance and
  mean-square sums and their small/large-region splits at the A48 split scale.
* `var_cell_id`, `varSum_eq_nvarSum`: the variance sum is exactly
  `nsum c − msqSum c`, cell by cell.
* `varSmall_le_c_smallMass`, `varLarge_le`, `msqSmall_le_c_sq_smallMass`,
  `msqLarge_le`: the four piece bounds from the split.
* `norm_sq_resid_obsM_le`: residual contraction, `‖r(m)‖² ≤ ‖m‖²`.
* `qfrac_le_one_sided`: **the improved one-sided explicit envelope**
  `q(c) ≤ 8·(1 + 1/c)·(smallMass c/m0sum c) + 8/(c·√(c·log c)) + 8/(c·log c)`,
  whose dominant term is `8/(c·log c)`.
* `smallMass_div_m0sum_mul_clogc_tendsto_zero`: the A48 exponential small-mass
  decay beats the polynomial factor `c·log c`.
* `qfrac_mul_clogc_eventually_le`: **the new rate** `q(c)·(c·log c) ≤ 17`
  eventually, i.e. `q(c) = O(1/(c·log c))`.
* `tendsto_qfrac_mul_sqrt_clogc_zero`: `q(c)·√(c·log c) → 0`, i.e.
  `q(c) = o(1/√(c·log c))`, strictly improving the A48 explicit envelope.

The remaining distance to the sharp `(log c)/(2c²)` is exactly the two-sided
saddle concentration at `n*` (`n*·log n* = 2c`): the bounds here all sit at the
A48 split scale `2√(c·log c)`, which is `o(n*)`.  That gap is named in
`Gap2SharpRateGap`.

All results audit to the base triple `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file).
-/

namespace Gap2CensusOneSidedRate

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Finset Filter
open scoped Gap2CensusProductForm Nat RealInnerProductSpace

/-!
## Section 1: the variance sum and its cell identity
-/

/-- The conditional-variance sum: per cell `(k/n)·(1−1/n)·n^(2k)/(n!·k!)`,
the census conditional variance of the loop count times `m0sum c`. -/
noncomputable def varSum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The variance sum restricted to the small region. -/
noncomputable def varSmall (c : ℕ) : ℝ :=
  ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The variance sum restricted to the large region. -/
noncomputable def varLarge (c : ℕ) : ℝ :=
  ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The mean-square sum restricted to the small region. -/
noncomputable def msqSmall (c : ℕ) : ℝ :=
  ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The mean-square sum restricted to the large region. -/
noncomputable def msqLarge (c : ℕ) : ℝ :=
  ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

/-- The variance cell identity: the loop second moment minus the mean-square
is the conditional-variance weight, `(k/n)·(1−1/n)·n^(2k)`.  At `n = 0` every
side is `0` (the empty cells carry no mass). -/
theorem var_cell_id (n k : ℕ) :
    (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
      - ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      = ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [loopSqSum_eq]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hnf : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hkf : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    have hls : (loopSqSum n k : ℝ)
        = ((k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) ^ (2 * k) + (k : ℝ) * (n : ℝ) ^ (2 * k + 1))
          / (n : ℝ) ^ 2 :=
      (eq_div_iff_mul_eq (pow_ne_zero 2 hnR)).2 (loopSqSum_mul_sq n k)
    rw [hls]
    field_simp [hnR, hnf, hkf]
    ring

/-- The variance sum is exactly the A50 numerator `nsum c − msqSum c`. -/
theorem varSum_eq_nvarSum (c : ℕ) : varSum c = nvarSum c := by
  rw [nvarSum.eq_def, nsum, msqSum, varSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact (var_cell_id n k).symm

/-- The variance sum splits at the A48 split scale. -/
theorem varSum_eq_small_add_large (c : ℕ) :
    varSum c = varSmall c + varLarge c := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
    (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
    (fun n => ∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
  have hsm : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
      = varSmall c := rfl
  have hlg : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
      = varLarge c := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    show (Finset.range (c + 1)).filter (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
        = (Finset.range (c + 1)).filter (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2)
    apply Finset.filter_congr
    intro n _
    exact not_le
  rw [hsm, hlg] at h
  exact h.symm

/-- The mean-square sum splits at the A48 split scale. -/
theorem msqSum_eq_small_add_large (c : ℕ) :
    msqSum c = msqSmall c + msqLarge c := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
    (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
    (fun n => ∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
  have hsm : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
      = msqSmall c := rfl
  have hlg : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c),
      ∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)))
      = msqLarge c := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    show (Finset.range (c + 1)).filter (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
        = (Finset.range (c + 1)).filter (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2)
    apply Finset.filter_congr
    intro n _
    exact not_le
  rw [hsm, hlg] at h
  exact h.symm

/-!
## Section 2: the four piece bounds
-/

/-- The per-cell variance weight is at most `c` times the mass weight:
`(k/n)·(1−1/n) ≤ k ≤ c` for `k ≤ c` (and the `n = 0` row is `0`). -/
theorem var_cell_le (c n k : ℕ) (hk : k ≤ c) :
    ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ (c : ℝ) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
  have hW : (0 : ℝ) ≤ (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  rcases eq_or_ne n 0 with rfl | hn
  · have hW0 : (0 : ℝ) ≤ (0 : ℝ) ^ (2 * k) / (((0 : ℕ)! : ℝ) * (k ! : ℝ)) := by positivity
    simp only [Nat.cast_zero, div_zero, zero_mul, zero_div]
    exact mul_nonneg (Nat.cast_nonneg _) hW0
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hcoef : ((k : ℝ) / n) * (1 - 1 / n) ≤ (c : ℝ) := by
      have hkn : (k : ℝ) / n ≤ (k : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
        calc (k : ℝ) = k * 1 := by ring
          _ ≤ k * n := mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg _)
      have h11 : (1 : ℝ) - 1 / n ≤ 1 := by
        have h1nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        linarith
      have hkn0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
      calc ((k : ℝ) / n) * (1 - 1 / n)
          ≤ (k : ℝ) / n * 1 := mul_le_mul_of_nonneg_left h11 hkn0
        _ = (k : ℝ) / n := by ring
        _ ≤ (k : ℝ) := hkn
        _ ≤ (c : ℝ) := by exact_mod_cast hk
    calc ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        = (((k : ℝ) / n) * (1 - 1 / n))
          * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
      _ ≤ (c : ℝ) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef hW

/-- On a large row (`n² > c·log c`) the variance weight is at most
`(c/√(c·log c))` times the mass weight. -/
theorem var_cell_large_le {c n k : ℕ} (hc : 9 ≤ c) (hn : n ∈ largeSet c) (hk : k ≤ c) :
    ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c))
          * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
  rw [mem_largeSet] at hn
  obtain ⟨hnr, hnl⟩ := hn
  have hn5 : 5 ≤ n := largeSet_n_ge_five hc (mem_largeSet.2 ⟨hnr, hnl⟩)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hclog1 : (1 : ℝ) < (c : ℝ) * Real.log c := one_lt_clogc (by omega : 3 ≤ c)
  have hsqrt : Real.sqrt ((c : ℝ) * Real.log c) < (n : ℝ) := (Real.sqrt_lt' hn0).2 hnl
  have hW : (0 : ℝ) ≤ (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  have hcoef : ((k : ℝ) / n) * (1 - 1 / n)
      ≤ (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) := by
    have h11 : (1 : ℝ) - 1 / n ≤ 1 := by
      have h1nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    have hkn0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
    have hkc : (k : ℝ) ≤ (c : ℝ) := by exact_mod_cast hk
    calc ((k : ℝ) / n) * (1 - 1 / n)
        ≤ (k : ℝ) / n * 1 := mul_le_mul_of_nonneg_left h11 hkn0
      _ = (k : ℝ) / n := by ring
      _ ≤ (c : ℝ) / n := div_le_div_of_nonneg_right hkc hn0.le
      _ ≤ (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (Real.sqrt_pos.2 (by linarith : (0 : ℝ) < (c : ℝ) * Real.log c)) hsqrt.le
  calc ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      = (((k : ℝ) / n) * (1 - 1 / n))
        * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
    _ ≤ ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c))
        * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
      mul_le_mul_of_nonneg_right hcoef hW

/-- The per-cell mean-square weight is at most `c²` times the mass weight. -/
theorem msq_cell_le (c n k : ℕ) (hk : k ≤ c) :
    ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
  have hW : (0 : ℝ) ≤ (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  rcases eq_or_ne n 0 with rfl | hn
  · have hW0 : (0 : ℝ) ≤ (0 : ℝ) ^ (2 * k) / (((0 : ℕ)! : ℝ) * (k ! : ℝ)) := by positivity
    simp only [Nat.cast_zero, div_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num),
      zero_mul, zero_div]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hW0
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hcoef : ((k : ℝ) / n) ^ 2 ≤ (c : ℝ) ^ 2 := by
      have hkn : (k : ℝ) / n ≤ (k : ℝ) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ))]
        calc (k : ℝ) = k * 1 := by ring
          _ ≤ k * n := mul_le_mul_of_nonneg_left hn1 (Nat.cast_nonneg _)
      have hkn0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
      exact le_trans (pow_le_pow_left₀ hkn0 hkn 2)
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hk) 2)
    calc ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        = (((k : ℝ) / n) ^ 2) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
      _ ≤ (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef hW

/-- On a large row the mean-square weight is at most `(c/log c)` times the
mass weight: `(k/n)² ≤ c²/n² ≤ c²/(c·log c) = c/log c`. -/
theorem msq_cell_large_le {c n k : ℕ} (hc : 9 ≤ c) (hn : n ∈ largeSet c) (hk : k ≤ c) :
    ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      ≤ ((c : ℝ) / Real.log (c : ℝ))
          * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
  rw [mem_largeSet] at hn
  obtain ⟨hnr, hnl⟩ := hn
  have hn5 : 5 ≤ n := largeSet_n_ge_five hc (mem_largeSet.2 ⟨hnr, hnl⟩)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hclog1 : (1 : ℝ) < (c : ℝ) * Real.log c := one_lt_clogc (by omega : 3 ≤ c)
  have hc9 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hlog : (0 : ℝ) < Real.log (c : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hW : (0 : ℝ) ≤ (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) :=
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
  have hdp : ((k : ℝ) / (n : ℝ)) ^ 2 = (k : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [sq, sq, sq, div_mul_div_comm]
  have hcc : (c : ℝ) ^ 2 / ((c : ℝ) * Real.log c) = (c : ℝ) / Real.log c := by
    rw [div_eq_div_iff (mul_pos hc9 hlog).ne' hlog.ne', sq]
    ring
  have hcoef : ((k : ℝ) / n) ^ 2 ≤ (c : ℝ) / Real.log (c : ℝ) := by
    have hkc : (k : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hk) 2
    rw [hdp, ← hcc]
    exact le_trans (div_le_div_of_nonneg_right hkc (pow_nonneg (Nat.cast_nonneg _) _))
      (div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg _) _)
        (by linarith : (0 : ℝ) < (c : ℝ) * Real.log c) hnl.le)
  calc ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
      = (((k : ℝ) / n) ^ 2) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by ring
    _ ≤ ((c : ℝ) / Real.log (c : ℝ))
        * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) :=
      mul_le_mul_of_nonneg_right hcoef hW

/-- The small-region variance sum is at most `c·smallMass c`. -/
theorem varSmall_le_c_smallMass (c : ℕ) :
    varSmall c ≤ (c : ℝ) * smallMass c := by
  have hterm : ∀ n ∈ smallSet c, ∀ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (c : ℝ) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n _ k hk
    exact var_cell_le c n k (Nat.lt_succ_iff.mp (Finset.mem_range.1 hk))
  calc varSmall c
      ≤ ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
          (c : ℝ) * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
        exact Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = ∑ n ∈ smallSet c, (c : ℝ) * wrow c n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [wrow, ← Finset.mul_sum]
    _ = (c : ℝ) * smallMass c := by
        rw [smallMass, ← Finset.mul_sum]

/-- The large-region variance sum is at most `(c/√(c·log c))·m0sum c`. -/
theorem varLarge_le {c : ℕ} (hc : 9 ≤ c) :
    varLarge c
      ≤ ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) * m0sum c := by
  have hterm : ∀ n ∈ largeSet c, ∀ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c))
          * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n hn k hk
    exact var_cell_large_le hc hn (Nat.lt_succ_iff.mp (Finset.mem_range.1 hk))
  have hsub : largeSet c ⊆ Finset.range (c + 1) := Finset.filter_subset _ _
  have hcoef : (0 : ℝ) ≤ (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) :=
    div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  calc varLarge c
      ≤ ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
          ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c))
            * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
        exact Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = ∑ n ∈ largeSet c,
          ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) * wrow c n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [wrow, ← Finset.mul_sum]
    _ = ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) * (∑ n ∈ largeSet c, wrow c n) := by
        rw [← Finset.mul_sum]
    _ ≤ ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) * m0sum c := by
        rw [m0sum]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => wrow_nonneg c n) hcoef

/-- The small-region mean-square sum is at most `c²·smallMass c`. -/
theorem msqSmall_le_c_sq_smallMass (c : ℕ) :
    msqSmall c ≤ (c : ℝ) ^ 2 * smallMass c := by
  have hterm : ∀ n ∈ smallSet c, ∀ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n _ k hk
    exact msq_cell_le c n k (Nat.lt_succ_iff.mp (Finset.mem_range.1 hk))
  calc msqSmall c
      ≤ ∑ n ∈ smallSet c, ∑ k ∈ Finset.range (c + 1),
          (c : ℝ) ^ 2 * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
        exact Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = ∑ n ∈ smallSet c, (c : ℝ) ^ 2 * wrow c n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [wrow, ← Finset.mul_sum]
    _ = (c : ℝ) ^ 2 * smallMass c := by
        rw [smallMass, ← Finset.mul_sum]

/-- The large-region mean-square sum is at most `(c/log c)·m0sum c`. -/
theorem msqLarge_le {c : ℕ} (hc : 9 ≤ c) :
    msqLarge c ≤ ((c : ℝ) / Real.log (c : ℝ)) * m0sum c := by
  have hlog : (0 : ℝ) < Real.log (c : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hterm : ∀ n ∈ largeSet c, ∀ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))
        ≤ ((c : ℝ) / Real.log (c : ℝ))
          * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n hn k hk
    exact msq_cell_large_le hc hn (Nat.lt_succ_iff.mp (Finset.mem_range.1 hk))
  have hsub : largeSet c ⊆ Finset.range (c + 1) := Finset.filter_subset _ _
  have hcoef : (0 : ℝ) ≤ (c : ℝ) / Real.log (c : ℝ) := div_nonneg (Nat.cast_nonneg _) hlog.le
  calc msqLarge c
      ≤ ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
          ((c : ℝ) / Real.log (c : ℝ))
            * ((n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
        exact Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun k hk => hterm n hn k hk
    _ = ∑ n ∈ largeSet c, ((c : ℝ) / Real.log (c : ℝ)) * wrow c n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [wrow, ← Finset.mul_sum]
    _ = ((c : ℝ) / Real.log (c : ℝ)) * (∑ n ∈ largeSet c, wrow c n) := by
        rw [← Finset.mul_sum]
    _ ≤ ((c : ℝ) / Real.log (c : ℝ)) * m0sum c := by
        rw [m0sum]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => wrow_nonneg c n) hcoef

/-- Residual contraction: the mean residual is bounded by the mean norm,
`‖r(m)‖² ≤ ‖m‖² = msqSum c / m0sum c` (the test function `y = 0`). -/
theorem norm_sq_resid_obsM_le (c : ℕ) :
    ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
      ≤ msqSum c / m0sum c := by
  have h0 : (0 : L2fun c) ∈ countSpan (obsV c) (obsE c) (obsT c) :=
    Submodule.zero_mem _
  have h := Gap2CensusVarianceSep.norm_sq_resid_le_of_mem_span c (obsM c) 0 h0
  rw [sub_zero, Gap2CensusVarianceSep.norm_sq_obsM] at h
  exact h

/-!
## Section 3: the improved one-sided envelope
-/

/-- **The improved one-sided rate (TARGET 3, one-sided half).**  At caps
`c ≥ 9` with `smallMass c/m0sum c ≤ 1/2`,

  `q(c) ≤ 8·(1 + 1/c)·(smallMass c/m0sum c) + 8/(c·√(c·log c)) + 8/(c·log c)`.

The dominant term is `8/(c·log c)`: a full factor of `√(c·log c)` better than
the A48 explicit envelope `1/(√(c·log c) − 1)`.  The mechanism is the A50
variance separation: the variance numerator per cell is `(k/n)(1−1/n)` (one
power of `k/n` smaller than the raw second moment on large rows), and the
mean-residual is bounded by the mean-square `(k/n)²`, against
`dsum ≥ (c²/4)(m0sum − smallMass)`. -/
theorem qfrac_le_one_sided {c : ℕ} (hc : 9 ≤ c) (hs : smallMass c / m0sum c ≤ 1 / 2) :
    qfrac c ≤ 8 * (1 + 1 / (c : ℝ)) * (smallMass c / m0sum c)
      + 8 / ((c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c))
      + 8 / ((c : ℝ) * Real.log c) := by
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hd : (0 : ℝ) < dsum c := dsum_pos c (by omega : 2 ≤ c)
  have hc9 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hlog : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hclog : (0 : ℝ) < (c : ℝ) * Real.log c := mul_pos hc9 hlog
  have hsqrt : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := Real.sqrt_pos.2 hclog
  have hvS := varSmall_le_c_smallMass c
  have hvL := varLarge_le hc
  have hmS := msqSmall_le_c_sq_smallMass c
  have hmL := msqLarge_le hc
  have hsplit_v := varSum_eq_small_add_large c
  have hsplit_m := msqSum_eq_small_add_large c
  have hnv := varSum_eq_nvarSum c
  have hrm := norm_sq_resid_obsM_le c
  have hbulk := bulk_dsum_lower hc
  have hsm : smallMass c ≤ m0sum c / 2 := by
    rw [div_le_iff₀ hm0] at hs
    linarith
  have hd_low : (c : ℝ) ^ 2 / 8 * m0sum c ≤ dsum c := by
    have h1 : (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)
        = (c : ℝ) ^ 2 / 4 * m0sum c - (c : ℝ) ^ 2 / 4 * smallMass c := by ring
    have h2 : (c : ℝ) ^ 2 / 4 * smallMass c ≤ (c : ℝ) ^ 2 / 8 * m0sum c := by
      calc (c : ℝ) ^ 2 / 4 * smallMass c
          ≤ (c : ℝ) ^ 2 / 4 * (m0sum c / 2) :=
            mul_le_mul_of_nonneg_left hsm (by positivity)
        _ = (c : ℝ) ^ 2 / 8 * m0sum c := by ring
    rw [h1] at hbulk
    linarith
  have hrm' : ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c ≤ msqSum c := by
    have h := mul_le_mul_of_nonneg_right hrm hm0.le
    rwa [div_mul_cancel₀ _ hm0.ne'] at h
  have hnum : nvarSum c
      + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2 * m0sum c
      ≤ ((c : ℝ) + (c : ℝ) ^ 2) * smallMass c
        + ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) + (c : ℝ) / Real.log c) * m0sum c := by
    rw [← hnv, hsplit_v]
    linarith [hrm', hsplit_m, hvS, hvL, hmS, hmL]
  have hnum_nn : (0 : ℝ) ≤ ((c : ℝ) + (c : ℝ) ^ 2) * smallMass c
      + ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) + (c : ℝ) / Real.log c) * m0sum c :=
    add_nonneg
      (mul_nonneg (add_nonneg hc9.le (pow_nonneg hc9.le _)) (smallMass_nonneg c))
      (mul_nonneg (add_nonneg (div_nonneg hc9.le hsqrt.le) (div_nonneg hc9.le hlog.le)) hm0.le)
  have hd_low_pos : (0 : ℝ) < (c : ℝ) ^ 2 / 8 * m0sum c :=
    mul_pos (div_pos (pow_pos hc9 _) (by norm_num)) hm0
  calc qfrac c
      = (nvarSum c
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c) / dsum c :=
        qfrac_eval c (by omega : 2 ≤ c)
    _ ≤ (((c : ℝ) + (c : ℝ) ^ 2) * smallMass c
          + ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) + (c : ℝ) / Real.log c) * m0sum c)
        / dsum c :=
        div_le_div_of_nonneg_right hnum hd.le
    _ ≤ (((c : ℝ) + (c : ℝ) ^ 2) * smallMass c
          + ((c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) + (c : ℝ) / Real.log c) * m0sum c)
        / ((c : ℝ) ^ 2 / 8 * m0sum c) :=
        div_le_div_of_nonneg_left hnum_nn hd_low_pos hd_low
    _ = 8 * (1 + 1 / (c : ℝ)) * (smallMass c / m0sum c)
        + 8 / ((c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c))
        + 8 / ((c : ℝ) * Real.log c) := by
        field_simp [hm0.ne', hc9.ne', hsqrt.ne', hlog.ne']
        ring

/-- The improved envelope holds eventually, with no side hypotheses. -/
theorem qfrac_eventually_one_sided :
    ∀ᶠ c : ℕ in Filter.atTop,
      qfrac c ≤ 8 * (1 + 1 / (c : ℝ)) * (smallMass c / m0sum c)
        + 8 / ((c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c))
        + 8 / ((c : ℝ) * Real.log c) := by
  filter_upwards [eventually_ge_atTop 9,
    tendsto_smallMass_div_m0sum_zero.eventually
      (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with c hc hs
  exact qfrac_le_one_sided hc hs

/-!
## Section 4: the rate statements
-/

/-- The A48 exponential small-mass decay beats the polynomial factor `c·log c`:
`(smallMass c/m0sum c)·(c·log c) → 0`.  The bound is the A48 explicit
`K·(c+1)·√c·(1/2)^c` (with `K = e + 2e/√(2π)`), which is `o(c⁻⁴)`. -/
theorem smallMass_div_m0sum_mul_clogc_tendsto_zero :
    Filter.Tendsto (fun c : ℕ => (smallMass c / m0sum c) * ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) := by
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
  have hd4 : ∀ᶠ c : ℕ in atTop,
      4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c ≤ Real.log 2 * (c : ℝ) :=
    four_sqrt_clogc_log_le_eventually (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hhalf : ∀ᶠ c : ℕ in atTop,
      smallMass c / m0sum c
        ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c := by
    filter_upwards [eventually_ge_atTop 163000, hd4, he4] with c hc163 hdc he4c
    exact smallMass_div_m0sum_le_half_pow hc163 hdc he4c
  have hnn : ∀ᶠ c : ℕ in atTop,
      (0 : ℝ) ≤ (smallMass c / m0sum c) * ((c : ℝ) * Real.log c) := by
    filter_upwards [eventually_ge_atTop 1] with c hc
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    exact mul_nonneg (div_nonneg (smallMass_nonneg c) hm0.le)
      (mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hc : (1 : ℝ) ≤ c)))
  have hup : ∀ᶠ c : ℕ in atTop,
      (smallMass c / m0sum c) * ((c : ℝ) * Real.log c)
        ≤ 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) ^ 4 * (1 / 2 : ℝ) ^ c) := by
    filter_upwards [hhalf, eventually_ge_atTop 2] with c hsc hc2
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
    have hcpos : (0 : ℝ) < (c : ℝ) := by positivity
    have hlognn : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
    have hK : (0 : ℝ) ≤ Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi) := by positivity
    have hp2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ c := by positivity
    have hsqrtle : Real.sqrt (c : ℝ) ≤ (c : ℝ) := by
      rw [Real.sqrt_le_left hcpos.le]
      calc (c : ℝ) = c * 1 := by ring
        _ ≤ c * c := mul_le_mul_of_nonneg_left hc1 hcpos.le
        _ = (c : ℝ) ^ 2 := by ring
    have hlogle : Real.log (c : ℝ) ≤ (c : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hcpos
      linarith
    have hc1le : (c : ℝ) + 1 ≤ 2 * (c : ℝ) := by linarith
    have h1 : (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
        ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * (2 * (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hc1le hK
    have h2 : (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
          * Real.sqrt c
        ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * (2 * (c : ℝ))
          * (c : ℝ) := by
      have hKc1nn : (0 : ℝ) ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
          * ((c : ℝ) + 1) :=
        mul_nonneg hK (by linarith : (0 : ℝ) ≤ (c : ℝ) + 1)
      calc (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
            * Real.sqrt c
          ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
            * (c : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtle hKc1nn
        _ ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * (2 * (c : ℝ))
            * (c : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hcpos.le
    have h3 : (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * ((c : ℝ) + 1)
          * Real.sqrt c * (1 / 2 : ℝ) ^ c
        ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * (2 * (c : ℝ))
          * (c : ℝ) * (1 / 2 : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right h2 hp2
    have h4 : (c : ℝ) * Real.log c ≤ (c : ℝ) * (c : ℝ) :=
      mul_le_mul_of_nonneg_left hlogle hcpos.le
    have hRHS3nn : (0 : ℝ) ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
        * (2 * (c : ℝ)) * (c : ℝ) * (1 / 2 : ℝ) ^ c :=
      mul_nonneg (mul_nonneg (mul_nonneg hK (by positivity)) hcpos.le) hp2
    calc (smallMass c / m0sum c) * ((c : ℝ) * Real.log c)
        ≤ ((Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) + 1) * Real.sqrt c * (1 / 2 : ℝ) ^ c) * ((c : ℝ) * Real.log c) :=
          mul_le_mul_of_nonneg_right hsc (mul_nonneg hcpos.le hlognn)
      _ ≤ ((Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)) * (2 * (c : ℝ))
            * (c : ℝ) * (1 / 2 : ℝ) ^ c) * ((c : ℝ) * (c : ℝ)) :=
        le_trans (mul_le_mul_of_nonneg_right h3 (mul_nonneg hcpos.le hlognn))
          (mul_le_mul_of_nonneg_left h4 hRHS3nn)
      _ = 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) ^ 4 * (1 / 2 : ℝ) ^ c) := by ring
  have hlim : Filter.Tendsto
      (fun c : ℕ => 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
        * ((c : ℝ) ^ 4 * (1 / 2 : ℝ) ^ c)) Filter.atTop (nhds 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4
      (show |(1 / 2 : ℝ)| < 1 by norm_num)
    have h2 := h.const_mul (2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)))
    simpa [mul_zero] using h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hnn hup

/-- **The new one-sided rate (TARGET 3, banked form).**  Eventually
`q(c)·(c·log c) ≤ 17`, i.e. `q(c) = O(1/(c·log c))`: a factor of `√(c·log c)`
better than the A48 explicit envelope `O(1/√(c·log c))`.  The mean-square
piece `8/(c·log c)` is the obstruction to going further; beating it needs the
two-sided saddle concentration named in `Gap2SharpRateGap`. -/
theorem qfrac_mul_clogc_eventually_le :
    ∀ᶠ c : ℕ in Filter.atTop, qfrac c * ((c : ℝ) * Real.log c) ≤ 17 := by
  have h16 : ∀ᶠ c : ℕ in atTop,
      8 * (1 + 1 / (c : ℝ)) * ((smallMass c / m0sum c) * ((c : ℝ) * Real.log c)) ≤ 1 := by
    have hT := smallMass_div_m0sum_mul_clogc_tendsto_zero
    have h1 := hT.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
    filter_upwards [h1, eventually_ge_atTop 1] with c hc hc1
    have hc1' : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hX0 : (0 : ℝ) ≤ (smallMass c / m0sum c) * ((c : ℝ) * Real.log c) := by
      apply mul_nonneg (div_nonneg (smallMass_nonneg c) (m0sum_pos c).le)
      exact mul_nonneg (by positivity : (0 : ℝ) ≤ (c : ℝ))
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c)))
    have h12 : (1 : ℝ) + 1 / c ≤ 2 := by
      have hcpos : (0 : ℝ) < (c : ℝ) := by positivity
      have h : (1 : ℝ) / c ≤ 1 := by
        rw [div_le_one hcpos]
        exact hc1'
      linarith
    have h8nn : (0 : ℝ) ≤ 8 * (1 + 1 / (c : ℝ)) := by positivity
    calc 8 * (1 + 1 / (c : ℝ)) * ((smallMass c / m0sum c) * ((c : ℝ) * Real.log c))
        ≤ 8 * (1 + 1 / (c : ℝ)) * (1 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_left hc h8nn
      _ ≤ 8 * 2 * (1 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h12 (by norm_num : (0 : ℝ) ≤ 8)) (by norm_num)
      _ = 1 := by norm_num
  filter_upwards [qfrac_eventually_one_sided, h16, eventually_ge_atTop 9]
    with c hq hs16 hc
  have hc9 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hlog : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hclog : (0 : ℝ) < (c : ℝ) * Real.log c := mul_pos hc9 hlog
  have hsqrt : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := Real.sqrt_pos.2 hclog
  have hmul := mul_le_mul_of_nonneg_right hq hclog.le
  have hden1 : (c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c) ≠ 0 :=
    mul_ne_zero hc9.ne' hsqrt.ne'
  have hRHS : (8 * (1 + 1 / (c : ℝ)) * (smallMass c / m0sum c)
        + 8 / ((c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c))
        + 8 / ((c : ℝ) * Real.log c)) * ((c : ℝ) * Real.log c)
      = 8 * (1 + 1 / (c : ℝ)) * ((smallMass c / m0sum c) * ((c : ℝ) * Real.log c))
        + 8 * (Real.log (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) + 8 := by
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    field_simp [hden1, hclog.ne', hc9.ne', hm0.ne']
  have hterm2 : 8 * (Real.log (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) ≤ 8 := by
    have hle1 : Real.log (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c) ≤ 1 := by
      rw [div_le_one hsqrt, Real.le_sqrt hlog.le hclog.le, sq]
      have hlc : Real.log (c : ℝ) ≤ (c : ℝ) := by
        have h := Real.log_le_sub_one_of_pos hc9
        linarith
      exact mul_le_mul_of_nonneg_right hlc hlog.le
    have := mul_le_mul_of_nonneg_left hle1 (by norm_num : (0 : ℝ) ≤ 8)
    linarith
  calc qfrac c * ((c : ℝ) * Real.log c)
      ≤ (8 * (1 + 1 / (c : ℝ)) * (smallMass c / m0sum c)
          + 8 / ((c : ℝ) * Real.sqrt ((c : ℝ) * Real.log c))
          + 8 / ((c : ℝ) * Real.log c)) * ((c : ℝ) * Real.log c) := hmul
    _ = 8 * (1 + 1 / (c : ℝ)) * ((smallMass c / m0sum c) * ((c : ℝ) * Real.log c))
        + 8 * (Real.log (c : ℝ) / Real.sqrt ((c : ℝ) * Real.log c)) + 8 := hRHS
    _ ≤ 1 + 8 + 8 := by linarith [hs16, hterm2]
    _ = 17 := by norm_num

/-- **Strict improvement over the A48 envelope.**  `q(c)·√(c·log c) → 0`,
i.e. `q(c) = o(1/√(c·log c))`, where A48 banked `q(c) = O(1/√(c·log c))`
via `qfrac_le_explicit`. -/
theorem tendsto_qfrac_mul_sqrt_clogc_zero :
    Filter.Tendsto (fun c : ℕ => qfrac c * Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) := by
  have h17 := qfrac_mul_clogc_eventually_le
  have hclog_top : Filter.Tendsto (fun c : ℕ => (c : ℝ) * Real.log c)
      Filter.atTop Filter.atTop := by
    refine tendsto_atTop_mono' Filter.atTop ?_ (tendsto_natCast_atTop_atTop (R := ℝ))
    filter_upwards [eventually_ge_atTop 3] with c hc
    have hlog1 : (1 : ℝ) ≤ Real.log (c : ℝ) := by
      have h13 : (1 : ℝ) < Real.log 3 := one_lt_log_three
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by exact_mod_cast hc : (3 : ℝ) ≤ c)
      linarith
    calc (c : ℝ) = (c : ℝ) * 1 := by ring
      _ ≤ (c : ℝ) * Real.log c := mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg _)
  have hsqrt_top : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop Filter.atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hclog_top
    have heq : (fun c : ℕ => ((c : ℝ) * Real.log c) ^ ((1 : ℝ) / 2))
        =ᶠ[Filter.atTop] (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c)) :=
      Filter.Eventually.of_forall fun c => (Real.sqrt_eq_rpow _).symm
    exact h.congr' heq
  have hbound : Filter.Tendsto (fun c : ℕ => 17 / Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hsqrt_top
    have h2 := h.const_mul 17
    simpa [div_eq_mul_inv, mul_zero] using h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · filter_upwards with c
    exact mul_nonneg (qfrac_nonneg c) (Real.sqrt_nonneg _)
  · filter_upwards [h17, eventually_ge_atTop 3] with c h17c hc
    have hclog : (0 : ℝ) < (c : ℝ) * Real.log c :=
      lt_trans zero_lt_one (one_lt_clogc (by omega : 3 ≤ c))
    have hsqrt : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := Real.sqrt_pos.2 hclog
    rw [le_div_iff₀ hsqrt]
    calc qfrac c * Real.sqrt ((c : ℝ) * Real.log c) * Real.sqrt ((c : ℝ) * Real.log c)
        = qfrac c * ((c : ℝ) * Real.log c) := by
          rw [mul_assoc, Real.mul_self_sqrt hclog.le]
      _ ≤ 17 := h17c

#print axioms var_cell_id
#print axioms varSum_eq_nvarSum
#print axioms varSum_eq_small_add_large
#print axioms msqSum_eq_small_add_large
#print axioms varSmall_le_c_smallMass
#print axioms varLarge_le
#print axioms msqSmall_le_c_sq_smallMass
#print axioms msqLarge_le
#print axioms norm_sq_resid_obsM_le
#print axioms qfrac_le_one_sided
#print axioms qfrac_eventually_one_sided
#print axioms smallMass_div_m0sum_mul_clogc_tendsto_zero
#print axioms qfrac_mul_clogc_eventually_le
#print axioms tendsto_qfrac_mul_sqrt_clogc_zero

end Gap2CensusOneSidedRate
