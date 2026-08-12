import IndisputableMonolith.Gravity.SevenGaps.Gap2SharpRateGap

/-!
# Hostile-review probe: A50/A51 sharp-rate arc (self-review of the
Gap2CensusFirstMoments / Gap2CensusVarianceSep / Gap2CensusOneSidedRate /
Gap2SharpRateGap chain)

Outside-module checks on the sharp-rate arc, written with hostile intent:
nothing here is cited from the new modules' own assemblies where an
independent route exists, and every red test is a proved statement, not a
compile failure.

1. Re-audits of every charged head theorem of the four modules, from outside.
2. Definitional pins by `rfl`: `nvarSum = nsum − msqSum`, `msqSum` and
   `varSum` as double sums of their exact cell weights.
3. Non-vacuity witnesses: the variance sum, the anomaly fraction, the rate
   sequence `q(c)·(c·log c)`, and the first gap field's sequence are all
   eventually strictly positive, so every bound and limit on them has content.
4. Concreteness: `varSum 2 = 5/2` and `msqSum 2 = 15/2` by kernel
   computation, with decoys (`8` without the `(1−1/n)` variance factor, `7`
   without the mean-square square) proved NOT to be the values.
5. Red test 1: the A48 explicit envelope `1/(√(c·log c) − 1)` is eventually
   STRICTLY above the A51 rate bound `17/(c·log c)`, so no composition of the
   A48 bound could have delivered the new rate: the variance separation adds
   genuine content.
6. Red test 2: the conditional assembly reads the gap constant faithfully.
   Re-derived here at a general limit `L`; instantiated at the wrong constant
   `2` it returns the wrong limit, and `nhds 1 ≠ nhds 2` pins the difference.
   (The flip of the rate itself, `17 < q(c)·(c·log c)`, is refuted by the
   banked `qfrac_mul_clogc_eventually_le`; a sharper false statement about the
   sharp scale is exactly the open gap and is named as such.)
7. Structure pins: `SharpRateGap`'s three fields at their exact types, and
   the two banked rate theorems at their exact types.
-/

namespace QGSharpRateHostileProbe

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Gap2SharpRateGap Finset Filter
open scoped Nat

/-! ## 1. Outside-module axiom audits of the charged head theorems -/

-- Module A (TARGET 1, first moments)
#print axioms Gap2CensusFirstMoments.sum_j_cellCount
#print axioms Gap2CensusFirstMoments.loopMeanSum_eq
#print axioms Gap2CensusFirstMoments.properMeanSum_eq
#print axioms Gap2CensusFirstMoments.expect_nloop
#print axioms Gap2CensusFirstMoments.expect_nproper

-- Module B (TARGET 2, variance separation)
#print axioms Gap2CensusVarianceSep.sum_centered_cell
#print axioms Gap2CensusVarianceSep.inner_obsL_obsM
#print axioms Gap2CensusVarianceSep.norm_sq_obsM
#print axioms Gap2CensusVarianceSep.norm_sq_resid_obsL
#print axioms Gap2CensusVarianceSep.norm_sq_sub_obsM
#print axioms Gap2CensusVarianceSep.qfrac_eval
#print axioms Gap2CensusVarianceSep.norm_sq_resid_le_of_mem_span

-- Module C (TARGET 3, one-sided rate)
#print axioms Gap2CensusOneSidedRate.var_cell_id
#print axioms Gap2CensusOneSidedRate.varSum_eq_nvarSum
#print axioms Gap2CensusOneSidedRate.norm_sq_resid_obsM_le
#print axioms Gap2CensusOneSidedRate.qfrac_le_one_sided
#print axioms Gap2CensusOneSidedRate.smallMass_div_m0sum_mul_clogc_tendsto_zero
#print axioms Gap2CensusOneSidedRate.qfrac_mul_clogc_eventually_le
#print axioms Gap2CensusOneSidedRate.tendsto_qfrac_mul_sqrt_clogc_zero

-- Module D (TARGET 3 two-sided gap, TARGET 4 conditional assembly)
#print axioms Gap2SharpRateGap.qfrac_sharp_rate_of_gap
#print axioms Gap2SharpRateGap.qfrac_sharp_rate_one_add_o1

/-! ## 2. Definitional pins: the sums are the real objects -/

/-- `nvarSum` really is `nsum − msqSum`. -/
theorem nvarSum_eq (c : ℕ) : nvarSum c = nsum c - msqSum c := rfl

/-- `msqSum` really is the double sum of the mean-square weight `(k/n)²·n^{2k}/(n!·k!)`. -/
theorem msqSum_eq (c : ℕ) :
    msqSum c = ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := rfl

/-- `varSum` really is the double sum of the conditional-variance weight
`(k/n)·(1−1/n)·n^{2k}/(n!·k!)`. -/
theorem varSum_eq (c : ℕ) :
    varSum c = ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := rfl

/-! ## 3. Non-vacuity witnesses -/

/-- The variance cell weight is nonnegative everywhere (at `n = 0` the whole
cell vanishes; at `n ≥ 1` the factor `1 − 1/n` is nonnegative). -/
theorem var_cell_nonneg (n k : ℕ) :
    (0 : ℝ) ≤ ((k : ℝ) / n) * (1 - 1 / n) * (n : ℝ) ^ (2 * k)
      / ((n ! : ℝ) * (k ! : ℝ)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Nat.cast_zero, div_zero, zero_mul, zero_div, le_refl]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have h1n : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
      have h : (1 : ℝ) / (n : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ))]
        exact hn1
      linarith
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) h1n) (by positivity))
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-- The `(n, k) = (2, 1)` variance cell is exactly `1/2`. -/
theorem var_cell_21 :
    (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ) ^ (2 * 1)
      / (((2 : ℕ) ! : ℝ) * ((1 : ℕ) ! : ℝ)) = 1 / 2 := by
  norm_num [Nat.factorial]

/-- The variance sum is strictly positive for `c ≥ 2`: the `(2, 1)` cell
contributes `1/2`.  So every bound with `nvarSum` in the numerator has
content. -/
theorem varSum_pos {c : ℕ} (hc : 2 ≤ c) : 0 < varSum c := by
  have h2r : 2 ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
  have h1r : 1 ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
  have hrow : (1 : ℝ) / 2 ≤ ∑ k ∈ Finset.range (c + 1),
      ((k : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ) ^ (2 * k)
        / (((2 : ℕ) ! : ℝ) * (k ! : ℝ)) := by
    have h : (((1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ))
        * ((2 : ℕ) : ℝ) ^ (2 * 1) / (((2 : ℕ) ! : ℝ) * ((1 : ℕ) ! : ℝ))
        ≤ ∑ k ∈ Finset.range (c + 1),
          ((k : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ) ^ (2 * k)
            / (((2 : ℕ) ! : ℝ) * (k ! : ℝ)) :=
      Finset.single_le_sum
        (f := fun k : ℕ => ((k : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ))
          * ((2 : ℕ) : ℝ) ^ (2 * k) / (((2 : ℕ) ! : ℝ) * (k ! : ℝ)))
        (fun k _ => var_cell_nonneg 2 k) h1r
    rwa [var_cell_21] at h
  have hcol : (∑ k ∈ Finset.range (c + 1),
        ((k : ℝ) / ((2 : ℕ) : ℝ)) * (1 - 1 / ((2 : ℕ) : ℝ)) * ((2 : ℕ) : ℝ) ^ (2 * k)
          / (((2 : ℕ) ! : ℝ) * (k ! : ℝ)))
      ≤ varSum c := by
    rw [varSum_eq c]
    exact Finset.single_le_sum (fun n _ =>
      Finset.sum_nonneg fun k _ => var_cell_nonneg n k) h2r
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hrow.trans hcol)

/-- The variance numerator of the sharp rate is strictly positive for `c ≥ 2`. -/
theorem nvarSum_pos {c : ℕ} (hc : 2 ≤ c) : 0 < nvarSum c := by
  rw [← varSum_eq_nvarSum c]
  exact varSum_pos hc

/-- The anomaly fraction is strictly positive for `c ≥ 2`: `q(c) → 0` and the
rate statements about `q` all have content. -/
theorem qfrac_pos {c : ℕ} (hc : 2 ≤ c) : 0 < qfrac c := by
  rw [qfrac_eval c hc]
  exact div_pos
    (add_pos_of_pos_of_nonneg (nvarSum_pos hc)
      (mul_nonneg (sq_nonneg _) (m0sum_pos c).le))
    (dsum_pos c hc)

/-- The rate sequence is strictly positive for `c ≥ 2`: `q(c)·(c·log c) ≤ 17`
eventually bounds a strictly positive sequence. -/
theorem rate_seq_pos {c : ℕ} (hc : 2 ≤ c) :
    0 < qfrac c * ((c : ℝ) * Real.log c) :=
  mul_pos (qfrac_pos hc)
    (mul_pos (by exact_mod_cast (by omega : 0 < c))
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))))

/-- The first gap field's sequence is strictly positive for `c ≥ 2`: the
limit-`1` claim of `SharpRateGap.nvar_sharp` is about a nonzero sequence. -/
theorem gap_nvar_seq_pos {c : ℕ} (hc : 2 ≤ c) :
    0 < nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c) :=
  div_pos
    (mul_pos (nvarSum_pos hc)
      (mul_pos (by norm_num) (pow_pos (by exact_mod_cast (by omega : 0 < c)) _)))
    (mul_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < c))) (dsum_pos c hc))

/-! ## 4. Concreteness: kernel computation of the sums at `c = 2` -/

/-- The variance sum at `c = 2` is exactly `5/2`: the only nonzero cells are
`(2, 1) ↦ 1/2` and `(2, 2) ↦ 2`. -/
theorem varSum_two : varSum 2 = 5 / 2 := by
  norm_num [varSum, Finset.sum_range_succ, Nat.factorial, div_zero, zero_div]

/-- Decoy rejected: dropping the `(1−1/n)` variance factor would give `8`. -/
theorem varSum_two_ne_decoy : varSum 2 ≠ 8 := by
  rw [varSum_two]
  norm_num

/-- The mean-square sum at `c = 2` is exactly `15/2`: cells
`(1, 1) ↦ 1`, `(1, 2) ↦ 2`, `(2, 1) ↦ 1/2`, `(2, 2) ↦ 4`. -/
theorem msqSum_two : msqSum 2 = 15 / 2 := by
  norm_num [msqSum, Finset.sum_range_succ, Nat.factorial, div_zero, zero_div]

/-- Decoy rejected: dropping the square on `k/n` would give `7`. -/
theorem msqSum_two_ne_decoy : msqSum 2 ≠ 7 := by
  rw [msqSum_two]
  norm_num

/-- Consistency with Module C's cell identity: `nvarSum 2 = 5/2 = varSum 2`. -/
theorem nvarSum_two : nvarSum 2 = 5 / 2 := by
  rw [← varSum_eq_nvarSum 2]
  exact varSum_two

/-! ## 5. Red test 1: the A48 envelope cannot deliver the A51 rate

The A48 explicit bound on the anomaly fraction decayed like
`1/(√(c·log c) − 1)`.  The A51 rate is `q(c)·(c·log c) ≤ 17` eventually.  If
the old envelope could have delivered the new rate, the envelope would
eventually sit below `17/(c·log c)`.  It does not: eventually it is strictly
above, so the variance separation genuinely adds content. -/

/-- Eventually `1/(√(c·log c) − 1) > 17/(c·log c)`: the flip of "A48 implies
A51" is FALSE.  At `X = c·log c > 324` (`√X > 18`) we have
`X > 17·(√X − 1)`. -/
theorem a48_envelope_cannot_deliver_rate :
    ∀ᶠ c : ℕ in atTop,
      ¬ (1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1)
        ≤ 17 / ((c : ℝ) * Real.log c)) := by
  filter_upwards [eventually_ge_atTop 163] with c hc
  have hcR : (163 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hlog2 : (2 : ℝ) ≤ Real.log (c : ℝ) := by
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by exact_mod_cast (by omega : 9 ≤ c) : (9 : ℝ) ≤ c)
    linarith [two_lt_log_nine]
  have hX : (324 : ℝ) < (c : ℝ) * Real.log c := by
    calc (324 : ℝ) < 2 * (163 : ℝ) := by norm_num
      _ ≤ 2 * (c : ℝ) := by linarith
      _ = (c : ℝ) * 2 := by ring
      _ ≤ (c : ℝ) * Real.log (c : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
  have hsqrt18 : (18 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [show (18 : ℝ) = Real.sqrt (324 : ℝ) by
      rw [show (324 : ℝ) = (18 : ℝ) ^ 2 by norm_num]
      exact (Real.sqrt_sq (show (0 : ℝ) ≤ (18 : ℝ) by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 324 by norm_num) hX
  have hXpos : (0 : ℝ) < (c : ℝ) * Real.log c := by linarith
  have hs1 : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) - 1 := by linarith
  have hXX : Real.sqrt ((c : ℝ) * Real.log c) * Real.sqrt ((c : ℝ) * Real.log c)
      = (c : ℝ) * Real.log c := Real.mul_self_sqrt hXpos.le
  have hhint : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c)
      * (Real.sqrt ((c : ℝ) * Real.log c) - 17) :=
    mul_pos (by linarith) (by linarith)
  rw [not_le, lt_div_iff₀ hs1, div_mul_eq_mul_div, div_lt_iff₀ hXpos, one_mul]
  nlinarith [hXX, hhint]

/-! ## 6. Red test 2: the assembly reads the gap constant faithfully

The conditional assembly of Module D is re-derived here at a general limit
`L`: the field algebra never mentions the constant, so feeding it gap data
with limit `2` returns the rate with limit `2`.  The `1` in the sharp rate is
therefore exactly the content of the named gap, not something the assembly
manufactures. -/

/-- The eventually-valid field algebra behind the assembly, independently
re-derived: for `c ≥ 2`, `q(c)·(2c²/log c)` splits into the first two gap
fields. -/
theorem qfrac_mul_sharp_split :
    ∀ᶠ c : ℕ in atTop,
      qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c)
        = nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c) := by
  filter_upwards [eventually_ge_atTop 2] with c hc
  have hd : (0 : ℝ) < dsum c := dsum_pos c hc
  have hlog : Real.log (c : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
  rw [qfrac_eval c hc]
  field_simp [hd.ne', hlog]

/-- The assembly at a general gap limit `L`. -/
theorem qfrac_sharp_rate_of_general (L : ℝ)
    (h1 : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds L))
    (h2 : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds L) := by
  have hadd := h1.add h2
  rw [add_zero] at hadd
  apply hadd.congr'
  filter_upwards [qfrac_mul_sharp_split] with c hc
  exact hc.symm

/-- Green: at the gap's own constant the re-derived assembly agrees with
Module D's `qfrac_sharp_rate_of_gap`. -/
theorem assembly_at_gap_constant (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) :=
  qfrac_sharp_rate_of_general 1 hgap.nvar_sharp hgap.resid_negligible

/-- RED: fed the wrong constant, the assembly returns the wrong rate; the
assembly is faithful, not vacuous. -/
theorem assembly_at_wrong_constant
    (h1 : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 2))
    (h2 : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 2) :=
  qfrac_sharp_rate_of_general 2 h1 h2

/-- The two outcomes are genuinely different limits. -/
theorem nhds_one_ne_two : nhds (1 : ℝ) ≠ nhds 2 := by
  intro h
  obtain ⟨s, t, hs, ht, h1s, h2t, hdisj⟩ :=
    t2_separation (show (1 : ℝ) ≠ 2 by norm_num)
  have hsn : s ∈ nhds (1 : ℝ) := hs.mem_nhds h1s
  have htn : t ∈ nhds (1 : ℝ) := h.symm ▸ ht.mem_nhds h2t
  have hst : s ∩ t ∈ nhds (1 : ℝ) := Filter.inter_mem hsn htn
  have hempty : s ∩ t = (∅ : Set ℝ) := Set.disjoint_iff_inter_eq_empty.1 hdisj
  rw [hempty] at hst
  exact Filter.empty_notMem _ hst

/-- The flip of the banked rate is eventually FALSE: `q(c)·(c·log c)` does
not exceed `17` eventually. -/
theorem flipped_rate_eventually_false :
    ∀ᶠ c : ℕ in atTop, ¬ (17 < qfrac c * ((c : ℝ) * Real.log c)) :=
  qfrac_mul_clogc_eventually_le.mono fun _c h => not_lt.2 h

/-! ## 7. Structure pins: the named gap and the banked rates at exact types -/

/-- Gap field 1 at its exact type. -/
theorem gap_nvar_at_type (g : SharpRateGap) :
    Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1) :=
  g.nvar_sharp

/-- Gap field 2 at its exact type. -/
theorem gap_resid_at_type (g : SharpRateGap) :
    Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0) :=
  g.resid_negligible

/-- Gap field 3 at its exact type. -/
theorem gap_dsum_at_type (g : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c))
      Filter.atTop (nhds 1) :=
  g.dsum_saddle

/-- The banked one-sided rate at its exact type. -/
theorem rate_at_type :
    ∀ᶠ c : ℕ in Filter.atTop, qfrac c * ((c : ℝ) * Real.log c) ≤ 17 :=
  Gap2CensusOneSidedRate.qfrac_mul_clogc_eventually_le

/-- The banked strict improvement over A48 at its exact type. -/
theorem improvement_at_type :
    Filter.Tendsto (fun c : ℕ => qfrac c * Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) :=
  Gap2CensusOneSidedRate.tendsto_qfrac_mul_sqrt_clogc_zero

/-! ## 8. Audits of this probe's own theorems -/

#print axioms QGSharpRateHostileProbe.varSum_pos
#print axioms QGSharpRateHostileProbe.nvarSum_pos
#print axioms QGSharpRateHostileProbe.qfrac_pos
#print axioms QGSharpRateHostileProbe.rate_seq_pos
#print axioms QGSharpRateHostileProbe.varSum_two
#print axioms QGSharpRateHostileProbe.msqSum_two
#print axioms QGSharpRateHostileProbe.nvarSum_two
#print axioms QGSharpRateHostileProbe.a48_envelope_cannot_deliver_rate
#print axioms QGSharpRateHostileProbe.qfrac_sharp_rate_of_general
#print axioms QGSharpRateHostileProbe.assembly_at_wrong_constant
#print axioms QGSharpRateHostileProbe.flipped_rate_eventually_false
#print axioms QGSharpRateHostileProbe.gap_nvar_at_type

end QGSharpRateHostileProbe
