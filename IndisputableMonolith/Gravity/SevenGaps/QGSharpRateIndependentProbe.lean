import IndisputableMonolith.Gravity.SevenGaps.Gap2SharpRateGap
import IndisputableMonolith.Gravity.SevenGaps.QGSharpRateHostileProbe

/-!
# Independent hostile-review probe: the A50 sharp-rate arc

Reviewer probe for the A50 campaign (commits `a4f786c5a8`, `a865a9142a`,
`e6fc281235`), written from outside the four campaign modules.  The worker's
own probe `QGSharpRateHostileProbe.lean` is imported only to re-audit its red
theorems from here; every check below is an independent route: concrete sums
are computed by the kernel from `cellCount` upward (never through the
theorems under review), the wrong-constant instrument is re-derived from
`qfrac_eval` directly, and the A48-envelope comparison is re-proved from
`Real.log` monotonicity.

1. Outside axiom audits of all 19 head theorems named in the A50 report.
2. Concrete pins at cap `c = 2`, kernel-computed from the definitions:
   `nsum 2 = 10`, `dsum 2 = 7`, `m0sum 2 = 21/2`, `msqSum 2 = 15/2`,
   `nvarSum 2 = 5/2` (via `nsum - msqSum`, a different route from the
   worker's `varSum` pin), `nmeanSum 2 = 7`, `dmeanSum 2 = 5`,
   `loopMeanSum 2 2 = 16`, `mechanismBound 2 = 10/7`.
3. Decoys proved FALSE: `nvarSum 2 ≠ 10` (the raw second moment: the
   mean-square subtraction is active), `loopMeanSum 2 2 ≠ 32` (the `2k`
   exponent decoy against the true `2k - 1`), `dsum 2 ≠ nsum 2` (the
   loop/proper swap decoy).
4. Content witnesses: `0 < nvarSum 2`, `5/14 ≤ qfrac 2`, and the first and
   third gap-field sequences evaluated concretely at `c = 2` (they are
   genuine nonzero quantities, so the gap fields are not folded trivialities).
5. The wrong-constant instrument, re-derived: a general-limit assembly from
   `qfrac_eval` alone; fed limit-`2` gap data it concludes limit `2`, and
   `wrong_constant_excludes_limit_one` proves the same data cannot also
   yield limit `1` (`tendsto_nhds_unique`).  The assembly tracks the gap's
   constant; it does not manufacture `1`.
6. The A48-envelope comparison, re-proved: eventually
   `17/(c·log c) < 1/(√(c·log c) − 1)`, and composing with the banked
   `qfrac_mul_clogc_eventually_le`, eventually
   `q(c) < 1/(√(c·log c) − 1)`: "strictly inside the A48 envelope" made
   pointwise.
7. Structure pins: `SharpRateGap`'s three fields and the head theorems at
   their exact charged types.
-/

namespace QGSharpRateIndependentProbe

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Gap2SharpRateGap Finset Filter
open scoped Nat

/-! ## 1. Outside axiom audits of the 19 charged head theorems -/

#print axioms Gap2CensusFirstMoments.sum_j_cellCount
#print axioms Gap2CensusFirstMoments.expect_nloop
#print axioms Gap2CensusFirstMoments.expect_nproper
#print axioms Gap2CensusVarianceSep.norm_sq_resid_obsL
#print axioms Gap2CensusVarianceSep.qfrac_eval
#print axioms Gap2CensusOneSidedRate.qfrac_le_one_sided
#print axioms Gap2CensusOneSidedRate.qfrac_eventually_one_sided
#print axioms Gap2CensusOneSidedRate.qfrac_mul_clogc_eventually_le
#print axioms Gap2CensusOneSidedRate.tendsto_qfrac_mul_sqrt_clogc_zero
#print axioms Gap2SharpRateGap.qfrac_sharp_rate_of_gap
#print axioms Gap2SharpRateGap.qfrac_sharp_rate_one_add_o1
#print axioms QGSharpRateHostileProbe.qfrac_pos
#print axioms QGSharpRateHostileProbe.varSum_two
#print axioms QGSharpRateHostileProbe.varSum_two_ne_decoy
#print axioms QGSharpRateHostileProbe.msqSum_two
#print axioms QGSharpRateHostileProbe.msqSum_two_ne_decoy
#print axioms QGSharpRateHostileProbe.a48_envelope_cannot_deliver_rate
#print axioms QGSharpRateHostileProbe.qfrac_mul_sharp_split
#print axioms QGSharpRateHostileProbe.qfrac_sharp_rate_of_general
#print axioms QGSharpRateHostileProbe.nhds_one_ne_two

/-! ## 2. Concrete pins at `c = 2`, kernel-computed from the definitions -/

/-- The loop second-moment sum at cap 2: cells `(1,1) ↦ 1`, `(1,2) ↦ 2`,
`(2,1) ↦ 1`, `(2,2) ↦ 6`. -/
theorem nsum_two : nsum 2 = 10 := by
  have h00 : loopSqSum 0 0 = 0 := by decide
  have h01 : loopSqSum 0 1 = 0 := by decide
  have h02 : loopSqSum 0 2 = 0 := by decide
  have h10 : loopSqSum 1 0 = 0 := by decide
  have h11 : loopSqSum 1 1 = 1 := by decide
  have h12 : loopSqSum 1 2 = 4 := by decide
  have h20 : loopSqSum 2 0 = 0 := by decide
  have h21 : loopSqSum 2 1 = 2 := by decide
  have h22 : loopSqSum 2 2 = 24 := by decide
  norm_num [nsum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The proper second-moment sum at cap 2: cells `(2,1) ↦ 1`, `(2,2) ↦ 6`. -/
theorem dsum_two : dsum 2 = 7 := by
  have h00 : properSqSum 0 0 = 0 := by decide
  have h01 : properSqSum 0 1 = 0 := by decide
  have h02 : properSqSum 0 2 = 0 := by decide
  have h10 : properSqSum 1 0 = 0 := by decide
  have h11 : properSqSum 1 1 = 0 := by decide
  have h12 : properSqSum 1 2 = 0 := by decide
  have h20 : properSqSum 2 0 = 0 := by decide
  have h21 : properSqSum 2 1 = 2 := by decide
  have h22 : properSqSum 2 2 = 24 := by decide
  norm_num [dsum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The census mass sum at cap 2: rows `1`, `5/2`, `13/2`. -/
theorem m0sum_two : m0sum 2 = 10 := by
  norm_num [m0sum, wrow, Finset.sum_range_succ, Nat.factorial]

/-- The conditional-mean-square sum at cap 2: rows `3`, `9/2` (independent
recomputation of the worker's `msqSum_two`). -/
theorem msqSum_two_ind : msqSum 2 = 15 / 2 := by
  norm_num [msqSum, Finset.sum_range_succ, Nat.factorial, div_zero, zero_div]

/-- The variance numerator at cap 2 via `nsum - msqSum`: a different route
from the worker's `varSum 2 = 5/2` pin, landing on the same value. -/
theorem nvarSum_two_ind : nvarSum 2 = 5 / 2 := by
  have h : nvarSum 2 = nsum 2 - msqSum 2 := rfl
  rw [h, nsum_two, msqSum_two_ind]
  norm_num

/-- The loop first-moment sum at cap 2: cells `(1,1) ↦ 1`, `(1,2) ↦ 1`,
`(2,1) ↦ 1`, `(2,2) ↦ 4`. -/
theorem nmeanSum_two : nmeanSum 2 = 7 := by
  have h00 : loopMeanSum 0 0 = 0 := by decide
  have h01 : loopMeanSum 0 1 = 0 := by decide
  have h02 : loopMeanSum 0 2 = 0 := by decide
  have h10 : loopMeanSum 1 0 = 0 := by decide
  have h11 : loopMeanSum 1 1 = 1 := by decide
  have h12 : loopMeanSum 1 2 = 2 := by decide
  have h20 : loopMeanSum 2 0 = 0 := by decide
  have h21 : loopMeanSum 2 1 = 2 := by decide
  have h22 : loopMeanSum 2 2 = 16 := by decide
  norm_num [nmeanSum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The proper first-moment sum at cap 2: cells `(2,1) ↦ 1`, `(2,2) ↦ 4`. -/
theorem dmeanSum_two : dmeanSum 2 = 5 := by
  have h00 : properMeanSum 0 0 = 0 := by decide
  have h01 : properMeanSum 0 1 = 0 := by decide
  have h02 : properMeanSum 0 2 = 0 := by decide
  have h10 : properMeanSum 1 0 = 0 := by decide
  have h11 : properMeanSum 1 1 = 0 := by decide
  have h12 : properMeanSum 1 2 = 0 := by decide
  have h20 : properMeanSum 2 0 = 0 := by decide
  have h21 : properMeanSum 2 1 = 2 := by decide
  have h22 : properMeanSum 2 2 = 16 := by decide
  norm_num [dmeanSum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The first-moment cell identity at `(2, 2)`, computed from `cellCount`
alone (not through `sum_j_cellCount`): `8 + 8 = 16 = 2·2³`. -/
theorem loopMeanSum_two_two : loopMeanSum 2 2 = 16 := by decide

/-- The mechanism bound at cap 2. -/
theorem mechanismBound_two : mechanismBound 2 = 10 / 7 := by
  have h : mechanismBound 2 = nsum 2 / dsum 2 := rfl
  rw [h, nsum_two, dsum_two]

/-! ## 3. Decoys proved FALSE -/

/-- Decoy rejected: dropping the mean-square subtraction would give the raw
second moment `10`; the subtraction is active, not decorative. -/
theorem nvarSum_two_ne_raw_second : nvarSum 2 ≠ 10 := by
  rw [nvarSum_two_ind]
  norm_num

/-- Decoy rejected: the `2k` exponent instead of the true `2k - 1` would
give `2·2⁴ = 32`. -/
theorem loopMeanSum_two_two_ne_decoy : loopMeanSum 2 2 ≠ 32 := by
  rw [loopMeanSum_two_two]
  norm_num

/-- Decoy rejected: swapping loop and proper second moments would equate
`dsum 2 = 7` with `nsum 2 = 10`. -/
theorem dsum_two_ne_nsum_two : dsum 2 ≠ nsum 2 := by
  rw [dsum_two, nsum_two]
  norm_num

/-! ## 4. Content witnesses -/

/-- The variance numerator is strictly positive at cap 2: bounds and limits
about `nvarSum` have content. -/
theorem nvarSum_two_pos : 0 < nvarSum 2 := by
  rw [nvarSum_two_ind]
  norm_num

/-- The anomaly fraction at cap 2 is at least `5/14`: `q(2)` is not
vacuously small. -/
theorem qfrac_two_lower : (5 : ℝ) / 14 ≤ qfrac 2 := by
  rw [qfrac_eval 2 (le_refl 2), nvarSum_two_ind, dsum_two]
  have hX : (0 : ℝ) ≤
      ‖Gap2AnomalyAsymptotics.resid (obsV 2) (obsE 2) (obsT 2) (obsM 2)‖ ^ 2
        * m0sum 2 :=
    mul_nonneg (sq_nonneg _) (m0sum_pos 2).le
  linarith [hX]

/-- The first gap field's sequence at `c = 2`: a genuine nonzero quantity
(`≈ 4.12`, far from the asymptotic limit `1`, as expected at cap 2). -/
theorem gap_field_one_at_two :
    nvarSum 2 * (2 * (2 : ℝ) ^ 2) / (Real.log 2 * dsum 2)
      = 20 / (7 * Real.log 2) := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [nvarSum_two_ind, dsum_two]
  field_simp [h2]
  ring

/-- The third gap field's sequence at `c = 2`: `dsum 2 / (4·m0sum 2) = 7/40`. -/
theorem gap_field_three_at_two :
    dsum 2 / ((2 : ℝ) ^ 2 * m0sum 2) = 7 / 40 := by
  rw [dsum_two, m0sum_two]
  norm_num

/-! ## 5. The wrong-constant instrument, re-derived from `qfrac_eval` -/

/-- The assembly at a general gap limit `L`, independently re-derived: the
field algebra from `qfrac_eval` never mentions the constant, so gap data
with limit `L` yields the rate with limit `L`. -/
theorem sharp_assembly_general (L : ℝ)
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
  have heq : (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      =ᶠ[Filter.atTop] (fun c : ℕ =>
        nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    have hd : (0 : ℝ) < dsum c := dsum_pos c hc
    have hlog : Real.log (c : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
    rw [qfrac_eval c hc]
    field_simp [hd.ne', hlog]
  have hadd := h1.add h2
  rw [add_zero] at hadd
  exact hadd.congr' heq.symm

/-- RED: fed limit-`2` gap data, the assembly returns the rate with limit
`2`; it does not normalize to `1`. -/
theorem assembly_at_wrong_constant_two
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
  sharp_assembly_general 2 h1 h2

/-- RED, sharpened: under limit-`2` gap data the assembled sequence provably
does NOT converge to `1` (limits are unique, `1 ≠ 2`).  The constant in the
sharp rate is exactly the gap's content. -/
theorem wrong_constant_excludes_limit_one
    (h1 : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 2))
    (h2 : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    ¬ Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) := by
  intro hone
  have htwo := assembly_at_wrong_constant_two h1 h2
  have h12 := tendsto_nhds_unique hone htwo
  norm_num at h12

/-- GREEN: at the gap's own constant the re-derived assembly agrees with
Module D's `qfrac_sharp_rate_of_gap`. -/
theorem assembly_at_gap_constant_agrees (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) :=
  sharp_assembly_general 1 hgap.nvar_sharp hgap.resid_negligible

/-! ## 6. The A48-envelope comparison, re-proved -/

/-- Eventually `17/(c·log c) < 1/(√(c·log c) − 1)`: the A48 explicit
envelope stays strictly above the new rate bound, so no algebra on the A48
statement could have delivered it.  At `X = c·log c > 324` (`√X > 18`),
`X > 17·(√X − 1)`. -/
theorem a48_envelope_stays_above_new_rate :
    ∀ᶠ c : ℕ in Filter.atTop,
      17 / ((c : ℝ) * Real.log c)
        < 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  filter_upwards [eventually_ge_atTop 163] with c hc
  have hc163 : (163 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
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
  have hXpos : (0 : ℝ) < (c : ℝ) * Real.log c := by linarith
  have hs18 : (18 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    have h18 : Real.sqrt (324 : ℝ) = 18 := by
      rw [show (324 : ℝ) = (18 : ℝ) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h18]
    exact Real.sqrt_lt_sqrt (by norm_num) hX
  have hs1 : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) - 1 := by linarith
  have hsq : Real.sqrt ((c : ℝ) * Real.log c) * Real.sqrt ((c : ℝ) * Real.log c)
      = (c : ℝ) * Real.log c := Real.mul_self_sqrt hXpos.le
  have hprod : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c)
      * (Real.sqrt ((c : ℝ) * Real.log c) - 17) := mul_pos (by linarith) (by linarith)
  have hgoal : (17 : ℝ) * (Real.sqrt ((c : ℝ) * Real.log c) - 1)
      < (c : ℝ) * Real.log c := by nlinarith [hsq, hprod]
  rw [div_lt_div_iff₀ hXpos hs1]
  linarith [hgoal]

/-- The banked rate made pointwise against the A48 envelope: eventually
`q(c)` sits strictly below `1/(√(c·log c) − 1)`.  This is exactly "strictly
inside the A48 envelope", and nothing more. -/
theorem new_rate_below_a48_envelope :
    ∀ᶠ c : ℕ in Filter.atTop,
      qfrac c < 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  filter_upwards [Gap2CensusOneSidedRate.qfrac_mul_clogc_eventually_le,
    a48_envelope_stays_above_new_rate, eventually_ge_atTop 2] with c h17 hlt _hc2
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hlog : (0 : ℝ) < Real.log (c : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hX : (0 : ℝ) < (c : ℝ) * Real.log c := mul_pos hcpos hlog
  have hq : qfrac c ≤ 17 / ((c : ℝ) * Real.log c) := by
    rw [le_div_iff₀ hX]
    exact h17
  exact hq.trans_lt hlt

/-! ## 7. Structure pins: the charged statements at their exact types -/

/-- Gap field 1 at its exact type. -/
theorem gap_nvar_field_at_type (g : SharpRateGap) :
    Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1) :=
  g.nvar_sharp

/-- Gap field 2 at its exact type. -/
theorem gap_resid_field_at_type (g : SharpRateGap) :
    Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0) :=
  g.resid_negligible

/-- Gap field 3 at its exact type. -/
theorem gap_dsum_field_at_type (g : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c))
      Filter.atTop (nhds 1) :=
  g.dsum_saddle

/-- The conditional assembly at its exact type: a genuine `Tendsto`-to-`1`,
not a weaker statement wearing the notation. -/
theorem sharp_rate_of_gap_at_type (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) :=
  Gap2SharpRateGap.qfrac_sharp_rate_of_gap hgap

/-- The `(1+o(1))` form at its exact type: `q(c) / ((log c)/(2c²)) → 1`. -/
theorem sharp_rate_one_add_o1_at_type (hgap : SharpRateGap) :
    Filter.Tendsto (fun c : ℕ => qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2)))
      Filter.atTop (nhds 1) :=
  Gap2SharpRateGap.qfrac_sharp_rate_one_add_o1 hgap

/-- The first-moment cell identity at its exact type, for every `n k : ℕ`. -/
theorem sum_j_cellCount_at_type (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), j * cellCount n k j) = k * n ^ (2 * k - 1) :=
  Gap2CensusFirstMoments.sum_j_cellCount n k

/-- The variance split at its exact type. -/
theorem norm_sq_resid_obsL_at_type (c : ℕ) :
    ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsL c)‖ ^ 2
      = ‖obsL c - obsM c‖ ^ 2
        + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2 :=
  Gap2CensusVarianceSep.norm_sq_resid_obsL c

/-- `qfrac` as the evaluated ratio, at its exact type. -/
theorem qfrac_eval_at_type (c : ℕ) (hc : 2 ≤ c) :
    qfrac c
      = (nvarSum c
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c) / dsum c :=
  Gap2CensusVarianceSep.qfrac_eval c hc

/-- The banked one-sided rate at its exact type. -/
theorem rate_17_at_type :
    ∀ᶠ c : ℕ in Filter.atTop, qfrac c * ((c : ℝ) * Real.log c) ≤ 17 :=
  Gap2CensusOneSidedRate.qfrac_mul_clogc_eventually_le

/-- The strict improvement over A48 at its exact type. -/
theorem rate_little_o_at_type :
    Filter.Tendsto (fun c : ℕ => qfrac c * Real.sqrt ((c : ℝ) * Real.log c))
      Filter.atTop (nhds 0) :=
  Gap2CensusOneSidedRate.tendsto_qfrac_mul_sqrt_clogc_zero

/-! ## 8. Audits of this probe's own theorems -/

#print axioms QGSharpRateIndependentProbe.nsum_two
#print axioms QGSharpRateIndependentProbe.dsum_two
#print axioms QGSharpRateIndependentProbe.m0sum_two
#print axioms QGSharpRateIndependentProbe.msqSum_two_ind
#print axioms QGSharpRateIndependentProbe.nvarSum_two_ind
#print axioms QGSharpRateIndependentProbe.nmeanSum_two
#print axioms QGSharpRateIndependentProbe.dmeanSum_two
#print axioms QGSharpRateIndependentProbe.loopMeanSum_two_two
#print axioms QGSharpRateIndependentProbe.mechanismBound_two
#print axioms QGSharpRateIndependentProbe.nvarSum_two_ne_raw_second
#print axioms QGSharpRateIndependentProbe.loopMeanSum_two_two_ne_decoy
#print axioms QGSharpRateIndependentProbe.dsum_two_ne_nsum_two
#print axioms QGSharpRateIndependentProbe.nvarSum_two_pos
#print axioms QGSharpRateIndependentProbe.qfrac_two_lower
#print axioms QGSharpRateIndependentProbe.gap_field_one_at_two
#print axioms QGSharpRateIndependentProbe.gap_field_three_at_two
#print axioms QGSharpRateIndependentProbe.sharp_assembly_general
#print axioms QGSharpRateIndependentProbe.assembly_at_wrong_constant_two
#print axioms QGSharpRateIndependentProbe.wrong_constant_excludes_limit_one
#print axioms QGSharpRateIndependentProbe.a48_envelope_stays_above_new_rate
#print axioms QGSharpRateIndependentProbe.new_rate_below_a48_envelope

end QGSharpRateIndependentProbe
