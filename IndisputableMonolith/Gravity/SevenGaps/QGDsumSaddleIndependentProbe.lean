import IndisputableMonolith.Gravity.SevenGaps.DsumSaddleCheck

/-!
# Hostile-review independent probe for A51 (`dsum_saddle`)

Session `qg-a51-review`, 2026-08-01.  The work under review:
`Gap2CensusDsumSaddle.dsum_saddle` (the third `SharpRateGap` field, claimed
THEOREM at kernel strength) and its red-test module `DsumSaddleCheck`.  This
probe re-verifies from outside.  Nothing here reuses the worker's proof
machinery: the numeric pins are computed from `cellCount` upward, and the only
inputs taken as given are the reviewed A48 to A50 modules and the definitions.

## 1. Statement fidelity

The third field's type is transcribed here from scratch (same opens as
`Gap2SharpRateGap.lean`) and discharged by the proved theorem; a
structure-update repackaging and a from-scratch packaging with my own binder
names give two further kernel checks that the proved statement IS the field,
not a weaker statement wearing the notation.  The A50 conditional assembly is
then applied to MY packaging.

## 2. Vacuity

`dsum` and `m0sum` kernel-computed at `c = 2` and `c = 3` from `cellCount`
upward (my own cell pins, never the worker's ratio route).  The ratio sequence
is `7/40` at `c = 2` and `89/265` at `c = 3`: genuine nonzero quantities,
strictly below 1, rising, consistent with the claimed concentration to 1.

## 3. Decoys, each refuted by kernel computation

* loop/proper swap: `dsum 2 = 7 ≠ 10 = nsum 2`;
* wrong saddle scale: with the cut at `n² ≤ 2c` instead of `n² ≤ c·log c`, the
  `c = 2` small region is every row and the small-mass ratio is `1`; at the
  true scale it is `7/20` (`smallSet 2 = {0, 1}` proved from `1/2 ≤ log 2 < 1`);
* dropped `(1−1/n)²` factor: the per-cell deficit bound would read
  `c² − ρ ≤ c² − k²`; at `(c, n, k) = (2, 2, 2)` that says `5/2 ≤ 0`, false,
  so the `2k²/n` term (and hence the `(1−1/n)²` factor) is load-bearing.

## 4. Axiom audits

Printed from THIS file for every head theorem of both modules under review,
plus the probe's own field-fidelity theorems.
-/

namespace QGDsumSaddleIndependentProbe

open Gap2SharpRateGap Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Finset Filter

/-! ## 1. Statement fidelity, ascribed from scratch -/

/-- The third field's type, transcribed independently, discharged by the
proved theorem. -/
theorem dsum_saddle_has_field_type :
    Filter.Tendsto (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c)) Filter.atTop (nhds 1) :=
  Gap2CensusDsumSaddle.dsum_saddle

/-- Structure-update check: swap the proved theorem into ANY `SharpRateGap`'s
third field.  Elaborates only if the theorem's type is definitionally the
field's type. -/
def repackagedGap (g : SharpRateGap) : SharpRateGap :=
  { g with dsum_saddle := Gap2CensusDsumSaddle.dsum_saddle }

/-- My own from-scratch packaging (own binder names), independent of
`DsumSaddleCheck.gapWithDsumSaddle`. -/
def myOwnGap
    (nvar_field : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1))
    (resid_field : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    SharpRateGap where
  nvar_sharp := nvar_field
  resid_negligible := resid_field
  dsum_saddle := Gap2CensusDsumSaddle.dsum_saddle

/-- The A50 conditional assembly consumes MY packaging: with the first two
fields supplied, the sharp rate follows.  This is the check that the proved
field slots into the assembly exactly where the gap's third field sits. -/
theorem assembly_consumes_my_gap
    (h1 : Filter.Tendsto
      (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1))
    (h2 : Filter.Tendsto
      (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) :=
  qfrac_sharp_rate_of_gap (myOwnGap h1 h2)

/-! ## 2. Vacuity: kernel pins from `cellCount` upward -/

-- Cell pins, each by kernel evaluation of the census definition
-- `cellCount n k j = C(k,j) · n^j · (n²−n)^(k−j)`.
theorem cc_2_1_0 : cellCount 2 1 0 = 2 := by decide
theorem cc_2_1_1 : cellCount 2 1 1 = 2 := by decide
theorem cc_2_2_0 : cellCount 2 2 0 = 4 := by decide
theorem cc_2_2_1 : cellCount 2 2 1 = 8 := by decide
theorem cc_2_2_2 : cellCount 2 2 2 = 4 := by decide
theorem cc_2_3_0 : cellCount 2 3 0 = 8 := by decide
theorem cc_2_3_1 : cellCount 2 3 1 = 24 := by decide
theorem cc_2_3_2 : cellCount 2 3 2 = 24 := by decide
theorem cc_2_3_3 : cellCount 2 3 3 = 8 := by decide
theorem cc_3_1_0 : cellCount 3 1 0 = 6 := by decide
theorem cc_3_1_1 : cellCount 3 1 1 = 3 := by decide
theorem cc_3_2_0 : cellCount 3 2 0 = 36 := by decide
theorem cc_3_2_1 : cellCount 3 2 1 = 36 := by decide
theorem cc_3_2_2 : cellCount 3 2 2 = 9 := by decide
theorem cc_3_3_0 : cellCount 3 3 0 = 216 := by decide
theorem cc_3_3_1 : cellCount 3 3 1 = 324 := by decide
theorem cc_3_3_2 : cellCount 3 3 2 = 162 := by decide
theorem cc_3_3_3 : cellCount 3 3 3 = 27 := by decide

/-- `properSqSum 2 1`, summed from my cell pins (range recursion, not the
worker's ratio theorem). -/
theorem pss_2_1 : properSqSum 2 1 = 2 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    cc_2_1_0, cc_2_1_1]
  decide

theorem pss_2_2 : properSqSum 2 2 = 24 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, cc_2_2_0, cc_2_2_1, cc_2_2_2]
  decide

theorem pss_2_3 : properSqSum 2 3 = 192 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, cc_2_3_0, cc_2_3_1, cc_2_3_2, cc_2_3_3]
  decide

theorem pss_3_1 : properSqSum 3 1 = 6 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    cc_3_1_0, cc_3_1_1]
  decide

theorem pss_3_2 : properSqSum 3 2 = 180 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, cc_3_2_0, cc_3_2_1, cc_3_2_2]
  decide

theorem pss_3_3 : properSqSum 3 3 = 3402 := by
  unfold properSqSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, cc_3_3_0, cc_3_3_1, cc_3_3_2, cc_3_3_3]
  decide

/-- The proper second-moment sum at cap 2: only cells `(2,1) ↦ 1` and
`(2,2) ↦ 6` contribute. -/
theorem dsum_two_pin : dsum 2 = 7 := by
  have z00 : properSqSum 0 0 = 0 := by decide
  have z01 : properSqSum 0 1 = 0 := by decide
  have z02 : properSqSum 0 2 = 0 := by decide
  have z10 : properSqSum 1 0 = 0 := by decide
  have z11 : properSqSum 1 1 = 0 := by decide
  have z12 : properSqSum 1 2 = 0 := by decide
  have z20 : properSqSum 2 0 = 0 := by decide
  norm_num [dsum, Finset.sum_range_succ, Nat.factorial,
    z00, z01, z02, z10, z11, z12, z20, pss_2_1, pss_2_2]

/-- The proper second-moment sum at cap 3: cells `(2,1) ↦ 1`, `(2,2) ↦ 6`,
`(2,3) ↦ 16`, `(3,1) ↦ 1`, `(3,2) ↦ 15`, `(3,3) ↦ 189/2`. -/
theorem dsum_three_pin : dsum 3 = 267 / 2 := by
  have z00 : properSqSum 0 0 = 0 := by decide
  have z01 : properSqSum 0 1 = 0 := by decide
  have z02 : properSqSum 0 2 = 0 := by decide
  have z03 : properSqSum 0 3 = 0 := by decide
  have z10 : properSqSum 1 0 = 0 := by decide
  have z11 : properSqSum 1 1 = 0 := by decide
  have z12 : properSqSum 1 2 = 0 := by decide
  have z13 : properSqSum 1 3 = 0 := by decide
  have z20 : properSqSum 2 0 = 0 := by decide
  have z30 : properSqSum 3 0 = 0 := by decide
  norm_num [dsum, Finset.sum_range_succ, Nat.factorial,
    z00, z01, z02, z03, z10, z11, z12, z13, z20, z30,
    pss_2_1, pss_2_2, pss_2_3, pss_3_1, pss_3_2, pss_3_3]

/-- The census mass sum at cap 2: rows `1`, `5/2`, `13/2`. -/
theorem m0sum_two_pin : m0sum 2 = 10 := by
  norm_num [m0sum, wrow, Finset.sum_range_succ, Nat.factorial]

/-- The census mass sum at cap 3: rows `1`, `8/3`, `71/6`, `86/3`. -/
theorem m0sum_three_pin : m0sum 3 = 265 / 6 := by
  norm_num [m0sum, wrow, Finset.sum_range_succ, Nat.factorial]

/-- The saddle ratio at `c = 2`: a genuine nonzero quantity. -/
theorem ratio_at_two : dsum 2 / ((2:ℝ)^2 * m0sum 2) = 7 / 40 := by
  rw [dsum_two_pin, m0sum_two_pin]; norm_num

/-- The saddle ratio at `c = 3`. -/
theorem ratio_at_three : dsum 3 / ((3:ℝ)^2 * m0sum 3) = 89 / 265 := by
  rw [dsum_three_pin, m0sum_three_pin]; norm_num

/-- Content witness: the ratio sequence is nonzero, strictly below 1, and
rising at caps 2 and 3, consistent with the claimed concentration to 1 and
inconsistent with a vacuous or constant reading of the statement. -/
theorem ratio_content_witness :
    (0:ℝ) < 7 / 40 ∧ (7:ℝ)/40 < 89/265 ∧ (89:ℝ)/265 < 1 := by norm_num

/-! ## 3. Decoys, each refuted -/

/-- The loop second-moment sum at cap 2, from the census definitions. -/
theorem nsum_two_pin : nsum 2 = 10 := by
  have l00 : loopSqSum 0 0 = 0 := by decide
  have l01 : loopSqSum 0 1 = 0 := by decide
  have l02 : loopSqSum 0 2 = 0 := by decide
  have l10 : loopSqSum 1 0 = 0 := by decide
  have l11 : loopSqSum 1 1 = 1 := by decide
  have l12 : loopSqSum 1 2 = 4 := by decide
  have l20 : loopSqSum 2 0 = 0 := by decide
  have l21 : loopSqSum 2 1 = 2 := by decide
  have l22 : loopSqSum 2 2 = 24 := by decide
  norm_num [nsum, Finset.sum_range_succ, Nat.factorial,
    l00, l01, l02, l10, l11, l12, l20, l21, l22]

/-- DECOY REFUTED (loop/proper swap): `dsum` is the proper second moment, not
the loop one; confusing them changes the value at cap 2. -/
theorem loop_proper_swap_decoy : dsum 2 ≠ nsum 2 := by
  rw [dsum_two_pin, nsum_two_pin]; norm_num

/-- `1/2 ≤ log 2`, from `exp(1/2)² = exp 1 < 2.7182818286 < 4`. -/
theorem half_le_log_two : (1:ℝ)/2 ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
  have h2 : (Real.exp ((1:ℝ)/2)) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add, show (1:ℝ)/2 + 1/2 = 1 by norm_num]
  have h3 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hpos : (0:ℝ) < Real.exp ((1:ℝ)/2) := Real.exp_pos _
  nlinarith [h2, h3, hpos]

/-- `log 2 < 1`, from `log x < x − 1` off 1. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
  linarith

theorem zero_in_true_cut : ((0:ℕ):ℝ)^2 ≤ ((2:ℕ):ℝ) * Real.log ((2:ℕ):ℝ) := by
  have h0 : (0:ℝ) ≤ Real.log 2 := by linarith [half_le_log_two]
  have e1 : (((0:ℕ):ℝ)^2) = 0 := by norm_num
  have e2 : ((2:ℕ):ℝ) = 2 := by norm_num
  rw [e1, e2]
  linarith

theorem one_in_true_cut : ((1:ℕ):ℝ)^2 ≤ ((2:ℕ):ℝ) * Real.log ((2:ℕ):ℝ) := by
  have e1 : (((1:ℕ):ℝ)^2) = 1 := by norm_num
  have e2 : ((2:ℕ):ℝ) = 2 := by norm_num
  rw [e1, e2]
  linarith [half_le_log_two]

theorem two_not_in_true_cut : ¬ (((2:ℕ):ℝ)^2 ≤ ((2:ℕ):ℝ) * Real.log ((2:ℕ):ℝ)) := by
  have e1 : (((2:ℕ):ℝ)^2) = 4 := by norm_num
  have e2 : ((2:ℕ):ℝ) = 2 := by norm_num
  rw [e1, e2]
  intro h
  linarith [log_two_lt_one]

/-- The true saddle cut at cap 2 is exactly `{0, 1}`: row 2, which carries 6
of the 7 units of `dsum 2`, sits in the LARGE region.  The split is real. -/
theorem smallSet_two_eq : smallSet 2 = {0, 1} := by
  ext n
  simp only [smallSet, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hn3, hle⟩
    have hncases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hncases with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hle two_not_in_true_cut
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, zero_in_true_cut⟩
    · exact ⟨by norm_num, one_in_true_cut⟩

/-- The small mass at cap 2 under the TRUE saddle scale: rows `1` and `5/2`. -/
theorem smallMass_two_pin : smallMass 2 = 7 / 2 := by
  have h : smallMass 2 = wrow 2 0 + wrow 2 1 := by
    simp only [smallMass, smallSet_two_eq]
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  rw [h]
  norm_num [wrow, Finset.sum_range_succ, Nat.factorial]

/-- The small-mass ratio at the true scale: `7/20`, a genuine proper
submass. -/
theorem true_scale_small_ratio : smallMass 2 / m0sum 2 = 7 / 20 := by
  rw [smallMass_two_pin, m0sum_two_pin]; norm_num

/-- DECOY SETUP (wrong saddle scale): with the cut at `n² ≤ 2c` instead of
`n² ≤ c·log c`, the cap-2 small region is every row. -/
theorem wrong_scale_region_two :
    (Finset.range 3).filter (fun n : ℕ => (n:ℝ)^2 ≤ 2 * 2) = {0, 1, 2} := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hn3, -⟩
    have hncases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hncases with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩

/-- DECOY REFUTED (wrong saddle scale): at the wrong cut the cap-2 "small"
mass is the whole mass, ratio `1`, so the small-mass term of the deficit bound
carries nothing; the true scale `c·log c` (ratio `7/20` and proved to tend to
0 by A48) is load-bearing, not decorative. -/
theorem wrong_scale_ratio_is_one :
    (∑ n ∈ (Finset.range 3).filter (fun n : ℕ => (n:ℝ)^2 ≤ 2 * 2), wrow 2 n) / m0sum 2 = 1 := by
  rw [wrong_scale_region_two]
  have hrange : ({0, 1, 2} : Finset ℕ) = Finset.range 3 := by decide
  rw [hrange]
  exact div_self (m0sum_pos 2).ne'

/-- The contrast, stated: the true-scale ratio is not 1. -/
theorem wrong_scale_contrast : smallMass 2 / m0sum 2 ≠ 1 := by
  rw [true_scale_small_ratio]; norm_num

/-- The conditional proper second moment at `(2,2)`, from the worker's ratio
DEFINITION (not his theorems): `(2·(1/2))² + (2/2)(1/2) = 3/2`. -/
theorem properRatio_two_two : Gap2CensusDsumSaddle.properRatio 2 2 = 3 / 2 := by
  simp only [Gap2CensusDsumSaddle.properRatio]
  norm_num

/-- Cross-check from my own cell pins, independent of the worker's
`conditional_proper_sq_mean` route: `properSqSum 2 2 / 2⁴ = 24/16 = 3/2`,
agreeing with the ratio the proof manipulates. -/
theorem proper_ratio_cross_check : (properSqSum 2 2 : ℝ) / (2:ℝ) ^ (2 * 2) = 3 / 2 := by
  rw [pss_2_2]; norm_num

/-- DECOY REFUTED (dropped `(1−1/n)²` factor): without that factor the
per-cell deficit bound would read `c² − ρ ≤ c² − k²`; at `(c,n,k) = (2,2,2)`
that is `5/2 ≤ 0`, false.  The `2k²/n` term in the worker's
`c_sq_sub_properRatio_le` is load-bearing. -/
theorem dropped_factor_decoy_fails :
    ¬ ((2:ℝ)^2 - Gap2CensusDsumSaddle.properRatio 2 2 ≤ (2:ℝ)^2 - (2:ℝ)^2) := by
  rw [properRatio_two_two]; norm_num

/-! ## 4. The lower bound carries three terms (killed-route check)

The killed A48-era overclaim was "mechanismBound from `smallMass/m0sum`
alone".  The A51 lower bound's own STATEMENT shows the deficit is bounded by
three terms, only one of which is the small-mass ratio; the `4/c` and
`2/√(c·log c)` terms come from the large-row per-cell bound and the geometric
`k`-sum, not from any mass ratio.  The `#check`s record the statements in the
build log. -/

#check @Gap2CensusDsumSaddle.one_sub_le_dsum_div
#check @Gap2CensusDsumSaddle.c_sq_m0sum_sub_dsum_le
#check @Gap2CensusDsumSaddle.large_row_deficit_le'
#check @Gap2CensusDsumSaddle.sum_sq_sub_cellW_le
#check @Gap2CensusDsumSaddle.dsum_saddle

/-! ## 5. Axiom audits, printed from this probe -/

#print axioms Gap2CensusDsumSaddle.dsum_saddle
#print axioms Gap2CensusDsumSaddle.dsum_le
#print axioms Gap2CensusDsumSaddle.dsum_div_le
#print axioms Gap2CensusDsumSaddle.one_sub_le_dsum_div
#print axioms Gap2CensusDsumSaddle.c_sq_m0sum_sub_dsum_le
#print axioms Gap2CensusDsumSaddle.large_row_deficit_le
#print axioms Gap2CensusDsumSaddle.large_row_deficit_le'
#print axioms Gap2CensusDsumSaddle.sum_sq_sub_cellW_le
#print axioms Gap2CensusDsumSaddle.sum_sub_cellW_le_two_wrow
#print axioms Gap2CensusDsumSaddle.sum_k_sq_div_cellW_le
#print axioms Gap2CensusDsumSaddle.properRatio_le
#print axioms Gap2CensusDsumSaddle.c_sq_sub_properRatio_le
#print axioms Gap2CensusDsumSaddle.weighted_geom_half
#print axioms Gap2CensusDsumSaddle.weighted_geom_rev
#print axioms Gap2CensusDsumSaddle.properSqSum_eq_pow_mul_ratio
#print axioms Gap2CensusDsumSaddle.properSqSum_zero_left
#print axioms Gap2CensusDsumSaddle.pRow_nonneg
#print axioms Gap2CensusDsumSaddle.cellW_top_le_wrow
#print axioms Gap2CensusDsumSaddle.largeSet_mem_ge_one
#print axioms Gap2CensusDsumSaddle.largeSet_mem_two_c_le
#print axioms DsumSaddleCheck.gapWithDsumSaddle
#print axioms dsum_saddle_has_field_type
#print axioms myOwnGap
#print axioms assembly_consumes_my_gap

end QGDsumSaddleIndependentProbe
