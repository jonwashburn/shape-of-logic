import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusNvarSharp

/-!
# QG / C11 / A53 hostile review: the INDEPENDENT probe (reviewer side)

This is the hostile reviewer's own probe of `Gap2CensusNvarSharp`, written
from the reviewed module's statements and the banked context modules, not
from the worker's probe `NvarSharpCheck.lean`.  Every charged name below is
fully qualified and no `Gap2` namespace is opened, so the pins catch any
namespace shadowing or local redefinition inside the reviewed module.

1. **Axiom audits.**  `#print axioms` on the five head theorems and the
   consumed engines, from outside the proof module.  Each must show exactly
   `[propext, Classical.choice, Quot.sound]`.
2. **Statement pins at fully qualified types.**  The five head theorems are
   ascribed to types written with `Gap2CensusEnsembleLimit.qfrac`,
   `Gap2CensusVarianceSep.nvarSum`, `Gap2M0Asymptotics.dsum`,
   `Gap2M0Asymptotics.m0sum`, `Gap2AnomalyAsymptotics.resid`, and
   `Gap2SharpRateGap.SharpRateGap`, so a redefined ratio or a local copy of
   the gap structure breaks this build.
3. **Unconditionality.**  The discharged structure and the two TARGET 4
   theorems are hypothesis-free terms; the unconditional theorem is
   definitionally the A50 conditional assembly applied to the discharged
   structure; the conditional assembly still carries its hypothesis.
4. **Vacuity, recomputed from the definitions.**  The cap-2 census rows
   (`1`, `5/2`, `13/2`), `m0sum 2 = 10` summed from the rows,
   `nvarSum 2 = 5/2` by two independent routes (the `varSum` evaluation and
   the `nsum − msqSum` split), `dsum 2 = 7` from the `properSqSum` cells,
   and `0 < qfrac 2`.
5. **Wrong-constant and wrong-rate instruments on the UNCONDITIONAL
   theorems** (the worker's red tests covered the gap fields; these cover
   TARGET 4 itself): the scaled anomaly fraction cannot tend to `2` or to
   `0`, the `(1+o(1))` form cannot tend to `2`, and halving the rate scale
   (`c²/log c` instead of `2c²/log c`) gives limit `1/2`, hence cannot give
   `1`.  The constant `1` at the scale `2c²/log c` is pinned from both
   sides.
6. **The two shortcut claims, re-derived.**  (a) The A51 k-deficit lemma
   `sum_sub_cellW_le_two_wrow` is pinned at its real statement and
   `rowF_ge` is re-proved from it by the reviewer's own algebra.  (b) The
   resid test function is shown to be exactly `(log c / 2c) • nE` and a
   member of the count span, and the residual bound
   `‖r(m)‖²·m0sum ≤ residNumSum` is re-derived from the A50 span lemma and
   the module's product-sum evaluation, independently of the module's own
   `resid_negligible` proof.
-/

namespace QGNvarSharpIndependentProbe

open Topology

/-! ## 1. Outside-module axiom audits -/

#print axioms Gap2CensusNvarSharp.nvar_sharp
#print axioms Gap2CensusNvarSharp.resid_negligible
#print axioms Gap2CensusNvarSharp.sharpRateGap_discharged
#print axioms Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional
#print axioms Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional

-- The consumed engines and the two shortcut load-bearers.
#print axioms Gap2CensusDsumSaddle.dsum_saddle
#print axioms Gap2CensusDsumSaddle.sum_sub_cellW_le_two_wrow
#print axioms Gap2CensusNvarSharp.rowF_ge
#print axioms Gap2CensusNvarSharp.norm_sq_sub_smul_obsE
#print axioms Gap2CensusNvarSharp.tendsto_residNumSum_scale_zero
#print axioms Gap2CensusNvarSharp.tendsto_c_sq_log_mul_tailMassM_div_m0sum_zero

/-! ## 2. Statement pins at fully qualified types -/

/-- `nvar_sharp`, pinned with the genuine `nvarSum` and `dsum`. -/
theorem nvar_sharp_at_claimed_type : Filter.Tendsto
    (fun c : ℕ => Gap2CensusVarianceSep.nvarSum c * (2 * (c : ℝ) ^ 2)
      / (Real.log c * Gap2M0Asymptotics.dsum c))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.nvar_sharp

/-- `resid_negligible`, pinned with the genuine `resid`, observables,
`m0sum` and `dsum`. -/
theorem resid_negligible_at_claimed_type : Filter.Tendsto
    (fun c : ℕ =>
      ‖Gap2AnomalyAsymptotics.resid (Gap2CensusEnsembleLimit.obsV c)
          (Gap2CensusEnsembleLimit.obsE c) (Gap2CensusEnsembleLimit.obsT c)
          (Gap2CensusVarianceSep.obsM c)‖ ^ 2
        * Gap2M0Asymptotics.m0sum c * (2 * (c : ℝ) ^ 2)
        / (Real.log c * Gap2M0Asymptotics.dsum c))
    Filter.atTop (nhds 0) :=
  Gap2CensusNvarSharp.resid_negligible

/-- The discharged structure instantiates THE `SharpRateGap` from
`Gap2SharpRateGap.lean`, not a local copy. -/
theorem discharged_at_sharp_rate_gap : Gap2SharpRateGap.SharpRateGap :=
  Gap2CensusNvarSharp.sharpRateGap_discharged

/-- TARGET 4, pinned with the genuine `qfrac` of `Gap2CensusEnsembleLimit`. -/
theorem qfrac_sharp_rate_at_claimed_type : Filter.Tendsto
    (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional

/-- The `(1 + o(1))` form, pinned with the genuine `qfrac`. -/
theorem qfrac_one_add_o1_at_claimed_type : Filter.Tendsto
    (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2)))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional

/-- The structure's own first field, extracted and ascribed: the field
inside the discharged structure has the claimed type, not only the
standalone theorem. -/
theorem field_nvar_from_structure : Filter.Tendsto
    (fun c : ℕ => Gap2CensusVarianceSep.nvarSum c * (2 * (c : ℝ) ^ 2)
      / (Real.log c * Gap2M0Asymptotics.dsum c))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.sharpRateGap_discharged.nvar_sharp

/-- The structure's own second field, extracted and ascribed. -/
theorem field_resid_from_structure : Filter.Tendsto
    (fun c : ℕ =>
      ‖Gap2AnomalyAsymptotics.resid (Gap2CensusEnsembleLimit.obsV c)
          (Gap2CensusEnsembleLimit.obsE c) (Gap2CensusEnsembleLimit.obsT c)
          (Gap2CensusVarianceSep.obsM c)‖ ^ 2
        * Gap2M0Asymptotics.m0sum c * (2 * (c : ℝ) ^ 2)
        / (Real.log c * Gap2M0Asymptotics.dsum c))
    Filter.atTop (nhds 0) :=
  Gap2CensusNvarSharp.sharpRateGap_discharged.resid_negligible

/-- The structure's own third field is A51's `dsum_saddle`. -/
theorem field_dsum_from_structure : Filter.Tendsto
    (fun c : ℕ => Gap2M0Asymptotics.dsum c
      / ((c : ℝ) ^ 2 * Gap2M0Asymptotics.m0sum c))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.sharpRateGap_discharged.dsum_saddle

/-! ## 3. Unconditionality -/

/-- The unconditional theorem IS the A50 conditional assembly applied to the
discharged structure: no re-proof, no parallel argument. -/
theorem unconditional_is_conditional_at_discharged :
    Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional
      = Gap2SharpRateGap.qfrac_sharp_rate_of_gap
          Gap2CensusNvarSharp.sharpRateGap_discharged := rfl

/-- The `(1+o(1))` form is likewise the conditional one applied to the
discharged structure. -/
theorem one_add_o1_is_conditional_at_discharged :
    Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional
      = Gap2SharpRateGap.qfrac_sharp_rate_one_add_o1
          Gap2CensusNvarSharp.sharpRateGap_discharged := rfl

/-- Sanity in the other direction: the A50 assembly still carries its
hypothesis (nothing was weakened to make the discharge easier). -/
theorem conditional_still_conditional :
    Gap2SharpRateGap.SharpRateGap → Filter.Tendsto
      (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
      Filter.atTop (nhds 1) :=
  Gap2SharpRateGap.qfrac_sharp_rate_of_gap

/-- The structure's fields are definitionally the proved theorems. -/
example : Gap2CensusNvarSharp.sharpRateGap_discharged.nvar_sharp
    = Gap2CensusNvarSharp.nvar_sharp := rfl
example : Gap2CensusNvarSharp.sharpRateGap_discharged.resid_negligible
    = Gap2CensusNvarSharp.resid_negligible := rfl
example : Gap2CensusNvarSharp.sharpRateGap_discharged.dsum_saddle
    = Gap2CensusDsumSaddle.dsum_saddle := rfl

/-! ## 4. Vacuity, recomputed from the definitions -/

/-- Cap-2 census row at `n = 0`: only the `k = 0` cell contributes. -/
theorem wrow_two_zero_mine : Gap2M0Asymptotics.wrow 2 0 = 1 := by
  norm_num [Gap2M0Asymptotics.wrow, Finset.sum_range_succ, Nat.factorial]

/-- Cap-2 census row at `n = 1`: cells `1 + 1 + 1/2`. -/
theorem wrow_two_one_mine : Gap2M0Asymptotics.wrow 2 1 = 5 / 2 := by
  norm_num [Gap2M0Asymptotics.wrow, Finset.sum_range_succ, Nat.factorial]

/-- Cap-2 census row at `n = 2`: cells `1/2 + 2 + 4`. -/
theorem wrow_two_two_mine : Gap2M0Asymptotics.wrow 2 2 = 13 / 2 := by
  norm_num [Gap2M0Asymptotics.wrow, Finset.sum_range_succ, Nat.factorial]

/-- The cap-2 census mass, summed from the three rows recomputed above. -/
theorem m0sum_two_mine : Gap2M0Asymptotics.m0sum 2 = 10 := by
  have h : Gap2M0Asymptotics.m0sum 2
      = Gap2M0Asymptotics.wrow 2 0 + Gap2M0Asymptotics.wrow 2 1
        + Gap2M0Asymptotics.wrow 2 2 := by
    norm_num [Gap2M0Asymptotics.m0sum, Finset.sum_range_succ]
  rw [h, wrow_two_zero_mine, wrow_two_one_mine, wrow_two_two_mine]
  norm_num

/-- The variance sum at cap 2, computed directly from `varSum`'s
definition: only the `n = 2` row contributes, cells `1/2` and `2`. -/
theorem varSum_two_mine : Gap2CensusOneSidedRate.varSum 2 = 5 / 2 := by
  norm_num [Gap2CensusOneSidedRate.varSum, Finset.sum_range_succ, Nat.factorial,
    div_zero, zero_div]

/-- Route 1 to `nvarSum 2`: through `varSum`. -/
theorem nvarSum_two_via_varSum : Gap2CensusVarianceSep.nvarSum 2 = 5 / 2 := by
  rw [← Gap2CensusOneSidedRate.varSum_eq_nvarSum]
  exact varSum_two_mine

/-- The loop second-moment sum at cap 2, from the `loopSqSum` cells. -/
theorem nsum_two_mine : Gap2M0Asymptotics.nsum 2 = 10 := by
  have h00 : Gap2M0Asymptotics.loopSqSum 0 0 = 0 := by decide
  have h01 : Gap2M0Asymptotics.loopSqSum 0 1 = 0 := by decide
  have h02 : Gap2M0Asymptotics.loopSqSum 0 2 = 0 := by decide
  have h10 : Gap2M0Asymptotics.loopSqSum 1 0 = 0 := by decide
  have h11 : Gap2M0Asymptotics.loopSqSum 1 1 = 1 := by decide
  have h12 : Gap2M0Asymptotics.loopSqSum 1 2 = 4 := by decide
  have h20 : Gap2M0Asymptotics.loopSqSum 2 0 = 0 := by decide
  have h21 : Gap2M0Asymptotics.loopSqSum 2 1 = 2 := by decide
  have h22 : Gap2M0Asymptotics.loopSqSum 2 2 = 24 := by decide
  norm_num [Gap2M0Asymptotics.nsum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The conditional-mean-square sum at cap 2, from `msqSum`'s definition:
rows `0`, `3`, `9/2`. -/
theorem msqSum_two_mine : Gap2CensusVarianceSep.msqSum 2 = 15 / 2 := by
  norm_num [Gap2CensusVarianceSep.msqSum, Finset.sum_range_succ, Nat.factorial,
    div_zero, zero_div]

/-- Route 2 to `nvarSum 2`: through the `nsum − msqSum` split. -/
theorem nvarSum_two_via_sub : Gap2CensusVarianceSep.nvarSum 2 = 5 / 2 := by
  have h : Gap2CensusVarianceSep.nvarSum 2
      = Gap2M0Asymptotics.nsum 2 - Gap2CensusVarianceSep.msqSum 2 := rfl
  rw [h, nsum_two_mine, msqSum_two_mine]
  norm_num

/-- The two routes agree (and hence each is `5/2`, not junk). -/
theorem nvarSum_two_routes_agree :
    Gap2CensusVarianceSep.nvarSum 2 = 5 / 2
      ∧ Gap2CensusVarianceSep.nvarSum 2 = 5 / 2 :=
  ⟨nvarSum_two_via_varSum, nvarSum_two_via_sub⟩

/-- The proper second-moment sum at cap 2, from the `properSqSum` cells:
`(2,1) ↦ 1`, `(2,2) ↦ 6`. -/
theorem dsum_two_mine : Gap2M0Asymptotics.dsum 2 = 7 := by
  have h00 : Gap2M0Asymptotics.properSqSum 0 0 = 0 := by decide
  have h01 : Gap2M0Asymptotics.properSqSum 0 1 = 0 := by decide
  have h02 : Gap2M0Asymptotics.properSqSum 0 2 = 0 := by decide
  have h10 : Gap2M0Asymptotics.properSqSum 1 0 = 0 := by decide
  have h11 : Gap2M0Asymptotics.properSqSum 1 1 = 0 := by decide
  have h12 : Gap2M0Asymptotics.properSqSum 1 2 = 0 := by decide
  have h20 : Gap2M0Asymptotics.properSqSum 2 0 = 0 := by decide
  have h21 : Gap2M0Asymptotics.properSqSum 2 1 = 2 := by decide
  have h22 : Gap2M0Asymptotics.properSqSum 2 2 = 24 := by decide
  norm_num [Gap2M0Asymptotics.dsum, Finset.sum_range_succ, Nat.factorial,
    h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- The anomaly fraction at cap 2 is strictly positive: the sequences the
rate theorems are about are genuinely nonzero.  Recomputed here from
`qfrac_eval` plus the reviewer's own cap-2 numbers. -/
theorem qfrac_two_pos_mine : 0 < Gap2CensusEnsembleLimit.qfrac 2 := by
  rw [Gap2CensusVarianceSep.qfrac_eval 2 (le_refl 2), nvarSum_two_via_varSum,
    dsum_two_mine]
  have hX : (0 : ℝ) ≤ ‖Gap2AnomalyAsymptotics.resid (Gap2CensusEnsembleLimit.obsV 2)
        (Gap2CensusEnsembleLimit.obsE 2) (Gap2CensusEnsembleLimit.obsT 2)
        (Gap2CensusVarianceSep.obsM 2)‖ ^ 2 * Gap2M0Asymptotics.m0sum 2 :=
    mul_nonneg (sq_nonneg _) (Gap2M0Asymptotics.m0sum_pos 2).le
  exact div_pos
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 2) (le_add_of_nonneg_right hX))
    (by norm_num)

/-- The sharp-rate limit has content: the scaled anomaly fraction is
eventually within `(1/2, 3/2)` of `1`. -/
theorem scaled_qfrac_eventually_near_one :
    ∀ᶠ c : ℕ in Filter.atTop,
      Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c)
        ∈ Set.Ioo (1 / 2) (3 / 2) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional.eventually
    (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))

/-- The third field's limit has content: `dsum / (c²·m0sum)` is eventually
within `(1/2, 3/2)` of `1`. -/
theorem dsum_ratio_eventually_near_one :
    ∀ᶠ c : ℕ in Filter.atTop,
      Gap2M0Asymptotics.dsum c / ((c : ℝ) ^ 2 * Gap2M0Asymptotics.m0sum c)
        ∈ Set.Ioo (1 / 2) (3 / 2) :=
  Gap2CensusDsumSaddle.dsum_saddle.eventually
    (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3 / 2))

/-! ## 5. Wrong-constant and wrong-rate instruments on TARGET 4 itself -/

/-- WRONG CONSTANT, refuted: the scaled anomaly fraction cannot tend to
`2`.  Limit uniqueness against the proved unconditional theorem. -/
theorem wrong_constant_two_refuted :
    ¬ Filter.Tendsto
        (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
        Filter.atTop (nhds 2) := by
  intro h
  have huniq := tendsto_nhds_unique Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional h
  norm_num at huniq

/-- WRONG CONSTANT, refuted: the scaled anomaly fraction cannot tend to
`0` either (the rate is not faster than `(log c)/(2c²)`). -/
theorem wrong_constant_zero_refuted :
    ¬ Filter.Tendsto
        (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c))
        Filter.atTop (nhds 0) := by
  intro h
  have huniq := tendsto_nhds_unique Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional h
  norm_num at huniq

/-- WRONG CONSTANT, refuted: the `(1+o(1))` form cannot tend to `2`. -/
theorem one_add_o1_wrong_constant_refuted :
    ¬ Filter.Tendsto
        (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2)))
        Filter.atTop (nhds 2) := by
  intro h
  have huniq :=
    tendsto_nhds_unique Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional h
  norm_num at huniq

/-- WRONG CONSTANT on the first gap field, refuted with a constant the
worker's probe did not test: `nvar_sharp` cannot tend to `0`. -/
theorem nvar_sharp_wrong_constant_zero_refuted :
    ¬ Filter.Tendsto
        (fun c : ℕ => Gap2CensusVarianceSep.nvarSum c * (2 * (c : ℝ) ^ 2)
          / (Real.log c * Gap2M0Asymptotics.dsum c))
        Filter.atTop (nhds 0) := by
  intro h
  have huniq := tendsto_nhds_unique Gap2CensusNvarSharp.nvar_sharp h
  norm_num at huniq

/-- WRONG RATE SCALE, computed: at half the rate scale (`c²/log c` instead
of `2c²/log c`) the limit is `1/2`, derived from the proved theorem. -/
theorem half_scale_gives_half :
    Filter.Tendsto
        (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * ((c : ℝ) ^ 2 / Real.log c))
        Filter.atTop (nhds (1 / 2)) := by
  have hdiv := Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional.div
    tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0)
  have heq : (fun c : ℕ =>
        Gap2CensusEnsembleLimit.qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c) / 2)
      =ᶠ[Filter.atTop] (fun c : ℕ =>
        Gap2CensusEnsembleLimit.qfrac c * ((c : ℝ) ^ 2 / Real.log c)) := by
    filter_upwards [Filter.eventually_ge_atTop 2] with c hc
    have hL : Real.log (c : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
    field_simp [hL]
  exact hdiv.congr' heq

/-- WRONG RATE SCALE, refuted: the half-scaled ratio cannot tend to `1`.
The scale constant `2` is pinned, not just the limit constant `1`. -/
theorem half_scale_cannot_give_one :
    ¬ Filter.Tendsto
        (fun c : ℕ => Gap2CensusEnsembleLimit.qfrac c * ((c : ℝ) ^ 2 / Real.log c))
        Filter.atTop (nhds 1) := by
  intro h
  have huniq := tendsto_nhds_unique half_scale_gives_half h
  norm_num at huniq

/-! ## 6. The two shortcut claims, re-derived -/

/-- The A51 k-deficit lemma, pinned at its real statement with the genuine
`cellW` and `wrow`. -/
theorem a51_kdeficit_pinned : ∀ (c n : ℕ), (2 : ℝ) * c ≤ (n : ℝ) ^ 2 →
    ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * Gap2CensusDsumSaddle.cellW c n k
      ≤ 2 * Gap2M0Asymptotics.wrow c n :=
  Gap2CensusDsumSaddle.sum_sub_cellW_le_two_wrow

/-- The module's `rowF_ge`, pinned at its stated conclusion. -/
theorem rowF_ge_pinned (c n : ℕ) (hn : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2) :
    ((c : ℝ) - 2) * Gap2M0Asymptotics.wrow c n ≤ Gap2CensusNvarSharp.rowF c n :=
  Gap2CensusNvarSharp.rowF_ge c n hn

/-- SHORTCUT (a), re-derived by the reviewer: the `(c−2)·wrow` lower bound
on the row first moment follows from the pinned A51 k-deficit lemma by the
cap-split identity `c·wrow = rowF + Σ (c−k)·cellW`, with no separate
k-window machinery. -/
theorem rowF_ge_rederived (c n : ℕ) (hn : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2) :
    ((c : ℝ) - 2) * Gap2M0Asymptotics.wrow c n ≤ Gap2CensusNvarSharp.rowF c n := by
  have h := Gap2CensusDsumSaddle.sum_sub_cellW_le_two_wrow c n hn
  have hsplit : (c : ℝ) * Gap2M0Asymptotics.wrow c n
      = Gap2CensusNvarSharp.rowF c n
        + ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * Gap2CensusDsumSaddle.cellW c n k := by
    simp only [Gap2CensusNvarSharp.rowF]
    rw [Gap2CensusDsumSaddle.wrow_eq_sum_cellW, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkc : k ≤ c := Nat.lt_succ_iff.1 hk
    rw [Nat.cast_sub hkc]
    ring
  have hwr : (0 : ℝ) ≤ Gap2M0Asymptotics.wrow c n := Gap2M0Asymptotics.wrow_nonneg c n
  linarith [h, hsplit]

/-- The resid test scale is definitionally `(log c)/(2c)`. -/
example (c : ℕ) : Gap2CensusNvarSharp.aResid c = Real.log (c : ℝ) / (2 * (c : ℝ)) := rfl

/-- The edge-count observable is definitionally `nE`. -/
example (c : ℕ) : Gap2CensusEnsembleLimit.obsE c = Gap2CensusMeasure.nE (c := c) := rfl

/-- SHORTCUT (b), membership leg: the resid test function
`y = (log c / 2c) • nE` is a member of the count span, verified directly. -/
theorem test_function_in_count_span (c : ℕ) :
    (Gap2CensusNvarSharp.aResid c) • Gap2CensusEnsembleLimit.obsE c
      ∈ Gap2AnomalyAsymptotics.countSpan (Gap2CensusEnsembleLimit.obsV c)
          (Gap2CensusEnsembleLimit.obsE c) (Gap2CensusEnsembleLimit.obsT c) :=
  Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The module's product-sum evaluation, pinned. -/
theorem norm_sq_sub_smul_obsE_pinned (c : ℕ) (a : ℝ) :
    ‖Gap2CensusVarianceSep.obsM c - a • Gap2CensusEnsembleLimit.obsE c‖ ^ 2
      = Gap2CensusNvarSharp.residNumSum c a / Gap2M0Asymptotics.m0sum c :=
  Gap2CensusNvarSharp.norm_sq_sub_smul_obsE c a

/-- SHORTCUT (b), bound leg, re-derived by the reviewer: the residual bound
`‖r(m)‖²·m0sum ≤ residNumSum` from the A50 span lemma and the pinned
product-sum evaluation, independently of the module's `resid_negligible`. -/
theorem resid_bound_rederived (c : ℕ) :
    ‖Gap2AnomalyAsymptotics.resid (Gap2CensusEnsembleLimit.obsV c)
        (Gap2CensusEnsembleLimit.obsE c) (Gap2CensusEnsembleLimit.obsT c)
        (Gap2CensusVarianceSep.obsM c)‖ ^ 2 * Gap2M0Asymptotics.m0sum c
      ≤ Gap2CensusNvarSharp.residNumSum c (Gap2CensusNvarSharp.aResid c) := by
  have hm0 : (0 : ℝ) < Gap2M0Asymptotics.m0sum c := Gap2M0Asymptotics.m0sum_pos c
  have h1 := Gap2CensusVarianceSep.norm_sq_resid_le_of_mem_span c
    (Gap2CensusVarianceSep.obsM c)
    ((Gap2CensusNvarSharp.aResid c) • Gap2CensusEnsembleLimit.obsE c)
    (test_function_in_count_span c)
  rw [Gap2CensusNvarSharp.norm_sq_sub_smul_obsE] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 hm0.le
  rwa [div_mul_cancel₀ _ hm0.ne'] at h2

/-! ## 7. Audits of this probe's own theorems -/

#print axioms QGNvarSharpIndependentProbe.qfrac_two_pos_mine
#print axioms QGNvarSharpIndependentProbe.m0sum_two_mine
#print axioms QGNvarSharpIndependentProbe.nvarSum_two_via_varSum
#print axioms QGNvarSharpIndependentProbe.nvarSum_two_via_sub
#print axioms QGNvarSharpIndependentProbe.dsum_two_mine
#print axioms QGNvarSharpIndependentProbe.wrong_constant_two_refuted
#print axioms QGNvarSharpIndependentProbe.wrong_constant_zero_refuted
#print axioms QGNvarSharpIndependentProbe.one_add_o1_wrong_constant_refuted
#print axioms QGNvarSharpIndependentProbe.half_scale_cannot_give_one
#print axioms QGNvarSharpIndependentProbe.rowF_ge_rederived
#print axioms QGNvarSharpIndependentProbe.resid_bound_rederived
#print axioms QGNvarSharpIndependentProbe.unconditional_is_conditional_at_discharged

end QGNvarSharpIndependentProbe
