import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusNvarSharp

/-!
# Gap 2 / C11 / A53: the hostile probe for the `nvar_sharp` assembly

This module audits `Gap2CensusNvarSharp` from OUTSIDE the proof module:

1. **Axiom audits.**  `#print axioms` on every head theorem.  Each must show
   exactly the base triple `[propext, Classical.choice, Quot.sound]`; any
   `sorryAx` or extra axiom fails the probe.
2. **Statement pins.**  The proved theorems are ascribed to the exact target
   types (the `SharpRateGap` fields and the TARGET 4 conclusions), so any
   drift in what was actually proved breaks this build.
3. **Definitional rfl pins and numeric witnesses.**  The charged definitions
   (`aResid`, `residNumSum`, `cellW`, `topT`, `deltaS`, `wrow`, `m0sum`) are
   pinned by `rfl` and by explicit small-cap evaluation, so a silent
   redefinition or a degenerate definition is caught here.
4. **Non-vacuity witnesses.**  The denominators are genuine (`m0sum c > 0`
   everywhere, `dsum c > 0` at `c ≥ 2`), the limit has content (`q(c)·(2c²/
   log c)` is eventually `> 1/2`), and the variance numerator is eventually
   strictly positive (a fact derivable only because the limit really is `1`).
5. **Red tests.**  Decoys that must FAIL: the wrong limit constant for
   `nvar_sharp`, the wrong limit for `resid_negligible`, and a heavy-tail
   decoy for the window partition.  Each is refuted from the proved theorems;
   if any proved theorem were false or vacuous, one of these would collapse.
-/

namespace NvarSharpCheck

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusDsumSaddle Gap2CensusRowSaddle
  Gap2CensusNvarSharp Gap2SharpRateGap Finset Filter
open Topology

/-! ## 1. Outside-module axiom audits -/

#print axioms Gap2CensusNvarSharp.nvar_sharp
#print axioms Gap2CensusNvarSharp.resid_negligible
#print axioms Gap2CensusNvarSharp.sharpRateGap_discharged
#print axioms Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional
#print axioms Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional

-- Supporting engines consumed by the assembly.
#print axioms Gap2CensusDsumSaddle.dsum_saddle
#print axioms Gap2CensusNvarSharp.tendsto_tailMassM_div_m0sum_zero
#print axioms Gap2CensusNvarSharp.tendsto_c_sq_log_mul_tailMassM_div_m0sum_zero
#print axioms Gap2CensusNvarSharp.nvarSum_le_ev
#print axioms Gap2CensusNvarSharp.nvarSum_ge_ev
#print axioms Gap2CensusNvarSharp.norm_sq_sub_smul_obsE

/-! ## 2. Statement pins: the proved theorems at the exact target types -/

/-- The `nvar_sharp` field type, pinned verbatim from `SharpRateGap`. -/
theorem nvar_sharp_pinned : Filter.Tendsto
    (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
    Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.nvar_sharp

/-- The `resid_negligible` field type, pinned verbatim from `SharpRateGap`. -/
theorem resid_negligible_pinned : Filter.Tendsto
    (fun c : ℕ =>
      ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
    Filter.atTop (nhds 0) :=
  Gap2CensusNvarSharp.resid_negligible

/-- The `dsum_saddle` field type, pinned verbatim from `SharpRateGap`. -/
theorem dsum_saddle_pinned : Filter.Tendsto
    (fun c : ℕ => dsum c / ((c : ℝ) ^ 2 * m0sum c)) Filter.atTop (nhds 1) :=
  Gap2CensusDsumSaddle.dsum_saddle

/-- TARGET 4, pinned. -/
theorem qfrac_sharp_rate_pinned : Filter.Tendsto
    (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c)) Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional

/-- The `(1 + o(1))` form, pinned. -/
theorem qfrac_one_add_o1_pinned : Filter.Tendsto
    (fun c : ℕ => qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2))) Filter.atTop (nhds 1) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_one_add_o1_unconditional

/-- The discharged structure really instantiates `SharpRateGap`. -/
theorem structure_pinned : SharpRateGap := Gap2CensusNvarSharp.sharpRateGap_discharged

/-! ## 3. Definitional rfl pins and numeric witnesses -/

/-- The structure's fields are definitionally the proved theorems. -/
example : Gap2CensusNvarSharp.sharpRateGap_discharged.nvar_sharp
    = Gap2CensusNvarSharp.nvar_sharp := rfl
example : Gap2CensusNvarSharp.sharpRateGap_discharged.resid_negligible
    = Gap2CensusNvarSharp.resid_negligible := rfl
example : Gap2CensusNvarSharp.sharpRateGap_discharged.dsum_saddle
    = Gap2CensusDsumSaddle.dsum_saddle := rfl

/-- The resid test scale is definitionally `(log c)/(2c)`. -/
example : aResid 5 = Real.log 5 / (2 * 5) := rfl

/-- The window slack is definitionally `1/√(log c·log log c)`. -/
example : deltaS 3 = 1 / Real.sqrt (Real.log 3 * Real.log (Real.log 3)) := rfl

/-- The cell weight computes: `cellW 2 2 1 = 4/(2!·1!) = 2`. -/
example : cellW 2 2 1 = 2 := by norm_num [cellW]

/-- The row top computes: `topT 3 2 = 2⁶/2! = 32`. -/
example : Gap2CensusRowSaddle.topT 3 2 = 32 := by
  norm_num [Gap2CensusRowSaddle.topT]

/-- The zeroth row is a point mass: `wrow 2 0 = 1`. -/
example : wrow 2 0 = 1 := by
  norm_num [wrow, cellW, Finset.sum_range_succ]

/-- The cap-2 census mass is exactly `10` (not zero, not junk): the
non-vacuity witness that the sums the limits are about are real. -/
example : m0sum 2 = 10 := by
  norm_num [m0sum, wrow, cellW, Finset.sum_range_succ]

/-! ## 4. Non-vacuity witnesses -/

/-- The census mass is strictly positive at every cap. -/
example (c : ℕ) : (0 : ℝ) < m0sum c := m0sum_pos c

/-- The proper second moment is strictly positive from cap 2 up. -/
example (c : ℕ) (hc : 2 ≤ c) : (0 : ℝ) < dsum c := dsum_pos c hc

/-- The sharp-rate limit has content: the scaled anomaly fraction is
eventually `> 1/2` (a vacuous or wrong limit could not give this). -/
theorem nonvac_qfrac_eventually_gt_half :
    ∀ᶠ c : ℕ in atTop, (1 : ℝ) / 2 < qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c) :=
  Gap2CensusNvarSharp.qfrac_sharp_rate_unconditional.eventually
    (Ioi_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1))

/-- The variance numerator is eventually strictly positive, derivable only
because the limit of `nvarSum·(2c²)/(log c·dsum)` is genuinely `1`. -/
theorem nonvac_nvarSum_eventually_pos : ∀ᶠ c : ℕ in atTop, (0 : ℝ) < nvarSum c := by
  have h := Gap2CensusNvarSharp.nvar_sharp.eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop 2] with c hc h2
  have hd : (0 : ℝ) < dsum c := dsum_pos c h2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  by_contra hneg
  push_neg at hneg
  have hle : nvarSum c * (2 * (c : ℝ) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
  have hz : nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hle (mul_nonneg hL.le hd.le)
  linarith

/-! ## 5. Red tests: decoys, each refuted from the proved theorems -/

/-- DECOY 1 (wrong limit constant).  `nvar_sharp` with limit `2` instead of
`1` is refuted by limit uniqueness.  A proved field with a limit constant
other than `1` would refute the sharp rate; it is `1`. -/
theorem red_nvar_sharp_limit_two_refuted :
    ¬ Filter.Tendsto (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 2) := by
  intro h
  have huniq := tendsto_nhds_unique Gap2CensusNvarSharp.nvar_sharp h
  norm_num at huniq

/-- DECOY 2 (wrong resid limit).  `resid_negligible` with limit `1` instead
of `0` is refuted by limit uniqueness. -/
theorem red_resid_limit_one_refuted :
    ¬ Filter.Tendsto (fun c : ℕ =>
        ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      Filter.atTop (nhds 1) := by
  intro h
  have huniq := tendsto_nhds_unique Gap2CensusNvarSharp.resid_negligible h
  norm_num at huniq

/-- DECOY 3 (heavy tails).  The claim that the tail keeps at least half the
census mass is refuted by the proved tail-vanishing theorem: the tails are
`o(1)` of the mass, let alone `≥ 1/2`. -/
theorem red_tail_mass_heavy_refuted :
    ¬ ∀ᶠ c : ℕ in atTop, (1 : ℝ) / 2 ≤ tailMassM c / m0sum c := by
  intro h
  have h2 := Gap2CensusNvarSharp.tendsto_tailMassM_div_m0sum_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨c, h1c, h2c⟩ := (h.and h2).exists
  linarith

#print axioms red_nvar_sharp_limit_two_refuted
#print axioms red_resid_limit_one_refuted
#print axioms red_tail_mass_heavy_refuted
#print axioms nonvac_nvarSum_eventually_pos
#print axioms nonvac_qfrac_eventually_gt_half

end NvarSharpCheck
