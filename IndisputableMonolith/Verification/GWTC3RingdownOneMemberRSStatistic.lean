import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownHDF5SampleSummary

/-!
# GWTC-3 Ringdown One-Member RS Amplitude Statistic

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the first explicitly RS-referenced statistic on a
range-read GWTC-3 ringdown posterior table.

Member:

* `rin/rin_S190727h_pyring_DS_1mode_10M.h5`

Dataset:

* `/EXP6/posterior_samples`

Column:

* `logA_t_0`

RS structural target:

* `log(φ^-44) = -44 log φ ≈ -21.173320302623`

Result:

* posterior mean `logA_t_0 ≈ -22.244585483768`
* posterior std `≈ 0.398295292686`
* posterior median `≈ -22.211884808706`
* target is not inside the central 90% or 68% posterior intervals
* target is about `2.689626` posterior std above the mean
* sample fraction above target is `0.000331`

This is one-member amplitude-scale comparison only. It does not prove
that `logA_t_0` is the final RS echo amplitude observable, and it does
not compute an archive-wide likelihood.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownOneMemberRSStatistic

open IndisputableMonolith.Verification.GWTC3RingdownHDF5SampleSummary

/-! ## §1. Statistic constants -/

def rsLogPhiNeg44Target : ℝ := -21.173320302623
def logAPosteriorMean : ℝ := -22.244585483768
def logAPosteriorStd : ℝ := 0.398295292686
def logAPosteriorMedian : ℝ := -22.211884808706
def logAQ05 : ℝ := -22.911300360855
def logAQ16 : ℝ := -22.719806844144
def logAQ84 : ℝ := -21.824897151633
def logAQ95 : ℝ := -21.638354687882
def logAResidualFromMean : ℝ := 1.071265181145
def logAResidualFromMedian : ℝ := 1.038564506083
def logAZFromMean : ℝ := 2.689626
def logAFractionAboveTarget : ℝ := 0.000331

/-! ## §2. Basic inequalities -/

theorem target_above_q95 :
    logAQ95 < rsLogPhiNeg44Target := by
  unfold logAQ95 rsLogPhiNeg44Target
  norm_num

theorem target_outside_90_interval :
    ¬ (logAQ05 ≤ rsLogPhiNeg44Target ∧ rsLogPhiNeg44Target ≤ logAQ95) := by
  intro h
  have hlt := target_above_q95
  linarith

theorem target_outside_68_interval :
    ¬ (logAQ16 ≤ rsLogPhiNeg44Target ∧ rsLogPhiNeg44Target ≤ logAQ84) := by
  intro h
  unfold logAQ84 rsLogPhiNeg44Target at h
  norm_num at h

theorem z_from_mean_gt_two :
    2 < logAZFromMean := by
  unfold logAZFromMean
  norm_num

theorem fraction_above_target_small :
    logAFractionAboveTarget < 0.001 := by
  unfold logAFractionAboveTarget
  norm_num

theorem posterior_summary_available :
    Nonempty GWTC3RingdownHDF5SampleSummaryCert :=
  gwtc3RingdownHDF5SampleSummaryCert_inhabited

/-! ## §3. Master cert -/

structure GWTC3RingdownOneMemberRSStatisticCert where
  target_above_q95 : logAQ95 < rsLogPhiNeg44Target
  target_outside_90 :
    ¬ (logAQ05 ≤ rsLogPhiNeg44Target ∧ rsLogPhiNeg44Target ≤ logAQ95)
  target_outside_68 :
    ¬ (logAQ16 ≤ rsLogPhiNeg44Target ∧ rsLogPhiNeg44Target ≤ logAQ84)
  z_gt_two : 2 < logAZFromMean
  fraction_small : logAFractionAboveTarget < 0.001
  summary_available : Nonempty GWTC3RingdownHDF5SampleSummaryCert

def gwtc3RingdownOneMemberRSStatisticCert :
    GWTC3RingdownOneMemberRSStatisticCert where
  target_above_q95 := target_above_q95
  target_outside_90 := target_outside_90_interval
  target_outside_68 := target_outside_68_interval
  z_gt_two := z_from_mean_gt_two
  fraction_small := fraction_above_target_small
  summary_available := posterior_summary_available

theorem gwtc3RingdownOneMemberRSStatisticCert_inhabited :
    Nonempty GWTC3RingdownOneMemberRSStatisticCert :=
  ⟨gwtc3RingdownOneMemberRSStatisticCert⟩

/-- One-statement theorem for the one-member RS amplitude-scale statistic. -/
theorem gwtc3_ringdown_one_member_rs_statistic_one_statement :
    (logAQ95 < rsLogPhiNeg44Target) ∧
    (2 < logAZFromMean) ∧
    (logAFractionAboveTarget < 0.001) ∧
    Nonempty GWTC3RingdownOneMemberRSStatisticCert :=
  ⟨target_above_q95,
   z_from_mean_gt_two,
   fraction_above_target_small,
   gwtc3RingdownOneMemberRSStatisticCert_inhabited⟩

end GWTC3RingdownOneMemberRSStatistic
end Verification
end IndisputableMonolith
