import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily

/-!
# GWTC-3 Ringdown Kerr_220_10M Family Damping Statistic

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the second controlled Kerr-family damping statistic.
It keeps the same Kerr 220 QNM mode as Session 128 but changes the
ringdown start-time window to `10M`.

Family:

* model `Kerr_220_10M`
* 22 HDF5 files
* 22 events
* 664,154 pooled posterior samples

Result:

* pooled mean `0.348730205961`
* pooled std `0.103850136706`
* pooled median `0.320171053042`
* pooled q05/q95 `0.233283419046 / 0.546003135309`
* pooled q16/q84 `0.248744219541 / 0.459021150603`
* target `1/φ` outside pooled 90% and 68% intervals
* 0 of 22 member-level central 68% intervals contain the target

This is controlled-family only. It is not a full archive likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownKerr22010MDampingFamily

open IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily

/-! ## §1. Family constants -/

def kerr22010ModelName : String := "Kerr_220_10M"
def kerr22010MemberCount : Nat := 22
def kerr22010EventCount : Nat := 22
def kerr22010TotalSampleCount : Nat := 664154
def kerr22010RSDampingTarget : ℝ := 0.618033988750
def kerr22010PooledMean : ℝ := 0.348730205961
def kerr22010PooledStd : ℝ := 0.103850136706
def kerr22010PooledMedian : ℝ := 0.320171053042
def kerr22010PooledQ05 : ℝ := 0.233283419046
def kerr22010PooledQ16 : ℝ := 0.248744219541
def kerr22010PooledQ84 : ℝ := 0.459021150603
def kerr22010PooledQ95 : ℝ := 0.546003135309
def kerr22010PooledZFromMean : ℝ := 2.593196
def kerr22010PooledFractionBelowTarget : ℝ := 0.981447
def kerr22010MembersInside68Count : Nat := 0

/-! ## §2. Count and interval facts -/

theorem kerr22010_member_count_pos : 0 < kerr22010MemberCount := by
  unfold kerr22010MemberCount
  decide

theorem kerr22010_event_count_pos : 0 < kerr22010EventCount := by
  unfold kerr22010EventCount
  decide

theorem kerr22010_sample_count_pos : 0 < kerr22010TotalSampleCount := by
  unfold kerr22010TotalSampleCount
  decide

theorem kerr22010_target_above_pooled_95 :
    kerr22010PooledQ95 < kerr22010RSDampingTarget := by
  unfold kerr22010PooledQ95 kerr22010RSDampingTarget
  norm_num

theorem kerr22010_target_above_pooled_84 :
    kerr22010PooledQ84 < kerr22010RSDampingTarget := by
  unfold kerr22010PooledQ84 kerr22010RSDampingTarget
  norm_num

theorem kerr22010_z_from_mean_gt_two :
    2 < kerr22010PooledZFromMean := by
  unfold kerr22010PooledZFromMean
  norm_num

theorem kerr22010_fraction_below_target_valid :
    0 < kerr22010PooledFractionBelowTarget ∧ kerr22010PooledFractionBelowTarget < 1 := by
  unfold kerr22010PooledFractionBelowTarget
  norm_num

theorem kerr22010_no_members_inside68 :
    kerr22010MembersInside68Count = 0 := rfl

theorem kerr22010_mean_lt_kerr2200_mean :
    kerr22010PooledMean < kerr2200PooledMean := by
  unfold kerr22010PooledMean kerr2200PooledMean
  norm_num

/-! ## §3. Master cert -/

structure GWTC3RingdownKerr22010MDampingFamilyCert where
  member_count_pos : 0 < kerr22010MemberCount
  event_count_pos : 0 < kerr22010EventCount
  sample_count_pos : 0 < kerr22010TotalSampleCount
  target_above_pooled_95 : kerr22010PooledQ95 < kerr22010RSDampingTarget
  target_above_pooled_84 : kerr22010PooledQ84 < kerr22010RSDampingTarget
  z_gt_two : 2 < kerr22010PooledZFromMean
  fraction_valid :
    0 < kerr22010PooledFractionBelowTarget ∧ kerr22010PooledFractionBelowTarget < 1
  no_members_inside68 : kerr22010MembersInside68Count = 0
  mean_lt_kerr2200 : kerr22010PooledMean < kerr2200PooledMean
  kerr2200_available : Nonempty GWTC3RingdownKerr2200MDampingFamilyCert

def gwtc3RingdownKerr22010MDampingFamilyCert :
    GWTC3RingdownKerr22010MDampingFamilyCert where
  member_count_pos := kerr22010_member_count_pos
  event_count_pos := kerr22010_event_count_pos
  sample_count_pos := kerr22010_sample_count_pos
  target_above_pooled_95 := kerr22010_target_above_pooled_95
  target_above_pooled_84 := kerr22010_target_above_pooled_84
  z_gt_two := kerr22010_z_from_mean_gt_two
  fraction_valid := kerr22010_fraction_below_target_valid
  no_members_inside68 := kerr22010_no_members_inside68
  mean_lt_kerr2200 := kerr22010_mean_lt_kerr2200_mean
  kerr2200_available := gwtc3RingdownKerr2200MDampingFamilyCert_inhabited

theorem gwtc3RingdownKerr22010MDampingFamilyCert_inhabited :
    Nonempty GWTC3RingdownKerr22010MDampingFamilyCert :=
  ⟨gwtc3RingdownKerr22010MDampingFamilyCert⟩

/-- One-statement Kerr_220_10M family damping theorem. -/
theorem gwtc3_ringdown_kerr22010m_damping_family_one_statement :
    (kerr22010MemberCount = 22) ∧
    (kerr22010EventCount = 22) ∧
    (kerr22010TotalSampleCount = 664154) ∧
    (kerr22010PooledQ95 < kerr22010RSDampingTarget) ∧
    (2 < kerr22010PooledZFromMean) ∧
    (kerr22010MembersInside68Count = 0) ∧
    (kerr22010PooledMean < kerr2200PooledMean) ∧
    Nonempty GWTC3RingdownKerr22010MDampingFamilyCert :=
  ⟨rfl, rfl, rfl,
   kerr22010_target_above_pooled_95,
   kerr22010_z_from_mean_gt_two,
   rfl,
   kerr22010_mean_lt_kerr2200_mean,
   gwtc3RingdownKerr22010MDampingFamilyCert_inhabited⟩

end GWTC3RingdownKerr22010MDampingFamily
end Verification
end IndisputableMonolith
