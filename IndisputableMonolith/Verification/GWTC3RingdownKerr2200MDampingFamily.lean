import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy
import IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily

/-!
# GWTC-3 Ringdown Kerr_220_0M Family Damping Statistic

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the first controlled Kerr-family scaling of the QNM
damping statistic.

Family:

* model `Kerr_220_0M`
* 22 HDF5 files
* 22 events
* 647,220 pooled posterior samples

Observable:

For Kerr files the posterior table has `af` rather than explicit
`f_t_0` and `tau_t_0`. The companion script uses the standard Berti-style
Kerr-220 quality-factor fit

`Q_220(a) = 0.7000 + 1.4187 (1-a)^(-0.4990)`

and maps it to

`damping_per_cycle = exp(-π / Q_220)`.

RS target:

* `1/φ ≈ 0.618033988750`

Result:

* pooled mean `0.438208510863`
* pooled std `0.122250226107`
* pooled median `0.433285700166`
* pooled q05/q95 `0.249303771620 / 0.643869947920`
* pooled q16/q84 `0.299869164713 / 0.575770415071`
* target inside pooled 90% but not inside pooled 68%
* 3 of 22 member-level central 68% intervals contain the target

This is controlled-family only. It is not a full archive likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownKerr2200MDampingFamily

open IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy
open IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily

/-! ## §1. Family constants -/

def kerr2200ModelName : String := "Kerr_220_0M"
def kerr2200MemberCount : Nat := 22
def kerr2200EventCount : Nat := 22
def kerr2200TotalSampleCount : Nat := 647220
def kerr2200RSDampingTarget : ℝ := 0.618033988750
def kerr2200PooledMean : ℝ := 0.438208510863
def kerr2200PooledStd : ℝ := 0.122250226107
def kerr2200PooledMedian : ℝ := 0.433285700166
def kerr2200PooledQ05 : ℝ := 0.249303771620
def kerr2200PooledQ16 : ℝ := 0.299869164713
def kerr2200PooledQ84 : ℝ := 0.575770415071
def kerr2200PooledQ95 : ℝ := 0.643869947920
def kerr2200PooledZFromMean : ℝ := 1.470962
def kerr2200PooledFractionBelowTarget : ℝ := 0.914513
def kerr2200MembersInside68Count : Nat := 3

/-! ## §2. Count and interval facts -/

theorem kerr2200_member_count_pos : 0 < kerr2200MemberCount := by
  unfold kerr2200MemberCount
  decide

theorem kerr2200_event_count_pos : 0 < kerr2200EventCount := by
  unfold kerr2200EventCount
  decide

theorem kerr2200_sample_count_pos : 0 < kerr2200TotalSampleCount := by
  unfold kerr2200TotalSampleCount
  decide

theorem kerr2200_target_inside_pooled_90 :
    kerr2200PooledQ05 < kerr2200RSDampingTarget ∧
      kerr2200RSDampingTarget < kerr2200PooledQ95 := by
  unfold kerr2200PooledQ05 kerr2200RSDampingTarget kerr2200PooledQ95
  norm_num

theorem kerr2200_target_not_inside_pooled_68 :
    kerr2200PooledQ84 < kerr2200RSDampingTarget := by
  unfold kerr2200PooledQ84 kerr2200RSDampingTarget
  norm_num

theorem kerr2200_z_from_mean_gt_one :
    1 < kerr2200PooledZFromMean := by
  unfold kerr2200PooledZFromMean
  norm_num

theorem kerr2200_fraction_below_target_valid :
    0 < kerr2200PooledFractionBelowTarget ∧ kerr2200PooledFractionBelowTarget < 1 := by
  unfold kerr2200PooledFractionBelowTarget
  norm_num

theorem kerr2200_members_inside68_nonzero :
    0 < kerr2200MembersInside68Count ∧ kerr2200MembersInside68Count < kerr2200MemberCount := by
  unfold kerr2200MembersInside68Count kerr2200MemberCount
  decide

theorem ds_vs_kerr_mean_order :
    kerr2200PooledMean < dsPooledMean := by
  unfold kerr2200PooledMean dsPooledMean
  norm_num

/-! ## §3. Master cert -/

structure GWTC3RingdownKerr2200MDampingFamilyCert where
  member_count_pos : 0 < kerr2200MemberCount
  event_count_pos : 0 < kerr2200EventCount
  sample_count_pos : 0 < kerr2200TotalSampleCount
  target_inside_pooled_90 :
    kerr2200PooledQ05 < kerr2200RSDampingTarget ∧
      kerr2200RSDampingTarget < kerr2200PooledQ95
  target_not_inside_pooled_68 :
    kerr2200PooledQ84 < kerr2200RSDampingTarget
  z_gt_one : 1 < kerr2200PooledZFromMean
  fraction_valid :
    0 < kerr2200PooledFractionBelowTarget ∧ kerr2200PooledFractionBelowTarget < 1
  member_inside_count_nonzero :
    0 < kerr2200MembersInside68Count ∧ kerr2200MembersInside68Count < kerr2200MemberCount
  ds_mean_greater :
    kerr2200PooledMean < dsPooledMean
  taxonomy_available : Nonempty GWTC3RingdownFilenameTaxonomyCert
  ds_family_available : Nonempty GWTC3RingdownDS1Mode10MDampingFamilyCert

def gwtc3RingdownKerr2200MDampingFamilyCert :
    GWTC3RingdownKerr2200MDampingFamilyCert where
  member_count_pos := kerr2200_member_count_pos
  event_count_pos := kerr2200_event_count_pos
  sample_count_pos := kerr2200_sample_count_pos
  target_inside_pooled_90 := kerr2200_target_inside_pooled_90
  target_not_inside_pooled_68 := kerr2200_target_not_inside_pooled_68
  z_gt_one := kerr2200_z_from_mean_gt_one
  fraction_valid := kerr2200_fraction_below_target_valid
  member_inside_count_nonzero := kerr2200_members_inside68_nonzero
  ds_mean_greater := ds_vs_kerr_mean_order
  taxonomy_available := gwtc3RingdownFilenameTaxonomyCert_inhabited
  ds_family_available := gwtc3RingdownDS1Mode10MDampingFamilyCert_inhabited

theorem gwtc3RingdownKerr2200MDampingFamilyCert_inhabited :
    Nonempty GWTC3RingdownKerr2200MDampingFamilyCert :=
  ⟨gwtc3RingdownKerr2200MDampingFamilyCert⟩

/-- One-statement Kerr-family damping theorem. -/
theorem gwtc3_ringdown_kerr2200m_damping_family_one_statement :
    (kerr2200MemberCount = 22) ∧
    (kerr2200EventCount = 22) ∧
    (kerr2200TotalSampleCount = 647220) ∧
    (kerr2200PooledQ05 < kerr2200RSDampingTarget ∧
      kerr2200RSDampingTarget < kerr2200PooledQ95) ∧
    (kerr2200PooledQ84 < kerr2200RSDampingTarget) ∧
    (kerr2200PooledMean < dsPooledMean) ∧
    Nonempty GWTC3RingdownKerr2200MDampingFamilyCert :=
  ⟨rfl, rfl, rfl,
   kerr2200_target_inside_pooled_90,
   kerr2200_target_not_inside_pooled_68,
   ds_vs_kerr_mean_order,
   gwtc3RingdownKerr2200MDampingFamilyCert_inhabited⟩

end GWTC3RingdownKerr2200MDampingFamily
end Verification
end IndisputableMonolith
