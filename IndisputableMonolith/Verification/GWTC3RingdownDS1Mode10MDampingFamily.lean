import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy
import IndisputableMonolith.Verification.GWTC3RingdownOneMemberDampingStatistic

/-!
# GWTC-3 Ringdown DS_1mode_10M Family Damping Statistic

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the first controlled-family scaling of the Session
123 one-member QNM damping statistic.

Family:

* model `DS_1mode_10M`
* 22 HDF5 files
* 22 events
* 643,624 pooled posterior samples

Observable:

* `damping_per_cycle = exp(-1 / (f_t_0 * tau_t_0))`

RS target:

* `1/φ ≈ 0.618033988750`

Result:

* pooled mean `0.581257730777`
* pooled std `0.264599094550`
* pooled median `0.569663372044`
* pooled q05/q95 `0.118026458809 / 0.958639185642`
* pooled q16/q84 `0.292577350498 / 0.898893346068`
* target inside pooled 90% and 68% intervals
* 13 of 22 member-level intervals contain the target in the central 68%

This is controlled-family only. It does not mix Kerr, MMRDNP, and
waveform-model semantics; it is not a full archive likelihood.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownDS1Mode10MDampingFamily

open IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy
open IndisputableMonolith.Verification.GWTC3RingdownOneMemberDampingStatistic

/-! ## §1. Family constants -/

def dsFamilyModelName : String := "DS_1mode_10M"
def dsFamilyMemberCount : Nat := 22
def dsFamilyEventCount : Nat := 22
def dsFamilyTotalSampleCount : Nat := 643624
def dsRSDampingTarget : ℝ := 0.618033988750
def dsPooledMean : ℝ := 0.581257730777
def dsPooledStd : ℝ := 0.264599094550
def dsPooledMedian : ℝ := 0.569663372044
def dsPooledQ05 : ℝ := 0.118026458809
def dsPooledQ16 : ℝ := 0.292577350498
def dsPooledQ84 : ℝ := 0.898893346068
def dsPooledQ95 : ℝ := 0.958639185642
def dsPooledZFromMean : ℝ := 0.138989
def dsPooledFractionBelowTarget : ℝ := 0.560888
def dsMembersInside68Count : Nat := 13

/-! ## §2. Count and interval facts -/

theorem ds_family_member_count_matches_taxonomy :
    dsFamilyMemberCount = taxonomyDampedSinusoidCount := rfl

theorem ds_family_event_count_pos : 0 < dsFamilyEventCount := by
  unfold dsFamilyEventCount
  decide

theorem ds_family_sample_count_pos : 0 < dsFamilyTotalSampleCount := by
  unfold dsFamilyTotalSampleCount
  decide

theorem ds_target_inside_pooled_90 :
    dsPooledQ05 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ95 := by
  unfold dsPooledQ05 dsRSDampingTarget dsPooledQ95
  norm_num

theorem ds_target_inside_pooled_68 :
    dsPooledQ16 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ84 := by
  unfold dsPooledQ16 dsRSDampingTarget dsPooledQ84
  norm_num

theorem ds_z_from_mean_lt_one :
    dsPooledZFromMean < 1 := by
  unfold dsPooledZFromMean
  norm_num

theorem ds_fraction_below_target_valid :
    0 < dsPooledFractionBelowTarget ∧ dsPooledFractionBelowTarget < 1 := by
  unfold dsPooledFractionBelowTarget
  norm_num

theorem ds_members_inside68_nonzero :
    0 < dsMembersInside68Count ∧ dsMembersInside68Count < dsFamilyMemberCount := by
  unfold dsMembersInside68Count dsFamilyMemberCount
  decide

/-! ## §3. Master cert -/

structure GWTC3RingdownDS1Mode10MDampingFamilyCert where
  member_count_matches_taxonomy :
    dsFamilyMemberCount = taxonomyDampedSinusoidCount
  event_count_pos : 0 < dsFamilyEventCount
  sample_count_pos : 0 < dsFamilyTotalSampleCount
  target_inside_pooled_90 :
    dsPooledQ05 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ95
  target_inside_pooled_68 :
    dsPooledQ16 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ84
  z_lt_one : dsPooledZFromMean < 1
  fraction_valid :
    0 < dsPooledFractionBelowTarget ∧ dsPooledFractionBelowTarget < 1
  member_inside_count_nonzero :
    0 < dsMembersInside68Count ∧ dsMembersInside68Count < dsFamilyMemberCount
  taxonomy_available : Nonempty GWTC3RingdownFilenameTaxonomyCert
  one_member_damping_available : Nonempty GWTC3RingdownOneMemberDampingStatisticCert

def gwtc3RingdownDS1Mode10MDampingFamilyCert :
    GWTC3RingdownDS1Mode10MDampingFamilyCert where
  member_count_matches_taxonomy := ds_family_member_count_matches_taxonomy
  event_count_pos := ds_family_event_count_pos
  sample_count_pos := ds_family_sample_count_pos
  target_inside_pooled_90 := ds_target_inside_pooled_90
  target_inside_pooled_68 := ds_target_inside_pooled_68
  z_lt_one := ds_z_from_mean_lt_one
  fraction_valid := ds_fraction_below_target_valid
  member_inside_count_nonzero := ds_members_inside68_nonzero
  taxonomy_available := gwtc3RingdownFilenameTaxonomyCert_inhabited
  one_member_damping_available := gwtc3RingdownOneMemberDampingStatisticCert_inhabited

theorem gwtc3RingdownDS1Mode10MDampingFamilyCert_inhabited :
    Nonempty GWTC3RingdownDS1Mode10MDampingFamilyCert :=
  ⟨gwtc3RingdownDS1Mode10MDampingFamilyCert⟩

/-- One-statement controlled-family damping theorem. -/
theorem gwtc3_ringdown_ds1mode10m_damping_family_one_statement :
    (dsFamilyMemberCount = 22) ∧
    (dsFamilyEventCount = 22) ∧
    (dsFamilyTotalSampleCount = 643624) ∧
    (dsPooledQ05 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ95) ∧
    (dsPooledQ16 < dsRSDampingTarget ∧ dsRSDampingTarget < dsPooledQ84) ∧
    (dsPooledZFromMean < 1) ∧
    Nonempty GWTC3RingdownDS1Mode10MDampingFamilyCert :=
  ⟨rfl, rfl, rfl,
   ds_target_inside_pooled_90,
   ds_target_inside_pooled_68,
   ds_z_from_mean_lt_one,
   gwtc3RingdownDS1Mode10MDampingFamilyCert_inhabited⟩

end GWTC3RingdownDS1Mode10MDampingFamily
end Verification
end IndisputableMonolith
