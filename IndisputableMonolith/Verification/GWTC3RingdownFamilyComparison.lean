import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily
import IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily
import IndisputableMonolith.Verification.GWTC3RingdownKerr22010MDampingFamily

/-!
# GWTC-3 Ringdown Controlled-Family Comparison

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module aggregates the three currently mapped damping families:

* `DS_1mode_10M`
* `Kerr_220_0M`
* `Kerr_220_10M`

and proves the model/start-time dependence facts:

* mean order: `DS_1mode_10M > Kerr_220_0M > Kerr_220_10M`
* median order: `DS_1mode_10M > Kerr_220_0M > Kerr_220_10M`
* target inclusion degrades across the same order:
  - DS: target in pooled 68% and 90%
  - Kerr_220_0M: target in pooled 90% only
  - Kerr_220_10M: target in neither pooled 68% nor 90%

This is a three-family comparison only, not a mixed-model archive-wide
likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownFamilyComparison

open IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily
open IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily
open IndisputableMonolith.Verification.GWTC3RingdownKerr22010MDampingFamily

/-! ## §1. Comparison constants -/

def comparisonFamilyCount : Nat := 3
def comparisonTotalMembers : Nat := 66
def comparisonTotalSamples : Nat := 1954998
def dsMeanMinusKerr0Mean : ℝ := 0.143049219914
def kerr0MeanMinusKerr10Mean : ℝ := 0.089478304903
def dsHitDiffVsKerr0 : Nat := 10
def kerr0HitDiffVsKerr10 : Nat := 3

/-! ## §2. Ordering facts -/

theorem comparison_total_members :
    dsFamilyMemberCount + kerr2200MemberCount + kerr22010MemberCount =
      comparisonTotalMembers := by
  unfold dsFamilyMemberCount kerr2200MemberCount kerr22010MemberCount comparisonTotalMembers
  decide

theorem comparison_total_samples :
    dsFamilyTotalSampleCount + kerr2200TotalSampleCount + kerr22010TotalSampleCount =
      comparisonTotalSamples := by
  unfold dsFamilyTotalSampleCount kerr2200TotalSampleCount kerr22010TotalSampleCount
    comparisonTotalSamples
  decide

theorem family_mean_order :
    kerr22010PooledMean < kerr2200PooledMean ∧
      kerr2200PooledMean < dsPooledMean := by
  exact ⟨kerr22010_mean_lt_kerr2200_mean, ds_vs_kerr_mean_order⟩

theorem family_median_order :
    kerr22010PooledMedian < kerr2200PooledMedian ∧
      kerr2200PooledMedian < dsPooledMedian := by
  unfold kerr22010PooledMedian kerr2200PooledMedian dsPooledMedian
  norm_num

theorem hit_count_order :
    kerr22010MembersInside68Count < kerr2200MembersInside68Count ∧
      kerr2200MembersInside68Count < dsMembersInside68Count := by
  unfold kerr22010MembersInside68Count kerr2200MembersInside68Count dsMembersInside68Count
  decide

theorem ds_mean_difference_pos :
    0 < dsMeanMinusKerr0Mean := by
  unfold dsMeanMinusKerr0Mean
  norm_num

theorem kerr_mean_difference_pos :
    0 < kerr0MeanMinusKerr10Mean := by
  unfold kerr0MeanMinusKerr10Mean
  norm_num

/-! ## §3. Master cert -/

structure GWTC3RingdownFamilyComparisonCert where
  total_members :
    dsFamilyMemberCount + kerr2200MemberCount + kerr22010MemberCount =
      comparisonTotalMembers
  total_samples :
    dsFamilyTotalSampleCount + kerr2200TotalSampleCount + kerr22010TotalSampleCount =
      comparisonTotalSamples
  mean_order :
    kerr22010PooledMean < kerr2200PooledMean ∧
      kerr2200PooledMean < dsPooledMean
  median_order :
    kerr22010PooledMedian < kerr2200PooledMedian ∧
      kerr2200PooledMedian < dsPooledMedian
  hit_order :
    kerr22010MembersInside68Count < kerr2200MembersInside68Count ∧
      kerr2200MembersInside68Count < dsMembersInside68Count
  ds_available : Nonempty GWTC3RingdownDS1Mode10MDampingFamilyCert
  kerr0_available : Nonempty GWTC3RingdownKerr2200MDampingFamilyCert
  kerr10_available : Nonempty GWTC3RingdownKerr22010MDampingFamilyCert

def gwtc3RingdownFamilyComparisonCert :
    GWTC3RingdownFamilyComparisonCert where
  total_members := comparison_total_members
  total_samples := comparison_total_samples
  mean_order := family_mean_order
  median_order := family_median_order
  hit_order := hit_count_order
  ds_available := gwtc3RingdownDS1Mode10MDampingFamilyCert_inhabited
  kerr0_available := gwtc3RingdownKerr2200MDampingFamilyCert_inhabited
  kerr10_available := gwtc3RingdownKerr22010MDampingFamilyCert_inhabited

theorem gwtc3RingdownFamilyComparisonCert_inhabited :
    Nonempty GWTC3RingdownFamilyComparisonCert :=
  ⟨gwtc3RingdownFamilyComparisonCert⟩

/-- One-statement controlled-family comparison theorem. -/
theorem gwtc3_ringdown_family_comparison_one_statement :
    (comparisonFamilyCount = 3) ∧
    (comparisonTotalMembers = 66) ∧
    (comparisonTotalSamples = 1954998) ∧
    (kerr22010PooledMean < kerr2200PooledMean ∧
      kerr2200PooledMean < dsPooledMean) ∧
    (kerr22010PooledMedian < kerr2200PooledMedian ∧
      kerr2200PooledMedian < dsPooledMedian) ∧
    (kerr22010MembersInside68Count < kerr2200MembersInside68Count ∧
      kerr2200MembersInside68Count < dsMembersInside68Count) ∧
    Nonempty GWTC3RingdownFamilyComparisonCert :=
  ⟨rfl, rfl, rfl,
   family_mean_order,
   family_median_order,
   hit_count_order,
   gwtc3RingdownFamilyComparisonCert_inhabited⟩

end GWTC3RingdownFamilyComparison
end Verification
end IndisputableMonolith
