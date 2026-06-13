import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownHDF5SampleSchema

/-!
# GWTC-3 Ringdown HDF5 Sample Summary

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the first posterior-summary statistics extracted
from a range-read GWTC-3 ringdown HDF5 file:

* member: `rin/rin_S190727h_pyring_DS_1mode_10M.h5`
* dataset: `/EXP6/posterior_samples`
* sample count: `15114`
* field count: `7`
* fields: `psi`, `logA_t_0`, `f_t_0`, `tau_t_0`, `phi_t_0`, `logL`, `logPrior`

Companion script:

* `papers/reproducibility/gwtc3_ringdown_hdf5_sample_summary.py`

This is one-member posterior summary only, not an RS echo/QNM
likelihood. The purpose is to establish the column names and basic
numerical ranges needed by the later likelihood parser.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownHDF5SampleSummary

open IndisputableMonolith.Verification.GWTC3RingdownHDF5SampleSchema

/-! ## §1. Summary constants -/

def summaryMemberName : String := "rin/rin_S190727h_pyring_DS_1mode_10M.h5"
def summaryPosteriorPath : String := "/EXP6/posterior_samples"
def summarySampleCount : Nat := 15114
def summaryFieldCount : Nat := 7

def psiMean : ℝ := 1.5465191
def logAMean : ℝ := -22.244585
def fMean : ℝ := 420.95381
def tauMean : ℝ := 0.022773848
def phiMean : ℝ := 3.1523706
def logLMean : ℝ := 58695.535
def logPriorMean : ℝ := 0

def fQ16 : ℝ := 172.53798
def fMedian : ℝ := 345.41413
def fQ84 : ℝ := 819.88387

def tauQ16 : ℝ := 0.0076396112
def tauMedian : ℝ := 0.021072448
def tauQ84 : ℝ := 0.039327675

/-! ## §2. Basic schema and sign facts -/

theorem summary_member_matches_schema :
    summaryMemberName = sampleMemberName := rfl

theorem summary_path_matches_schema :
    summaryPosteriorPath = posteriorSamplesDatasetPath := rfl

theorem summary_sample_count_matches_schema :
    summarySampleCount = posteriorSamplesCount := rfl

theorem summary_field_count_matches_schema :
    summaryFieldCount = posteriorFieldCount := rfl

theorem summary_sample_count_pos : 0 < summarySampleCount := by
  unfold summarySampleCount
  decide

theorem summary_field_count_pos : 0 < summaryFieldCount := by
  unfold summaryFieldCount
  decide

theorem mean_signs :
    0 < psiMean ∧ logAMean < 0 ∧ 0 < fMean ∧ 0 < tauMean ∧
      0 < phiMean ∧ 0 < logLMean ∧ logPriorMean = 0 := by
  unfold psiMean logAMean fMean tauMean phiMean logLMean logPriorMean
  norm_num

theorem f_quantile_order :
    fQ16 < fMedian ∧ fMedian < fQ84 := by
  unfold fQ16 fMedian fQ84
  norm_num

theorem tau_quantile_order :
    tauQ16 < tauMedian ∧ tauMedian < tauQ84 := by
  unfold tauQ16 tauMedian tauQ84
  norm_num

/-! ## §3. Master cert -/

structure GWTC3RingdownHDF5SampleSummaryCert where
  member_matches_schema : summaryMemberName = sampleMemberName
  path_matches_schema : summaryPosteriorPath = posteriorSamplesDatasetPath
  sample_count_matches_schema : summarySampleCount = posteriorSamplesCount
  field_count_matches_schema : summaryFieldCount = posteriorFieldCount
  sample_count_pos : 0 < summarySampleCount
  field_count_pos : 0 < summaryFieldCount
  signs :
    0 < psiMean ∧ logAMean < 0 ∧ 0 < fMean ∧ 0 < tauMean ∧
      0 < phiMean ∧ 0 < logLMean ∧ logPriorMean = 0
  f_quantiles : fQ16 < fMedian ∧ fMedian < fQ84
  tau_quantiles : tauQ16 < tauMedian ∧ tauMedian < tauQ84
  schema_cert_available : Nonempty GWTC3RingdownHDF5SampleSchemaCert

def gwtc3RingdownHDF5SampleSummaryCert :
    GWTC3RingdownHDF5SampleSummaryCert where
  member_matches_schema := summary_member_matches_schema
  path_matches_schema := summary_path_matches_schema
  sample_count_matches_schema := summary_sample_count_matches_schema
  field_count_matches_schema := summary_field_count_matches_schema
  sample_count_pos := summary_sample_count_pos
  field_count_pos := summary_field_count_pos
  signs := mean_signs
  f_quantiles := f_quantile_order
  tau_quantiles := tau_quantile_order
  schema_cert_available := gwtc3RingdownHDF5SampleSchemaCert_inhabited

theorem gwtc3RingdownHDF5SampleSummaryCert_inhabited :
    Nonempty GWTC3RingdownHDF5SampleSummaryCert :=
  ⟨gwtc3RingdownHDF5SampleSummaryCert⟩

/-- One-statement posterior-summary theorem for the range-read HDF5 sample. -/
theorem gwtc3_ringdown_hdf5_sample_summary_one_statement :
    (summarySampleCount = 15114) ∧
    (summaryFieldCount = 7) ∧
    (0 < fMean) ∧
    (0 < tauMean) ∧
    (logAMean < 0) ∧
    (logPriorMean = 0) ∧
    (fQ16 < fMedian ∧ fMedian < fQ84) ∧
    (tauQ16 < tauMedian ∧ tauMedian < tauQ84) ∧
    Nonempty GWTC3RingdownHDF5SampleSummaryCert :=
  ⟨rfl, rfl,
   mean_signs.2.2.1,
   mean_signs.2.2.2.1,
   mean_signs.2.1,
   mean_signs.2.2.2.2.2.2,
   f_quantile_order,
   tau_quantile_order,
   gwtc3RingdownHDF5SampleSummaryCert_inhabited⟩

end GWTC3RingdownHDF5SampleSummary
end Verification
end IndisputableMonolith
