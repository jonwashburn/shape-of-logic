import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownFamilyComparison
import IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy

/-!
# GWTC-3 Ringdown Family-Stratified Likelihood Selector

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the selector policy for future GWTC-3 ringdown
likelihoods.

Mapped / eligible families:

* `DS_1mode_10M` — direct `f_t_0` / `tau_t_0` damping mapping.
* `Kerr_220_0M` — Kerr 220 quality-factor mapping at 0M start.
* `Kerr_220_10M` — Kerr 220 quality-factor mapping at 10M start.

Blocked families:

* every `Kerr_221*` family until a 221-mode mapping is formalized;
* every `MMRDNP*` family until its observable mapping is formalized;
* `pseobnrv4hm` until waveform-family semantics are formalized.

Counts:

* total HDF5 files: `243`
* eligible files: `66`
* blocked files: `177`
* total model families: `14`
* eligible model families: `3`
* blocked model families: `11`

This is selector policy only. It computes no posterior likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownLikelihoodSelector

open IndisputableMonolith.Verification.GWTC3RingdownFilenameTaxonomy
open IndisputableMonolith.Verification.GWTC3RingdownFamilyComparison

/-! ## §1. Selector counts -/

def selectorTotalHDF5Files : Nat := 243
def selectorEligibleFiles : Nat := 66
def selectorBlockedFiles : Nat := 177
def selectorTotalModels : Nat := 14
def selectorEligibleModels : Nat := 3
def selectorBlockedModels : Nat := 11
def selectorNoMixedAggregation : Bool := true

/-! ## §2. Arithmetic facts -/

theorem selector_file_count_partition :
    selectorEligibleFiles + selectorBlockedFiles = selectorTotalHDF5Files := by
  unfold selectorEligibleFiles selectorBlockedFiles selectorTotalHDF5Files
  decide

theorem selector_model_count_partition :
    selectorEligibleModels + selectorBlockedModels = selectorTotalModels := by
  unfold selectorEligibleModels selectorBlockedModels selectorTotalModels
  decide

theorem selector_eligible_files_match_comparison :
    selectorEligibleFiles = comparisonTotalMembers := rfl

theorem selector_total_files_match_taxonomy :
    selectorTotalHDF5Files = taxonomyHDF5FileCount := rfl

theorem selector_has_blocked_files :
    0 < selectorBlockedFiles := by
  unfold selectorBlockedFiles
  decide

theorem selector_no_mixed_aggregation_true :
    selectorNoMixedAggregation = true := rfl

/-! ## §3. Master cert -/

structure GWTC3RingdownLikelihoodSelectorCert where
  file_count_partition :
    selectorEligibleFiles + selectorBlockedFiles = selectorTotalHDF5Files
  model_count_partition :
    selectorEligibleModels + selectorBlockedModels = selectorTotalModels
  eligible_files_match_comparison :
    selectorEligibleFiles = comparisonTotalMembers
  total_files_match_taxonomy :
    selectorTotalHDF5Files = taxonomyHDF5FileCount
  has_blocked_files :
    0 < selectorBlockedFiles
  no_mixed_aggregation :
    selectorNoMixedAggregation = true
  comparison_available :
    Nonempty GWTC3RingdownFamilyComparisonCert
  taxonomy_available :
    Nonempty GWTC3RingdownFilenameTaxonomyCert

def gwtc3RingdownLikelihoodSelectorCert :
    GWTC3RingdownLikelihoodSelectorCert where
  file_count_partition := selector_file_count_partition
  model_count_partition := selector_model_count_partition
  eligible_files_match_comparison := selector_eligible_files_match_comparison
  total_files_match_taxonomy := selector_total_files_match_taxonomy
  has_blocked_files := selector_has_blocked_files
  no_mixed_aggregation := selector_no_mixed_aggregation_true
  comparison_available := gwtc3RingdownFamilyComparisonCert_inhabited
  taxonomy_available := gwtc3RingdownFilenameTaxonomyCert_inhabited

theorem gwtc3RingdownLikelihoodSelectorCert_inhabited :
    Nonempty GWTC3RingdownLikelihoodSelectorCert :=
  ⟨gwtc3RingdownLikelihoodSelectorCert⟩

/-- One-statement selector theorem. -/
theorem gwtc3_ringdown_likelihood_selector_one_statement :
    (selectorTotalHDF5Files = 243) ∧
    (selectorEligibleFiles = 66) ∧
    (selectorBlockedFiles = 177) ∧
    (selectorTotalModels = 14) ∧
    (selectorEligibleModels = 3) ∧
    (selectorBlockedModels = 11) ∧
    (selectorNoMixedAggregation = true) ∧
    Nonempty GWTC3RingdownLikelihoodSelectorCert :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   gwtc3RingdownLikelihoodSelectorCert_inhabited⟩

end GWTC3RingdownLikelihoodSelector
end Verification
end IndisputableMonolith
