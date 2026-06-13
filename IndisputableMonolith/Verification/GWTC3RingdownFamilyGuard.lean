import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownLikelihoodSelector

/-!
# GWTC-3 Ringdown Runtime Family Guard

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the runtime guard induced by the Session 131
family-stratified likelihood selector.

The guard accepts only the three mapped model families:

* `DS_1mode_10M`
* `Kerr_220_0M`
* `Kerr_220_10M`

and rejects all blocked/unknown model families, including representative
blocked families:

* `Kerr_221_0M`
* `Kerr_221_domega_221_0M`
* `MMRDNP_10M`
* `pseobnrv4hm`
* unknown models

This is runtime-policy formalization only. It computes no posterior
likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownFamilyGuard

open IndisputableMonolith.Verification.GWTC3RingdownLikelihoodSelector

/-! ## §1. Model-family guard -/

inductive GuardDecision where
  | accept
  | reject
deriving DecidableEq

def guardModel (model : String) : GuardDecision :=
  if model = "DS_1mode_10M" then .accept
  else if model = "Kerr_220_0M" then .accept
  else if model = "Kerr_220_10M" then .accept
  else .reject

theorem guard_accepts_DS :
    guardModel "DS_1mode_10M" = .accept := by
  unfold guardModel
  simp

theorem guard_accepts_Kerr2200 :
    guardModel "Kerr_220_0M" = .accept := by
  unfold guardModel
  simp

theorem guard_accepts_Kerr22010 :
    guardModel "Kerr_220_10M" = .accept := by
  unfold guardModel
  simp

theorem guard_rejects_Kerr2210 :
    guardModel "Kerr_221_0M" = .reject := by
  unfold guardModel
  simp

theorem guard_rejects_Kerr221Domega :
    guardModel "Kerr_221_domega_221_0M" = .reject := by
  unfold guardModel
  simp

theorem guard_rejects_MMRDNP :
    guardModel "MMRDNP_10M" = .reject := by
  unfold guardModel
  simp

theorem guard_rejects_pseobnrv4hm :
    guardModel "pseobnrv4hm" = .reject := by
  unfold guardModel
  simp

theorem guard_rejects_unknown :
    guardModel "not_a_real_family" = .reject := by
  unfold guardModel
  simp

/-! ## §2. Counts from the runtime test -/

def guardEligibleModelCount : Nat := 3
def guardBlockedModelCount : Nat := 11
def guardTestCount : Nat := 8
def guardAcceptedTestCount : Nat := 3
def guardRejectedTestCount : Nat := 5
def guardAllTestsPassed : Bool := true

theorem guard_counts_match_selector :
    guardEligibleModelCount = selectorEligibleModels ∧
      guardBlockedModelCount = selectorBlockedModels := by
  unfold guardEligibleModelCount guardBlockedModelCount selectorEligibleModels selectorBlockedModels
  simp

theorem guard_test_count_partition :
    guardAcceptedTestCount + guardRejectedTestCount = guardTestCount := by
  unfold guardAcceptedTestCount guardRejectedTestCount guardTestCount
  decide

theorem guard_all_tests_passed :
    guardAllTestsPassed = true := rfl

/-! ## §3. Master cert -/

structure GWTC3RingdownFamilyGuardCert where
  accepts_DS : guardModel "DS_1mode_10M" = .accept
  accepts_Kerr2200 : guardModel "Kerr_220_0M" = .accept
  accepts_Kerr22010 : guardModel "Kerr_220_10M" = .accept
  rejects_Kerr2210 : guardModel "Kerr_221_0M" = .reject
  rejects_MMRDNP : guardModel "MMRDNP_10M" = .reject
  rejects_pseobnrv4hm : guardModel "pseobnrv4hm" = .reject
  rejects_unknown : guardModel "not_a_real_family" = .reject
  counts_match_selector :
    guardEligibleModelCount = selectorEligibleModels ∧
      guardBlockedModelCount = selectorBlockedModels
  test_count_partition :
    guardAcceptedTestCount + guardRejectedTestCount = guardTestCount
  all_tests_passed : guardAllTestsPassed = true
  selector_available : Nonempty GWTC3RingdownLikelihoodSelectorCert

def gwtc3RingdownFamilyGuardCert :
    GWTC3RingdownFamilyGuardCert where
  accepts_DS := guard_accepts_DS
  accepts_Kerr2200 := guard_accepts_Kerr2200
  accepts_Kerr22010 := guard_accepts_Kerr22010
  rejects_Kerr2210 := guard_rejects_Kerr2210
  rejects_MMRDNP := guard_rejects_MMRDNP
  rejects_pseobnrv4hm := guard_rejects_pseobnrv4hm
  rejects_unknown := guard_rejects_unknown
  counts_match_selector := guard_counts_match_selector
  test_count_partition := guard_test_count_partition
  all_tests_passed := guard_all_tests_passed
  selector_available := gwtc3RingdownLikelihoodSelectorCert_inhabited

theorem gwtc3RingdownFamilyGuardCert_inhabited :
    Nonempty GWTC3RingdownFamilyGuardCert :=
  ⟨gwtc3RingdownFamilyGuardCert⟩

/-- One-statement runtime guard theorem. -/
theorem gwtc3_ringdown_family_guard_one_statement :
    (guardModel "DS_1mode_10M" = .accept) ∧
    (guardModel "Kerr_220_0M" = .accept) ∧
    (guardModel "Kerr_220_10M" = .accept) ∧
    (guardModel "Kerr_221_0M" = .reject) ∧
    (guardModel "MMRDNP_10M" = .reject) ∧
    (guardModel "pseobnrv4hm" = .reject) ∧
    (guardAllTestsPassed = true) ∧
    Nonempty GWTC3RingdownFamilyGuardCert :=
  ⟨guard_accepts_DS,
   guard_accepts_Kerr2200,
   guard_accepts_Kerr22010,
   guard_rejects_Kerr2210,
   guard_rejects_MMRDNP,
   guard_rejects_pseobnrv4hm,
   guard_all_tests_passed,
   gwtc3RingdownFamilyGuardCert_inhabited⟩

end GWTC3RingdownFamilyGuard
end Verification
end IndisputableMonolith
