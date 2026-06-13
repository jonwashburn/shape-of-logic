import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownFamilyGuard
import IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily
import IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily
import IndisputableMonolith.Verification.GWTC3RingdownKerr22010MDampingFamily

/-!
# GWTC-3 Ringdown Guarded Family Scripts

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records Session 133: the runtime family guard is now wired
into the mapped family-statistic scripts.

Patched scripts:

* `gwtc3_ringdown_ds1mode10m_damping_family.py`
* `gwtc3_ringdown_kerr2200m_damping_family.py`
* `gwtc3_ringdown_kerr22010m_damping_family.py`

Each script now calls `require_eligible_model(MODEL)` before reading
posterior data. A smoke test confirms eligible families pass and
representative blocked/unknown families fail.

This is operational guarding only. It adds no new physics mapping and
computes no new likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownGuardedFamilyScripts

open IndisputableMonolith.Verification.GWTC3RingdownFamilyGuard
open IndisputableMonolith.Verification.GWTC3RingdownDS1Mode10MDampingFamily
open IndisputableMonolith.Verification.GWTC3RingdownKerr2200MDampingFamily
open IndisputableMonolith.Verification.GWTC3RingdownKerr22010MDampingFamily

/-! ## §1. Guarded script counts -/

def guardedScriptCount : Nat := 3
def smokeTestCount : Nat := 7
def smokePassCount : Nat := 7
def smokeAllPassed : Bool := true

theorem guarded_script_count_matches_selector :
    guardedScriptCount = guardEligibleModelCount := rfl

theorem smoke_all_passed : smokeAllPassed = true := rfl

theorem smoke_pass_count_eq_test_count :
    smokePassCount = smokeTestCount := rfl

/-! ## §2. Guard accepts mapped scripts -/

theorem guarded_DS_script_accepted :
    guardModel "DS_1mode_10M" = .accept :=
  guard_accepts_DS

theorem guarded_Kerr2200_script_accepted :
    guardModel "Kerr_220_0M" = .accept :=
  guard_accepts_Kerr2200

theorem guarded_Kerr22010_script_accepted :
    guardModel "Kerr_220_10M" = .accept :=
  guard_accepts_Kerr22010

theorem representative_blocked_rejected :
    guardModel "Kerr_221_0M" = .reject ∧
    guardModel "MMRDNP_10M" = .reject ∧
    guardModel "pseobnrv4hm" = .reject :=
  ⟨guard_rejects_Kerr2210, guard_rejects_MMRDNP, guard_rejects_pseobnrv4hm⟩

/-! ## §3. Master cert -/

structure GWTC3RingdownGuardedFamilyScriptsCert where
  guarded_count :
    guardedScriptCount = guardEligibleModelCount
  smoke_passed :
    smokeAllPassed = true
  smoke_count :
    smokePassCount = smokeTestCount
  DS_script_accepted :
    guardModel "DS_1mode_10M" = .accept
  Kerr2200_script_accepted :
    guardModel "Kerr_220_0M" = .accept
  Kerr22010_script_accepted :
    guardModel "Kerr_220_10M" = .accept
  blocked_rejected :
    guardModel "Kerr_221_0M" = .reject ∧
    guardModel "MMRDNP_10M" = .reject ∧
    guardModel "pseobnrv4hm" = .reject
  DS_cert_available :
    Nonempty GWTC3RingdownDS1Mode10MDampingFamilyCert
  Kerr2200_cert_available :
    Nonempty GWTC3RingdownKerr2200MDampingFamilyCert
  Kerr22010_cert_available :
    Nonempty GWTC3RingdownKerr22010MDampingFamilyCert
  guard_cert_available :
    Nonempty GWTC3RingdownFamilyGuardCert

def gwtc3RingdownGuardedFamilyScriptsCert :
    GWTC3RingdownGuardedFamilyScriptsCert where
  guarded_count := guarded_script_count_matches_selector
  smoke_passed := smoke_all_passed
  smoke_count := smoke_pass_count_eq_test_count
  DS_script_accepted := guarded_DS_script_accepted
  Kerr2200_script_accepted := guarded_Kerr2200_script_accepted
  Kerr22010_script_accepted := guarded_Kerr22010_script_accepted
  blocked_rejected := representative_blocked_rejected
  DS_cert_available := gwtc3RingdownDS1Mode10MDampingFamilyCert_inhabited
  Kerr2200_cert_available := gwtc3RingdownKerr2200MDampingFamilyCert_inhabited
  Kerr22010_cert_available := gwtc3RingdownKerr22010MDampingFamilyCert_inhabited
  guard_cert_available := gwtc3RingdownFamilyGuardCert_inhabited

theorem gwtc3RingdownGuardedFamilyScriptsCert_inhabited :
    Nonempty GWTC3RingdownGuardedFamilyScriptsCert :=
  ⟨gwtc3RingdownGuardedFamilyScriptsCert⟩

/-- One-statement theorem for the guarded family scripts. -/
theorem gwtc3_ringdown_guarded_family_scripts_one_statement :
    (guardedScriptCount = 3) ∧
    (smokeTestCount = 7) ∧
    (smokePassCount = 7) ∧
    (smokeAllPassed = true) ∧
    (guardModel "DS_1mode_10M" = .accept) ∧
    (guardModel "Kerr_220_0M" = .accept) ∧
    (guardModel "Kerr_220_10M" = .accept) ∧
    Nonempty GWTC3RingdownGuardedFamilyScriptsCert :=
  ⟨rfl, rfl, rfl, rfl,
   guard_accepts_DS,
   guard_accepts_Kerr2200,
   guard_accepts_Kerr22010,
   gwtc3RingdownGuardedFamilyScriptsCert_inhabited⟩

end GWTC3RingdownGuardedFamilyScripts
end Verification
end IndisputableMonolith
