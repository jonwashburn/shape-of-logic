import Mathlib
import IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-!
# E_coh Scale Reconciliation Audit

This module closes the theorem-grade audit layer for the P2 mass-bridge
problem.

The current non-circular `tau_n` bridge is honest: it uses no measured
particle mass. But if the raw `tau_n` bridge is applied directly to the
heavy-quark `massAtAnchor` values, the missing display factor is not a
single universal φ-shift. The evaluated required shifts for charm, bottom,
and top are different.

This file proves that fact as a reusable certificate. It does not close the
physical display map. It prevents the next pass from trying the wrong target:
`exists n, all masses close by phi^n`. Since charm and top share the same
`ZOf` value but require different raw exponents, the remaining bridge cannot
be only a function of `Z`; it must also see rung/generation data or the RG
running window.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Bridge
namespace EcohScaleReconciliation

open IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-- A universal real exponent would assign the same extra φ-shift to charm,
bottom, and top under the raw `tau_n` bridge. -/
def UniversalRealHeavyQuarkShift (n : ℝ) : Prop :=
  n = charm_required_phi_exponent ∧
  n = bottom_required_phi_exponent ∧
  n = top_required_phi_exponent

/-- A universal integer exponent is the old "single φ-power bridge" target. -/
def UniversalIntegerHeavyQuarkShift (n : ℤ) : Prop :=
  UniversalRealHeavyQuarkShift (n : ℝ)

/-- A Z-only display shift would assign one exponent to each `ZOf` value. This
is already too weak for heavy quarks because charm and top both have `ZOf = 276`
but require different evaluated shifts under the raw `tau_n` bridge. -/
def ZOnlyHeavyQuarkShift (shift : ℤ → ℝ) : Prop :=
  shift 276 = charm_required_phi_exponent ∧
  shift 24 = bottom_required_phi_exponent ∧
  shift 276 = top_required_phi_exponent

/-- The evaluated heavy-quark required exponents do not admit one universal
real shift. This is stronger than ruling out a universal integer shift. -/
theorem no_universal_real_heavy_quark_shift :
    ¬ ∃ n : ℝ, UniversalRealHeavyQuarkShift n := by
  intro h
  rcases h with ⟨n, hn⟩
  obtain ⟨h_charm_bottom, _, _⟩ := required_exponents_not_equal
  exact h_charm_bottom (by
    calc
      charm_required_phi_exponent = n := hn.1.symm
      _ = bottom_required_phi_exponent := hn.2.1)

/-- Therefore the old integer-φ-power reconciliation target is impossible on
the evaluated raw heavy-quark bridge. -/
theorem no_universal_integer_heavy_quark_shift :
    ¬ ∃ n : ℤ, UniversalIntegerHeavyQuarkShift n := by
  intro h
  rcases h with ⟨n, hn⟩
  exact no_universal_real_heavy_quark_shift ⟨(n : ℝ), hn⟩

/-- A display correction depending only on `ZOf` cannot close the evaluated raw
heavy-quark bridge: charm and top share `ZOf = 276` but demand different
exponents. -/
theorem no_z_only_heavy_quark_shift :
    ¬ ∃ shift : ℤ → ℝ, ZOnlyHeavyQuarkShift shift := by
  intro h
  rcases h with ⟨shift, hshift⟩
  obtain ⟨_, _, h_charm_top⟩ := required_exponents_not_equal
  exact h_charm_top (by
    calc
      charm_required_phi_exponent = shift 276 := hshift.1.symm
      _ = top_required_phi_exponent := hshift.2.2)

/-- The P2 audit conclusion: the remaining bridge must be sector/species
dependent, and in practice must see rung/generation or RG-window data in
addition to `Z`. A single scalar exponent cannot close charm, bottom, and top
under the raw `tau_n` bridge. -/
structure EcohScaleReconciliationAuditCert where
  no_real_universal_shift :
    ¬ ∃ n : ℝ, UniversalRealHeavyQuarkShift n
  no_integer_universal_shift :
    ¬ ∃ n : ℤ, UniversalIntegerHeavyQuarkShift n
  no_Z_only_shift :
    ¬ ∃ shift : ℤ → ℝ, ZOnlyHeavyQuarkShift shift
  heavy_quark_raw_obstruction :
    HeavyQuarkClosureObstructionCert

def ecohScaleReconciliationAuditCert_holds :
    EcohScaleReconciliationAuditCert where
  no_real_universal_shift := no_universal_real_heavy_quark_shift
  no_integer_universal_shift := no_universal_integer_heavy_quark_shift
  no_Z_only_shift := no_z_only_heavy_quark_shift
  heavy_quark_raw_obstruction := heavyQuarkClosureObstructionCert_holds

end EcohScaleReconciliation
end Bridge
end IndisputableMonolith
