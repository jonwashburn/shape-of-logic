import Mathlib
import IndisputableMonolith.Bridge.CosmicZDisplayFormula

/-!
# Cosmic-Z Display Formula Derivation Contract

This module narrows the remaining particle-mass bridge target.

Earlier modules prove:

* no universal shift can close the raw `tau_n` heavy-quark bridge;
* no `ZOf`-only shift can close it;
* the paired key `(ZOf f, rung f)` separates the charged spectrum;
* a formula interface over that paired key is buildable.

This file adds one more guard: a rung-only shift also cannot close the
heavy-quark bridge. Hence the next physical derivation cannot depend on only
one coordinate. It must derive a law on the paired key, or on richer data that
projects to that paired key, such as theta phase plus RG window.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Bridge
namespace CosmicZDisplayFormulaDerivation

open IndisputableMonolith.Bridge.CosmicZDisplayMap
open IndisputableMonolith.Bridge.CosmicZDisplayFormula
open IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-- A rung-only display shift would assign one exponent to each rung. This is
too coarse because bottom and top both sit at rung 21 but need different raw
exponents under the `tau_n` bridge. -/
def RungOnlyHeavyQuarkShift (shift : ℤ → ℝ) : Prop :=
  shift 15 = charm_required_phi_exponent ∧
  shift 21 = bottom_required_phi_exponent ∧
  shift 21 = top_required_phi_exponent

/-- A display correction depending only on rung cannot close the evaluated raw
heavy-quark bridge: bottom and top share rung 21 but demand different
exponents. -/
theorem no_rung_only_heavy_quark_shift :
    ¬ ∃ shift : ℤ → ℝ, RungOnlyHeavyQuarkShift shift := by
  intro h
  rcases h with ⟨shift, hshift⟩
  obtain ⟨_, h_bottom_top, _⟩ := required_exponents_not_equal
  exact h_bottom_top (by
    calc
      bottom_required_phi_exponent = shift 21 := hshift.2.1.symm
      _ = top_required_phi_exponent := hshift.2.2)

/-- Coordinate-minimality for the current heavy-quark obstruction: neither
coordinate alone is enough, while the pair `(ZOf,rung)` is expressive enough
to represent the audited shifts. -/
structure CoordinateMinimalityCert where
  no_Z_only :
    ¬ ∃ shift : ℤ → ℝ, EcohScaleReconciliation.ZOnlyHeavyQuarkShift shift
  no_rung_only :
    ¬ ∃ shift : ℤ → ℝ, RungOnlyHeavyQuarkShift shift
  paired_key_represents_audit :
    ∃ F : CosmicZFormula, HeavyQuarkShiftMatch F

theorem coordinateMinimalityCert_holds : CoordinateMinimalityCert where
  no_Z_only := EcohScaleReconciliation.no_z_only_heavy_quark_shift
  no_rung_only := no_rung_only_heavy_quark_shift
  paired_key_represents_audit := ⟨evaluatedAuditFormula, evaluatedAuditFormula_matches_heavy_quarks⟩

/-- Abstract first-principles kernel for the eventual derivation. The kernel
may use theta/RG/cosmic-Z data internally; its exported observable is the
paired-key shift law. -/
structure CosmicZKernel where
  shiftLaw : DisplayKey → ℝ

/-- Convert a kernel into the formula interface used downstream. -/
def CosmicZKernel.toFormula (K : CosmicZKernel) : CosmicZFormula where
  shift := K.shiftLaw

/-- The exact heavy-quark closure condition required of a future kernel. -/
def KernelClosesHeavyQuarkAudit (K : CosmicZKernel) : Prop :=
  HeavyQuarkShiftMatch K.toFormula

/-- Transport theorem: once a first-principles kernel proves the heavy-quark
match predicate, it supplies a valid `CosmicZFormula` for the existing
interface. -/
theorem formula_of_kernel_closes_heavy_quark_audit
    (K : CosmicZKernel)
    (hK : KernelClosesHeavyQuarkAudit K) :
    ∃ F : CosmicZFormula, HeavyQuarkShiftMatch F :=
  ⟨K.toFormula, hK⟩

/-- Audit witness as a kernel. This is not the physical kernel; it only proves
the contract is inhabited and keeps the theorem surface executable. -/
noncomputable def evaluatedAuditKernel : CosmicZKernel where
  shiftLaw := evaluatedZRungShift

theorem evaluatedAuditKernel_closes_heavy_quark_audit :
    KernelClosesHeavyQuarkAudit evaluatedAuditKernel :=
  evaluatedAuditFormula_matches_heavy_quarks

/-- Certificate for the P2d derivation contract. -/
structure CosmicZDisplayFormulaDerivationContractCert where
  coordinate_minimality :
    CoordinateMinimalityCert
  kernel_transport :
    ∀ K : CosmicZKernel,
      KernelClosesHeavyQuarkAudit K →
      ∃ F : CosmicZFormula, HeavyQuarkShiftMatch F
  audit_kernel_inhabits_contract :
    KernelClosesHeavyQuarkAudit evaluatedAuditKernel

theorem cosmicZDisplayFormulaDerivationContractCert_holds :
    CosmicZDisplayFormulaDerivationContractCert where
  coordinate_minimality := coordinateMinimalityCert_holds
  kernel_transport := formula_of_kernel_closes_heavy_quark_audit
  audit_kernel_inhabits_contract := evaluatedAuditKernel_closes_heavy_quark_audit

end CosmicZDisplayFormulaDerivation
end Bridge
end IndisputableMonolith
