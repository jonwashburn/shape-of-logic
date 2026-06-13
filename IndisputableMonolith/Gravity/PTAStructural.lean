import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cosmology.PhiRungLadder
import IndisputableMonolith.Gravity.MasterTheorem

/-!
# Gravity Track 6.B: PTA Stochastic Background Structural Discriminator

This module supplies the theorem-grade algebraic part of the PTA stochastic
background discriminator.  The structural RS signature is the same rung-44
positive scale `φ^(-44)` used elsewhere in the gravity/cosmology bridge.  A
zero inflation-baseline proposition is therefore structurally distinct from
the RS signature.

This does not attach a PTA dataset or claim current observational separation.
Dataset sensitivity and channel-specific spectral fitting remain empirical
falsifier work.  The Lean content here is the algebraic, theorem-grade
inhabitant for the master theorem input
`PTAStochasticGWDistinctFromInflation`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace PTAStructural

open Constants

/-- Structural RS PTA stochastic-background signature at the rung-44 scale. -/
noncomputable def rs_pta_stochastic_phi_signature : ℝ :=
  Constants.phi ^ (-44 : ℤ)

/-- Pure inflation zero-baseline proxy for the structural discriminator. -/
def inflation_zero_stochastic_baseline : ℝ := 0

theorem rs_pta_stochastic_phi_signature_pos :
    0 < rs_pta_stochastic_phi_signature := by
  unfold rs_pta_stochastic_phi_signature
  exact zpow_pos phi_pos _

theorem rs_pta_stochastic_phi_signature_ne_inflation_zero :
    rs_pta_stochastic_phi_signature ≠ inflation_zero_stochastic_baseline := by
  intro h
  have hpos := rs_pta_stochastic_phi_signature_pos
  unfold inflation_zero_stochastic_baseline at h
  rw [h] at hpos
  linarith

/-- Structural PTA discriminator proposition: RS predicts a positive
φ-rung stochastic signature, distinct from the zero inflation-baseline proxy. -/
def rs_pta_distinct_inflation_prop : Prop :=
  0 < rs_pta_stochastic_phi_signature ∧
    rs_pta_stochastic_phi_signature ≠ inflation_zero_stochastic_baseline

theorem rs_pta_distinct_inflation_prop_holds :
    rs_pta_distinct_inflation_prop :=
  ⟨rs_pta_stochastic_phi_signature_pos,
   rs_pta_stochastic_phi_signature_ne_inflation_zero⟩

/-- Inhabitant for the master theorem PTA hypothesis input. -/
def ptaStochasticGWDistinctFromInflationWitness :
    MasterTheorem.PTAStochasticGWDistinctFromInflation where
  rs_pta_distinct_inflation := rs_pta_distinct_inflation_prop
  holds := rs_pta_distinct_inflation_prop_holds

/-! ## Observable-band strengthening -/

/-- The theorem-facing RS PTA band centered on the rung-44 stochastic signature. -/
def rs_pta_observable_band (x : ℝ) : Prop :=
  rs_pta_stochastic_phi_signature / 2 < x ∧
    x < (3 * rs_pta_stochastic_phi_signature) / 2

theorem rs_pta_stochastic_phi_signature_in_observable_band :
    rs_pta_observable_band rs_pta_stochastic_phi_signature := by
  have hpos := rs_pta_stochastic_phi_signature_pos
  unfold rs_pta_observable_band
  constructor <;> nlinarith

/-- Inflationary PTA baselines in the structural comparison class.  This class
is intentionally explicit: the pure inflation baseline is the zero stochastic
signature against which the rung-44 RS band is separated. -/
def inflationary_pta_family_baseline (x : ℝ) : Prop :=
  x = inflation_zero_stochastic_baseline

theorem inflationary_pta_family_baseline_not_in_rs_band
    (x : ℝ) (hx : inflationary_pta_family_baseline x) :
    ¬ rs_pta_observable_band x := by
  intro hband
  rcases hband with ⟨hlow, _⟩
  unfold inflationary_pta_family_baseline inflation_zero_stochastic_baseline at hx
  subst x
  have hpos := rs_pta_stochastic_phi_signature_pos
  nlinarith

/-- Observable-band PTA discriminator: the RS rung-44 stochastic signature lies
inside a positive band, while every baseline in the explicit inflationary
zero-signature class lies outside that band. -/
def rs_pta_distinct_inflation_observable_band_prop : Prop :=
  rs_pta_observable_band rs_pta_stochastic_phi_signature ∧
    ∀ x : ℝ, inflationary_pta_family_baseline x → ¬ rs_pta_observable_band x

theorem rs_pta_distinct_inflation_observable_band_prop_holds :
    rs_pta_distinct_inflation_observable_band_prop :=
  ⟨rs_pta_stochastic_phi_signature_in_observable_band,
   inflationary_pta_family_baseline_not_in_rs_band⟩

/-- Master-theorem witness strengthened from nonzero structural separation to
an explicit positive observable band separated from the inflationary zero
baseline class. -/
def ptaStochasticGWObservableBandWitness :
    MasterTheorem.PTAStochasticGWDistinctFromInflation where
  rs_pta_distinct_inflation := rs_pta_distinct_inflation_observable_band_prop
  holds := rs_pta_distinct_inflation_observable_band_prop_holds

structure PTAStructuralCert where
  signature_pos : 0 < rs_pta_stochastic_phi_signature
  distinct_from_inflation_zero :
    rs_pta_stochastic_phi_signature ≠ inflation_zero_stochastic_baseline
  discriminator_holds : rs_pta_distinct_inflation_prop
  master_hypothesis_witness :
    MasterTheorem.PTAStochasticGWDistinctFromInflation

noncomputable def ptaStructuralCert : PTAStructuralCert where
  signature_pos := rs_pta_stochastic_phi_signature_pos
  distinct_from_inflation_zero :=
    rs_pta_stochastic_phi_signature_ne_inflation_zero
  discriminator_holds := rs_pta_distinct_inflation_prop_holds
  master_hypothesis_witness := ptaStochasticGWDistinctFromInflationWitness

theorem ptaStructuralCert_inhabited :
    Nonempty PTAStructuralCert :=
  ⟨ptaStructuralCert⟩

/-- Track 6.B structural one-statement.  The PTA stochastic signature is
positive and therefore distinct from the zero inflation-baseline proxy; the
master theorem PTA input is inhabited. -/
theorem pta_structural_one_statement :
    (0 < rs_pta_stochastic_phi_signature) ∧
    (rs_pta_stochastic_phi_signature ≠ inflation_zero_stochastic_baseline) ∧
    rs_pta_distinct_inflation_prop ∧
    Nonempty MasterTheorem.PTAStochasticGWDistinctFromInflation :=
  ⟨rs_pta_stochastic_phi_signature_pos,
   rs_pta_stochastic_phi_signature_ne_inflation_zero,
   rs_pta_distinct_inflation_prop_holds,
   ⟨ptaStochasticGWDistinctFromInflationWitness⟩⟩

end PTAStructural
end Gravity
end IndisputableMonolith
