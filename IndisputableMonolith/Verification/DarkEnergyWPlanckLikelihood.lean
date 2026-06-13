import Mathlib
import IndisputableMonolith.Cosmology.DarkEnergyWofZStructural
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# Dark-Energy w0 Planck/BAO/SNe Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 dark-energy `w(z)` falsifier row with a
dataset-specific likelihood-style certificate.

Dataset handle:

* Planck 2018 + BAO + SNe constant-w example:
  `w0 = -1.03 ± 0.03`.

RS structural target:

* `w_RS(0) = -1`, from
  `Cosmology.DarkEnergyWofZStructural.w_RS_linear_at_zero`.
* sub-leading deviations away from zero redshift are suppressed by
  `φ⁻⁴⁴ z`, and are far below present `w` precision.

The certificate proves three honest facts:

1. The RS baseline `w_RS(0) = -1` is within one sigma of the constant-w
   Planck/BAO/SNe central value (the residual equals the quoted sigma).
2. The `φ⁻⁴⁴` z-scale target is below current one-sigma `w` precision.
3. The §7 row remains marked not currently sensitive in the dataset
   attachment.

This is a constant-w baseline consistency / non-sensitivity test, not a
confirmation of the dynamic RS `w(z)` function.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace DarkEnergyWPlanckLikelihood

open IndisputableMonolith.Cosmology.DarkEnergyWofZStructural
open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset constants and residual -/

/-- Planck+BAO+SNe constant-w central value. -/
def planckW0Central : ℝ := -1.03

/-- Planck+BAO+SNe constant-w one-sigma uncertainty. -/
def planckW0Sigma : ℝ := 0.03

/-- RS structural baseline at z=0. -/
def rsW0Baseline : ℝ := w_RS_linear 0

/-- RS structural deviation target at z=1, from the dataset attachment. -/
def rsW1DeviationTarget : ℝ := darkEnergyWAttachment.rsTargetScale

/-- Residual between Planck+BAO+SNe constant-w central value and RS baseline. -/
def darkEnergyWResidual : ℝ :=
  |planckW0Central - rsW0Baseline|

theorem planckW0Sigma_pos : 0 < planckW0Sigma := by
  unfold planckW0Sigma
  norm_num

theorem rsW1DeviationTarget_pos : 0 < rsW1DeviationTarget := by
  unfold rsW1DeviationTarget darkEnergyWAttachment
  norm_num

/-! ## §2. Likelihood-style statements -/

/-- The RS z=0 baseline is within one sigma of the Planck+BAO+SNe constant-w result.
The residual equals the quoted sigma, so the statement is non-strict. -/
theorem darkEnergyW_residual_le_one_sigma :
    darkEnergyWResidual ≤ planckW0Sigma := by
  unfold darkEnergyWResidual planckW0Central rsW0Baseline planckW0Sigma
  rw [w_RS_linear_at_zero]
  norm_num

/-- Current `w` precision is not sensitive to the φ⁻⁴⁴ z-scale target. -/
theorem darkEnergyW_sigma_gt_rs_z1_target :
    rsW1DeviationTarget < planckW0Sigma := by
  unfold rsW1DeviationTarget darkEnergyWAttachment planckW0Sigma
  norm_num

/-- Dark-energy `w(z)` dataset attachment is present, positive, and
explicitly marked not currently sensitive. -/
theorem darkEnergyW_dataset_attachment_status :
    HasPositiveSensitivity darkEnergyWAttachment ∧
    HasPositiveTargetScale darkEnergyWAttachment ∧
    darkEnergyWAttachment.currentlySensitive = false :=
  ⟨darkEnergyW_sensitivity_pos, darkEnergyW_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure DarkEnergyWPlanckLikelihoodCert where
  sigma_pos : 0 < planckW0Sigma
  target_pos : 0 < rsW1DeviationTarget
  residual_le_one_sigma :
    darkEnergyWResidual ≤ planckW0Sigma
  not_currently_sensitive :
    rsW1DeviationTarget < planckW0Sigma
  dataset_status :
    HasPositiveSensitivity darkEnergyWAttachment ∧
    HasPositiveTargetScale darkEnergyWAttachment ∧
    darkEnergyWAttachment.currentlySensitive = false

def darkEnergyWPlanckLikelihoodCert : DarkEnergyWPlanckLikelihoodCert where
  sigma_pos := planckW0Sigma_pos
  target_pos := rsW1DeviationTarget_pos
  residual_le_one_sigma := darkEnergyW_residual_le_one_sigma
  not_currently_sensitive := darkEnergyW_sigma_gt_rs_z1_target
  dataset_status := darkEnergyW_dataset_attachment_status

theorem darkEnergyWPlanckLikelihoodCert_inhabited :
    Nonempty DarkEnergyWPlanckLikelihoodCert :=
  ⟨darkEnergyWPlanckLikelihoodCert⟩

/-- One-statement dark-energy w0 likelihood attachment theorem. -/
theorem dark_energy_w_planck_likelihood_one_statement :
    (darkEnergyWResidual ≤ planckW0Sigma) ∧
    (rsW1DeviationTarget < planckW0Sigma) ∧
    (darkEnergyWAttachment.currentlySensitive = false) ∧
    Nonempty DarkEnergyWPlanckLikelihoodCert :=
  ⟨darkEnergyW_residual_le_one_sigma,
   darkEnergyW_sigma_gt_rs_z1_target,
   rfl,
   darkEnergyWPlanckLikelihoodCert_inhabited⟩

end

end DarkEnergyWPlanckLikelihood
end Verification
end IndisputableMonolith
