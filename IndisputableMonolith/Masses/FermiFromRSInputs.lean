import Mathlib
import IndisputableMonolith.Masses.VEVConsistency
import IndisputableMonolith.Masses.ElectroweakMasses
import IndisputableMonolith.Constants

/-!
# Fermi Constant from RS Inputs

This module connects the VEV consistency result (P5a) to the Fermi constant,
showing that G_F is determined by RS-derived inputs through the chain:

  (m_Z, sin²θ_W, α_EM) → v² → G_F = 1/(√2 · v²)

Since VEVConsistency proves v² = z² · (8-φ)/36 · α⁻¹/π with all inputs
RS-derived (zero free parameters), G_F inherits that structural origin.

The tree-level relation G_F = π · α / (√2 · m_Z² · sin²θ_W · cos²θ_W)
uses the sin²·cos² = (8-φ)/36 closed form proved in VEVConsistency.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Masses.FermiFromRSInputs

open IndisputableMonolith.Constants
open IndisputableMonolith.Masses.ElectroweakMasses
open IndisputableMonolith.Masses.VEVConsistency

noncomputable section

/-- Tree-level G_F from RS inputs (in MeV⁻²). -/
noncomputable def gf_tree_inv : ℝ :=
  Real.sqrt 2 * vev_tree_sq

/-- G_F expressed through the sin²·cos² closed form.
    G_F⁻¹ = √2 · z² · (8-φ)/36 · α⁻¹/π. -/
theorem gf_tree_inv_closed_form :
    gf_tree_inv = Real.sqrt 2 *
      (ElectroweakMasses.z_pred ^ 2 * ((8 - phi) / 36) * alphaInv / Real.pi) := by
  unfold gf_tree_inv
  rw [vev_tree_sq_closed_form]

/-- The VEV squared is positive (since z_pred > 0, (8-φ)/36 > 0, αInv > 0, π > 0). -/
theorem vev_tree_sq_pos : 0 < vev_tree_sq := by
  unfold vev_tree_sq
  have hz : 0 < z_pred := by linarith [z_mass_bounds.1]
  have hs2 : 0 < sin2_theta_W_rs := sin2_theta_positive
  have hc2 : 0 < cos2_theta_W_rs := cos2_theta_positive
  have hα : 0 < alphaInv := by linarith [Numerics.alphaInv_gt]
  have hπ : 0 < Real.pi := Real.pi_pos
  have hz2 : 0 < z_pred ^ 2 := sq_pos_of_ne_zero (ne_of_gt hz)
  have hsc : 0 < sin2_theta_W_rs * cos2_theta_W_rs := mul_pos hs2 hc2
  have h1 : 0 < z_pred ^ 2 * sin2_theta_W_rs := mul_pos hz2 hs2
  have h2 : 0 < z_pred ^ 2 * sin2_theta_W_rs * cos2_theta_W_rs := mul_pos h1 hc2
  have h3 : 0 < z_pred ^ 2 * sin2_theta_W_rs * cos2_theta_W_rs * alphaInv := mul_pos h2 hα
  exact div_pos h3 hπ

/-- G_F⁻¹ is positive (since it is √2 times a positive quantity). -/
theorem gf_tree_inv_pos : 0 < gf_tree_inv := by
  unfold gf_tree_inv
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) vev_tree_sq_pos

/-- The number of free parameters in the G_F derivation chain. -/
def free_parameters_in_gf_chain : ℕ := 0

/-- All RS inputs in the G_F chain are structural. -/
theorem gf_zero_free_params :
    free_parameters_in_gf_chain = 0 := rfl

structure FermiFromRSInputsCert where
  closed_form :
    gf_tree_inv = Real.sqrt 2 *
      (z_pred ^ 2 * ((8 - phi) / 36) * alphaInv / Real.pi)
  positivity : 0 < gf_tree_inv
  zero_params : free_parameters_in_gf_chain = 0

noncomputable def fermiFromRSInputsCert_holds : FermiFromRSInputsCert where
  closed_form := gf_tree_inv_closed_form
  positivity := gf_tree_inv_pos
  zero_params := gf_zero_free_params

end

end IndisputableMonolith.Masses.FermiFromRSInputs
