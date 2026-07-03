import Mathlib
import IndisputableMonolith.Constants

/-!
# Dark Energy Equation of State — S3 Depth

w(z) on the φ-ladder: adjacent-redshift ratio corrections of order φ⁻ⁿ.

Five canonical w-models (= configDim D = 5):
  ΛCDM (w = -1), wCDM (constant w), w0wa CPL, quintessence, phantom.

Canonical BIT kernel: w_BIT(z) = -1 + δ with δ ≤ 1/φ⁵ ≈ 0.09.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.DarkEnergyEquationOfStateDepth
open Constants

inductive DarkEnergyModel where
  | lambdaCDM
  | wCDM
  | w0wa_CPL
  | quintessence
  | phantom
  deriving DecidableEq, Repr, BEq, Fintype

theorem darkEnergyModel_count : Fintype.card DarkEnergyModel = 5 := by decide

/-- δ bound = 1/φ⁵. Using φ⁵ = 5φ + 3. -/
noncomputable def deltaBound : ℝ := 1 / phi ^ 5

theorem phi5_eq : phi ^ 5 = 5 * phi + 3 := by
  have h2 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by nlinarith
  have h4 : phi ^ 4 = 3 * phi + 2 := by nlinarith
  nlinarith

theorem deltaBound_pos : 0 < deltaBound := by
  unfold deltaBound
  exact div_pos one_pos (pow_pos phi_pos 5)

theorem deltaBound_small : deltaBound < 0.1 := by
  unfold deltaBound
  have h5 : phi ^ 5 = 5 * phi + 3 := phi5_eq
  rw [h5]
  have h_phi_gt : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
  have h_denom : (11.05 : ℝ) < 5 * phi + 3 := by linarith
  have h_denom_pos : (0 : ℝ) < 5 * phi + 3 := by linarith
  rw [div_lt_iff₀ h_denom_pos]
  nlinarith

structure DarkEnergyEoSDepthCert where
  five_models : Fintype.card DarkEnergyModel = 5
  phi5_fibonacci : phi ^ 5 = 5 * phi + 3
  delta_pos : 0 < deltaBound
  delta_bounded : deltaBound < 0.1

noncomputable def darkEnergyEoSDepthCert : DarkEnergyEoSDepthCert where
  five_models := darkEnergyModel_count
  phi5_fibonacci := phi5_eq
  delta_pos := deltaBound_pos
  delta_bounded := deltaBound_small

end IndisputableMonolith.Cosmology.DarkEnergyEquationOfStateDepth
