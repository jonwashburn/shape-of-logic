import Mathlib
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Physics.MassTopology
import IndisputableMonolith.Physics.LeptonGenerations.Defs
import IndisputableMonolith.Verification.WallpaperEndogenousBridge

/-!
# Wallpaper Sufficiency for the Mass Path

This module formalizes the "sufficiency route" for O6 in the mass framework:
the canonical mass-path formulas are unchanged when the imported crystallographic
constant `wallpaper_groups` is replaced by the endogenous cube-derived
`W_from_cube = E_passive + F` (at `D=3`).
-/

namespace IndisputableMonolith
namespace Verification
namespace WallpaperSufficiencyMassPath

open Constants.AlphaDerivation
open Physics.MassTopology
open Physics.LeptonGenerations
open WallpaperEndogenousBridge

noncomputable section

/-- Endogenous and imported `W` coincide on the canonical dimension. -/
theorem W_endogenous_eq_massTopology_W : W_from_cube = W := by
  simpa [W] using W_from_cube_eq_wallpaper_groups

/-- The ledger-fraction formula is invariant under replacing `W` by `W_from_cube`. -/
theorem ledger_fraction_rewrite_endogenous :
    ledger_fraction = (W_from_cube + E_total) / (4 * E_passive) := by
  unfold ledger_fraction
  rw [W_endogenous_eq_massTopology_W]

/-- The base shift is invariant under the endogenous replacement of `W`. -/
theorem base_shift_rewrite_endogenous :
    base_shift = 2 * (W_from_cube : ℝ) + ((W_from_cube + E_total) / (4 * E_passive) : ℚ) := by
  have hW : (W : ℝ) = (W_from_cube : ℝ) := by
    exact_mod_cast W_endogenous_eq_massTopology_W.symm
  calc
    base_shift = 2 * (W : ℝ) + (ledger_fraction : ℝ) := by simp [base_shift]
    _ = 2 * (W_from_cube : ℝ) + ((W_from_cube + E_total) / (4 * E_passive) : ℚ) := by
          simp [hW, ledger_fraction_rewrite_endogenous]

/-- The mu→tau step formula is invariant under the endogenous replacement of `W`. -/
theorem step_mu_tau_rewrite_endogenous :
    step_mu_tau = (cube_faces D : ℝ) - (2 * W_from_cube + D) / 2 * Constants.alpha := by
  have hW : wallpaper_groups = W_from_cube := by
    simpa [W] using W_endogenous_eq_massTopology_W.symm
  simp [step_mu_tau, hW]

/-- Packaged mass-path closure: all canonical `W`-bearing formulas used in the
mass path are invariant under replacing imported `wallpaper_groups` with
endogenous `W_from_cube`. -/
theorem mass_path_endogenous_replacement_complete :
    W_from_cube = W ∧
    ledger_fraction = (W_from_cube + E_total) / (4 * E_passive) ∧
    base_shift = 2 * (W_from_cube : ℝ) + ((W_from_cube + E_total) / (4 * E_passive) : ℚ) ∧
    step_mu_tau = (cube_faces D : ℝ) - (2 * W_from_cube + D) / 2 * Constants.alpha := by
  refine ⟨W_endogenous_eq_massTopology_W, ledger_fraction_rewrite_endogenous,
    base_shift_rewrite_endogenous, step_mu_tau_rewrite_endogenous⟩

end
end WallpaperSufficiencyMassPath
end Verification
end IndisputableMonolith
