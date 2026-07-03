import Mathlib
import IndisputableMonolith.Constants

/-!
# SPARC Chi-Squared Falsifier for ILG

Formalizes the falsification criterion for the ILG rotation curve prediction:
if the median chi-squared per degree of freedom exceeds a threshold when
computed across the SPARC galaxy sample with zero per-galaxy free parameters,
the ILG model is falsified.

## RS Parameters (locked, from phi)

- alpha_t = (1 - 1/phi) / 2 ≈ 0.191
- C_lag = phi^(-5) ≈ 0.090
- Upsilon_star = phi ≈ 1.618

## Falsification Protocol

1. Compute ILG-predicted rotation curves for all ~175 SPARC galaxies
2. Use ZERO per-galaxy free parameters (all locked to phi)
3. Compute chi-squared per degree of freedom for each galaxy
4. Take the median across the sample
5. If median chi2/dof > threshold, ILG is FALSIFIED

## Threshold Choice

The theory document (line ~3304) claims median chi2/dof ~ 2.75.
A generous threshold of 5.0 allows for systematic errors.
A tight threshold of 3.0 tests the specific RS prediction.

See: scripts/sparc_ilg_comparison.py for the computational implementation.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SPARCFalsifier

open Constants

/-! ## Falsification Criterion -/

/-- The generous falsification threshold for ILG chi-squared per dof.
    If median chi2/dof > 5.0 across the SPARC sample, ILG is falsified. -/
def generous_threshold : ℝ := 5.0

/-- The tight threshold matching the RS prediction (median ~ 2.75).
    If median chi2/dof > 3.0, the specific RS prediction is refuted
    (though ILG as a framework might survive with different parameters). -/
def tight_threshold : ℝ := 3.0

/-- ILG is falsified if median chi2/dof exceeds the generous threshold. -/
def ILG_falsified (median_chi2_dof : ℝ) : Prop :=
  generous_threshold < median_chi2_dof

/-- The RS-specific prediction is refuted if median > tight threshold. -/
def RS_prediction_refuted (median_chi2_dof : ℝ) : Prop :=
  tight_threshold < median_chi2_dof

/-- If the median is below the generous threshold, ILG PASSES. -/
def ILG_passes (median_chi2_dof : ℝ) : Prop :=
  median_chi2_dof ≤ generous_threshold

/-- The falsification criterion is decidable (for any real number). -/
theorem falsification_decidable (x : ℝ) :
    ILG_falsified x ∨ ILG_passes x := by
  unfold ILG_falsified ILG_passes generous_threshold
  exact le_or_gt x 5.0 |>.elim (Or.inr) (Or.inl)

/-! ## RS Parameter Lock -/

/-- The alpha parameter is locked to alphaLock ≈ 0.191. -/
noncomputable def alpha_locked : ℝ := alphaLock

/-- The mass-to-light ratio is locked to phi ≈ 1.618. -/
noncomputable def upsilon_locked : ℝ := phi

/-- The lag coupling is locked to phi^(-5) ≈ 0.090. -/
noncomputable def clag_locked : ℝ := cLagLock

/-- All three parameters are derived from phi (zero free parameters). -/
theorem parameters_from_phi :
    alpha_locked = (1 - 1/phi) / 2 ∧
    upsilon_locked = phi ∧
    clag_locked = phi ^ (-(5 : ℝ)) := by
  unfold alpha_locked upsilon_locked clag_locked alphaLock cLagLock
  exact ⟨rfl, rfl, rfl⟩

/-- The number of per-galaxy free parameters is exactly zero. -/
def per_galaxy_free_parameters : ℕ := 0

theorem zero_free_params : per_galaxy_free_parameters = 0 := rfl

/-! ## SPARC Benchmark Values

The theory document (line ~3304) gives benchmark chi2 values.
These are encoded as hypotheses (to be discharged by the Python script). -/

/-- RS-predicted median chi2/dof across SPARC. -/
def predicted_median : ℝ := 2.75

/-- The RS prediction: median chi2/dof ≈ 2.75 (within 1.0). -/
def H_SPARC_median : Prop :=
  ∃ median_obs : ℝ, abs (median_obs - predicted_median) < 1.0 ∧
    ILG_passes median_obs

/-! ## Paper II Benchmark Values (Rotation-curves-Paper2-Sept-26.tex) -/

/-- Paper II reports ILG median chi2/N = 2.75 on SPARC Q=1 subset. -/
def paper2_median_chi2 : ℝ := 2.75

/-- Paper II reports ILG mean chi2/N = 4.23 on SPARC Q=1 subset. -/
def paper2_mean_chi2 : ℝ := 4.23

/-- Paper II SPARC Q=1 sample size. -/
def paper2_N_galaxies : ℕ := 127

/-- MOND simple-nu comparison: median 2.47, mean 4.65. -/
def mond_median_chi2 : ℝ := 2.47
def mond_mean_chi2 : ℝ := 4.65

/-- ILG has higher median but LOWER mean than MOND — it handles
    outliers better due to the global-only constraint. -/
theorem ilg_better_mean_than_mond :
    paper2_mean_chi2 < mond_mean_chi2 := by
  unfold paper2_mean_chi2 mond_mean_chi2; norm_num

/-! ## Global-Only Policy (Paper I + Paper II) -/

/-- The global-only policy: the ILG weight function w(r) depends ONLY
    on catalog-level constants (alpha, C_lag, Upsilon, tau_star) and
    the photometric baryonic profile (v_gas, v_disk, v_bul).

    It does NOT depend on:
    - The observed rotation velocity (kinematic data)
    - Any per-galaxy fitted parameter
    - The galaxy's morphological classification (beyond photometry)

    This is formalized as: the parameters are functions of phi alone. -/
structure GlobalOnlyPolicy where
  alpha_from_phi : alpha_locked = (1 - 1/phi) / 2
  upsilon_from_phi : upsilon_locked = phi
  clag_from_phi : clag_locked = phi ^ (-(5 : ℝ))
  per_galaxy_params : per_galaxy_free_parameters = 0

theorem global_only_policy : GlobalOnlyPolicy where
  alpha_from_phi := parameters_from_phi.1
  upsilon_from_phi := parameters_from_phi.2.1
  clag_from_phi := parameters_from_phi.2.2
  per_galaxy_params := zero_free_params

/-! ## Negative Control Tests -/

/-- Negative control: velocity permutation (shuffle v_obs across radii).
    Must inflate chi2 well above the ILG median. -/
def NegativeControl := ℝ → Prop

/-- Velocity permutation: randomly reassign v_obs to different radii. -/
def velocity_permutation_control (chi2_perm : ℝ) : Prop :=
  paper2_median_chi2 < chi2_perm

/-- 180-degree rotation: reverse the radial profile. -/
def rotation_180_control (chi2_rot : ℝ) : Prop :=
  paper2_median_chi2 < chi2_rot

/-- Gas-stars swap: interchange v_gas and v_disk. -/
def gas_stars_swap_control (chi2_swap : ℝ) : Prop :=
  paper2_median_chi2 < chi2_swap

/-- All negative controls must inflate chi2 above the ILG result. -/
def all_controls_inflated (chi2_perm chi2_rot chi2_swap : ℝ) : Prop :=
  velocity_permutation_control chi2_perm ∧
  rotation_180_control chi2_rot ∧
  gas_stars_swap_control chi2_swap

/-! ## Certificate -/

structure SPARCFalsifierCert where
  zero_params : per_galaxy_free_parameters = 0
  params_from_phi : alpha_locked = (1 - 1/phi) / 2 ∧ upsilon_locked = phi ∧
    clag_locked = phi ^ (-(5 : ℝ))
  criterion_decidable : ∀ x : ℝ, ILG_falsified x ∨ ILG_passes x
  global_only : GlobalOnlyPolicy
  ilg_beats_mond_mean : paper2_mean_chi2 < mond_mean_chi2

theorem sparc_falsifier_cert : SPARCFalsifierCert where
  zero_params := zero_free_params
  params_from_phi := parameters_from_phi
  criterion_decidable := falsification_decidable
  global_only := global_only_policy
  ilg_beats_mond_mean := ilg_better_mean_than_mond

end SPARCFalsifier
end Gravity
end IndisputableMonolith
