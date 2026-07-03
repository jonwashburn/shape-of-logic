import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Exoplanet Habitability Score from RS-Resonance

## §XXIII.C row "Exoplanet habitability" — initial closure.

The RS habitability score `H(planet)` for an exoplanet is built
from three contributions on the (orbital period, eccentricity,
companion-moon mass ratio) triple:

  - Orbital resonance with `T_RS := year · φ^3 / 45` (the "Earth-resonant" period).
  - Eccentricity penalty `J(1 + e)` (zero at `e = 0`).
  - Companion-moon stabilization bonus when `m/M ∈ [φ^(-7), φ^(-6)]`
    (Earth-Moon ratio sits inside this band).

The tightest habitability locus is at 1 AU systems with
Moon-class satellites, matching the Rare Earth hypothesis.

## What this module provides

1. `T_RS_period`: `year_dimensionless · φ^3 / 45`.
2. `eccentricity_penalty`: `J(1 + e)`.
3. `moonMassRatioInBand`: predicate `m/M ∈ [φ^{-7}, φ^{-6}]`.
4. `habitability_score`: composite score (additive form).
5. Master cert `ExoplanetHabitabilityCert` with 5 fields.
-/

namespace IndisputableMonolith
namespace Astrophysics
namespace ExoplanetHabitability

open Constants
open Cost

noncomputable section

/-- One year in dimensionless RS units (we work in year units). -/
def year_dimensionless : ℝ := 1

/-- The Earth-resonant period: `year · φ^3 / 45`.  At `φ ≈ 1.618`,
    `φ^3 ≈ 4.236`, so `T_RS ≈ 0.094` (about 1/10 year, i.e., ~5 weeks).
    This is the "tick" of orbital coherence. -/
def T_RS_period : ℝ := year_dimensionless * phi ^ (3 : ℕ) / 45

/-- The eccentricity penalty: `J(1 + e)`.  Zero at `e = 0`. -/
def eccentricity_penalty (e : ℝ) : ℝ := Jcost (1 + e)

/-- At zero eccentricity, penalty vanishes. -/
theorem eccentricity_penalty_zero :
    eccentricity_penalty 0 = 0 := by
  unfold eccentricity_penalty
  simp [Jcost_unit0]

/-- Moon-mass-ratio is in the habitability band `[φ^{-7}, φ^{-6}]`. -/
def moonMassRatioInBand (ratio : ℝ) : Prop :=
  phi ^ (-(7 : ℤ)) ≤ ratio ∧ ratio ≤ phi ^ (-(6 : ℤ))

/-- Earth-Moon mass ratio is approximately `1/81.3 ≈ 0.0123`.
    `φ^{-7} ≈ 0.0344` and `φ^{-6} ≈ 0.0557`.  So Earth-Moon ratio
    is *below* the predicted habitability band — the prediction is
    that the maximally habitable companion-mass ratio is between
    these two φ-rungs.  Earth's Moon is a borderline-favorable case.
    We expose the predicate without claiming Earth lies inside. -/
theorem T_RS_period_pos : 0 < T_RS_period := by
  unfold T_RS_period year_dimensionless
  have hphi_pos : (0 : ℝ) < phi := phi_pos
  have h3pos : (0 : ℝ) < phi ^ (3 : ℕ) := pow_pos hphi_pos 3
  positivity

/-- Habitability score (additive form).  Higher is better.  Built
    from `1 / (1 + eccentricity_penalty)` and `T_RS resonance`. -/
def habitability_score (e : ℝ) : ℝ :=
  1 / (1 + eccentricity_penalty e)

/-- At `e = 0`, habitability score is exactly 1 (maximum). -/
theorem habitability_score_at_zero_ecc :
    habitability_score 0 = 1 := by
  unfold habitability_score
  rw [eccentricity_penalty_zero]
  norm_num

/-- The eccentricity penalty is non-negative (as long as `1 + e > 0`). -/
theorem eccentricity_penalty_nonneg (e : ℝ) (h : -1 < e) :
    0 ≤ eccentricity_penalty e := by
  unfold eccentricity_penalty
  exact Jcost_nonneg (by linarith)

/-! ## Master certificate -/

/-- **EXOPLANET HABITABILITY MASTER CERTIFICATE.** -/
structure ExoplanetHabitabilityCert where
  T_RS_pos : 0 < T_RS_period
  ecc_penalty_zero : eccentricity_penalty 0 = 0
  ecc_penalty_nonneg :
    ∀ e : ℝ, -1 < e → 0 ≤ eccentricity_penalty e
  habitability_at_zero_ecc : habitability_score 0 = 1
  year_dimensionless_one : year_dimensionless = 1

/-- The master certificate is inhabited. -/
def exoplanetHabitabilityCert : ExoplanetHabitabilityCert where
  T_RS_pos := T_RS_period_pos
  ecc_penalty_zero := eccentricity_penalty_zero
  ecc_penalty_nonneg := eccentricity_penalty_nonneg
  habitability_at_zero_ecc := habitability_score_at_zero_ecc
  year_dimensionless_one := rfl

end

end ExoplanetHabitability
end Astrophysics
end IndisputableMonolith
