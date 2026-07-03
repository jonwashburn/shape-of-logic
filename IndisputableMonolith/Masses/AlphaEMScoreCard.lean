import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Fine-Structure Constant Scorecard (construction value; exact α(0) OPEN)

The assembled RS inverse fine-structure constant expression α⁻¹ is:
  αInv = alpha_seed × exp(-(f_gap / alpha_seed))
       = 44π × exp(-(w8 × ln φ / (44π)))

where alpha_seed = 44π and f_gap = w8 × ln φ (the DFT-8 gap weight).

This module records:
- αInv ∈ (137.030, 137.039)     [AlphaBounds, proved]
- CODATA 2018: α⁻¹ = 137.035999084(21)
- αInv lands ~0.007% (≈5.6 ppm) from CODATA, with nothing fit to CODATA.

HONEST STATUS (2026-06-19 alpha audit): this is the VALUE of the construction, NOT a
derivation of the measured infrared constant. The seed `4π·11` is an identification,
not a derived coupling (gauge-invariant photon count is the cycle rank 5, not 11;
`AlphaGenesis.U1Normalization`), `4π·11` is a category error against the genuine
quadratic J-cost `π²` (`CurvatureJCostVerdict`), and the first-order value is excluded
by measurement at >30000σ (`MeasurementVerdict`). RS forces the photon channel, the
`O(4π)` recognition-scale coupling, and the φ-dressing; the exact `α⁻¹(0)` is an
irreducible boundary condition, OPEN (negative closure: five routes tested, all closed).
CODATA falling inside the band is the ~5.6 ppm near-miss, not a forced equality.

Lean status: 0 sorry, 0 axiom. The theorems below are true facts about the expression;
none of them derive the measured α(0).
-/

namespace IndisputableMonolith
namespace Masses
namespace AlphaEMScoreCard

open Constants

noncomputable section

/-- CODATA 2018 value. -/
def alphaInv_codata : ℝ := 137.035999084

/-- RS αInv is bounded in (137.030, 137.039). -/
theorem alphaInv_in_range :
    (137.030 : ℝ) < alphaInv ∧ alphaInv < (137.039 : ℝ) :=
  ⟨Numerics.alphaInv_gt, Numerics.alphaInv_lt⟩

/-- The CODATA value falls inside the construction's band `(137.030, 137.039)`. This
is the ~5.6 ppm near-miss of the seed identification, NOT a derivation of α(0); the
exact infrared value is a boundary condition (OPEN). -/
theorem codata_in_rs_interval :
    (137.030 : ℝ) < alphaInv_codata ∧ alphaInv_codata < (137.039 : ℝ) := by
  unfold alphaInv_codata
  constructor <;> norm_num

/-- Tighter lower bound: αInv > 137.031. -/
theorem alphaInv_gt_tight :
    (137.031 : ℝ) < alphaInv := Numerics.alphaInv_gt_137031

/-- The α⁻¹ expression is assembled with zero fitted parameters from:
    alpha_seed = 44π (the 8-tick × 11-cell seed identification, not a derived coupling)
    f_gap = w8 × ln φ (the DFT-8 gap weight × golden ratio, forced, zero α-input)
    αInv = alpha_seed × exp(-f_gap / alpha_seed)

    Nothing here is fit to CODATA, but this is the value of the construction, not a
    derivation of the measured α(0) (boundary condition, OPEN; see header). -/
theorem alphaInv_is_structural : alphaInv = alpha_seed * Real.exp (-(f_gap / alpha_seed)) := by
  unfold alphaInv; ring

/-- Fine-structure constant scorecard certificate. -/
structure AlphaEMScoreCardCert where
  in_range : (137.030 : ℝ) < alphaInv ∧ alphaInv < (137.039 : ℝ)
  codata_in_band : (137.030 : ℝ) < alphaInv_codata ∧ alphaInv_codata < (137.039 : ℝ)
  structural : alphaInv = alpha_seed * Real.exp (-(f_gap / alpha_seed))
  tight_lower : (137.031 : ℝ) < alphaInv

noncomputable def alphaEMScoreCardCert_holds : AlphaEMScoreCardCert where
  in_range := alphaInv_in_range
  codata_in_band := codata_in_rs_interval
  structural := alphaInv_is_structural
  tight_lower := alphaInv_gt_tight

end

end AlphaEMScoreCard
end Masses
end IndisputableMonolith
