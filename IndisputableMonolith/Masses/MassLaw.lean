import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor

/-!
# The Master Mass Law

This module formalizes the master mass formula derived from first principles in Recognition Science.

## The Theory

1. Every stable recognition state (particle) occupies a rung on the φ-ladder.
2. The mass m is proportional to the coherence energy E_coh, scaled by sector yardstick and rung position.
3. The master formula: m = yardstick(Sector) * φ^{r - 8 + gap(Z)}

Where:
- yardstick(Sector) is the sector prefactor (binary and φ-offset)
- r is the species-specific rung integer
- 8 is the fundamental cycle period (τ₀)
- Z is the charge-based shift index
- gap(Z) is the correction term from the recognition gap series
-/

namespace IndisputableMonolith
namespace Masses
namespace MassLaw

open Constants
open Anchor
open Integers
open ChargeIndex

/-- The recognition gap correction term: gap(Z) = log_φ(1 + Z/φ).
    This term corrects the rung position based on the charge-induced skew. -/
noncomputable def gap_correction (Z_val : ℤ) : ℝ :=
  Real.log (1 + (Z_val : ℝ) / phi) / Real.log phi

/-- **THE MASTER MASS LAW**
    Predicts the mass of a species in a given sector. -/
noncomputable def predict_mass (sector : Sector) (rung : ℤ) (Z_val : ℤ) : ℝ :=
  yardstick sector * (phi ^ ((rung : ℝ) - 8 + gap_correction Z_val))

/-- Mass is positive for any valid configuration. -/
theorem predict_mass_pos (s : Sector) (r : ℤ) (Z_val : ℤ) :
    predict_mass s r Z_val > 0 := by
  unfold predict_mass
  apply mul_pos
  · -- yardstick is positive
    unfold yardstick Anchor.E_coh
    apply mul_pos
    · apply mul_pos
      · exact zpow_pos (by norm_num) (B_pow s)
      · exact zpow_pos phi_pos (-5 : ℤ)
    · exact zpow_pos phi_pos (r0 s)
  · -- phi^... is positive
    exact Real.rpow_pos_of_pos phi_pos _

/-! ## Derived Properties -/

/-- The mass law exhibits φ-scaling: increasing rung by 1 scales mass by φ. -/
theorem mass_rung_scaling (s : Sector) (r : ℤ) (Z_val : ℤ) :
    predict_mass s (r + 1) Z_val = phi * predict_mass s r Z_val := by
  unfold predict_mass
  -- φ^(r+1-8+gap) = φ^1 * φ^(r-8+gap)
  set gap := gap_correction Z_val
  have h_add : (((r + 1 : ℤ) : ℝ) - 8 + gap) = 1 + (((r : ℤ) : ℝ) - 8 + gap) := by
    push_cast
    ring
  rw [h_add, Real.rpow_add phi_pos]
  rw [Real.rpow_one]
  ring

/-- The "gap" term corrects for the charge-based shift.
    When Z=0 (neutral sector baseline), gap(0) = 0. -/
theorem gap_zero_neutral : gap_correction 0 = 0 := by
  unfold gap_correction
  simp only [Int.cast_zero, zero_div, add_zero, Real.log_one, zero_div]

end MassLaw
end Masses
end IndisputableMonolith
