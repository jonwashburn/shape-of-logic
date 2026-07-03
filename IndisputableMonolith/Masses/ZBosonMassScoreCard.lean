import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.ElectroweakMasses

/-!
# Z Boson Mass Scorecard

The Z boson mass is derived from the φ-ladder at rung 1 in the Electroweak
sector:
  m_Z = 2 × φ^51 / 10^6 MeV

Results (from ElectroweakMasses):
- m_Z ∈ (91075.09, 91075.10) MeV
- PDG: 91187.6 MeV
- Relative error < 0.13% (zero fitted parameters)

This is a thin scorecard wrapper around the ElectroweakMasses proofs.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace ZBosonMassScoreCard

open Constants ElectroweakMasses

noncomputable section

/-- The Z mass prediction equals 2 × φ^51 / 10^6. -/
theorem z_from_phi_ladder : z_pred = 2 * phi ^ (51 : ℕ) / 1000000 := z_pred_eq

/-- Z mass is in a narrow interval. -/
theorem z_bounded : (91075.09 : ℝ) < z_pred ∧ z_pred < (91075.10 : ℝ) := z_mass_bounds

/-- The prediction is within 0.13% of PDG. -/
theorem z_within_013_pct : |z_pred - m_Z_exp| / m_Z_exp < 0.0013 := z_relative_error

/-- Scorecard certificate. -/
structure ZBosonMassScoreCardCert where
  formula : z_pred = 2 * phi ^ (51 : ℕ) / 1000000
  interval : (91075.09 : ℝ) < z_pred ∧ z_pred < (91075.10 : ℝ)
  relative_error : |z_pred - m_Z_exp| / m_Z_exp < 0.0013

noncomputable def zBosonMassScoreCardCert_holds : ZBosonMassScoreCardCert where
  formula := z_from_phi_ladder
  interval := z_bounded
  relative_error := z_within_013_pct

end

end ZBosonMassScoreCard
end Masses
end IndisputableMonolith
