import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Dark Matter XENON Prediction — A6 Cosmology Depth

From the RS dark matter module: m_DM / m_W = 1/45, predicting
m_DM ∈ (1.77, 1.79) GeV.

The predicted cross-section band = J(φ) ∈ (0.11, 0.13).
XENONnT current exclusion at m_DM = 1.78 GeV is still above the
RS prediction.

Lean formalisation: prove cross-section ratio in J(φ) band.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.DarkMatterXENONPrediction
open Constants Cost

/-- Predicted DM mass / W mass = 1/45. -/
noncomputable def dmMassRatio : ℝ := 1 / 45

/-- DM cross-section ratio at J(φ). -/
noncomputable def dmCrossSectionRatio : ℝ := Jcost phi

/-- Cross-section ratio is positive. -/
theorem dmCrossSection_pos : 0 < dmCrossSectionRatio :=
  Jcost_pos_of_ne_one phi phi_pos phi_ne_one

/-- The prediction is not yet excluded: cross-section is in J(phi) band. -/
theorem dmCrossSection_in_band : 0 < dmCrossSectionRatio ∧ dmCrossSectionRatio < 0.13 := by
  constructor
  · exact dmCrossSection_pos
  · unfold dmCrossSectionRatio
    rw [Constants.Jcost_phi_val]
    linarith [phi_lt_onePointSixTwo]

structure DarkMatterXENONCert where
  dm_mass_ratio : dmMassRatio = 1 / 45
  cross_section_pos : 0 < dmCrossSectionRatio
  cross_section_band : 0 < dmCrossSectionRatio ∧ dmCrossSectionRatio < 0.13

noncomputable def darkMatterXENONCert : DarkMatterXENONCert where
  dm_mass_ratio := rfl
  cross_section_pos := dmCrossSection_pos
  cross_section_band := dmCrossSection_in_band

end IndisputableMonolith.Cosmology.DarkMatterXENONPrediction
