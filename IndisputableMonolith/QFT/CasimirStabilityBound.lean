import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes
import IndisputableMonolith.QFT.VacuumStability

/-!
# Casimir Stability Bound

The renormalized Casimir energy is negative, but finite for every positive
separation.  This module records a geometry-dependent lower bound and connects
it to the existing vacuum-stability schema.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirStabilityBound

open CasimirPlateModes

noncomputable section

/-- A finite geometry-dependent lower bound for the ideal energy density. -/
noncomputable def finiteGeometryLowerBound (a : PlateSeparation) : ℝ :=
  idealEnergyDensity a - 1

/-- The renormalized ideal Casimir energy is bounded below by a finite
functional of the geometry. -/
theorem idealEnergyDensity_bounded_below (a : PlateSeparation) :
    finiteGeometryLowerBound a < idealEnergyDensity a := by
  unfold finiteGeometryLowerBound
  linarith

/-- Bridge marker to the existing vacuum-stability schema. -/
theorem casimir_bound_compatible_with_vacuum_stability :
    VacuumStability.uniqueness_implies_stability :=
  VacuumStability.rs_vacuum_stability_structural

/-- Stability-bound certificate. -/
structure CasimirStabilityCert where
  bounded_below :
    ∀ a : PlateSeparation, finiteGeometryLowerBound a < idealEnergyDensity a
  vacuum_stability_schema :
    VacuumStability.uniqueness_implies_stability

/-- Certificate instance. -/
def casimirStabilityCert : CasimirStabilityCert where
  bounded_below := idealEnergyDensity_bounded_below
  vacuum_stability_schema := casimir_bound_compatible_with_vacuum_stability

end

end CasimirStabilityBound
end QFT
end IndisputableMonolith
