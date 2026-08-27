import IndisputableMonolith.Foundation.HamiltonianCovering
import IndisputableMonolith.Foundation.CycleAsCircle
import IndisputableMonolith.Foundation.NoncontractibilityWeaker
import IndisputableMonolith.Foundation.IsotopyComplementHomology
import IndisputableMonolith.Foundation.HomologySphereAlgebra
import IndisputableMonolith.Foundation.SharpnessCountermodels
import IndisputableMonolith.Foundation.ArityCostFloors
import IndisputableMonolith.Foundation.ComplementClassRealization
import IndisputableMonolith.Foundation.LeastCostUnitLinking
import IndisputableMonolith.Foundation.SemanticClockFromMeasure

/-!
# D=3 paper residuals, barrel

Combinatorial, algebraic, and working-model halves of the remaining
claims in *Three Dimensions from a Recognition Requirement*. Poincaré
duality, general-`M` Alexander duality, and full C¹ straightening stay
as hypotheses or paper-only.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace D3PaperResiduals

export HamiltonianCovering (min_covering_walk_is_hamiltonian grayCycle3_is_simple)
export CycleAsCircle (hamiltonian_is_combinatorial_circle circle_embedding_of_injection)
export NoncontractibilityWeaker (noncontractibility_does_not_force_H1)
export IsotopyComplementHomology (complement_H1_homeomorph_invariant)
export HomologySphereAlgebra
  (homology_sphere_of_duality orientability_of_H1_zero codimension_of_alexander)
export SharpnessCountermodels (compactness_is_sharp acyclicity_is_sharp)
export ArityCostFloors (arityFourFloor_at_five arityFloor_exceeds_eight)
export ComplementClassRealization
  (every_integer_is_a_winding least_cost_forces_unit_charge forced_gray_clock)
export LeastCostUnitLinking (least_cost_unit_linking)
export SemanticClockFromMeasure (eightTick_implies_gray)

end D3PaperResiduals
end Foundation
end IndisputableMonolith
