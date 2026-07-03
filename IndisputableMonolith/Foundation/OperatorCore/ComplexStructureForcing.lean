import IndisputableMonolith.Foundation.ComplexStructureForcing

namespace IndisputableMonolith
namespace Foundation
namespace OperatorCore

noncomputable section

/-- Authoritative IM alias for the 8-tick complex carrier. -/
abbrev Signal8 := IndisputableMonolith.Foundation.ComplexStructureForcing.Signal8

abbrev nextIdx := IndisputableMonolith.Foundation.ComplexStructureForcing.nextIdx
abbrev shift := IndisputableMonolith.Foundation.ComplexStructureForcing.shift
abbrev shiftIter := IndisputableMonolith.Foundation.ComplexStructureForcing.shiftIter
abbrev ζ := IndisputableMonolith.Foundation.ComplexStructureForcing.ζ
abbrev eigenvalue := IndisputableMonolith.Foundation.ComplexStructureForcing.eigenvalue
abbrev dft8 := IndisputableMonolith.Foundation.ComplexStructureForcing.dft8
abbrev idft8 := IndisputableMonolith.Foundation.ComplexStructureForcing.idft8
abbrev inner8 := IndisputableMonolith.Foundation.ComplexStructureForcing.inner8
abbrev JcostC := IndisputableMonolith.Foundation.ComplexStructureForcing.JcostC
abbrev totalModeCost := IndisputableMonolith.Foundation.ComplexStructureForcing.totalModeCost
abbrev UnitaryEvolution := IndisputableMonolith.Foundation.ComplexStructureForcing.UnitaryEvolution

abbrev shift_period_8 := IndisputableMonolith.Foundation.ComplexStructureForcing.shift_period_8
abbrev complexification_forced := IndisputableMonolith.Foundation.ComplexStructureForcing.complexification_forced
abbrev dft8_preserves_inner := IndisputableMonolith.Foundation.ComplexStructureForcing.dft8_preserves_inner
abbrev jcost_phase_invariant := IndisputableMonolith.Foundation.ComplexStructureForcing.jcost_phase_invariant
abbrev mode_cost_phase_invariant := IndisputableMonolith.Foundation.ComplexStructureForcing.mode_cost_phase_invariant
abbrev cost_phase_duality := IndisputableMonolith.Foundation.ComplexStructureForcing.cost_phase_duality

end

end OperatorCore
end Foundation
end IndisputableMonolith
