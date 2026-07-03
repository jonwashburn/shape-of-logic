import Mathlib
import IndisputableMonolith.NavierStokes.DiscreteNSOperator

/-!
# J-cost Monotonicity for the Concrete Lattice NS Operator

This module closes the bookkeeping part of the monotonicity program against a
concrete discrete incompressible Navier--Stokes operator surface:

1. transport cancellation is derived from conservative incompressible flux;
2. the stretching term is bounded by the operator's own RCL pair budget;
3. viscosity absorbs that operator-derived budget;
4. therefore the total J-cost derivative is nonpositive.

What remains open is no longer the existence of a good certificate object.  The
remaining PDE question is to verify, for the real lattice flow, the operator
inequalities packaged in `DiscreteNSOperator.IncompressibleNSOperator`.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace JcostMonotonicity

open DiscreteVorticity
open StretchingPairs
open DiscreteNSOperator

noncomputable section

/-- The actual lattice stretching contribution is absorbed by the operator's
viscous budget once the sitewise RCL pair bounds are summed. -/
theorem stretching_absorbed_by_viscosity {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    totalStretching ns.contributions ≤ - totalViscous ns.contributions := by
  exact le_trans (totalStretching_le_operatorPairBudget ns)
    (operatorPairBudget_absorbed_by_viscosity ns)

/-- The concrete discrete NS operator has nonincreasing total J-cost once its
pair budget is absorbed by viscosity. -/
theorem dJcost_dt_nonpos_of_operator {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) :
    ns.dJdt ≤ 0 :=
  dJdt_nonpos_of_transport_cancel_and_absorption ns.toEvolutionIdentity
    (operator_transport_zero ns) (stretching_absorbed_by_viscosity ns)

/-- Packaged monotonicity certificate for the concrete lattice operator. -/
structure MonotonicityCert (siteCount : ℕ) where
  operator : IncompressibleNSOperator siteCount
  nonpositive_derivative : operator.dJdt ≤ 0

/-- Any concrete lattice NS operator yields a monotonicity certificate once its
operator-derived pair budget is absorbed by viscosity. -/
def monotonicityCert {siteCount : ℕ}
    (ns : IncompressibleNSOperator siteCount) : MonotonicityCert siteCount where
  operator := ns
  nonpositive_derivative := dJcost_dt_nonpos_of_operator ns

end

end JcostMonotonicity
end NavierStokes
end IndisputableMonolith
