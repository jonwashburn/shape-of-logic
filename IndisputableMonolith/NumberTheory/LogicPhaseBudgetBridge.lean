import Mathlib
import IndisputableMonolith.NumberTheory.PhaseBudgetToErdosStraus
import IndisputableMonolith.NumberTheory.LogicErdosStrausBoxPhase

/-!
  LogicPhaseBudgetBridge.lean

  Logic-native wrapper for the Erdős-Straus phase-budget engine.

  The existing phase-budget engine remains the computational bridge. This
  module packages it behind recovered-natural inputs and proves that the
  final residual theorem can be read as a recovered-rational theorem.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicPhaseBudgetBridge

open Foundation.ArithmeticFromLogic
open Foundation.ArithmeticFromLogic.LogicNat
open Foundation.RationalsFromLogic.LogicRat
open LogicErdosStrausRCL

/-- Logic-native phase-budget engine. The bound and input carrier are
`LogicNat`; the actual finite gate witness is transported to the existing
classical engine surface. -/
structure PhaseBudgetEngineLogic where
  bound : LogicNat → LogicNat
  classical_engine : PhaseBudgetToErdosStraus.PhaseBudgetEngine
  bound_compat : ∀ n : LogicNat, toNat (bound n) = classical_engine.bound (toNat n)

/-- Forget the logic-native wrapper to the current classical phase-budget
engine. -/
def toClassicalEngine (engine : PhaseBudgetEngineLogic) :
    PhaseBudgetToErdosStraus.PhaseBudgetEngine :=
  engine.classical_engine

/-- The phase-budget engine solves residual traps in the recovered rational
reading. -/
theorem erdos_straus_residual_from_phaseBudget_logic
    (engine : PhaseBudgetEngineLogic)
    {n : LogicNat}
    (hn : ErdosStrausRotationHierarchy.ResidualTrap (toNat n)) :
    HasRationalErdosStrausReprLogic (fromRat (toNat n : ℚ)) := by
  apply reprLogic_fromRat_of_classical
  exact PhaseBudgetToErdosStraus.erdos_straus_residual_from_phaseBudget
    engine.classical_engine hn

end LogicPhaseBudgetBridge
end NumberTheory
end IndisputableMonolith
