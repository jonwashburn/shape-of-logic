import Mathlib
import IndisputableMonolith.NumberTheory.PhaseBudgetEngineFromRS

/-!
# Erdős-Straus Residual Closure

Final residual theorem, conditional on the recovered-ledger bounded visibility
engine.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ErdosStrausResidualClosed

open ErdosStrausRotationHierarchy
open BoundedPhaseVisibility
open PhaseBudgetEngineFromRS

/-- Conditional residual closure: once bounded phase visibility is supplied
for recovered integer ledgers, every residual trapped `n` has an
Erdős-Straus representation. -/
theorem erdos_straus_residual_closed
    (engine : BoundedVisibilityEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  PhaseBudgetToErdosStraus.erdos_straus_residual_from_phaseBudget
    (phaseBudgetEngine_of_boundedVisibilityEngine engine) hn

end ErdosStrausResidualClosed
end NumberTheory
end IndisputableMonolith
