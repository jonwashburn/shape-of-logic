import Mathlib
import IndisputableMonolith.Verification.CPMBridge.Domain.NavierStokesPinch
import IndisputableMonolith.Verification.Dimension

/-!
# NavierStokesPinch Dimension Bridge

This bridge is intentionally separate from the topological-frustration bridge.
It uses the `Cost`-based verification path (`Verification.Dimension`) and can
be imported independently without mixing cost kernels.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge
namespace Domain
namespace NavierStokesPinch
namespace DimensionBridge

/-- Dimension-rigidity bridge used by the Alexander-duality veto interface. -/
theorem dimension_three_from_gap45_sync {D : ℕ}
    (h : IndisputableMonolith.Verification.Dimension.RSCounting_Gap45_Absolute D) :
    D = 3 := by
  exact IndisputableMonolith.Verification.Dimension.onlyD3_satisfies_RSCounting_Gap45_Absolute h

end DimensionBridge
end NavierStokesPinch
end Domain
end CPMBridge
end Verification
end IndisputableMonolith
