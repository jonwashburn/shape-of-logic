import Mathlib
import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Foundation.PhiForcing

namespace IndisputableMonolith
namespace Foundation
namespace HierarchyMinimality

open PhiForcingDerived
open PhiForcing

/-!
# Hierarchy Minimality

This module isolates the minimal algebraic hierarchy data needed for the B1
closure step: a discrete geometric ledger together with the smallest closure
condition `scale 0 + scale 1 = scale 2`.
-/

/-- Minimal discrete hierarchy: a geometric scale ladder closed under the first
    non-trivial composition step. -/
structure MinimalHierarchy where
  scales : GeometricScaleSequence
  minimalClosure : scales.isClosed

/-- The first closure step is exactly the Fibonacci relation. -/
theorem hierarchy_forces_golden_equation (H : MinimalHierarchy) :
    H.scales.ratio ^ 2 = H.scales.ratio + 1 :=
  closure_forces_golden_equation H.scales H.minimalClosure

/-- Minimal closure already forces the unique positive self-similar ratio `φ`. -/
theorem hierarchy_forces_phi (H : MinimalHierarchy) :
    H.scales.ratio = φ :=
  closed_ratio_is_phi H.scales H.minimalClosure

end HierarchyMinimality
end Foundation
end IndisputableMonolith
