import IndisputableMonolith.Unification.UnifiedRH

/-!
# T1 Boundary Exclusion

Extracts the proved theorem that a T1-bounded physically realizable ledger
cannot approach the non-existence boundary `x = 0`.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Unification.UnifiedRH

/-- A physically realizable ledger cannot approach the T1 boundary. -/
theorem realizable_not_boundary_approaching
    (sensor : DefectSensor) [PhysicallyRealizableLedger sensor] :
    ¬ BoundaryApproaching sensor :=
  physicallyRealizableLedger_not_boundaryApproaching sensor

/-- Certificate for the T1 boundary exclusion theorem. -/
structure T1BoundaryExclusionCert where
  no_boundary :
    ∀ sensor : DefectSensor, [PhysicallyRealizableLedger sensor] →
      ¬ BoundaryApproaching sensor

/-- The proved T1 boundary exclusion certificate. -/
def t1BoundaryExclusionCert : T1BoundaryExclusionCert where
  no_boundary := fun sensor => by
    intro
    exact realizable_not_boundary_approaching sensor

end NumberTheory
end IndisputableMonolith
