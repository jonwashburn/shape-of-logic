import Mathlib
import IndisputableMonolith.CondensedMatter.StronglyCorrelatedElectronsStructure

namespace IndisputableMonolith
namespace CondensedMatter
namespace TopologicalPhasesStructure

open StronglyCorrelatedElectronsStructure

def topological_phases_from_ledger : Prop := strongly_correlated_electrons_from_ledger

theorem topological_phases_structure : topological_phases_from_ledger :=
  strongly_correlated_electrons_structure

/-- Topological-phase structure implies strongly-correlated-electron input. -/
theorem topological_phases_implies_strongly_correlated (h : topological_phases_from_ledger) :
    strongly_correlated_electrons_from_ledger :=
  h

end TopologicalPhasesStructure
end CondensedMatter
end IndisputableMonolith
