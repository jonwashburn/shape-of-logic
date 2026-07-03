import Mathlib
import IndisputableMonolith.CondensedMatter.GlassTransitionStructure

namespace IndisputableMonolith
namespace CondensedMatter
namespace StronglyCorrelatedElectronsStructure

open GlassTransitionStructure

def strongly_correlated_electrons_from_ledger : Prop := glass_transition_from_ledger

theorem strongly_correlated_electrons_structure :
    strongly_correlated_electrons_from_ledger := glass_transition_structure

/-- Strong-correlation structure implies glass-transition structural input. -/
theorem strongly_correlated_implies_glass (h : strongly_correlated_electrons_from_ledger) :
    glass_transition_from_ledger :=
  h

end StronglyCorrelatedElectronsStructure
end CondensedMatter
end IndisputableMonolith
