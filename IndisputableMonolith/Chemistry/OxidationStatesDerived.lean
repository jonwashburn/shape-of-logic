import Mathlib
import IndisputableMonolith.Chemistry.OxidationStateFromConfigDim

/-!
# Derived Oxidation-State Targets

This module is Phase 8B of the periodic-table closure plan.

The existing `OxidationStateFromConfigDim` module proves the count-law spine.
This file installs the chemistry-facing target table for accessible oxidation
states, starting with the acceptance cases in the plan: Fe and Mn.

The definitions are still target-level for the selected elements. The next
theorem must derive these lists from valence occupation plus J-cost removal.
-/

namespace IndisputableMonolith.Chemistry.OxidationStatesDerived

open IndisputableMonolith.Chemistry

/-- Target accessible oxidation states for selected elements. -/
def accessibleOxidationStates (Z : Nat) : List Int :=
  if Z = 26 then [0, 2, 3, 6]
  else if Z = 25 then [-1, 0, 2, 3, 4, 6, 7]
  else []

/-- Iron's accessible oxidation states in the Phase 8 target table. -/
theorem iron_oxidation_states :
    accessibleOxidationStates 26 = [0, 2, 3, 6] := by
  native_decide

/-- Manganese reaches +7. -/
theorem manganese_max_seven :
    (7 : Int) ∈ accessibleOxidationStates 25 := by
  native_decide

/-- The manganese target list has the canonical seven common states. -/
theorem manganese_state_count :
    (accessibleOxidationStates 25).length = 7 := by
  native_decide

/-- Iron's target list has no duplicate oxidation states. -/
theorem iron_oxidation_states_nodup :
    (accessibleOxidationStates 26).Nodup := by
  native_decide

/-- Manganese's target list has no duplicate oxidation states. -/
theorem manganese_oxidation_states_nodup :
    (accessibleOxidationStates 25).Nodup := by
  native_decide

/-- The count-law oxidation certificate remains available. -/
theorem oxidation_count_law_available :
    Nonempty OxidationStateFromConfigDim.OxidationStateCert :=
  OxidationStateFromConfigDim.cert_inhabited

/-- Phase 8B certificate: oxidation-state targets are installed. -/
structure OxidationStatesDerivedCert : Prop where
  iron_exact : accessibleOxidationStates 26 = [0, 2, 3, 6]
  manganese_reaches_seven : (7 : Int) ∈ accessibleOxidationStates 25
  manganese_count : (accessibleOxidationStates 25).length = 7
  iron_nodup : (accessibleOxidationStates 26).Nodup
  manganese_nodup : (accessibleOxidationStates 25).Nodup
  count_law : Nonempty OxidationStateFromConfigDim.OxidationStateCert

/-- The Phase 8B oxidation-state target layer is certified. -/
theorem oxidation_states_derived_certified :
    OxidationStatesDerivedCert where
  iron_exact := iron_oxidation_states
  manganese_reaches_seven := manganese_max_seven
  manganese_count := manganese_state_count
  iron_nodup := iron_oxidation_states_nodup
  manganese_nodup := manganese_oxidation_states_nodup
  count_law := oxidation_count_law_available

end IndisputableMonolith.Chemistry.OxidationStatesDerived
