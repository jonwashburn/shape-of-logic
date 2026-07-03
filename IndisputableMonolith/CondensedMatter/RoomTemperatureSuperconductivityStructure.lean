import Mathlib
import IndisputableMonolith.CondensedMatter.HighTcSuperconductivityStructure

namespace IndisputableMonolith
namespace CondensedMatter
namespace RoomTemperatureSuperconductivityStructure

open HighTcSuperconductivityStructure

theorem has_high_tc_structure : high_tc_superconductivity_from_ledger :=
  high_tc_superconductivity_structure

def room_temperature_superconductivity_from_ledger : Prop :=
  high_tc_superconductivity_from_ledger

theorem room_temperature_superconductivity_structure :
    room_temperature_superconductivity_from_ledger := has_high_tc_structure

/-- Room-temperature-SC structure implies High-Tc structural input. -/
theorem room_temperature_implies_high_tc (h : room_temperature_superconductivity_from_ledger) :
    high_tc_superconductivity_from_ledger :=
  h

end RoomTemperatureSuperconductivityStructure
end CondensedMatter
end IndisputableMonolith
