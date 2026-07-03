import Mathlib
import IndisputableMonolith.Experimental.GalliumAnomalyStructure

namespace IndisputableMonolith
namespace Experimental
namespace ANITAUpgoingStructure

open GalliumAnomalyStructure

def anita_upgoing_from_ledger : Prop := gallium_anomaly_from_ledger

theorem anita_upgoing_structure : anita_upgoing_from_ledger := gallium_anomaly_structure

/-- ANITA-upgoing structure implies gallium-anomaly structural input. -/
theorem anita_implies_gallium (h : anita_upgoing_from_ledger) :
    gallium_anomaly_from_ledger :=
  h

end ANITAUpgoingStructure
end Experimental
end IndisputableMonolith
