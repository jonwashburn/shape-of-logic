import Mathlib
import IndisputableMonolith.Experimental.AtomkiX17Structure

namespace IndisputableMonolith
namespace Experimental
namespace FlybyAnomalyStructure

open AtomkiX17Structure

def flyby_anomaly_from_ledger : Prop := atomki_x17_from_ledger

theorem flyby_anomaly_structure : flyby_anomaly_from_ledger := atomki_x17_structure

/-- Flyby-anomaly structure implies Atomki-X17 structural input. -/
theorem flyby_implies_atomki_x17 (h : flyby_anomaly_from_ledger) :
    atomki_x17_from_ledger :=
  h

end FlybyAnomalyStructure
end Experimental
end IndisputableMonolith
