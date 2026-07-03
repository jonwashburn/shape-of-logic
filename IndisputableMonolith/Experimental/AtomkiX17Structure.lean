import Mathlib
import IndisputableMonolith.Experimental.XenonExcessStructure

namespace IndisputableMonolith
namespace Experimental
namespace AtomkiX17Structure

open XenonExcessStructure

def atomki_x17_from_ledger : Prop := xenon_excess_from_ledger

theorem atomki_x17_structure : atomki_x17_from_ledger := xenon_excess_structure

/-- Atomki-X17 structure implies xenon-excess structural input. -/
theorem atomki_x17_implies_xenon (h : atomki_x17_from_ledger) :
    xenon_excess_from_ledger :=
  h

end AtomkiX17Structure
end Experimental
end IndisputableMonolith
