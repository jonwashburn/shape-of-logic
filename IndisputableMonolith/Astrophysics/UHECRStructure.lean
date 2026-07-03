import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Astrophysics
namespace UHECRStructure

open Constants

def uhecr_from_ledger : Prop := 0 < phi

theorem uhecr_structure : uhecr_from_ledger := phi_pos

/-- UHECR structure implies positivity of `phi`. -/
theorem uhecr_implies_phi_pos (h : uhecr_from_ledger) : 0 < phi :=
  h

end UHECRStructure
end Astrophysics
end IndisputableMonolith
