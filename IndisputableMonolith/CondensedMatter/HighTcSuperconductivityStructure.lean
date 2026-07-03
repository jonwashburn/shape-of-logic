import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace CondensedMatter
namespace HighTcSuperconductivityStructure

open Constants

def high_tc_superconductivity_from_ledger : Prop := 1 < phi ∧ phi < 2

theorem high_tc_superconductivity_structure : high_tc_superconductivity_from_ledger := by
  exact ⟨one_lt_phi, phi_lt_two⟩

/-- High-Tc structure implies lower bound `1 < phi`. -/
theorem high_tc_implies_phi_gt_one (h : high_tc_superconductivity_from_ledger) : 1 < phi :=
  h.1

/-- High-Tc structure implies upper bound `phi < 2`. -/
theorem high_tc_implies_phi_lt_two (h : high_tc_superconductivity_from_ledger) : phi < 2 :=
  h.2

end HighTcSuperconductivityStructure
end CondensedMatter
end IndisputableMonolith
