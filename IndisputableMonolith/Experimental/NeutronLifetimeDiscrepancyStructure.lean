import Mathlib
import IndisputableMonolith.Nuclear.NeutronLifetimeStructure

namespace IndisputableMonolith
namespace Experimental
namespace NeutronLifetimeDiscrepancyStructure

open Nuclear.NeutronLifetimeStructure

theorem has_neutron_lifetime_input : neutron_lifetime_from_ledger :=
  neutron_lifetime_structure

def neutron_lifetime_discrepancy_from_ledger : Prop := neutron_lifetime_from_ledger

theorem neutron_lifetime_discrepancy_structure :
    neutron_lifetime_discrepancy_from_ledger := has_neutron_lifetime_input

/-- Neutron-lifetime-discrepancy structure implies neutron-lifetime input. -/
theorem neutron_discrepancy_implies_lifetime_input
    (h : neutron_lifetime_discrepancy_from_ledger) :
    neutron_lifetime_from_ledger :=
  h

end NeutronLifetimeDiscrepancyStructure
end Experimental
end IndisputableMonolith
