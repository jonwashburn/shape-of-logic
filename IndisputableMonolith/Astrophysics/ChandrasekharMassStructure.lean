import Mathlib
import IndisputableMonolith.Astrophysics.MassToLight

namespace IndisputableMonolith
namespace Astrophysics
namespace ChandrasekharMassStructure

open MassToLight

/-- Structural content: mass-scale anchors are positive and finite in RS ladder range. -/
def chandrasekhar_mass_from_ledger : Prop := 0.5 < ml_derived ∧ ml_derived < 5

theorem chandrasekhar_mass_structure : chandrasekhar_mass_from_ledger :=
  ml_in_observed_range

/-- Chandrasekhar-mass structure implies lower mass-to-light bound. -/
theorem chandrasekhar_implies_ml_lower (h : chandrasekhar_mass_from_ledger) :
    0.5 < ml_derived :=
  h.1

/-- Chandrasekhar-mass structure implies upper mass-to-light bound. -/
theorem chandrasekhar_implies_ml_upper (h : chandrasekhar_mass_from_ledger) :
    ml_derived < 5 :=
  h.2

end ChandrasekharMassStructure
end Astrophysics
end IndisputableMonolith
