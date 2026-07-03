import Mathlib
import IndisputableMonolith.Astrophysics.StellarIMFStructure

namespace IndisputableMonolith
namespace Astrophysics
namespace SupernovaMechanismStructure

open StellarIMFStructure

def supernova_mechanism_from_ledger : Prop := stellar_imf_from_ledger

theorem supernova_mechanism_structure : supernova_mechanism_from_ledger := stellar_imf_structure

/-- Supernova-mechanism structure implies IMF-side structural input. -/
theorem supernova_implies_stellar_imf (h : supernova_mechanism_from_ledger) :
    stellar_imf_from_ledger :=
  h

end SupernovaMechanismStructure
end Astrophysics
end IndisputableMonolith
