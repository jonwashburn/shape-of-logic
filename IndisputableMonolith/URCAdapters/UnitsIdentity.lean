import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace URCAdapters

/-- Units identity as a Prop: c·τ0 = ℓ0 for all anchors. -/
def units_identity_prop : Prop :=
  ∀ U : IndisputableMonolith.Constants.RSUnits, U.c * U.tau0 = U.ell0

lemma units_identity_holds : units_identity_prop := by
  intro U; simpa using U.c_ell0_tau0

end URCAdapters
end IndisputableMonolith
