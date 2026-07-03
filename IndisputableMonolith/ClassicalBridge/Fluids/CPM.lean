import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

namespace IndisputableMonolith
namespace ClassicalBridge
namespace Fluids

/-!
# Fluids Bridge: CPM interface

The CPM core (`IndisputableMonolith/CPM/LawOfExistence.lean`) is domain-agnostic.
For Navier–Stokes we must *instantiate* it with:

- a state type (discrete NS state),
- concrete functionals (defectMass, orthoMass, energyGap, tests), and
- proofs of the required inequalities (A/B/C).

This file defines a minimal bundle to carry such an instantiation for later reuse.
-/

open IndisputableMonolith.CPM.LawOfExistence

/-- A CPM instantiation for a particular state type. -/
structure CPMBridge (State : Type) where
  /-- The fully packaged CPM model (includes the A/B/C inequality proofs). -/
  model : Model State
  /-- Human-readable interpretation notes (kept here for traceability). -/
  defectMeaning : String := ""
  energyMeaning  : String := ""
  testsMeaning   : String := ""

end Fluids
end ClassicalBridge
end IndisputableMonolith
