import Mathlib
import IndisputableMonolith.Physics.PMNS.Types

namespace IndisputableMonolith.Physics.PMNS

open Complex

/-- **CONJECTURE (open)**: there exists a unitary PMNS matrix whose entry magnitudes
match the framework’s weight assignment.

This is *not* used for any of the hard‑falsifiable angle / mass‑splitting claims
in `IndisputableMonolith.Physics.MixingDerivation`. -/
def pmns_unitarity_exists : Prop :=
  ∃ U : Matrix (Fin 3) (Fin 3) ℂ, PMNSUnitarity U

end IndisputableMonolith.Physics.PMNS
