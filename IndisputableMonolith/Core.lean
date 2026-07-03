import Mathlib
import IndisputableMonolith.Core.ConstantsAndPatterns
import IndisputableMonolith.Core.Streams
import IndisputableMonolith.Core.RS
import IndisputableMonolith.Core.Complexity
import IndisputableMonolith.Core.URC
import IndisputableMonolith.Core.Recognition
-- import IndisputableMonolith.Ethics.Invariants -- This import is no longer needed as Invariants are moved to RecogSpec.Core

namespace IndisputableMonolith
/-! ### Core umbrella: imports stable submodules only. -/
-- Ethics invariants are defined in their dedicated modules; do not re-declare stubs here.

/-! #### Compatibility aliases kept minimal -/
abbrev Pattern (d : Nat) := Patterns.Pattern d
abbrev CompleteCover := Patterns.CompleteCover

end IndisputableMonolith
