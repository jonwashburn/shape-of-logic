import Mathlib
import IndisputableMonolith.Patterns

namespace IndisputableMonolith
namespace URCAdapters

/-- Eight‑beat existence (period exactly 8). -/
def eightbeat_prop : Prop := ∃ w : IndisputableMonolith.Patterns.CompleteCover 3, w.period = 8

lemma eightbeat_holds : eightbeat_prop := by
  simpa using IndisputableMonolith.Patterns.period_exactly_8

end URCAdapters
end IndisputableMonolith
