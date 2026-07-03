import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Support

open Constants

/-- phi^(0:ℤ) = 1 as a convenience lemma for integer powers of φ. -/
lemma phi_zpow_zero : phi ^ (0 : ℤ) = (1 : ℝ) := by
  simpa using (zpow_zero (phi : ℝ))

end Support
end IndisputableMonolith









