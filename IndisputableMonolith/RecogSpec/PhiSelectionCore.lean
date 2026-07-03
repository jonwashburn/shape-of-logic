import Mathlib

namespace IndisputableMonolith
namespace RecogSpec

/-- φ selection criterion: φ² = φ + 1 and φ > 0. -/
def PhiSelection (φ : ℝ) : Prop :=
  φ ^ 2 = φ + 1 ∧ φ > 0

end RecogSpec
end IndisputableMonolith
