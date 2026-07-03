import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace URCAdapters

/-! EL stationarity and minimality on the log axis (extracted).
    Re-expose the minimal Prop and witness using the central `Cost` module. -/

noncomputable section

def EL_prop : Prop :=
  (deriv Cost.Jlog 0 = 0) ∧ (∀ t : ℝ, Cost.Jlog 0 ≤ Cost.Jlog t)

lemma EL_holds : EL_prop := by
  exact ⟨Cost.EL_stationary_at_zero, Cost.EL_global_min⟩

end

end URCAdapters
end IndisputableMonolith
