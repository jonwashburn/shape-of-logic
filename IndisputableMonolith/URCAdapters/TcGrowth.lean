import Mathlib
import IndisputableMonolith.RecogSpec.Scales

namespace IndisputableMonolith
namespace URCAdapters

/-! Simple computation growth interface wired to a concrete monotonicity lemma on PhiPow.
    We export a Prop that holds because PhiPow is strictly increasing when φ>1. -/
def tc_growth_prop : Prop :=
  ∀ x y : ℝ, x ≤ y → IndisputableMonolith.RecogSpec.PhiPow x ≤ IndisputableMonolith.RecogSpec.PhiPow y

lemma tc_growth_holds : tc_growth_prop := by
  intro x y hxy
  -- PhiPow(x) = exp(log φ * x); since log φ > 0, it is monotone.
  have hφpos : 0 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.phi_pos
  have hlogpos : 0 < Real.log (IndisputableMonolith.Constants.phi) := by
    have hx : 0 ≤ IndisputableMonolith.Constants.phi := le_of_lt hφpos
    have hx1 : 1 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.one_lt_phi
    exact (Real.log_pos_iff hx).2 hx1
  dsimp [IndisputableMonolith.RecogSpec.PhiPow]
  -- Use monotonicity of exp and multiplication by positive scalar
  have : Real.log (IndisputableMonolith.Constants.phi) * x ≤ Real.log (IndisputableMonolith.Constants.phi) * y :=
    by exact mul_le_mul_of_nonneg_left hxy (le_of_lt hlogpos)
  exact (Real.exp_le_exp.mpr this)

end URCAdapters
end IndisputableMonolith
