import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Uniform Failure Floor

Defines the RS floor scale used in the phase-budget engine:

`KTheta = J(φ) / 45`.

This file proves only positivity.  The claim that every failed finite phase
gate costs at least `KTheta` is kept as a separate explicit interface in
`BoundedPhaseVisibility`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace UniformFailureFloor

open Constants Cost

/-- The RS phase-failure floor scale. -/
noncomputable def KTheta : ℝ := Jcost phi / 45

theorem Jcost_phi_pos : 0 < Jcost phi :=
  Jcost_pos_of_ne_one phi phi_pos phi_ne_one

theorem KTheta_pos : 0 < KTheta := by
  unfold KTheta
  exact div_pos Jcost_phi_pos (by norm_num : (0 : ℝ) < 45)

theorem KTheta_nonneg : 0 ≤ KTheta := le_of_lt KTheta_pos

end UniformFailureFloor
end NumberTheory
end IndisputableMonolith
