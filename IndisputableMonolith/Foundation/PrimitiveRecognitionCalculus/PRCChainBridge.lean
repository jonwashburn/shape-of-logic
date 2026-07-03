/-
  PrimitiveRecognitionCalculus/PRCChainBridge.lean

  Item 3 of the δ frontier: the δ → RS-chain bridge.

  The RS forcing chain (T5 unique J → T6 φ → T7 eight-tick → T8 D = 3 → the
  constants) is anchored at the recognition cost `Cost.Jcost`. The δ framework
  forces the cost FORM (the `cosh(c·t) − 1` gauge family, `Calibration`) and
  pins the minimal countable field the constants live in (`MinimalField`). What
  was missing was the explicit weld: that the chain's cost entry IS the
  calibrated δ cost, and that the chain's first physical output (φ) lives inside
  the countable δ field rather than requiring the continuum.

  This module supplies that weld:

  * `jcost_log_eq_clog_one`:   `Cost.Jcost` in log coordinates is the c = 1
                               member of the δ-forced family.
  * `jcost_logCurvature_one`:  `Cost.Jcost` is calibrated (log-curvature 1 at the
                               unit), i.e. it is exactly the gauge-fixed δ cost.
  * `phi_in_minimal_field`:    the T6 output φ lies in the countable RS field.
  * `delta_cost_feeds_rs_chain`: the headline weld.

  HONEST SCOPING. The φ-forcing itself (every minimal self-similar hierarchy has
  base ratio φ) is `UnifiedForcingChain.minimalHierarchy_ratio_eq_phi`, and the
  two-sided assembly is `UniversalForcing.OneLaw.one_law_forces_arithmetic_and_phi`.
  This module does not re-prove those. It adds the two facts that turn the
  assembly into a wiring: (i) the chain's cost is the calibrated δ cost (not just
  "the same cost up to a constant c"), and (ii) the φ output is a countable-field
  element. The remaining rungs (eight-tick = 2³, D = 3, the transcendental
  constants) run downstream of φ on the same field; verifying each output value
  is itself a countable-field element is the natural continuation (the eight-tick
  and dimension outputs are integers, hence trivially in the field; the
  transcendental constants are covered by `MinimalField.rs_physics_below_continuum`).

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCMinimalField

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ChainBridge

/-- `Cost.Jcost` in log coordinates is the `c = 1` member of the δ-forced cost
family: `Jcost(eᵗ) = cosh(1·t) − 1`. -/
theorem jcost_log_eq_clog_one (t : ℝ) :
    Cost.Jcost (Real.exp t) = Real.cosh (1 * t) - 1 := by
  simp only [Cost.Jcost, one_mul, Real.cosh_eq, Real.exp_neg]

/-- The RS chain's cost entry is the *calibrated* δ cost: its log-curvature at the
unit is exactly 1. So `Cost.Jcost` is not merely a member of the δ-forced gauge
family; it is the gauge-fixed (unit = 1) member that `Calibration` singles out as
J. -/
theorem jcost_logCurvature_one :
    deriv (deriv (fun t => Cost.Jcost (Real.exp t))) 0 = 1 := by
  have hfun : (fun t => Cost.Jcost (Real.exp t))
      = (fun t => Real.cosh (1 * t) - 1) := by
    funext t; exact jcost_log_eq_clog_one t
  rw [hfun, Calibration.logCurvature 1]
  norm_num

/-- The T6 output φ is a countable-field element: it lives in the minimal RS
field, never requiring the uncountable continuum. -/
theorem phi_in_minimal_field : Real.goldenRatio ∈ MinimalField.rsField :=
  MinimalField.rsField_mem_phi

/-- **Item 3 headline (the weld).** The RS forcing chain's cost entry is the
calibrated δ cost, and the chain's first physical output φ lives in the countable
RS field, which is strictly below the continuum. The chain is therefore fed by the
δ cost and runs on a countable carrier at the J and φ rungs. -/
theorem delta_cost_feeds_rs_chain :
    deriv (deriv (fun t => Cost.Jcost (Real.exp t))) 0 = 1
      ∧ Real.goldenRatio ∈ MinimalField.rsField
      ∧ (MinimalField.rsField : Set ℝ).Countable :=
  ⟨jcost_logCurvature_one, phi_in_minimal_field, MinimalField.rsField_countable⟩

/-- **Item 3, sharpened: every chain output lands in the countable field.** The
calibrated δ cost feeds the chain, and each of the chain's named outputs, the base
ratio φ (T6), the eight-tick cadence 8 = 2³ (T7), and the spatial dimension 3
(T8), is an element of the countable RS field. The forcing chain runs end to end on
a countable carrier; the continuum is never the home of any rung. -/
theorem rs_chain_all_rungs_in_field :
    deriv (deriv (fun t => Cost.Jcost (Real.exp t))) 0 = 1
      ∧ Real.goldenRatio ∈ MinimalField.rsField
      ∧ (8 : ℝ) ∈ MinimalField.rsField
      ∧ (3 : ℝ) ∈ MinimalField.rsField
      ∧ (MinimalField.rsField : Set ℝ).Countable :=
  ⟨jcost_logCurvature_one, phi_in_minimal_field,
    MinimalField.rsField_eight_tick, MinimalField.rsField_dimension,
    MinimalField.rsField_countable⟩

end ChainBridge
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
