/-
  PrimitiveRecognitionCalculus/PRCShrunkCertificate.lean

  Cleanup item: the load-bearing δ certificate.

  The flagship credibility does not need the ~500-field open-targets object. The
  δ claim rests on four independently substantive proved statements. This module
  is the small conjunction that actually carries the program, each conjunct a
  headline theorem proved with no project-local axioms and no sorry:

    (A) ONE PRIMITIVE. The same/different judgment is derived from the act, not a
        second primitive (`OnePrimitive.comparison_is_derived_not_primitive`).

    (B) COST FORM, FREE UNIT. δ forces the cost form (a faithful one-parameter
        gauge family); the unit is the single residual free positive real; J is
        the curvature-1 member (`Calibration.calibration_unit_is_a_gauge`).

    (C) BELOW THE CONTINUUM. Every named RS constant lives in one countable
        subfield of ℝ that is a proper subset of the continuum
        (`MinimalField.rs_physics_below_continuum`).

    (D) CHAIN FED BY δ. The RS forcing chain's cost entry is the calibrated δ
        cost, and its φ output lives in the countable field
        (`ChainBridge.delta_cost_feeds_rs_chain`).

    (E) SCAFFOLD ON THE COUNTABLE CARRIER. The whole working machinery, every
        integer power of φ (the mass ladder) and the chain's integer outputs
        (eight-tick 8, dimension 3), are elements of the countable field
        (`MinimalField.rsField_phi_zpow`, `rsField_eight_tick`,
        `rsField_dimension`). The chain runs end to end below the continuum.

    (F) OPERATIONS BELOW THE CONTINUUM. One countable subfield of ℝ is closed
        under exactly the operations the constants are built from (field ops,
        exp, log) and already contains π, φ, e, and α⁻¹
        (`ExpLogField.rs_operations_below_continuum`). The construction, not just
        the answers, stays inside a countable field.

    (G) DISTINCTION IS NOT OPTIONAL. Any foundation with a reflexive expression
        order is either degenerate (distinguishes nothing, cannot do mathematics)
        or realizes the δ core (`DistinctionDichotomy.distinction_dichotomy`).
        Every foundation that can express a single non-trivial distinction
        contains δ.

  This is the certificate to cite for "what δ establishes". It is small enough to
  read in full (seven conjuncts) and every conjunct is load-bearing.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCOnePrimitive
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCMinimalField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCChainBridge
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCExpLogField
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCDistinctionDichotomy

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ShrunkCertificate

/-- The four load-bearing statements of the δ program, as one small object. -/
structure PRCShrunkCertificate : Prop where
  /-- (A) Recognition is one primitive: the comparison is derived from the act. -/
  one_primitive :
    ∀ (J : TraceJudgment),
      (∀ (T : Trace) (a b : Endpoint), J.diff T a b ↔ ¬ J.same T a b) →
      (∀ T : Trace, J.diff T Endpoint.left Endpoint.right) →
      ∀ (T : Trace) (a b : Endpoint),
        (J.same T a b ↔ a = b)
          ∧ (J.same T a b ↔ OnePrimitive.actJudgment.same T a b)
  /-- (B) The cost form is forced; the unit is a gauge; J is the curvature-1 member. -/
  cost_form_free_unit :
    (∀ c : ℝ, deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = c ^ 2)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d)
      ∧ (∀ c : ℝ, 0 < c →
          (deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = 1 ↔ c = 1))
  /-- (C) Every named RS constant lives in a countable field below the continuum. -/
  below_continuum :
    (MinimalField.rsField : Set ℝ).Countable
      ∧ Real.goldenRatio ∈ MinimalField.rsField
      ∧ Real.pi ∈ MinimalField.rsField
      ∧ Real.exp 1 ∈ MinimalField.rsField
      ∧ MinimalField.alphaInv ∈ MinimalField.rsField
      ∧ (MinimalField.rsField : Set ℝ) ≠ Set.univ
  /-- (D) The RS chain's cost entry is the calibrated δ cost; φ is in the field. -/
  chain_fed_by_delta :
    deriv (deriv (fun t => Cost.Jcost (Real.exp t))) 0 = 1
      ∧ Real.goldenRatio ∈ MinimalField.rsField
      ∧ (MinimalField.rsField : Set ℝ).Countable
  /-- (E) The whole RS scaffold (φ-ladder, eight-tick, dimension) lives in the
  countable field; the chain runs end to end on a countable carrier. -/
  scaffold_in_field :
    (∀ n : ℤ, Real.goldenRatio ^ n ∈ MinimalField.rsField)
      ∧ (8 : ℝ) ∈ MinimalField.rsField
      ∧ (3 : ℝ) ∈ MinimalField.rsField
  /-- (F) The deep half of Item 1: there is one countable subfield of ℝ closed
  under exactly the operations the constants are built from (field ops, exp, log)
  that already contains π, φ, e, and α⁻¹. The construction, not just the outputs,
  stays below the continuum. -/
  operations_below_continuum :
    ∃ K : Subfield ℝ,
      (K : Set ℝ).Countable
        ∧ (∀ x ∈ K, Real.exp x ∈ K)
        ∧ (∀ x ∈ K, Real.log x ∈ K)
        ∧ Real.pi ∈ K
        ∧ Real.goldenRatio ∈ K
        ∧ Real.exp 1 ∈ K
        ∧ MinimalField.alphaInv ∈ K
        ∧ (K : Set ℝ) ≠ Set.univ
  /-- (G) Item 4 as a classification: every foundation with a reflexive expression
  order is either degenerate (distinguishes nothing) or realizes δ. -/
  distinction_not_optional :
    ∀ F : FormalSystem, DistinctionDichotomy.ExprReflexive F →
      DistinctionDichotomy.Degenerate F ∨ DistinctionDichotomy.RealizesDelta F

/-- **The δ program certificate holds.** Seven proved headlines, no axioms, no
sorry. -/
theorem prc_shrunk_certificate : PRCShrunkCertificate where
  one_primitive := OnePrimitive.comparison_is_derived_not_primitive
  cost_form_free_unit := Calibration.calibration_unit_is_a_gauge
  below_continuum := MinimalField.rs_physics_below_continuum
  chain_fed_by_delta := ChainBridge.delta_cost_feeds_rs_chain
  scaffold_in_field :=
    ⟨MinimalField.rsField_phi_zpow, MinimalField.rsField_eight_tick,
      MinimalField.rsField_dimension⟩
  operations_below_continuum := ExpLogField.rs_operations_below_continuum
  distinction_not_optional := DistinctionDichotomy.distinction_dichotomy

end ShrunkCertificate
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
