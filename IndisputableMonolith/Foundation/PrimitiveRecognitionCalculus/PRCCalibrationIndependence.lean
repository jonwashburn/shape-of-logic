/-
  PrimitiveRecognitionCalculus/PRCCalibrationIndependence.lean

  Item 2, the negative direction, proved (not just asserted in prose).

  `PRCCalibrationTarget.lean` established the POSITIVE structure of the residual
  calibration freedom: the δ-forced cost form is a faithful one-parameter family,
  its only invariant is the log-curvature `c²` at the unit, and "curvature = 1"
  picks out `J`. From that it CLAIMED, in prose, that the unit `c` is a gauge --
  "not a δ-forced constant" -- because curvature is a continuum-side
  second-derivative datum the discrete carrier does not supply.

  That claim was never a theorem. This module proves it, as the exact analogue of
  `PRCCompletenessIndependence.completeness_not_forced_by_genuine_cost_laws`:

  The multiplicative gauge family

      costLambda c x = ½(x^c + x^{−c}) − 1      (real exponent, x > 0)

  satisfies, for EVERY positive `c`, the genuine recognition cost laws recorded in
  `Cost.CostRequirements` (reciprocal symmetry `F x = F x⁻¹` and the unit law
  `F 1 = 0`), and each member is moreover continuous on `(0,∞)`. The family is
  faithful (`costLambda_inj`): distinct positive `c` give genuinely distinct cost
  functions. The `c = 1` member is exactly `Cost.Jcost`.

  Consequence (`calibration_unit_not_forced_by_cost_laws`): two distinct functions
  (`costLambda 1 = J` and `costLambda 2`) both satisfy `Cost.CostRequirements`, so
  those laws do NOT entail `c = 1`. The unit of scale is logically independent of
  the cost laws; it is fixed only by the extra calibration hypothesis (leading
  log-curvature normalized to 1) carried by the upstream uniqueness theorem
  `Cost.FunctionalEquation.law_of_logic_forces_jcost`. Drop that one hypothesis and
  the whole family is admissible. So "δ forces the cost FORM" does not upgrade to
  "δ forces J": the unit is the one irreducible gauge choice.

  This is the credibility-gating form. A skeptic cannot say the independence rests
  on a weak premise: every member is a bona fide recognition cost (symmetric, unit
  law, continuous), differing only in the unforced unit.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationTarget

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Calibration

/-- The δ-forced cost gauge family in multiplicative coordinates:
`costLambda c x = ½(x^c + x^{−c}) − 1`, with the real exponent taken via
`Real.rpow`. The `c = 1` member is `J`. -/
noncomputable def costLambda (c x : ℝ) : ℝ := (x ^ c + x ^ (-c)) / 2 - 1

/-- On the positive reals the multiplicative form coincides with the additive
(log-coordinate) form `cosh(c·log x) − 1` used in `PRCCalibrationTarget`. -/
theorem costLambda_eq_cosh (c : ℝ) {x : ℝ} (hx : 0 < x) :
    costLambda c x = Real.cosh (c * Real.log x) - 1 := by
  have h1 : x ^ c = Real.exp (c * Real.log x) := by
    rw [Real.rpow_def_of_pos hx c, mul_comm]
  have h2 : x ^ (-c) = Real.exp (-(c * Real.log x)) := by
    rw [Real.rpow_def_of_pos hx (-c)]
    congr 1
    ring
  unfold costLambda
  rw [h1, h2, Real.cosh_eq]

/-- The unit law `F(1) = 0` holds for every member. -/
theorem costLambda_unit0 (c : ℝ) : costLambda c 1 = 0 := by
  rw [costLambda_eq_cosh c one_pos, Real.log_one, mul_zero, Real.cosh_zero]
  norm_num

/-- Reciprocal symmetry `F x = F x⁻¹` holds for every member on the positives. -/
theorem costLambda_symm (c : ℝ) {x : ℝ} (hx : 0 < x) :
    costLambda c x = costLambda c x⁻¹ := by
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
  rw [costLambda_eq_cosh c hx, costLambda_eq_cosh c hxinv, Real.log_inv, mul_neg,
    Real.cosh_neg]

/-- **Every gauge member is a bona fide recognition cost.** For every positive
`c`, `costLambda c` satisfies `Cost.CostRequirements` (the same structure
`PRCCompletenessIndependence.jcost_isCostRequirements` verifies for `J`). -/
theorem costLambda_isCostRequirements (c : ℝ) :
    Cost.CostRequirements (fun x => costLambda c x) where
  symmetric := fun {_} hx => costLambda_symm c hx
  unit0 := costLambda_unit0 c

/-- Each member is continuous on `(0,∞)`, so continuity (a hypothesis of the
upstream uniqueness theorem) does not discriminate within the family either. -/
theorem costLambda_continuousOn (c : ℝ) :
    ContinuousOn (fun x => costLambda c x) (Set.Ioi 0) := by
  have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
    Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  have hmul : ContinuousOn (fun x => c * Real.log x) (Set.Ioi 0) :=
    continuousOn_const.mul hlog
  have hcosh : ContinuousOn (fun x => Real.cosh (c * Real.log x) - 1) (Set.Ioi 0) := by
    apply ContinuousOn.sub _ continuousOn_const
    exact Real.continuous_cosh.comp_continuousOn hmul
  exact hcosh.congr (fun x hx => costLambda_eq_cosh c hx)

/-- The `c = 1` member is exactly `Cost.Jcost` on the positives. -/
theorem costLambda_one_eq_Jcost {x : ℝ} (hx : 0 < x) :
    costLambda 1 x = Cost.Jcost x := by
  rw [costLambda_eq_cosh 1 hx, one_mul]
  show Real.cosh (Real.log x) - 1 = (x + x⁻¹) / 2 - 1
  exact costLambda_one_eq_J x hx

/-- **The family is faithful.** Distinct positive curvature parameters give
genuinely distinct cost functions. Proved by transporting the equality along
`x = exp t` to the log-coordinate family and invoking `clog_inj`. -/
theorem costLambda_inj {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h : (fun x => costLambda c x) = (fun x => costLambda d x)) : c = d := by
  apply clog_inj hc hd
  funext t
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hval := congrFun h (Real.exp t)
  simp only at hval
  rw [costLambda_eq_cosh c hexp, costLambda_eq_cosh d hexp, Real.log_exp] at hval
  exact hval

/-- **Item 2, the negative direction.** The recognition cost laws
(`Cost.CostRequirements`) do not force the unit of scale.

The conjunction records: every member of the gauge family is a bona fide cost
(symmetric + unit law); the family is faithful (so the residual freedom is exactly
one real); the `c = 1` member is `J`; and there exist two genuinely distinct
members (`costLambda 1 = J` and `costLambda 2`) both satisfying the cost laws.
The last clause is the independence: the laws are satisfied by more than one
function, hence cannot single out `J`. The unit is fixed only by the extra
calibration hypothesis of the upstream uniqueness theorem, and is therefore the
one irreducible gauge choice. -/
theorem calibration_unit_not_forced_by_cost_laws :
    (∀ c : ℝ, Cost.CostRequirements (fun x => costLambda c x))
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun x => costLambda c x) = (fun x => costLambda d x) → c = d)
      ∧ (∀ x : ℝ, 0 < x → costLambda 1 x = Cost.Jcost x)
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ Cost.CostRequirements (fun x => costLambda c x)
            ∧ Cost.CostRequirements (fun x => costLambda d x)
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x)) := by
  refine ⟨fun c => costLambda_isCostRequirements c,
          fun c d hc hd h => costLambda_inj hc hd h,
          fun x hx => costLambda_one_eq_Jcost hx,
          ⟨1, 2, one_pos, two_pos, by norm_num,
           costLambda_isCostRequirements 1, costLambda_isCostRequirements 2, ?_⟩⟩
  intro h
  have h12 : (1 : ℝ) = 2 := costLambda_inj one_pos two_pos h
  norm_num at h12

/-! ## Independence against the FULL law set (RCL included)

The result above used only `Cost.CostRequirements = {symmetry, unit law}`. A skeptic
could object that those are weak, and that adding the reciprocal cost law (RCL, the
d'Alembert composition identity that actually drives the upstream classification) pins
the unit after all. It does not. The section below proves the gauge family satisfies
the EXACT non-calibration hypothesis set of
`Cost.FunctionalEquation.law_of_logic_forces_jcost`
(`IsReciprocalCost`, `IsNormalized`, `SatisfiesCompositionLaw`, `ContinuousOn (Ioi 0)`)
for every positive `c`, and that the remaining hypothesis `IsCalibrated` holds iff
`c = 1`. So calibration is the single hypothesis that pins `J`; everything else is
satisfied by the whole family. -/

/-- In log coordinates the gauge member reads off as `G(costLambda c) t = cosh(c·t) − 1`,
matching the `cosh(c·)` family that drives the upstream functional-equation classification. -/
theorem G_costLambda (c t : ℝ) :
    Cost.FunctionalEquation.G (fun x => costLambda c x) t = Real.cosh (c * t) - 1 := by
  show costLambda c (Real.exp t) = Real.cosh (c * t) - 1
  rw [costLambda_eq_cosh c (Real.exp_pos t), Real.log_exp]

/-- **Every gauge member satisfies the RCL** (the cosh-add / d'Alembert identity). Both
sides reduce to `2·cosh(ct)cosh(cu) − 2` via `cosh_add`/`cosh_sub`. -/
theorem costLambda_coshAddIdentity (c : ℝ) :
    Cost.FunctionalEquation.CoshAddIdentity (fun x => costLambda c x) := by
  intro t u
  simp only [G_costLambda]
  have e1 : c * (t + u) = c * t + c * u := by ring
  have e2 : c * (t - u) = c * t - c * u := by ring
  rw [e1, e2, Real.cosh_add, Real.cosh_sub]
  ring

theorem costLambda_isReciprocalCost (c : ℝ) :
    Cost.FunctionalEquation.IsReciprocalCost (fun x => costLambda c x) :=
  fun _ hx => costLambda_symm c hx

theorem costLambda_isNormalized (c : ℝ) :
    Cost.FunctionalEquation.IsNormalized (fun x => costLambda c x) :=
  costLambda_unit0 c

theorem costLambda_satisfiesCompositionLaw (c : ℝ) :
    Cost.FunctionalEquation.SatisfiesCompositionLaw (fun x => costLambda c x) :=
  (Cost.FunctionalEquation.composition_law_equiv_coshAdd _).mpr (costLambda_coshAddIdentity c)

/-- The remaining hypothesis, calibration (`G''(0) = 1`), holds iff `c = 1`, because
`G(costLambda c)'' (0) = c²`. -/
theorem costLambda_isCalibrated_iff {c : ℝ} (hc : 0 < c) :
    Cost.FunctionalEquation.IsCalibrated (fun x => costLambda c x) ↔ c = 1 := by
  have hG : Cost.FunctionalEquation.G (fun x => costLambda c x)
      = fun t => Real.cosh (c * t) - 1 := by
    funext t; exact G_costLambda c t
  unfold Cost.FunctionalEquation.IsCalibrated
  rw [hG]
  exact curvature_one_iff_J hc

/-- **Item 2, airtight: calibration is the ONLY hypothesis of the uniqueness theorem
that pins `J`.** Every gauge member satisfies the full non-calibration hypothesis set of
`law_of_logic_forces_jcost` (reciprocity, normalization, the RCL composition law, and
continuity on the positives); calibration holds iff `c = 1`; and the family contains
genuinely distinct members. Hence the four non-calibration hypotheses are satisfied by
more than one function and cannot determine `J`: the unit of scale is logically
independent of the entire law set except for the calibration choice. -/
theorem calibration_is_the_only_hypothesis_pinning_J :
    (∀ c : ℝ,
        Cost.FunctionalEquation.IsReciprocalCost (fun x => costLambda c x)
          ∧ Cost.FunctionalEquation.IsNormalized (fun x => costLambda c x)
          ∧ Cost.FunctionalEquation.SatisfiesCompositionLaw (fun x => costLambda c x)
          ∧ ContinuousOn (fun x => costLambda c x) (Set.Ioi 0))
      ∧ (∀ c : ℝ, 0 < c →
          (Cost.FunctionalEquation.IsCalibrated (fun x => costLambda c x) ↔ c = 1))
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x)) := by
  refine ⟨fun c => ⟨costLambda_isReciprocalCost c, costLambda_isNormalized c,
            costLambda_satisfiesCompositionLaw c, costLambda_continuousOn c⟩,
          fun c hc => costLambda_isCalibrated_iff hc, ?_⟩
  refine ⟨1, 2, one_pos, two_pos, by norm_num, ?_⟩
  intro h
  have h12 : (1 : ℝ) = 2 := costLambda_inj one_pos two_pos h
  norm_num at h12

end Calibration
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
