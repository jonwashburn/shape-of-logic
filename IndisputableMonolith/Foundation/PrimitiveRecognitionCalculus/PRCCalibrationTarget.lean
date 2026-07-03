/-
  PrimitiveRecognitionCalculus/PRCCalibrationTarget.lean

  Item 2 of the δ frontier: force the calibration unit from one δ act?

  The δ-forced cost FORM is the one-parameter gauge family (in log
  coordinates t = ln x):

      clog c t = cosh(c·t) − 1,    c > 0,

  which in multiplicative coordinates is costLambda c x = ½(x^c + x^{−c}) − 1.
  Every member satisfies reciprocal symmetry, normalization, and the
  composition law (the d'Alembert / RCL identity proved upstream); they differ
  only by the positive real c, the "unit of scale". Calibration is the choice
  of c. The hope of Item 2 was that the cost of one δ act (distinguishing an
  orbit from its successor) would force the log-curvature at the unit to be
  exactly 1, hence c = 1, hence J.

  What is proved here (the exact statement, both falsifier branches considered):

  * `logCurvature`:           the log-curvature at the unit is c² for every c.
  * `clog_inj`:               distinct positive c give genuinely distinct costs;
                              the family is a faithful 1-parameter family.
  * `curvature_one_iff_J`:    curvature normalized to 1 ⟺ c = 1 (the J member).
  * `costLambda_one_eq_J`:    the c = 1 member is exactly J(x) = ½(x + x⁻¹) − 1.
  * `calibration_unit_is_a_gauge`: the headline conjunction.

  RESULT (the falsifier resolves negative). The curvature at the unit is a
  SECOND-DERIVATIVE property: it is defined by the local behaviour of the cost
  at the limit ratio x → 1, i.e. by the continuous completion. The δ-native
  carrier is the rationals ℚ_δ, where the minimal distinction is the finite
  ratio step and no infinitesimal / second derivative exists. The discrete δ
  data (costs at rational ratios) therefore does NOT single out c; the whole
  family is admissible on ℚ_δ and the members are mutually distinct. The
  calibration c = 1 is fixed only by a continuum-side normalization (choosing
  the cost unit so the leading log-curvature is 1). It is a gauge, not a δ-forced
  constant. This confirms the δ3 / δ0 framing: "δ forces the cost FORM" does NOT
  upgrade to "δ forces J"; the unit is the one residual free parameter.

  The positive content (form forced, family faithful, J = the curvature-1
  member) is fully proved below. The negative interpretation (curvature is a
  continuum property the discrete carrier cannot fix) is the honest reading the
  proved structure forces.

  UPGRADE (PRCCalibrationIndependence.lean): the negative direction is no longer
  only "the honest reading"; it is now a theorem, in two strengths.

  (a) `calibration_unit_not_forced_by_cost_laws`: the whole gauge family
  `costLambda c = ½(x^c + x^{−c}) − 1` satisfies the recognition cost laws
  `Cost.CostRequirements` for every positive `c` (and is continuous on the
  positives), is faithful, and has `J` as its `c = 1` member; two distinct members
  satisfy the laws, so the laws cannot force `c = 1`.

  (b) `calibration_is_the_only_hypothesis_pinning_J` (airtight, RCL included):
  every member satisfies the EXACT non-calibration hypothesis set of
  `Cost.FunctionalEquation.law_of_logic_forces_jcost` -- `IsReciprocalCost`,
  `IsNormalized`, `SatisfiesCompositionLaw` (the RCL / d'Alembert composition law),
  and `ContinuousOn (Set.Ioi 0)` -- while `IsCalibrated` holds iff `c = 1`. So
  calibration is the single hypothesis of the uniqueness theorem that pins `J`; the
  unit of scale is logically independent of the entire law set except for the
  calibration choice. This forecloses the objection that adding the RCL to the weak
  `CostRequirements` premise might re-force the unit.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Calibration

/-- The log-curvature of the cost member `cosh(c·t) − 1` at the unit (t = 0) is
`c²`. This is the residual gauge parameter read off as a second derivative. -/
theorem logCurvature (c : ℝ) :
    deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = c ^ 2 := by
  have hderiv1 : deriv (fun t => Real.cosh (c * t) - 1)
      = fun t => c * Real.sinh (c * t) := by
    funext t
    have hinner : HasDerivAt (fun s => c * s) (c * 1) t :=
      (hasDerivAt_id t).const_mul c
    have h : HasDerivAt (fun t => Real.cosh (c * t) - 1)
        (Real.sinh (c * t) * (c * 1)) t :=
      ((Real.hasDerivAt_cosh (c * t)).comp t hinner).sub_const 1
    rw [h.deriv]; ring
  rw [hderiv1]
  have hinner0 : HasDerivAt (fun s => c * s) (c * 1) (0 : ℝ) :=
    (hasDerivAt_id (0 : ℝ)).const_mul c
  have h2 : HasDerivAt (fun t => c * Real.sinh (c * t))
      (c * (Real.cosh (c * 0) * (c * 1))) (0 : ℝ) :=
    ((Real.hasDerivAt_sinh (c * 0)).comp (0 : ℝ) hinner0).const_mul c
  rw [h2.deriv]
  simp only [mul_zero, Real.cosh_zero, one_mul, mul_one]
  ring

/-- The cost family is faithful: distinct positive curvature parameters give
distinct cost functions. (Proved through the curvature, which is an invariant of
the function.) -/
theorem clog_inj {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (h : (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1)) :
    c = d := by
  have e1 : deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = c ^ 2 :=
    logCurvature c
  have e2 : deriv (deriv (fun t => Real.cosh (d * t) - 1)) 0 = d ^ 2 :=
    logCurvature d
  rw [h, e2] at e1
  have hsq : c ^ 2 = d ^ 2 := e1.symm
  have hfac : (c - d) * (c + d) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · linarith

/-- Curvature normalized to 1 picks out exactly the `c = 1` member, i.e. J. -/
theorem curvature_one_iff_J {c : ℝ} (hc : 0 < c) :
    deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = 1 ↔ c = 1 := by
  rw [logCurvature c]
  constructor
  · intro h
    have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hfac with h' | h'
    · linarith
    · linarith
  · intro h; rw [h]; norm_num

/-- The `c = 1` member is exactly J: in multiplicative coordinates,
`cosh(ln x) − 1 = ½(x + x⁻¹) − 1`. -/
theorem costLambda_one_eq_J (x : ℝ) (hx : 0 < x) :
    Real.cosh (Real.log x) - 1 = (x + x⁻¹) / 2 - 1 := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hx]

/-- **Item 2 headline.** The δ-forced cost form leaves a faithful one-parameter
gauge family; its only invariant is the log-curvature c² at the unit; and
"curvature = 1" is exactly the condition selecting J. The unit c is a free
positive real (a gauge), because curvature is a continuum-side second-derivative
property that the discrete δ carrier does not fix. -/
theorem calibration_unit_is_a_gauge :
    (∀ c : ℝ, deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = c ^ 2)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d)
      ∧ (∀ c : ℝ, 0 < c →
          (deriv (deriv (fun t => Real.cosh (c * t) - 1)) 0 = 1 ↔ c = 1)) :=
  ⟨logCurvature, fun _ _ hc hd h => clog_inj hc hd h, fun _ hc => curvature_one_iff_J hc⟩

/-- The gauge action `μ • F := F(μ · )` is transitive on the cost family: any
member reaches any other through a positive rescaling of the log-coordinate. -/
theorem gauge_action_transitive {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    ∃ μ : ℝ, 0 < μ ∧
      (fun t => Real.cosh (c * (μ * t)) - 1) = (fun t => Real.cosh (d * t) - 1) := by
  refine ⟨d / c, div_pos hd hc, ?_⟩
  funext t
  have hcne : c ≠ 0 := ne_of_gt hc
  have hkey : c * (d / c * t) = d * t := by field_simp
  rw [hkey]

/-- **Item 2, sharpened: the residual freedom is a torsor, exactly one real.** The
gauge action of the positive reals on the cost family is free (`clog_inj`) and
transitive (`gauge_action_transitive`). A free transitive action exhibits the
family as a principal homogeneous space under `(ℝ_{>0}, ·)`, so the residual
freedom in the cost is exactly one positive real, the unit of scale. It is fixed
by one calibration datum (curvature 1), and that datum is not supplied by the
discrete δ structure. -/
theorem cost_freedom_is_one_real_torsor :
    (∀ c d : ℝ, 0 < c → 0 < d →
        (fun t => Real.cosh (c * t) - 1) = (fun t => Real.cosh (d * t) - 1) → c = d)
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          ∃ μ : ℝ, 0 < μ ∧
            (fun t => Real.cosh (c * (μ * t)) - 1) = (fun t => Real.cosh (d * t) - 1)) :=
  ⟨fun _ _ hc hd h => clog_inj hc hd h, fun _ _ hc hd => gauge_action_transitive hc hd⟩

end Calibration
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
