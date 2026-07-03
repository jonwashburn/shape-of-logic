import Mathlib
import IndisputableMonolith.Foundation.DAlembert.Inevitability
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.GeneralizedDAlembert.SmoothnessTop
import IndisputableMonolith.Cost.AczelProof
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
  GeneralizedDAlembert.lean

  Move 3: discharge polynomial regularity using continuity.

  The existing Translation Theorem requires that the route-independence
  combiner `P` be a polynomial of total degree at most two.  A
  counterexample (the quartic-log) shows that some regularity is
  required, but polynomial-degree-≤-2 is stronger than needed.  The
  classical result that does the work is the Aczél–Kannappan
  classification of continuous solutions of the d'Alembert functional
  equation: a continuous `H : ℝ → ℝ` with `H(0) = 1` satisfying
  `H(x+y) + H(x-y) = 2 H(x) H(y)` is either constant `1`, a hyperbolic
  cosine `cosh(α x)`, or a trigonometric cosine `cos(α x)`. Combined
  with the existing pipeline, this discharges the polynomial
  restriction: continuity of the combiner is enough.

  This module:
  1. **Proves** the Aczél–Kannappan classification of the d'Alembert
     functional equation (`aczel_kannappan_continuous_dAlembert`) as a
     theorem inside the framework: continuity + `H(0) = 1` + d'Alembert
     forces `H` to be the constant 1, a hyperbolic cosine, or a
     trigonometric cosine. The proof reduces to the existing
     `IndisputableMonolith.Cost.FunctionalEquation.dAlembert_classification`,
     which is in turn proved from the integration-bootstrap regularization,
     the universal d'Alembert-to-ODE derivation, and ODE uniqueness in each
     of the three branches of the trichotomy on `H''(0)`.
  2. Introduces a continuous-combiner predicate and a continuous
     route-independence predicate.
  3. Proves the algebraic assembly that would turn suitable
     combiner-side analysis inputs into a bilinear combiner. A later
     counterexample shows these inputs are not automatic from continuity
     alone: the quartic log-cost blocks the proposed second-derivative
     identity. Thus finite pairwise polynomial closure remains the sharp
     hypothesis for the Law-of-Logic paper.
  4. Provides a continuous-combiner version of `SatisfiesLawsOfLogic`
     that drops the polynomial-degree-≤-2 hypothesis.

  The intent is that downstream code can use the continuous-combiner
  version, and the polynomial-case Translation Theorem becomes a
  particular instance.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GeneralizedDAlembert

open IndisputableMonolith.Foundation.LogicAsFunctionalEquation
open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-! ## 1. The Aczél–Kannappan classification (proved inside the framework)

The d'Alembert functional equation `H(x+y) + H(x-y) = 2 H(x) H(y)`
on a continuous `H : ℝ → ℝ` with `H(0) = 1` has the classical
Aczél–Kannappan classification: every continuous solution is one of
the constant function 1, a hyperbolic cosine `cosh(α x)`, or a
trigonometric cosine `cos(α x)`.

This is **proved** inside the framework, not posited. The proof goes
through:

* `dAlembert_contDiff_smooth`: continuity + d'Alembert + `H(0)=1`
  upgrades `H` to `C^∞` via the integration-bootstrap construction
  (`Cost/AczelProof.lean`).
* `dAlembert_to_ODE_general`: a `C^2` d'Alembert solution satisfies
  `H'' = c · H` with `c = H''(0)` (`Cost/AczelProof.lean`,
  using `Cost/FunctionalEquation.lean`).
* The trichotomy on `c` and ODE uniqueness in each branch
  (cosh, cos, constant) — proved inside `Cost/FunctionalEquation.lean`
  and packaged in `dAlembert_classification`.
-/

/-- **Aczél–Kannappan classification** (proved theorem, not axiom):
every continuous solution of the d'Alembert functional equation
`H(x+y) + H(x-y) = 2 H(x) H(y)` with `H(0) = 1` is either the
constant 1, a hyperbolic cosine, or a trigonometric cosine.

The proof reduces to
`IndisputableMonolith.Cost.FunctionalEquation.dAlembert_classification`,
which assembles the integration bootstrap, universal-coefficient ODE
derivation, and ODE uniqueness lemmas into the disjunction. -/
theorem aczel_kannappan_continuous_dAlembert
    (H : ℝ → ℝ) (hCont : Continuous H) (h_one : H 0 = 1)
    (hEq : ∀ x y : ℝ, H (x + y) + H (x - y) = 2 * H x * H y) :
    (∀ x, H x = 1) ∨
    (∃ α : ℝ, ∀ x, H x = Real.cosh (α * x)) ∨
    (∃ α : ℝ, ∀ x, H x = Real.cos (α * x)) :=
  IndisputableMonolith.Cost.FunctionalEquation.dAlembert_classification
    H h_one hCont hEq

/-! ## 2. The continuous-combiner formulation

The polynomial case of the Translation Theorem assumes `P` is a
symmetric polynomial of total degree at most two. The continuous case
replaces this with continuity of `P : ℝ × ℝ → ℝ`. Symmetry is still
required (it follows from non-contradiction).
-/

/-- A *continuous-combiner* version of route-independence: there exists a
continuous, symmetric function `P : ℝ × ℝ → ℝ` such that
`F(xy) + F(x/y) = P(F(x), F(y))` on positive ratios. -/
def ContinuousRouteIndependence (C : ComparisonOperator) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    Continuous (Function.uncurry P) ∧
    (∀ u v, P u v = P v u) ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
       derivedCost C (x * y) + derivedCost C (x / y)
       = P (derivedCost C x) (derivedCost C y))

/-- A *continuous Law of Logic* — the existing `SatisfiesLawsOfLogic`
with polynomial route-independence replaced by continuous
route-independence. -/
structure SatisfiesLawsOfLogicContinuous (C : ComparisonOperator) : Prop where
  identity            : Identity C
  non_contradiction   : NonContradiction C
  excluded_middle     : ExcludedMiddle C
  scale_invariant     : ScaleInvariant C
  route_independence  : ContinuousRouteIndependence C
  non_trivial         : NonTrivial C

/-- Log-coordinate Aczél data extracted from a continuous-combiner Law of
Logic witness. -/
structure LogAczelData (G : ℝ → ℝ) (P : ℝ → ℝ → ℝ) : Prop where
  continuous_G : Continuous G
  zero_G       : G 0 = 0
  even_G       : Function.Even G
  continuous_P : Continuous (Function.uncurry P)
  symmetric_P  : ∀ u v, P u v = P v u
  aczel_eq     : ∀ t u : ℝ, G (t + u) + G (t - u) = P (G t) (G u)

/-- Continuity of the derived cost on positive ratios lifts to continuity of
the log-coordinate cost `G(t) = F(exp t)`. -/
theorem continuous_log_cost_of_continuousOn_positive
    (F : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Ioi (0 : ℝ))) :
    Continuous (fun t : ℝ => F (Real.exp t)) := by
  have hExpOn : ContinuousOn (fun t : ℝ => Real.exp t) (Set.univ : Set ℝ) :=
    Real.continuous_exp.continuousOn
  have hMaps : Set.MapsTo (fun t : ℝ => Real.exp t)
      (Set.univ : Set ℝ) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    exact Real.exp_pos t
  have hComp : ContinuousOn (F ∘ fun t : ℝ => Real.exp t) (Set.univ : Set ℝ) :=
    hF.comp hExpOn hMaps
  have hCont := continuousOn_univ.mp hComp
  simpa [Function.comp_def] using hCont

/-- The continuous-combiner Law of Logic gives a continuous log-coordinate
Aczél equation. This is the formal input object for the smoothness bootstrap. -/
theorem log_aczel_data_of_laws
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogicContinuous C) :
    ∃ P : ℝ → ℝ → ℝ,
      LogAczelData (fun t : ℝ => derivedCost C (Real.exp t)) P := by
  obtain ⟨P, hPcont, hPsym, hCons⟩ := h.route_independence
  refine ⟨P, ?_⟩
  have hFcont : ContinuousOn (derivedCost C) (Set.Ioi (0 : ℝ)) :=
    excluded_middle_implies_continuous C h.excluded_middle
  have hNorm : derivedCost C 1 = 0 :=
    identity_implies_normalized C h.identity
  have hSymm : IsSymmetric (derivedCost C) :=
    non_contradiction_and_scale_imply_reciprocal C h.non_contradiction h.scale_invariant
  refine
    { continuous_G := continuous_log_cost_of_continuousOn_positive (derivedCost C) hFcont
      zero_G := by simpa [derivedCost] using hNorm
      even_G := ?_
      continuous_P := hPcont
      symmetric_P := hPsym
      aczel_eq := ?_ }
  · exact IndisputableMonolith.Cost.FunctionalEquation.G_even_of_reciprocal_symmetry
      (derivedCost C) (by intro x hx; exact hSymm x hx)
  · intro t u
    have htu_pos : 0 < Real.exp t := Real.exp_pos t
    have huu_pos : 0 < Real.exp u := Real.exp_pos u
    have h := hCons (Real.exp t) (Real.exp u) htu_pos huu_pos
    simpa [Real.exp_add, Real.exp_sub] using h

/-! ## 2b. Piece 1 mollifier scaffold

The former residual `continuous_combiner_log_smoothness_bootstrap` says
`G(t) = F(exp t)` is `C^∞`. The classical argument is mollification:
convolve `G` with a `ContDiffBump` kernel to produce a smooth approximant
`G_φ` and then push smoothness back to `G` through the Aczél equation.

The scaffold below packages the parts Mathlib hands us for free and
isolates the genuine analytic content for later work.

In this section we prove:

* `mollified G φ` exists as a measurable function and is continuous.
* `mollified_pointwise_tendsto`: as the bump support shrinks, the
  mollification converges to `G` pointwise (via Mathlib's
  `ContDiffBump.convolution_tendsto_right_of_continuous`).

Smoothness of `G` itself still needs the equation-side argument, but
`G_φ` already inherits arbitrary regularity from the bump kernel.
-/

open scoped Convolution
open MeasureTheory

/-- Mollification of a continuous function on `ℝ` by a normalized
`ContDiffBump` kernel, written as a left convolution to align with
`ContDiffBump.convolution_tendsto_right_of_continuous`. -/
noncomputable def mollified (G : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) : ℝ → ℝ :=
  φ.normed (volume : MeasureTheory.Measure ℝ)
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : MeasureTheory.Measure ℝ)] G

/-- The normalized bump has compact support and is continuous; convolving
with a continuous function leaves a continuous function. -/
theorem mollified_continuous (G : ℝ → ℝ) (hG : Continuous G)
    (φ : ContDiffBump (0 : ℝ)) : Continuous (mollified G φ) := by
  unfold mollified
  refine HasCompactSupport.continuous_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) ?_ ?_ ?_
  · exact φ.hasCompactSupport_normed (μ := (volume : MeasureTheory.Measure ℝ))
  · have h0 : ContDiff ℝ ((0 : ℕ∞) : WithTop ℕ∞)
        (φ.normed (μ := (volume : MeasureTheory.Measure ℝ))) :=
      φ.contDiff_normed (μ := (volume : MeasureTheory.Measure ℝ)) (n := 0)
    -- ContDiff at level 0 is continuity.
    exact (contDiff_zero.mp (by exact_mod_cast h0))
  · exact hG.locallyIntegrable (μ := (volume : MeasureTheory.Measure ℝ))

/-- As the bump support shrinks, the mollification converges pointwise to
the original continuous function. -/
theorem mollified_pointwise_tendsto {ι : Type*}
    (G : ℝ → ℝ) (hG : Continuous G)
    {φ : ι → ContDiffBump (0 : ℝ)} {l : Filter ι}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (nhds 0)) (x₀ : ℝ) :
    Filter.Tendsto (fun i => mollified G (φ i) x₀) l (nhds (G x₀)) := by
  unfold mollified
  exact ContDiffBump.convolution_tendsto_right_of_continuous hφ hG x₀

/-- Helper predicate naming the residual analytic content for Piece 1.

`MollifierCkRoute` says: there is a parametrized family of `ContDiffBump`
kernels with shrinking support. This is *infrastructure only* — the
analytic blocker is uniform compact-set derivative bounds on
`mollified G (φ n)`, not the existence of the bump family. -/
def MollifierCkRoute : Prop :=
  ∃ (φ : ℕ → ContDiffBump (0 : ℝ)),
    Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0)

set_option maxHeartbeats 400000 in
/-- Existence of a shrinking-support bump family on `ℝ`. -/
theorem mollifierCkRoute_exists : MollifierCkRoute := by
  classical
  refine ⟨fun n => ?_, ?_⟩
  · refine
      { rIn := (1 : ℝ) / (2 * ((n : ℝ) + 1))
        rOut := (1 : ℝ) / ((n : ℝ) + 1)
        rIn_pos := by positivity
        rIn_lt_rOut := by
          have hn : (0 : ℝ) < ((n : ℝ) + 1) := by
            have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
            linarith
          have hlt : ((n : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by linarith
          exact one_div_lt_one_div_of_lt hn hlt }
  · -- (1 : ℝ) / ((n : ℝ) + 1) → 0
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using h

/-! ## 3. Promoting polynomial to continuous

The polynomial case is a special case of the continuous case. Concretely,
any polynomial of total degree at most two on `ℝ × ℝ` is continuous, so
`SatisfiesLawsOfLogic ⊆ SatisfiesLawsOfLogicContinuous`. -/

private theorem polynomial_continuous
    (a b c d e f : ℝ) :
    Continuous (Function.uncurry
      (fun u v : ℝ => a + b*u + c*v + d*u*v + e*u^2 + f*v^2)) := by
  unfold Function.uncurry
  fun_prop

/-- Polynomial route-independence implies continuous route-independence. -/
theorem polynomial_implies_continuous (C : ComparisonOperator)
    (hPoly : RouteIndependence C) :
    ContinuousRouteIndependence C := by
  obtain ⟨P, ⟨a, b, c, d, e, f, hPform⟩, hSymP, hCons⟩ := hPoly
  refine ⟨P, ?_, hSymP, hCons⟩
  -- Continuity of P from its polynomial form.
  have heq : Function.uncurry P
      = Function.uncurry (fun u v : ℝ => a + b*u + c*v + d*u*v + e*u^2 + f*v^2) := by
    funext ⟨u, v⟩
    simpa using hPform u v
  rw [heq]
  exact polynomial_continuous a b c d e f

/-- The polynomial-case `SatisfiesLawsOfLogic` is a special case of the
continuous-case `SatisfiesLawsOfLogicContinuous`. -/
theorem laws_polynomial_implies_continuous
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    SatisfiesLawsOfLogicContinuous C where
  identity := h.identity
  non_contradiction := h.non_contradiction
  excluded_middle := h.excluded_middle
  scale_invariant := h.scale_invariant
  route_independence := polynomial_implies_continuous C h.route_independence
  non_trivial := h.non_trivial

/-! ## 4. Conditional bilinear assembly

The remaining continuous-combiner work separates cleanly into two
parts. The hard analysis must classify the log-coordinate cost
`G(t) = F(exp t)`. Once that classification is available, the bilinear
combiner is just algebra.

This section proves the algebraic half. It is independent of the
regularization and ψ-affine forcing arguments.
-/

/-- Log-coordinate bilinear identity with coefficient `c`. -/
def LogBilinearIdentity (G : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ t u : ℝ,
    G (t + u) + G (t - u) = 2 * G t + 2 * G u + c * G t * G u

/-- A classified log-coordinate cost: parabolic, hyperbolic, trigonometric,
or zero. This is the algebraic target left after the smoothness/affine-forcing
analysis has been done. -/
def ClassifiedLogCost (G : ℝ → ℝ) : Prop :=
  (∀ t, G t = 0) ∨
  (∃ α : ℝ, ∀ t, G t = α * t^2) ∨
  (∃ α : ℝ, ∀ t, G t = Real.cosh (α * t) - 1) ∨
  (∃ α : ℝ, ∀ t, G t = 1 - Real.cos (α * t))

/-- The zero log-cost satisfies the bilinear identity with any coefficient. -/
theorem log_zero_bilinear_identity :
    LogBilinearIdentity (fun _ : ℝ => 0) 0 := by
  intro t u
  ring

/-- The parabolic log-cost satisfies the additive (`c = 0`) bilinear identity. -/
theorem log_parabolic_bilinear_identity (α : ℝ) :
    LogBilinearIdentity (fun t : ℝ => α * t^2) 0 := by
  intro t u
  ring

/-- The hyperbolic log-cost satisfies the RCL bilinear identity (`c = 2`). -/
theorem log_cosh_sub_one_bilinear_identity (α : ℝ) :
    LogBilinearIdentity (fun t : ℝ => Real.cosh (α * t) - 1) 2 := by
  intro t u
  simp only
  rw [show α * (t + u) = α * t + α * u by ring,
      show α * (t - u) = α * t - α * u by ring,
      Real.cosh_add, Real.cosh_sub]
  ring

/-- The trigonometric log-cost satisfies the bilinear identity with `c = -2`. -/
theorem log_one_sub_cos_bilinear_identity (α : ℝ) :
    LogBilinearIdentity (fun t : ℝ => 1 - Real.cos (α * t)) (-2) := by
  intro t u
  simp only
  rw [show α * (t + u) = α * t + α * u by ring,
      show α * (t - u) = α * t - α * u by ring,
      Real.cos_add, Real.cos_sub]
  ring

/-- Classified log-costs always give a bilinear identity. -/
theorem classified_log_cost_bilinear
    (G : ℝ → ℝ) (hG : ClassifiedLogCost G) :
    ∃ c : ℝ, LogBilinearIdentity G c := by
  rcases hG with h0 | ⟨α, hpar⟩ | ⟨α, hcosh⟩ | ⟨α, hcos⟩
  · refine ⟨0, ?_⟩
    intro t u
    rw [h0 (t + u), h0 (t - u), h0 t, h0 u]
    ring
  · refine ⟨0, ?_⟩
    intro t u
    rw [hpar (t + u), hpar (t - u), hpar t, hpar u]
    exact log_parabolic_bilinear_identity α t u
  · refine ⟨2, ?_⟩
    intro t u
    rw [hcosh (t + u), hcosh (t - u), hcosh t, hcosh u]
    exact log_cosh_sub_one_bilinear_identity α t u
  · refine ⟨-2, ?_⟩
    intro t u
    rw [hcos (t + u), hcos (t - u), hcos t, hcos u]
    exact log_one_sub_cos_bilinear_identity α t u

/-- A classified positive-ratio cost admits a bilinear combiner on positive
ratios. This is Piece 5 of the axiom-2 attack: once the log-coordinate
classification is known, the bilinear witness is explicit. -/
theorem classified_positive_cost_bilinear
    (F : ℝ → ℝ)
    (hClass : ClassifiedLogCost (fun t : ℝ => F (Real.exp t))) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        F (x * y) + F (x / y) = P (F x) (F y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) := by
  obtain ⟨c, hbil⟩ := classified_log_cost_bilinear (fun t : ℝ => F (Real.exp t)) hClass
  refine ⟨fun u v => 2*u + 2*v + c*u*v, c, ?_, ?_⟩
  · intro x y hx hy
    have hxne : x ≠ 0 := ne_of_gt hx
    have hyne : y ≠ 0 := ne_of_gt hy
    have hxy : 0 < x * y := mul_pos hx hy
    have hxdiv : 0 < x / y := div_pos hx hy
    have hlog_xy : Real.log (x * y) = Real.log x + Real.log y :=
      Real.log_mul hxne hyne
    have hlog_div : Real.log (x / y) = Real.log x - Real.log y :=
      Real.log_div hxne hyne
    have hx_exp : Real.exp (Real.log x) = x := Real.exp_log hx
    have hy_exp : Real.exp (Real.log y) = y := Real.exp_log hy
    have h := hbil (Real.log x) (Real.log y)
    dsimp only at h
    rw [← hx_exp, ← hy_exp]
    rw [← Real.exp_add, ← Real.exp_sub]
    exact h
  · intro u v
    rfl

/-- A log-bilinear identity becomes the standard d'Alembert equation after
the affine lift `H(t) = 1 + (c/2)G(t)`. This is Piece 4's algebraic core. -/
theorem log_bilinear_affine_lift_dAlembert
    (G : ℝ → ℝ) (c : ℝ)
    (hLog : LogBilinearIdentity G c) :
    ∀ t u : ℝ,
      (1 + (c / 2) * G (t + u)) + (1 + (c / 2) * G (t - u))
        = 2 * (1 + (c / 2) * G t) * (1 + (c / 2) * G u) := by
  intro t u
  have h := hLog t u
  linear_combination (c / 2) * h

/-- Once the log-bilinear identity is known, the affine lift is classified by
the already-discharged H-side Aczél–Kannappan theorem. -/
theorem log_bilinear_affine_lift_classification
    (G : ℝ → ℝ) (c : ℝ)
    (hCont : Continuous G) (hG0 : G 0 = 0)
    (hLog : LogBilinearIdentity G c) :
    (∀ x, 1 + (c / 2) * G x = 1) ∨
    (∃ α : ℝ, ∀ x, 1 + (c / 2) * G x = Real.cosh (α * x)) ∨
    (∃ α : ℝ, ∀ x, 1 + (c / 2) * G x = Real.cos (α * x)) := by
  let H : ℝ → ℝ := fun t => 1 + (c / 2) * G t
  have hH0 : H 0 = 1 := by simp [H, hG0]
  have hHCont : Continuous H := by
    exact continuous_const.add (continuous_const.mul hCont)
  have hHdA : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u := by
    intro t u
    exact log_bilinear_affine_lift_dAlembert G c hLog t u
  simpa [H] using aczel_kannappan_continuous_dAlembert H hHCont hH0 hHdA

/-- A log-coordinate bilinear identity lifts back to a bilinear combiner on
positive ratios. This is the final algebraic assembly step for axiom 2. -/
theorem log_bilinear_positive_cost_bilinear
    (F : ℝ → ℝ)
    (hLog : ∃ c : ℝ, LogBilinearIdentity (fun t : ℝ => F (Real.exp t)) c) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        F (x * y) + F (x / y) = P (F x) (F y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) := by
  obtain ⟨c, hbil⟩ := hLog
  refine ⟨fun u v => 2*u + 2*v + c*u*v, c, ?_, ?_⟩
  · intro x y hx hy
    have hx_exp : Real.exp (Real.log x) = x := Real.exp_log hx
    have hy_exp : Real.exp (Real.log y) = y := Real.exp_log hy
    have h := hbil (Real.log x) (Real.log y)
    dsimp only at h
    rw [← hx_exp, ← hy_exp]
    rw [← Real.exp_add, ← Real.exp_sub]
    exact h
  · intro u v
    rfl

/-! ## 4. Continuous version of `bilinear_family_forced`

Under continuity of the combiner, the Aczél–Kannappan classification
forces the same bilinear conclusion as the polynomial case. We obtain
the continuous-case Translation Theorem.

The argument matches the polynomial-case argument up to the point at
which the d'Alembert equation is recovered on the cosh-add identity.
At that point, the polynomial-case derivation used the
polynomial-form lemma; the continuous-case derivation uses the named
Aczél–Kannappan classification theorem above plus the two residual
combiner-side analysis inputs named below. -/

/-- **Named analysis input 1a: finite-order mollifier derivative control.**

For every finite differentiability order, the mollifier route gives a
`C^n` bound/limit certificate for the log-coordinate derived cost
`G(t) = F(exp t)`. This is the precise analytic estimate left in Piece 1:
the bump family exists and converges pointwise by theorem above; what remains
is controlling derivatives on compact intervals strongly enough to pass the
limit back to `G`. -/
def ContinuousCombinerMollifierFiniteSmoothness
    (C : ComparisonOperator)
    (_h : SatisfiesLawsOfLogicContinuous C) : Prop :=
    ∀ n : ℕ, ContDiff ℝ n (fun t : ℝ => derivedCost C (Real.exp t))

/-- **Residual input 1b: finite-order smoothness promotes to full top-level
smoothness for this log-cost.**

Lean's `ContDiff` index used by Mathlib distinguishes the imported `⊤ : ℕ∞`
from the outer `⊤ : WithTop ℕ∞` expected by downstream APIs. This input is the
formal promotion step from the finite-order certificates produced by the
mollifier route to the top-level smoothness statement consumed below. -/
theorem continuous_combiner_finite_smoothness_to_top
    (C : ComparisonOperator)
    (_h : SatisfiesLawsOfLogicContinuous C)
    (hFinite : ∀ n : ℕ, ContDiff ℝ n (fun t : ℝ => derivedCost C (Real.exp t))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => derivedCost C (Real.exp t)) := by
  exact SmoothnessTop.contDiff_top_of_contDiff_nat hFinite

/-- **Residual input 1 assembled:** finite-order mollifier derivative control
upgrades to the original `C^∞` smoothness statement. The old broad axiom is
now a theorem; the remaining named input is the finite-order derivative
control above. -/
theorem continuous_combiner_log_smoothness_bootstrap
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C)
    (hFinite : ContinuousCombinerMollifierFiniteSmoothness C h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => derivedCost C (Real.exp t)) := by
  exact continuous_combiner_finite_smoothness_to_top C h hFinite

/-- The second-derivative identity extracted from the smooth Aczél equation.
The function `ψ` is morally `∂₂ P(u, 0)`. -/
def AczelSecondDerivativeIdentity (G : ℝ → ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ,
    ∀ t : ℝ, 2 * deriv (deriv G) t = ψ (G t) * deriv (deriv G) 0

/-- Affineness of `ψ` on the image of the log-cost. -/
def PsiAffineOnImage (G : ℝ → ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ t : ℝ, ψ (G t) = 2 + c * G t

/-- **Named analysis input 2a: derivative identity for the combiner equation.**

This is the first differentiating step in the Stetkær/Aczél proof: from a
smooth log-coordinate Aczél equation, extract
`2 G''(t) = ψ(G(t)) G''(0)`.

This is not a theorem under the present hypotheses: the quartic log-cost
obstruction is formalized in
`Foundation.GeneralizedDAlembert.SecondDerivative`. -/
def ContinuousCombinerSecondDerivativeInput
    (C : ComparisonOperator)
    (_h : SatisfiesLawsOfLogicContinuous C)
    (_hSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => derivedCost C (Real.exp t))) : Prop :=
    AczelSecondDerivativeIdentity (fun t : ℝ => derivedCost C (Real.exp t))

/-- **Named analysis input 2b: ψ-affine completion.**

This is the remaining Stetkær/Aczél content: the derivative identity, symmetry
of the combiner, and the Aczél equation force the actual log-bilinear identity.
It is narrower than the former all-in ψ-affine forcing axiom because the
second-derivative extraction is now named separately. -/
def ContinuousCombinerPsiAffineCompletion
    (C : ComparisonOperator)
    (_h : SatisfiesLawsOfLogicContinuous C)
    (_hSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => derivedCost C (Real.exp t)))
    (_hDeriv : AczelSecondDerivativeIdentity (fun t : ℝ => derivedCost C (Real.exp t))) : Prop :=
    ∃ c : ℝ, LogBilinearIdentity (fun t : ℝ => derivedCost C (Real.exp t)) c

/-- Explicit package of the extra analysis needed to force bilinearity from
an arbitrary continuous combiner. This is deliberately a hypothesis package,
not an axiom. The quartic-log obstruction shows the package is not automatic
from `SatisfiesLawsOfLogicContinuous`. -/
structure ContinuousCombinerAnalysisInputs
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C) : Prop where
  finite_smoothness : ContinuousCombinerMollifierFiniteSmoothness C h
  second_derivative :
    ContinuousCombinerSecondDerivativeInput C h
      (continuous_combiner_log_smoothness_bootstrap C h finite_smoothness)
  psi_affine :
    ContinuousCombinerPsiAffineCompletion C h
      (continuous_combiner_log_smoothness_bootstrap C h finite_smoothness)
      second_derivative

/-- **Residual input 2 assembled:** smoothness plus the derivative identity
and ψ-affine completion give the required log-bilinear identity. -/
theorem continuous_combiner_psi_affine_forcing
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C)
    (hSmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => derivedCost C (Real.exp t)))
    (hDeriv : ContinuousCombinerSecondDerivativeInput C h hSmooth)
    (hPsi : ContinuousCombinerPsiAffineCompletion C h hSmooth hDeriv) :
    ∃ c : ℝ, LogBilinearIdentity (fun t : ℝ => derivedCost C (Real.exp t)) c := by
  exact hPsi

/-- **Continuous-combiner bilinear classification** (hypothesis-package form).

The final bilinear conclusion follows if the explicit analysis package is
provided. It is not automatic from `SatisfiesLawsOfLogicContinuous`; the
quartic log-cost refutes the proposed second-derivative input. -/
theorem continuous_combiner_bilinear_classification
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C)
    (hInputs : ContinuousCombinerAnalysisInputs C h) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        derivedCost C (x * y) + derivedCost C (x / y)
          = P (derivedCost C x) (derivedCost C y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) := by
  have hSmooth := continuous_combiner_log_smoothness_bootstrap C h hInputs.finite_smoothness
  have hLog := continuous_combiner_psi_affine_forcing C h hSmooth
    hInputs.second_derivative hInputs.psi_affine
  exact log_bilinear_positive_cost_bilinear (derivedCost C) hLog

/-- **Continuous-combiner Translation Theorem, hypothesis-package form**: a continuous comparison
operator satisfying the four Aristotelian conditions plus scale
invariance and continuous route independence admits a *bilinear*
combiner `P(u,v) = 2u + 2v + c·u·v` if the explicit analysis package is
also supplied. Polynomial-degree-≤-2 is not dropped by continuity alone. -/
theorem continuous_combiner_bilinear
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C)
    (hInputs : ContinuousCombinerAnalysisInputs C h) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        derivedCost C (x * y) + derivedCost C (x / y)
          = P (derivedCost C x) (derivedCost C y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) :=
  continuous_combiner_bilinear_classification C h hInputs

/-! ## 5. Generalized Translation Theorem

Under the continuous-combiner hypothesis (instead of polynomial
regularity), the four Aristotelian conditions on `C` plus scale
invariance and non-triviality imply the same RCL conclusion as the
polynomial case — the combiner has the canonical bilinear form. -/

/-- **Generalized Translation Theorem (named-hypothesis form)**.
Under the continuous-combiner hypothesis plus the explicit analysis
package, the Law of Logic forces the bilinear RCL family. -/
theorem RCL_is_unique_functional_form_of_logic_continuous
    (C : ComparisonOperator)
    (h : SatisfiesLawsOfLogicContinuous C)
    (hInputs : ContinuousCombinerAnalysisInputs C h) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        derivedCost C (x * y) + derivedCost C (x / y)
          = P (derivedCost C x) (derivedCost C y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) :=
  continuous_combiner_bilinear C h hInputs

/-- Every polynomial-LoL operator is a continuous-LoL operator. The bilinear
conclusion still requires the explicit analysis package at this level; the
ordinary polynomial theorem in `LogicAsFunctionalEquation` remains the
unconditional route. -/
theorem laws_continuous_subsumes_polynomial
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C)
    (hInputs : ContinuousCombinerAnalysisInputs C
      (laws_polynomial_implies_continuous C h)) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      (∀ x y : ℝ, 0 < x → 0 < y →
        derivedCost C (x * y) + derivedCost C (x / y)
          = P (derivedCost C x) (derivedCost C y)) ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) :=
  RCL_is_unique_functional_form_of_logic_continuous C
    (laws_polynomial_implies_continuous C h) hInputs

/-! ## Summary

The continuous-combiner Translation Theorem is retained only in
hypothesis-package form. Continuity alone does not discharge the
polynomial-degree-≤-2 hypothesis.

**Status of the two classical inputs that originally lived in this
module:**

* **Axiom 1, `aczel_kannappan_continuous_dAlembert` (the H-side
  classification):** `DISCHARGED`. Now a theorem, proved by reducing to
  `Cost.FunctionalEquation.dAlembert_classification`, which is itself
  built from the integration bootstrap, the universal d'Alembert-to-ODE
  derivation, and the three ODE uniqueness lemmas in
  `Cost/FunctionalEquation.lean`. No external classical content.

* **Axiom 2, `continuous_combiner_bilinear_classification` (the
  combiner-side classification):** `REFUTED AS AN AUTOMATIC CONSEQUENCE
  OF CONTINUITY`. The algebraic pieces are proved here:
  classified log-costs imply a log-bilinear identity; log-bilinear
  identities lift to positive-ratio bilinear combiners; and the affine
  lift `H(t)=1+(c/2)G(t)` satisfies the standard d'Alembert equation,
  so the already-discharged H-classification applies. But the
  second-derivative identity needed by the automatic route is false for
  the quartic log-cost. The bilinear conclusion is therefore exposed only
  behind `ContinuousCombinerAnalysisInputs`.

The polynomial case of the existing Translation Theorem remains the sharp
unconditional result.
-/

end GeneralizedDAlembert
end Foundation
end IndisputableMonolith
