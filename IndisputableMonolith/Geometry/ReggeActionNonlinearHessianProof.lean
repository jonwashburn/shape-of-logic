import IndisputableMonolith.Geometry.ReggeActionSecondVariation

/-!
# Nonlinear Regge Hessian Proof Interface

This module isolates the remaining hard calculation for the full nonlinear
Regge action: the second directional derivative at the flat potential must
equal the canonical incidence Hessian.

The theorem below is not a new assumption; it is the exact endpoint of the
second chain-rule calculation.  Once that calculation is supplied, the existing
`ReggeActionSecondVariationInput` follows immediately.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionNonlinearHessianProof

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open ReggeActionSmoothness
open ReggeActionSecondVariation

noncomputable section

theorem differentiableAt_eventually_of_contDiffAt_top
    (f : ℝ → ℝ) (x : ℝ)
    (h : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ∀ᶠ y : ℝ in nhds x, DifferentiableAt ℝ f y := by
  rcases h.contDiffOn (m := (1 : ℕ∞)) (by simp)
      (by intro htop; simp at htop) with ⟨u, hu, hcu⟩
  rcases mem_nhds_iff.mp hu with ⟨v, hvu, hvopen, hxv⟩
  filter_upwards [IsOpen.eventually_mem hvopen hxv] with y hy
  have huy : u ∈ nhds y :=
    Filter.mem_of_superset (IsOpen.mem_nhds hvopen hy) hvu
  exact (hcu.differentiableOn (by simp)).differentiableAt huy

theorem deriv_differentiableAt_of_contDiffAt_top
    (f : ℝ → ℝ) (x : ℝ)
    (h : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    DifferentiableAt ℝ (fun y : ℝ => deriv f y) x := by
  have htop : (1 : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (by exact le_top)
  have hfderiv : ContDiffAt ℝ (1 : ℕ∞) (fderiv ℝ f) x := by
    exact h.fderiv_right htop
  have hdiffF : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact hfderiv.differentiableAt (by norm_num)
  change DifferentiableAt ℝ (fun y : ℝ => (fderiv ℝ f y) 1) x
  exact ((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiableAt.comp x hdiffF)

theorem hasSecondDerivAt_const_add
    (f : ℝ → ℝ) (c d2 x : ℝ)
    (h : HasSecondDerivAt f d2 x) :
    HasSecondDerivAt (fun t : ℝ => c + f t) d2 x := by
  unfold HasSecondDerivAt at h ⊢
  have hderiv :
      (fun t : ℝ => deriv (fun y : ℝ => c + f y) t) =
        fun t : ℝ => deriv f t := by
    funext t
    exact deriv_const_add (f := f) (x := t) (c := c)
  simpa [hderiv] using h

/-- Exact second-directional-variation statement for the full nonlinear Regge
action. -/
def NonlinearReggeDirectionalHessianTheorem
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasSecondDerivAt (actionAlongLine K hK ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0

/-- The exact first-derivative linearization that remains after the local
geometric product rule, Cayley-Menger/arccos derivative, hinge derivative, and
Schlaefli cancellation are expanded near the flat point.  It is stronger than a
single derivative-at-zero statement and is precisely enough to give the
nonlinear Hessian. -/
def ActionDerivativeLinearizationNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ => deriv (actionAlongLine K hK ξ) t) =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ => t * hessianQuadratic (canonicalReggeHessian K hK) ξ

/-- The sharp Hessian target: the derivative of the full action along each
conformal line is tangent at first order to the canonical Hessian line.  Unlike
`ActionDerivativeLinearizationNearZeroTarget`, this allows cubic and higher
Regge terms. -/
def ActionDerivativeFirstOrderTangencyTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasDerivAt
      (fun t : ℝ =>
        deriv (actionAlongLine K hK ξ) t -
          t * hessianQuadratic (canonicalReggeHessian K hK) ξ)
      0 0

theorem nonlinearDirectionalHessian_of_actionDerivativeFirstOrderTangency
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hTan : ActionDerivativeFirstOrderTangencyTarget K hK) :
    NonlinearReggeDirectionalHessianTheorem K hK := by
  intro ξ
  unfold HasSecondDerivAt
  have hLinear : HasDerivAt
      (fun t : ℝ => t * hessianQuadratic (canonicalReggeHessian K hK) ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := by
    simpa using
      (hasDerivAt_id (0 : ℝ)).mul_const
        (hessianQuadratic (canonicalReggeHessian K hK) ξ)
  have hsum := (hTan ξ).add hLinear
  convert hsum using 1
  · ext t
    let q := hessianQuadratic (canonicalReggeHessian K hK) ξ
    change deriv (actionAlongLine K hK ξ) t =
      deriv (actionAlongLine K hK ξ) t - t * q + t * q
    ring
  · ring

theorem nonlinearDirectionalHessian_of_actionDerivativeLinearizationNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hLin : ActionDerivativeLinearizationNearZeroTarget K hK) :
    NonlinearReggeDirectionalHessianTheorem K hK := by
  intro ξ
  unfold HasSecondDerivAt
  have hLinear : HasDerivAt
      (fun t : ℝ => t * hessianQuadratic (canonicalReggeHessian K hK) ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := by
    simpa using
      (hasDerivAt_id (0 : ℝ)).mul_const
        (hessianQuadratic (canonicalReggeHessian K hK) ξ)
  exact hLinear.congr_of_eventuallyEq (hLin ξ)

theorem actionDerivativeFirstOrderTangency_of_linearizationNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hLin : ActionDerivativeLinearizationNearZeroTarget K hK) :
    ActionDerivativeFirstOrderTangencyTarget K hK := by
  intro ξ
  have hzero : HasDerivAt (fun _t : ℝ => (0 : ℝ)) 0 0 :=
    hasDerivAt_const 0 0
  refine hzero.congr_of_eventuallyEq ?_
  filter_upwards [hLin ξ] with t ht
  rw [ht]
  ring

/-- The canonical quadratic term restricted to a conformal line. -/
def canonicalQuadraticAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) : ℝ :=
  (1 / 2) *
    hessianQuadratic (canonicalReggeHessian K hK) (linePotential K ξ t)

/-- The canonical nonlinear remainder restricted to a conformal line. -/
def canonicalRemainderAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) : ℝ :=
  reggeActionRemainder K hK (canonicalReggeHessian K hK)
    (linePotential K ξ t)

/-- Exact one-dimensional split of the nonlinear Regge action along every
conformal line.  This is the algebraic reduction used by the nonlinear
Hessian proof: after this point the only remaining analytic content is the
second variation of the canonical remainder. -/
theorem actionAlongLine_canonical_split
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    actionAlongLine K hK ξ =
      fun t : ℝ =>
        reggeAction K hK (zeroPotential K) +
          canonicalQuadraticAlongLine K hK ξ t +
          canonicalRemainderAlongLine K hK ξ t := by
  funext t
  unfold actionAlongLine canonicalQuadraticAlongLine canonicalRemainderAlongLine
  simpa using
    reggeAction_taylor_decomposition K hK (canonicalReggeHessian K hK)
      (linePotential K ξ t)

/-- Equivalent explicit subtraction form of the canonical remainder along a
line.  This is the exact expression whose second derivative must vanish after
the Cayley-Menger/arccos/hinge chain rule is expanded. -/
theorem canonicalRemainderAlongLine_eq_action_sub_quadratic
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    canonicalRemainderAlongLine K hK ξ =
      fun t : ℝ =>
        actionAlongLine K hK ξ t -
          reggeAction K hK (zeroPotential K) -
          canonicalQuadraticAlongLine K hK ξ t := by
  funext t
  unfold canonicalRemainderAlongLine actionAlongLine canonicalQuadraticAlongLine
    reggeActionRemainder
  ring

/-- The canonical quadratic line has exactly the canonical Regge Hessian as
its second directional derivative. -/
theorem canonicalQuadraticAlongLine_hasSecondDerivAt_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) :
    HasSecondDerivAt (canonicalQuadraticAlongLine K hK ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := by
  change HasSecondDerivAt
    (fun t : ℝ =>
      (1 / 2) * hessianQuadratic (canonicalReggeHessian K hK)
        (linePotential K ξ t))
    (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0
  simpa using
    hessianQuadratic_along_line_hasSecondDerivAt_zero K
      (canonicalReggeHessian K hK) ξ

theorem canonicalQuadraticAlongLine_differentiableAt
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) :
    DifferentiableAt ℝ (canonicalQuadraticAlongLine K hK ξ) t := by
  have hquad :
      canonicalQuadraticAlongLine K hK ξ =
        fun t : ℝ =>
          (hessianQuadratic (canonicalReggeHessian K hK) ξ / 2) * t ^ 2 := by
    funext t
    unfold canonicalQuadraticAlongLine
    rw [hessianQuadratic_linePotential]
    ring
  rw [hquad]
  exact (((differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) t).pow 2).const_mul
    (hessianQuadratic (canonicalReggeHessian K hK) ξ / 2))

theorem canonicalQuadraticAlongLine_hasDerivAt
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) :
    HasDerivAt (canonicalQuadraticAlongLine K hK ξ)
      (t * hessianQuadratic (canonicalReggeHessian K hK) ξ) t := by
  have hquad :
      canonicalQuadraticAlongLine K hK ξ =
        fun t : ℝ =>
          (hessianQuadratic (canonicalReggeHessian K hK) ξ / 2) * t ^ 2 := by
    funext t
    unfold canonicalQuadraticAlongLine
    rw [hessianQuadratic_linePotential]
    ring
  rw [hquad]
  have hpow := ((hasDerivAt_id t).pow 2).const_mul
    (hessianQuadratic (canonicalReggeHessian K hK) ξ / 2)
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hpow

theorem deriv_canonicalQuadraticAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) :
    deriv (canonicalQuadraticAlongLine K hK ξ) t =
      t * hessianQuadratic (canonicalReggeHessian K hK) ξ :=
  (canonicalQuadraticAlongLine_hasDerivAt K hK ξ t).deriv

/-- Equivalent geometric target phrased against the actual derivative of the
canonical quadratic line rather than the simplified scalar formula. -/
def ActionDerivativeTangencyToQuadraticTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasDerivAt
      (fun t : ℝ =>
        deriv (actionAlongLine K hK ξ) t -
          deriv (canonicalQuadraticAlongLine K hK ξ) t)
      0 0

theorem actionDerivativeFirstOrderTangency_of_quadraticTangency
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hTan : ActionDerivativeTangencyToQuadraticTarget K hK) :
    ActionDerivativeFirstOrderTangencyTarget K hK := by
  intro ξ
  have h := hTan ξ
  convert h using 1
  ext t
  rw [deriv_canonicalQuadraticAlongLine K hK ξ t]

/-- Derivative of the conformal hinge length along a fixed conformal line,
defined by the one-variable derivative.  The remaining geometric product-rule
work should compute this explicitly near the flat point. -/
def hingeLineDeriv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) (t : ℝ) : ℝ :=
  deriv (fun s : ℝ =>
    hingeMeasureUnderConformal K hK (linePotential K ξ s) e) t

/-- Derivative of the deficit angle along a fixed conformal line, defined by
the one-variable derivative.  The remaining local cofactor/arccos derivative
work should compute this explicitly near the flat point. -/
def deficitLineDeriv
    (K : Triangulation3D)
    (ξ : VertexPotential K) (e : Fin K.nE) (t : ℝ) : ℝ :=
  deriv (fun s : ℝ => deficitAngle K (linePotential K ξ s) e) t

/-- Second derivative of the conformal hinge length along a fixed conformal
line, expressed as the derivative of `hingeLineDeriv`. -/
def hingeLineSecondDeriv
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) (t : ℝ) : ℝ :=
  deriv (fun s : ℝ => hingeLineDeriv K hK ξ e s) t

/-- Second derivative of the deficit angle along a fixed conformal line,
expressed as the derivative of `deficitLineDeriv`. -/
def deficitLineSecondDeriv
    (K : Triangulation3D)
    (ξ : VertexPotential K) (e : Fin K.nE) (t : ℝ) : ℝ :=
  deriv (fun s : ℝ => deficitLineDeriv K ξ e s) t

/-- Product-rule expression for the derivative of the full Regge action along
a conformal line.  This is the exact finite-sum expression obtained after
differentiating the hinge factor and the deficit factor. -/
def reggeActionProductRuleDerivative
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) : ℝ :=
  ∑ e : Fin K.nE,
    (hingeLineDeriv K hK ξ e t *
        deficitAngle K (linePotential K ξ t) e +
      hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
        deficitLineDeriv K ξ e t)

/-- Derivative of the product-rule expression, before using Schlaefli and the
Cayley-Menger/arccos algebra. -/
def reggeActionSecondProductRuleDerivative
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) : ℝ :=
  ∑ e : Fin K.nE,
    (hingeLineSecondDeriv K hK ξ e t *
        deficitAngle K (linePotential K ξ t) e +
      2 * hingeLineDeriv K hK ξ e t *
        deficitLineDeriv K ξ e t +
      hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
        deficitLineSecondDeriv K ξ e t)

/-- Product-rule target: near the flat point, the derivative of the full action
is the finite sum of hinge-derivative and deficit-derivative terms. -/
def ActionDerivativeProductRuleNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ => deriv (actionAlongLine K hK ξ) t) =ᶠ[nhds (0 : ℝ)]
      fun t : ℝ => reggeActionProductRuleDerivative K hK ξ t

/-- Sufficient differentiability condition for the finite product rule:
each hinge line and each deficit line is differentiable near the flat point. -/
def HingeDeficitLineDifferentiabilityNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ e : Fin K.nE,
        DifferentiableAt ℝ
          (fun s : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ s) e) t ∧
        DifferentiableAt ℝ
          (fun s : ℝ => deficitAngle K (linePotential K ξ s) e) t

/-- Sufficient differentiability condition for differentiating the product-rule
expression once more at the flat point. -/
def HingeDeficitSecondLineDifferentiabilityAtZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (e : Fin K.nE),
    DifferentiableAt ℝ (fun t : ℝ => hingeLineDeriv K hK ξ e t) 0 ∧
      DifferentiableAt ℝ (fun t : ℝ => deficitLineDeriv K ξ e t) 0

theorem hingeLineDeriv_differentiableAt_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    DifferentiableAt ℝ (fun t : ℝ => hingeLineDeriv K hK ξ e t) 0 := by
  unfold hingeLineDeriv hingeMeasureUnderConformal linePotential
  let uv := K.edgeVerts e
  let c : ℝ := (ξ uv.1 + ξ uv.2) / 2
  have hderiv :
      (fun t : ℝ =>
        deriv
          (fun s : ℝ =>
            Real.sqrt (hK.globalSqEdge e) *
              Real.exp ((s * ξ uv.1 + s * ξ uv.2) / 2)) t) =
        fun t : ℝ => Real.sqrt (hK.globalSqEdge e) * c * Real.exp (t * c) := by
    funext t
    have hlin :
        HasDerivAt (fun s : ℝ => (s * ξ uv.1 + s * ξ uv.2) / 2) c t := by
      have h1 : HasDerivAt (fun s : ℝ => s * ξ uv.1) (ξ uv.1) t := by
        simpa using (hasDerivAt_id t).mul_const (ξ uv.1)
      have h2 : HasDerivAt (fun s : ℝ => s * ξ uv.2) (ξ uv.2) t := by
        simpa using (hasDerivAt_id t).mul_const (ξ uv.2)
      simpa [c, add_div] using (h1.add h2).div_const 2
    have hexp :=
      (Real.hasDerivAt_exp ((t * ξ uv.1 + t * ξ uv.2) / 2)).comp t hlin
    have h' :
        HasDerivAt
          (fun s : ℝ =>
            Real.sqrt (hK.globalSqEdge e) *
              Real.exp ((s * ξ uv.1 + s * ξ uv.2) / 2))
          (Real.sqrt (hK.globalSqEdge e) *
            (c * Real.exp ((t * ξ uv.1 + t * ξ uv.2) / 2))) t := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hexp.const_mul (Real.sqrt (hK.globalSqEdge e))
    rw [h'.deriv]
    have hexp_arg : (t * ξ uv.1 + t * ξ uv.2) / 2 = t * c := by
      simp [c]
      ring
    rw [hexp_arg]
    ring
  rw [hderiv]
  fun_prop

def DeficitSecondLineDifferentiabilityAtZeroTarget
    (K : Triangulation3D) : Prop :=
  ∀ (ξ : VertexPotential K) (e : Fin K.nE),
    DifferentiableAt ℝ (fun t : ℝ => deficitLineDeriv K ξ e t) 0

theorem hingeDeficitSecondLineDifferentiability_of_deficit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hDef : DeficitSecondLineDifferentiabilityAtZeroTarget K) :
    HingeDeficitSecondLineDifferentiabilityAtZeroTarget K hK := by
  intro ξ e
  exact ⟨hingeLineDeriv_differentiableAt_zero K hK ξ e, hDef ξ e⟩

theorem hingeLine_contDiffAt_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e) 0 := by
  have hline : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
    rw [contDiffAt_pi]
    intro i
    unfold linePotential
    fun_prop
  have hhinge : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun η : VertexPotential K => hingeMeasureUnderConformal K hK η e)
      (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using
      ReggeActionSmoothness.hingeMeasureUnderConformal_contDiffAt_zero K hK e (⊤ : ℕ∞)
  have hcomp := ContDiffAt.comp (x := (0 : ℝ)) hhinge hline
  simpa [Function.comp_def] using hcomp

theorem deficitLine_contDiffAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t : ℝ => deficitAngle K (linePotential K ξ t) e) 0 := by
  have hline : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
    rw [contDiffAt_pi]
    intro i
    unfold linePotential
    fun_prop
  have hdef : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun η : VertexPotential K => deficitAngle K η e)
      (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using
      ReggeActionSmoothness.deficitAngle_contDiffAt_zero K e (⊤ : ℕ∞)
        hFlat.local_arccos_endpoint_free
  have hcomp := ContDiffAt.comp (x := (0 : ℝ)) hdef hline
  simpa [Function.comp_def] using hcomp

theorem deficitLineDeriv_differentiableAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    DifferentiableAt ℝ (fun t : ℝ => deficitLineDeriv K ξ e t) 0 := by
  unfold deficitLineDeriv
  exact deriv_differentiableAt_of_contDiffAt_top
    (fun t : ℝ => deficitAngle K (linePotential K ξ t) e) 0
    (deficitLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ e)

theorem hingeDeficitSecondLineDifferentiabilityAtZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    HingeDeficitSecondLineDifferentiabilityAtZeroTarget K hK := by
  intro ξ e
  exact ⟨hingeLineDeriv_differentiableAt_zero K hK ξ e,
    deficitLineDeriv_differentiableAt_zero_of_flatConfiguration K hK hFlat ξ e⟩

theorem hingeDeficitLineDifferentiabilityNearZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    HingeDeficitLineDifferentiabilityNearZeroTarget K hK := by
  intro ξ
  rw [Filter.eventually_all]
  intro e
  have hHinge :=
    differentiableAt_eventually_of_contDiffAt_top
      (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e) 0
      (hingeLine_contDiffAt_zero K hK ξ e)
  have hDef :=
    differentiableAt_eventually_of_contDiffAt_top
      (fun t : ℝ => deficitAngle K (linePotential K ξ t) e) 0
      (deficitLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ e)
  filter_upwards [hHinge, hDef] with t htHinge htDef
  exact ⟨htHinge, htDef⟩

theorem actionDerivativeProductRuleNearZero_of_factorDifferentiability
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hDiff : HingeDeficitLineDifferentiabilityNearZeroTarget K hK) :
    ActionDerivativeProductRuleNearZeroTarget K hK := by
  intro ξ
  filter_upwards [hDiff ξ] with t ht
  unfold actionAlongLine reggeAction reggeActionProductRuleDerivative
    hingeLineDeriv deficitLineDeriv
  have hEdge :
      ∀ e : Fin K.nE,
        HasDerivAt
          (fun s : ℝ =>
            hingeMeasureUnderConformal K hK (linePotential K ξ s) e *
              deficitAngle K (linePotential K ξ s) e)
          (deriv
              (fun s : ℝ =>
                hingeMeasureUnderConformal K hK (linePotential K ξ s) e) t *
              deficitAngle K (linePotential K ξ t) e +
            hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
              deriv (fun s : ℝ => deficitAngle K (linePotential K ξ s) e) t) t := by
    intro e
    have hL := (ht e).1.hasDerivAt
    have hD := (ht e).2.hasDerivAt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hL.mul hD
  have hsum :=
    HasDerivAt.sum
      (u := Finset.univ)
      (A := fun e s =>
        hingeMeasureUnderConformal K hK (linePotential K ξ s) e *
          deficitAngle K (linePotential K ξ s) e)
      (A' := fun e =>
        deriv
            (fun s : ℝ =>
              hingeMeasureUnderConformal K hK (linePotential K ξ s) e) t *
            deficitAngle K (linePotential K ξ t) e +
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deriv (fun s : ℝ => deficitAngle K (linePotential K ξ s) e) t)
      (x := t)
      (fun e _ => hEdge e)
  rw [show
      (fun t : ℝ =>
        ∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitAngle K (linePotential K ξ t) e) =
        (∑ e : Fin K.nE,
          fun s : ℝ =>
            hingeMeasureUnderConformal K hK (linePotential K ξ s) e *
              deficitAngle K (linePotential K ξ s) e) by
      funext s
      simp [Finset.sum_apply]]
  simpa using hsum.deriv

theorem actionDerivativeProductRuleNearZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    ActionDerivativeProductRuleNearZeroTarget K hK :=
  actionDerivativeProductRuleNearZero_of_factorDifferentiability K hK
    (hingeDeficitLineDifferentiabilityNearZero_of_flatConfiguration K hK hFlat)

theorem productRule_hasDerivAt_secondProduct
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSecond : HingeDeficitSecondLineDifferentiabilityAtZeroTarget K hK)
    (ξ : VertexPotential K) :
    HasDerivAt (reggeActionProductRuleDerivative K hK ξ)
      (reggeActionSecondProductRuleDerivative K hK ξ 0) 0 := by
  unfold reggeActionProductRuleDerivative reggeActionSecondProductRuleDerivative
  have hEdge :
      ∀ e : Fin K.nE,
        HasDerivAt
          (fun t : ℝ =>
            hingeLineDeriv K hK ξ e t *
                deficitAngle K (linePotential K ξ t) e +
              hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
                deficitLineDeriv K ξ e t)
          (hingeLineSecondDeriv K hK ξ e 0 *
                deficitAngle K (linePotential K ξ 0) e +
              2 * hingeLineDeriv K hK ξ e 0 *
                deficitLineDeriv K ξ e 0 +
              hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
                deficitLineSecondDeriv K ξ e 0) 0 := by
    intro e
    have hHinge0 : DifferentiableAt ℝ
        (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e) 0 :=
      (hingeLine_contDiffAt_zero K hK ξ e).differentiableAt (by simp)
    have hDef0 : DifferentiableAt ℝ
        (fun t : ℝ => deficitAngle K (linePotential K ξ t) e) 0 :=
      (deficitLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ e).differentiableAt
        (by simp)
    have hHingeDeriv : HasDerivAt (fun t : ℝ => hingeLineDeriv K hK ξ e t)
        (hingeLineSecondDeriv K hK ξ e 0) 0 := by
      simpa [hingeLineSecondDeriv] using (hSecond ξ e).1.hasDerivAt
    have hDefDeriv : HasDerivAt (fun t : ℝ => deficitLineDeriv K ξ e t)
        (deficitLineSecondDeriv K ξ e 0) 0 := by
      simpa [deficitLineSecondDeriv] using (hSecond ξ e).2.hasDerivAt
    have hDefLine : HasDerivAt
        (fun t : ℝ => deficitAngle K (linePotential K ξ t) e)
        (deficitLineDeriv K ξ e 0) 0 := by
      simpa [deficitLineDeriv] using hDef0.hasDerivAt
    have hHingeLine : HasDerivAt
        (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e)
        (hingeLineDeriv K hK ξ e 0) 0 := by
      simpa [hingeLineDeriv] using hHinge0.hasDerivAt
    have h1 := hHingeDeriv.mul hDefLine
    have h2 := hHingeLine.mul hDefDeriv
    have hsum := h1.add h2
    convert hsum using 1
    · ring
  have hsum :=
    HasDerivAt.sum
      (u := Finset.univ)
      (A := fun e t =>
        hingeLineDeriv K hK ξ e t *
            deficitAngle K (linePotential K ξ t) e +
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t)
      (A' := fun e =>
        hingeLineSecondDeriv K hK ξ e 0 *
            deficitAngle K (linePotential K ξ 0) e +
          2 * hingeLineDeriv K hK ξ e 0 *
            deficitLineDeriv K ξ e 0 +
          hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
            deficitLineSecondDeriv K ξ e 0)
      (x := 0)
      (fun e _ => hEdge e)
  rw [show
      (fun t : ℝ =>
        ∑ e : Fin K.nE,
          (hingeLineDeriv K hK ξ e t *
              deficitAngle K (linePotential K ξ t) e +
            hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
              deficitLineDeriv K ξ e t)) =
        (∑ e : Fin K.nE,
          fun t : ℝ =>
            hingeLineDeriv K hK ξ e t *
                deficitAngle K (linePotential K ξ t) e +
              hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
                deficitLineDeriv K ξ e t) by
      funext t
      simp [Finset.sum_apply]]
  simpa using hsum

/-- Final geometric identity after the second product rule: the second
product-rule expression at the flat point is the canonical Hessian quadratic
form. -/
def SecondProductRuleEqualsCanonicalHessianTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    reggeActionSecondProductRuleDerivative K hK ξ 0 =
      hessianQuadratic (canonicalReggeHessian K hK) ξ

/-- Second-order Schläfli identity along a conformal line.  After flatness kills
the explicit `deficitAngle(0)` term in the second product rule, this identity
cancels one copy of the mixed hinge/deficit derivative against the
length-weighted second deficit derivative. -/
def SecondSchlaefliAlongLineTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_hFlat : FlatConfiguration K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ e : Fin K.nE,
      (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
        hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
          deficitLineSecondDeriv K ξ e 0)) = 0

/-- The surviving mixed term after second-order Schläfli cancellation is the
canonical incidence Hessian quadratic form. -/
def MixedHingeDeficitCanonicalHessianTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ e : Fin K.nE,
      (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0)) =
        hessianQuadratic (canonicalReggeHessian K hK) ξ

theorem hingeLineDeriv_zero_eq_directional
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    hingeLineDeriv K hK ξ e 0 =
      ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e := by
  unfold hingeLineDeriv
  have h :=
    ReggeActionFirstVariation.hingeMeasureUnderConformal_hasDerivAt_line_zero
      K hK ξ e
  have h' : HasDerivAt
      (fun s : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ s) e)
      (ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e) 0 := by
    convert h using 1
  exact h'.deriv

theorem deficitLineDeriv_zero_eq_deficitPackage
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (ξ : VertexPotential K) (e : Fin K.nE) :
    deficitLineDeriv K ξ e 0 = D.deficitDeriv ξ e := by
  unfold deficitLineDeriv
  have h := D.deficit_hasDerivAt ξ e
  have h' : HasDerivAt
      (fun s : ℝ => deficitAngle K (linePotential K ξ s) e)
      (D.deficitDeriv ξ e) 0 := by
    convert h using 1
  exact h'.deriv

/-- Deficit-package form of the surviving mixed hinge/deficit target.  This
removes the opaque `deriv` wrappers from `MixedHingeDeficitCanonicalHessianTarget`
and exposes the exact first-variation deficit derivative that must be identified
with the canonical Hessian. -/
def MixedHingeDeficitFromDeficitPackageTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ e : Fin K.nE,
      ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e *
        D.deficitDeriv ξ e) =
      hessianQuadratic (canonicalReggeHessian K hK) ξ

/-- Dirichlet-energy form of the mixed target.  Since the canonical Hessian
quadratic has already been proved equal to the canonical graph Dirichlet energy,
this is the same remaining identity with the right-hand side in energy form. -/
def MixedHingeDeficitDirichletTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ e : Fin K.nE,
      ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e *
        D.deficitDeriv ξ e) =
      canonicalDirichletEnergy K hK ξ

theorem mixedHingeDeficitFromDeficitPackage_of_dirichlet
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hDir : MixedHingeDeficitDirichletTarget K hK D) :
    MixedHingeDeficitFromDeficitPackageTarget K hK D := by
  intro ξ
  rw [hDir ξ]
  exact (canonicalReggeHessian_quadratic_eq_dirichlet K hK ξ).symm

/-- Edge-stencil form of the mixed target.  This is the form meant for the
canonical periodic Freudenthal branch, where the abstract Dirichlet energy has
already been identified with the concrete periodic edge stencil. -/
def MixedHingeDeficitEdgeStencilTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    (∑ e : Fin K.nE,
      ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e *
        D.deficitDeriv ξ e) =
      canonicalEdgeStencilDirichletEnergy K hK ξ

theorem mixedHingeDeficitDirichlet_of_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    MixedHingeDeficitDirichletTarget K hK D := by
  intro ξ
  rw [hEdge ξ, hStencil ξ]

theorem mixedHingeDeficitFromDeficitPackage_of_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    MixedHingeDeficitFromDeficitPackageTarget K hK D :=
  mixedHingeDeficitFromDeficitPackage_of_dirichlet K hK D
    (mixedHingeDeficitDirichlet_of_edgeStencil K hK D hEdge hStencil)

theorem mixedHingeDeficitCanonicalHessian_of_deficitPackage
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hMixed : MixedHingeDeficitFromDeficitPackageTarget K hK D) :
    MixedHingeDeficitCanonicalHessianTarget K hK := by
  intro ξ
  calc
    (∑ e : Fin K.nE,
      (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0))
        = ∑ e : Fin K.nE,
            ReggeActionFirstVariation.hingeMeasureDirectionalDeriv K hK ξ e *
              D.deficitDeriv ξ e := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [hingeLineDeriv_zero_eq_directional K hK ξ e,
              deficitLineDeriv_zero_eq_deficitPackage K hK D ξ e]
    _ = hessianQuadratic (canonicalReggeHessian K hK) ξ := hMixed ξ

theorem mixedHingeDeficitCanonicalHessian_of_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    MixedHingeDeficitCanonicalHessianTarget K hK :=
  mixedHingeDeficitCanonicalHessian_of_deficitPackage K hK D
    (mixedHingeDeficitFromDeficitPackage_of_edgeStencil K hK D hEdge hStencil)

/-- Stationarity form of the second-order Schläfli target.  A later local
geometric proof should show that the weighted deficit-derivative sum is
stationary at the flat point, e.g. by differentiating the Schläfli cancellation
through the conformal line. -/
def WeightedDeficitDerivativeStationaryTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_hFlat : FlatConfiguration K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    HasDerivAt
      (fun t : ℝ =>
        ∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t)
      0 0

/-- Stronger near-flat Schläfli form: the weighted deficit-derivative sum
vanishes in a puncture-free neighbourhood of the flat point.  This is more than
the second-order proof needs, but it is the natural target produced by a
near-zero Schläfli cancellation theorem for the conformal line. -/
def WeightedDeficitDerivativeEventuallyZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_hFlat : FlatConfiguration K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ =>
      ∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
          deficitLineDeriv K ξ e t) =ᶠ[nhds (0 : ℝ)]
      fun _t : ℝ => 0

theorem weightedDeficitDerivativeStationary_of_eventuallyZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat) :
    WeightedDeficitDerivativeStationaryTarget K hK hFlat := by
  intro ξ
  have hconst : HasDerivAt (fun _t : ℝ => (0 : ℝ)) 0 0 :=
    hasDerivAt_const 0 0
  exact hconst.congr_of_eventuallyEq (hZero ξ)

/-- Strongest geometric Schläfli form: the weighted deficit-derivative sum
vanishes identically along the conformal line (for every parameter value, not
just near the flat point).  This is the direct consequence of the classical
Schläfli differential identity `∑_{e ∈ τ} ℓ_e dθ_{e,τ} = 0` applied at
every parameter `t` and summed over all tetrahedra: the per-tetrahedron
identities cancel the `∑ h δ'` term in the Regge first variation, leaving
`S'(t) = ∑ δ h'`, and therefore `V(t) = ∑ h δ' = 0`.

Proving this target closes the full `WeightedDeficitDerivativeStationaryTarget`
and all its downstream consumers (typed-edge targets, per-displacement-class
targets, etc.) without any per-class decomposition. -/
def ConformalSchlaefliAlongLineTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (t : ℝ),
    ∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
        deficitLineDeriv K ξ e t = 0

/-- Local along-line Schläfli identity in actual derivative form.  At every
parameter `t` on a conformal line and every tetrahedron `τ`, the local
length-weighted sum of actual dihedral-angle derivatives vanishes.

This is the tetrahedral calculus content of Schläfli away from the flat point:
it is the same identity as `local_conformal_schlaefli_cancellation`, but with
the tetrahedron evaluated at `linePotential K ξ t` and with the actual line
derivative `deriv (...) t` rather than the flat-point closed form. -/
def LocalConformalSchlaefliAlongLineTarget
    (K : Triangulation3D) : Prop :=
  ∀ (ξ : VertexPotential K) (t : ℝ) (τ : Fin K.nT),
    (∑ f : Fin 6,
      Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
        deriv
          (fun s : ℝ =>
            tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) = 0

/-- Global expansion of `∑_e h_e δ'_e` into the local tetrahedral Schläfli
sums at an arbitrary point on the conformal line.

This target contains the non-flat incidence/reindexing and derivative-of-deficit
bookkeeping:
* expand `deficitLineDeriv` as minus the sum of actual local angle derivatives;
* replace global hinge lengths by matching local conformal edge lengths for
  each incident tetrahedral edge slot;
* reindex global edge incidence to local tetrahedral edge slots. -/
def ConformalSchlaefliAlongLineExpansionTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (t : ℝ),
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
        deficitLineDeriv K ξ e t) =
      - ∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
              deriv
                (fun s : ℝ =>
                  tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t

/-- Local near-flat Schläfli identity along conformal lines.  This is the
right local target for the Hessian proof: it only asks for the conformal line
near `t = 0`, where the flat nondegenerate chart supplies the intended
tetrahedral domain. -/
def LocalConformalSchlaefliNearZeroTarget
    (K : Triangulation3D) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ τ : Fin K.nT,
        (∑ f : Fin 6,
          Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
            deriv
              (fun s : ℝ =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) = 0

/-- Non-flat local angle chain rule in squared-edge coordinates.  At a nearby
line parameter, each actual local dihedral derivative is the closed-form
squared-edge gradient paired with the derivative of the six conformal
squared-edge coordinates. -/
def LocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget
    (K : Triangulation3D) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ τ : Fin K.nT, ∀ f : Fin 6,
        deriv
          (fun s : ℝ =>
            tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t =
          ∑ k : Fin 6,
            DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
              (conformalTetSqEdges K (linePotential K ξ t) τ) f k *
              deriv
                (fun s : ℝ =>
                  conformalLocalSqEdge K (linePotential K ξ s) τ k) t

/-- Closed-form Schläfli zero at the deformed squared-edge tuple.  This is the
algebraic non-flat identity once the conformal tetrahedron is known to remain
inside the nondegenerate cone near `t = 0`. -/
def LocalConformalSchlaefliClosedFormZeroNearZeroTarget
    (K : Triangulation3D) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ τ : Fin K.nT, ∀ k : Fin 6,
        (∑ f : Fin 6,
          Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
            DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
              (conformalTetSqEdges K (linePotential K ξ t) τ) f k) = 0

theorem conformalLocalSqEdge_line_pos
    (K : Triangulation3D) (ξ : VertexPotential K)
    (t : ℝ) (τ : Fin K.nT) (f : Fin 6) :
    0 < conformalLocalSqEdge K (linePotential K ξ t) τ f := by
  unfold conformalLocalSqEdge linePotential
  exact mul_pos ((K.tet τ).sqEdge_pos f) (Real.exp_pos _)

theorem cm3_conformalTetSqEdges_line_pos_eventually
    (K : Triangulation3D) (ξ : VertexPotential K) (τ : Fin K.nT) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      CayleyMengerPolynomial.cm3 (conformalTetSqEdges K (linePotential K ξ t) τ) > 0 := by
  have hline : ContDiffAt ℝ (0 : ℕ∞)
      (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
    rw [contDiffAt_pi]
    intro i
    unfold linePotential
    fun_prop
  have htet : ContDiffAt ℝ (0 : ℕ∞)
      (fun η : VertexPotential K => conformalTetSqEdges K η τ)
      (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using
      (ReggeActionSmoothness.conformalTetSqEdges_contDiff K τ (0 : ℕ∞)).contDiffAt
  have htetLine : ContDiffAt ℝ (0 : ℕ∞)
      (fun t : ℝ => conformalTetSqEdges K (linePotential K ξ t) τ) (0 : ℝ) := by
    simpa [Function.comp_def] using
      (ContDiffAt.comp (x := (0 : ℝ)) htet hline)
  have hcm : ContinuousAt
      (fun t : ℝ =>
        CayleyMengerPolynomial.cm3 (conformalTetSqEdges K (linePotential K ξ t) τ))
      (0 : ℝ) := by
    have hbase : ContinuousAt CayleyMengerPolynomial.cm3
        (conformalTetSqEdges K (linePotential K ξ 0) τ) :=
      (CayleyMengerPolynomial.cm3_contDiff (0 : ℕ∞)).continuous.continuousAt
    exact ContinuousAt.comp
      (f := fun t : ℝ => conformalTetSqEdges K (linePotential K ξ t) τ)
      (g := CayleyMengerPolynomial.cm3)
      (x := (0 : ℝ))
      hbase htetLine.continuousAt
  have hpos0 :
      (0 : ℝ) <
        CayleyMengerPolynomial.cm3 (conformalTetSqEdges K (linePotential K ξ 0) τ) := by
    simpa [linePotential_zero K ξ, ReggeActionSmoothness.conformalTetSqEdges_zero K τ]
      using (K.tet τ).cm_pos
  exact hcm.eventually (Ioi_mem_nhds hpos0)

theorem localConformalSchlaefliClosedFormZeroNearZero
    (K : Triangulation3D) :
    LocalConformalSchlaefliClosedFormZeroNearZeroTarget K := by
  intro ξ
  rw [Filter.eventually_all]
  intro τ
  filter_upwards [cm3_conformalTetSqEdges_line_pos_eventually K ξ τ] with t hcm
  intro k
  let T : ReggeRigorousFoundation.NonDegenerateTet :=
    { sqEdge := conformalTetSqEdges K (linePotential K ξ t) τ
      sqEdge_pos := by
        intro f
        exact conformalLocalSqEdge_line_pos K ξ t τ f
      cm_pos := hcm }
  have hS := SchlaefliTetrahedronProof.tetraSchlaefliSixEdgeClosedForm T k
  simpa [T, SchlaefliTetrahedronProof.dihedralClosedDerivSq, conformalTetSqEdges]
    using hS

theorem dihedralCos3Sq_conformalTetSqEdges_line_endpoint_free_eventually
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (ξ : VertexPotential K) (τ : Fin K.nT) (f : Fin 6) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      DihedralCayleyMenger.dihedralCos3Sq
        (conformalTetSqEdges K (linePotential K ξ t) τ) f ≠ -1 ∧
      DihedralCayleyMenger.dihedralCos3Sq
        (conformalTetSqEdges K (linePotential K ξ t) τ) f ≠ 1 := by
  have hline : ContDiffAt ℝ (0 : ℕ∞)
      (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
    rw [contDiffAt_pi]
    intro i
    unfold linePotential
    fun_prop
  have hcosEta : ContinuousAt
      (fun η : VertexPotential K =>
        DihedralCayleyMenger.dihedralCos3Sq (conformalTetSqEdges K η τ) f)
      (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using
      ReggeActionSmoothness.dihedralCos3Sq_conformal_continuousAt_zero K τ f
  have hcos : ContinuousAt
      (fun t : ℝ =>
        DihedralCayleyMenger.dihedralCos3Sq
          (conformalTetSqEdges K (linePotential K ξ t) τ) f)
      (0 : ℝ) :=
    ContinuousAt.comp
      (f := fun t : ℝ => linePotential K ξ t)
      (g := fun η : VertexPotential K =>
        DihedralCayleyMenger.dihedralCos3Sq (conformalTetSqEdges K η τ) f)
      (x := (0 : ℝ))
      hcosEta hline.continuousAt
  have hneg0 :
      DihedralCayleyMenger.dihedralCos3Sq
        (conformalTetSqEdges K (linePotential K ξ 0) τ) f ≠ -1 := by
    simpa [linePotential_zero K ξ, ReggeActionSmoothness.conformalTetSqEdges_zero K τ]
      using (hFlat.local_arccos_endpoint_free τ f).1
  have hpos0 :
      DihedralCayleyMenger.dihedralCos3Sq
        (conformalTetSqEdges K (linePotential K ξ 0) τ) f ≠ 1 := by
    simpa [linePotential_zero K ξ, ReggeActionSmoothness.conformalTetSqEdges_zero K τ]
      using (hFlat.local_arccos_endpoint_free τ f).2
  filter_upwards [hcos.eventually_ne hneg0, hcos.eventually_ne hpos0] with t hneg hpos
  exact ⟨hneg, hpos⟩

theorem conformalTetSqEdges_hasDerivAt_line
    (K : Triangulation3D) (ξ : VertexPotential K)
    (t : ℝ) (τ : Fin K.nT) :
    HasDerivAt
      (fun s : ℝ => conformalTetSqEdges K (linePotential K ξ s) τ)
      (fun k : Fin 6 =>
        deriv
          (fun s : ℝ =>
            conformalLocalSqEdge K (linePotential K ξ s) τ k) t) t := by
  rw [hasDerivAt_pi]
  intro k
  have hdiff : DifferentiableAt ℝ
      (fun s : ℝ => conformalLocalSqEdge K (linePotential K ξ s) τ k) t := by
    unfold conformalLocalSqEdge linePotential
    fun_prop
  simpa [conformalTetSqEdges] using hdiff.hasDerivAt

theorem localConformalSchlaefliAngleSqEdgeChainRuleNearZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    LocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget K := by
  intro ξ
  rw [Filter.eventually_all]
  intro τ
  rw [Filter.eventually_all]
  intro f
  filter_upwards
    [cm3_conformalTetSqEdges_line_pos_eventually K ξ τ,
      dihedralCos3Sq_conformalTetSqEdges_line_endpoint_free_eventually K hK hFlat ξ τ f]
    with t hcm hEndpoint
  let T : ReggeRigorousFoundation.NonDegenerateTet :=
    { sqEdge := conformalTetSqEdges K (linePotential K ξ t) τ
      sqEdge_pos := by
        intro k
        exact conformalLocalSqEdge_line_pos K ξ t τ k
      cm_pos := hcm }
  let F : CayleyMengerPolynomial.SqEdges → ℝ :=
    fun a => DihedralDerivatives.dihedralAngle3Sq a f
  let v : CayleyMengerPolynomial.SqEdges :=
    fun k : Fin 6 =>
      deriv
        (fun s : ℝ =>
          conformalLocalSqEdge K (linePotential K ξ s) τ k) t
  have hAngle : ContDiffAt ℝ 1 F T.sqEdge := by
    simpa [F, T] using
      ReggeActionFirstVariation.dihedralAngle3Sq_contDiffAt_nonDegenerate
        T f 1 hEndpoint
  have hDiff : DifferentiableAt ℝ F T.sqEdge :=
    hAngle.differentiableAt (by simp)
  have hF : HasFDerivAt F (fderiv ℝ F T.sqEdge) T.sqEdge :=
    hDiff.hasFDerivAt
  have hgamma : HasDerivAt
      (fun s : ℝ => conformalTetSqEdges K (linePotential K ξ s) τ) v t := by
    simpa [v] using conformalTetSqEdges_hasDerivAt_line K ξ t τ
  have hcomp := HasFDerivAt.comp_hasDerivAt
    (x := t)
    (f := fun s : ℝ => conformalTetSqEdges K (linePotential K ξ s) τ)
    (l := F)
    hF hgamma
  have hvalue :
      (fderiv ℝ F T.sqEdge) v =
        ∑ k : Fin 6,
          DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
            (conformalTetSqEdges K (linePotential K ξ t) τ) f k *
            deriv
              (fun s : ℝ =>
                conformalLocalSqEdge K (linePotential K ξ s) τ k) t := by
    calc
      (fderiv ℝ F T.sqEdge) v
          = ∑ k : Fin 6,
              v k * (fderiv ℝ F T.sqEdge)
                (Pi.single (M := fun _ : Fin 6 => ℝ) k (1 : ℝ)) := by
            exact ReggeActionFirstVariation.continuousLinearMap_apply_eq_sum_single
              (fderiv ℝ F T.sqEdge) v
      _ = ∑ k : Fin 6,
          DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
            (conformalTetSqEdges K (linePotential K ξ t) τ) f k *
            deriv
              (fun s : ℝ =>
                conformalLocalSqEdge K (linePotential K ξ s) τ k) t := by
            refine Finset.sum_congr rfl ?_
            intro k _
            have hcoord :=
              ReggeActionFirstVariation.fderiv_dihedralAngle3Sq_apply_single
                T f k hEndpoint
            simp [F, T, v, hcoord, SchlaefliTetrahedronProof.dihedralClosedDerivSq,
              mul_comm]
  rw [hvalue] at hcomp
  simpa [F, Function.comp_def, tetDihedralAngleUnderConformal] using hcomp.deriv

theorem localConformalSchlaefliNearZero_of_sqEdgeChainRule_and_closedFormZero
    (K : Triangulation3D)
    (hChain : LocalConformalSchlaefliAngleSqEdgeChainRuleNearZeroTarget K)
    (hZero : LocalConformalSchlaefliClosedFormZeroNearZeroTarget K) :
    LocalConformalSchlaefliNearZeroTarget K := by
  intro ξ
  filter_upwards [hChain ξ, hZero ξ] with t hChain_t hZero_t
  intro τ
  calc
    (∑ f : Fin 6,
      Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
        deriv
          (fun s : ℝ =>
            tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t)
        =
      ∑ f : Fin 6,
        Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
          (∑ k : Fin 6,
            DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
              (conformalTetSqEdges K (linePotential K ξ t) τ) f k *
              deriv
                (fun s : ℝ =>
                  conformalLocalSqEdge K (linePotential K ξ s) τ k) t) := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [hChain_t τ f]
    _ =
      ∑ k : Fin 6,
        deriv
          (fun s : ℝ =>
            conformalLocalSqEdge K (linePotential K ξ s) τ k) t *
          (∑ f : Fin 6,
            Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
              DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
                (conformalTetSqEdges K (linePotential K ξ t) τ) f k) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro f _
          ring
    _ = ∑ k : Fin 6,
        deriv
          (fun s : ℝ =>
            conformalLocalSqEdge K (linePotential K ξ s) τ k) t * 0 := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hZero_t τ k]
    _ = 0 := by simp

/-- Near-flat global expansion of `∑_e h_e δ'_e` into local tetrahedral
Schläfli sums.  This is the local-in-`t` version of
`ConformalSchlaefliAlongLineExpansionTarget`, and is sufficient for
`WeightedDeficitDerivativeEventuallyZeroTarget`. -/
def ConformalSchlaefliNearZeroExpansionTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ =>
      ∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
          deficitLineDeriv K ξ e t) =ᶠ[nhds (0 : ℝ)]
      (fun t : ℝ =>
        - ∑ τ : Fin K.nT,
            ∑ f : Fin 6,
              Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
                deriv
                  (fun s : ℝ =>
                    tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t)

/-- Local dihedral-angle line differentiability near the flat point.  This is
the analytic input needed to expand the derivative of a deficit angle into the
finite sum of derivatives of its incident local dihedral angles. -/
def LocalDihedralAngleLineDifferentiabilityNearZeroTarget
    (K : Triangulation3D) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ τ : Fin K.nT, ∀ f : Fin 6,
        DifferentiableAt ℝ
          (fun s : ℝ =>
            tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t

theorem tetDihedralAngleUnderConformal_line_contDiffAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (ξ : VertexPotential K) (τ : Fin K.nT) (f : Fin 6) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun t : ℝ =>
        tetDihedralAngleUnderConformal K (linePotential K ξ t) τ f) 0 := by
  have hline : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
    rw [contDiffAt_pi]
    intro i
    unfold linePotential
    fun_prop
  have hangle : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun η : VertexPotential K => tetDihedralAngleUnderConformal K η τ f)
      (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using
      ReggeActionSmoothness.tetDihedralAngleUnderConformal_contDiffAt_zero
        K τ f (⊤ : ℕ∞) (hFlat.local_arccos_endpoint_free τ f)
  have hcomp := ContDiffAt.comp (x := (0 : ℝ)) hangle hline
  simpa [Function.comp_def] using hcomp

theorem localDihedralAngleLineDifferentiabilityNearZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    LocalDihedralAngleLineDifferentiabilityNearZeroTarget K := by
  intro ξ
  rw [Filter.eventually_all]
  intro τ
  rw [Filter.eventually_all]
  intro f
  exact differentiableAt_eventually_of_contDiffAt_top
    (fun t : ℝ => tetDihedralAngleUnderConformal K (linePotential K ξ t) τ f)
    0
    (tetDihedralAngleUnderConformal_line_contDiffAt_zero_of_flatConfiguration
      K hK hFlat ξ τ f)

theorem hingeMeasureUnderConformal_eq_local_sqrt_of_incident
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (e : Fin K.nE) (τ : Fin K.nT) (f : Fin 6)
    (h : K.edgeInTet e τ = some f) :
    hingeMeasureUnderConformal K hK ξ e =
      Real.sqrt (conformalLocalSqEdge K ξ τ f) := by
  unfold hingeMeasureUnderConformal conformalLocalSqEdge
  let ev := K.edgeVerts e
  let fv := ReggeRigorousFoundation.edgeVertices f
  have hsq : (K.tet τ).sqEdge f = hK.globalSqEdge e :=
    hK.local_sqEdge_eq_global e τ f h
  have hverts := hK.edgeInTet_vertices e τ f h
  have hexp_arg :
      ξ (K.tetVerts τ fv.1) + ξ (K.tetVerts τ fv.2) =
        ξ ev.1 + ξ ev.2 := by
    dsimp [ev, fv] at hverts ⊢
    rcases hverts with hdir | hrev
    · rw [hdir.1, hdir.2]
    · rw [hrev.1, hrev.2]
      ring
  rw [hsq]
  change Real.sqrt (hK.globalSqEdge e) * Real.exp ((ξ ev.1 + ξ ev.2) / 2) =
    Real.sqrt
      (hK.globalSqEdge e *
        Real.exp (ξ (K.tetVerts τ fv.1) + ξ (K.tetVerts τ fv.2)))
  rw [hexp_arg]
  have hglobal_nonneg : 0 ≤ hK.globalSqEdge e := by
    rw [← hsq]
    exact le_of_lt ((K.tet τ).sqEdge_pos f)
  rw [Real.sqrt_mul hglobal_nonneg]
  have hsqrt_exp :
      Real.sqrt (Real.exp (ξ ev.1 + ξ ev.2)) =
        Real.exp ((ξ ev.1 + ξ ev.2) / 2) := by
    have hsquare :
        Real.exp (ξ ev.1 + ξ ev.2) =
          (Real.exp ((ξ ev.1 + ξ ev.2) / 2)) ^ (2 : ℕ) := by
      have hadd :
          (ξ ev.1 + ξ ev.2) / 2 + (ξ ev.1 + ξ ev.2) / 2 =
            ξ ev.1 + ξ ev.2 := by
        ring
      rw [pow_two, ← Real.exp_add]
      rw [hadd]
    rw [hsquare, Real.sqrt_sq_eq_abs]
    exact abs_of_pos (Real.exp_pos _)
  rw [hsqrt_exp]

theorem incidenceEdgeSlotPartition_edge_sum_for_tet_conformal
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (P : ReggeActionFirstVariation.IncidenceEdgeSlotPartition K hK)
    (ξ : VertexPotential K)
    (w : Fin K.nT → Fin 6 → ℝ) (τ : Fin K.nT) :
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK ξ e *
        (match K.edgeInTet e τ with
        | none => 0
        | some f => w τ f)) =
      ∑ f : Fin 6, Real.sqrt (conformalLocalSqEdge K ξ τ f) * w τ f := by
  calc
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK ξ e *
        (match K.edgeInTet e τ with
        | none => 0
        | some f => w τ f))
        =
      ∑ e : Fin K.nE,
        ∑ f : Fin 6,
          if K.edgeInTet e τ = some f then
            hingeMeasureUnderConformal K hK ξ e * w τ f
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro e _
          cases h : K.edgeInTet e τ with
          | none =>
              simp
          | some f0 =>
              simp
    _ = ∑ f : Fin 6,
        ∑ e : Fin K.nE,
          if K.edgeInTet e τ = some f then
            hingeMeasureUnderConformal K hK ξ e * w τ f
          else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ f : Fin 6,
        hingeMeasureUnderConformal K hK ξ (P.localEdgeOf τ f) * w τ f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          have hsum := Finset.sum_eq_single
            (s := Finset.univ)
            (f := fun e : Fin K.nE =>
              (if K.edgeInTet e τ = some f then
                hingeMeasureUnderConformal K hK ξ e * w τ f
              else 0 : ℝ))
            (P.localEdgeOf τ f) ?_ ?_
          · simpa [P.localEdgeOf_incident τ f] using hsum
          · intro e _ he_ne
            have hnot : K.edgeInTet e τ ≠ some f := by
              intro h
              exact he_ne ((P.edgeInTet_iff e τ f).1 h)
            simp [hnot]
          · intro hnot_mem
            exact (hnot_mem (Finset.mem_univ _)).elim
    _ = ∑ f : Fin 6, Real.sqrt (conformalLocalSqEdge K ξ τ f) * w τ f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [hingeMeasureUnderConformal_eq_local_sqrt_of_incident
            K hK ξ (P.localEdgeOf τ f) τ f (P.localEdgeOf_incident τ f)]

theorem incidenceEdgeSlotPartition_sum_match_conformal
    {K : Triangulation3D} {hK : IncidenceConsistent K}
    (P : ReggeActionFirstVariation.IncidenceEdgeSlotPartition K hK)
    (ξ : VertexPotential K)
    (w : Fin K.nT → Fin 6 → ℝ) :
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK ξ e *
        (∑ τ : Fin K.nT,
          match K.edgeInTet e τ with
          | none => 0
          | some f => w τ f)) =
      ∑ τ : Fin K.nT,
        ∑ f : Fin 6,
          Real.sqrt (conformalLocalSqEdge K ξ τ f) * w τ f := by
  calc
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK ξ e *
        (∑ τ : Fin K.nT,
          match K.edgeInTet e τ with
          | none => 0
          | some f => w τ f))
        =
      ∑ e : Fin K.nE,
        ∑ τ : Fin K.nT,
          hingeMeasureUnderConformal K hK ξ e *
            (match K.edgeInTet e τ with
            | none => 0
            | some f => w τ f) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [Finset.mul_sum]
    _ = ∑ τ : Fin K.nT,
        ∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK ξ e *
            (match K.edgeInTet e τ with
            | none => 0
            | some f => w τ f) := by
          rw [Finset.sum_comm]
    _ = ∑ τ : Fin K.nT,
        ∑ f : Fin 6,
          Real.sqrt (conformalLocalSqEdge K ξ τ f) * w τ f := by
          refine Finset.sum_congr rfl ?_
          intro τ _
          exact incidenceEdgeSlotPartition_edge_sum_for_tet_conformal P ξ w τ

theorem deficitLineDeriv_eq_neg_sum_local_nearZero
    (K : Triangulation3D)
    (hDiff : LocalDihedralAngleLineDifferentiabilityNearZeroTarget K)
    (ξ : VertexPotential K) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∀ e : Fin K.nE,
        deficitLineDeriv K ξ e t =
          - ∑ τ : Fin K.nT,
              match K.edgeInTet e τ with
              | none => 0
              | some f =>
                  deriv
                    (fun s : ℝ =>
                      tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t := by
  filter_upwards [hDiff ξ] with t ht e
  unfold deficitLineDeriv deficitAngle localDeficitAngleContribution
  have hlocal :
      ∀ τ : Fin K.nT,
        HasDerivAt
          (fun s : ℝ =>
            match K.edgeInTet e τ with
            | none => 0
            | some f =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f)
          (match K.edgeInTet e τ with
            | none => 0
            | some f =>
                deriv
                  (fun s : ℝ =>
                    tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) t := by
    intro τ
    cases h : K.edgeInTet e τ with
    | none =>
        simpa [h] using (hasDerivAt_const t (0 : ℝ))
    | some f =>
        simpa [h] using (ht τ f).hasDerivAt
  have hsum : HasDerivAt
      (fun s : ℝ =>
        ∑ τ : Fin K.nT,
          match K.edgeInTet e τ with
          | none => 0
          | some f =>
              tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f)
      (∑ τ : Fin K.nT,
        match K.edgeInTet e τ with
        | none => 0
        | some f =>
            deriv
              (fun s : ℝ =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) t := by
    have hsum' :=
      HasDerivAt.sum
        (u := Finset.univ)
        (A := fun τ s =>
          match K.edgeInTet e τ with
          | none => 0
          | some f =>
              tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f)
        (A' := fun τ =>
          match K.edgeInTet e τ with
          | none => 0
          | some f =>
              deriv
                (fun s : ℝ =>
                  tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t)
        (x := t)
        (fun τ _ => hlocal τ)
    convert hsum' using 1
    ext s
    simp [Finset.sum_apply]
  have hconst : HasDerivAt (fun _s : ℝ => 2 * Real.pi) 0 t :=
    hasDerivAt_const t (2 * Real.pi)
  have hderiv := hconst.sub hsum
  have hfun :
      (fun s : ℝ =>
        2 * Real.pi -
          ∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | some f =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f
            | none => 0) =
        ((fun _s : ℝ => 2 * Real.pi) -
          fun s : ℝ =>
            ∑ τ : Fin K.nT,
              match K.edgeInTet e τ with
              | none => 0
              | some f =>
                  tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) := by
    funext s
    have hsum_match :
        (∑ τ : Fin K.nT,
          match K.edgeInTet e τ with
          | some f =>
              tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f
          | none => 0) =
          ∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f := by
      refine Finset.sum_congr rfl ?_
      intro τ _
      cases K.edgeInTet e τ <;> rfl
    simp [Pi.sub_apply, hsum_match]
  have hleft_has : HasDerivAt
      (fun s : ℝ =>
        2 * Real.pi -
          ∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | some f =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f
            | none => 0)
      (-∑ τ : Fin K.nT,
        match K.edgeInTet e τ with
        | none => 0
        | some f =>
            deriv
              (fun s : ℝ =>
                tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) t := by
    rw [hfun]
    simpa [Pi.sub_apply] using hderiv
  simpa [mul_comm] using hleft_has.deriv

theorem conformalSchlaefliNearZeroExpansion_of_angleDiff_and_partition
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (P : ReggeActionFirstVariation.IncidenceEdgeSlotPartition K hK)
    (hDiff : LocalDihedralAngleLineDifferentiabilityNearZeroTarget K) :
    ConformalSchlaefliNearZeroExpansionTarget K hK := by
  intro ξ
  filter_upwards [deficitLineDeriv_eq_neg_sum_local_nearZero K hDiff ξ] with t ht
  calc
    (∑ e : Fin K.nE,
      hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
        deficitLineDeriv K ξ e t)
        =
      ∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
          (-∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f =>
                deriv
                  (fun s : ℝ =>
                    tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [ht e]
    _ =
      - (∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
          (∑ τ : Fin K.nT,
            match K.edgeInTet e τ with
            | none => 0
            | some f =>
                deriv
                  (fun s : ℝ =>
                    tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro e _
          ring
    _ =
      - ∑ τ : Fin K.nT,
          ∑ f : Fin 6,
            Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
              deriv
                (fun s : ℝ =>
                  tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t := by
          rw [incidenceEdgeSlotPartition_sum_match_conformal P (linePotential K ξ t)
            (fun τ f =>
              deriv
                (fun s : ℝ =>
                  tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t)]

theorem weightedDeficitDerivativeEventuallyZero_of_nearZeroExpansion_and_local
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hExpand : ConformalSchlaefliNearZeroExpansionTarget K hK)
    (hLocal : LocalConformalSchlaefliNearZeroTarget K) :
    WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat := by
  intro ξ
  filter_upwards [hExpand ξ, hLocal ξ] with t hExpand_t hLocal_t
  rw [hExpand_t]
  have hτ : ∀ τ : Fin K.nT,
      (∑ f : Fin 6,
        Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
          deriv
            (fun s : ℝ =>
              tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) = 0 := by
    intro τ
    exact hLocal_t τ
  simp_rw [hτ]
  simp

theorem weightedDeficitDerivativeStationary_of_nearZeroExpansion_and_local
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hExpand : ConformalSchlaefliNearZeroExpansionTarget K hK)
    (hLocal : LocalConformalSchlaefliNearZeroTarget K) :
    WeightedDeficitDerivativeStationaryTarget K hK hFlat :=
  weightedDeficitDerivativeStationary_of_eventuallyZero K hK hFlat
    (weightedDeficitDerivativeEventuallyZero_of_nearZeroExpansion_and_local
      K hK hFlat hExpand hLocal)

theorem conformalSchlaefliAlongLine_of_expansion_and_local
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hExpand : ConformalSchlaefliAlongLineExpansionTarget K hK)
    (hLocal : LocalConformalSchlaefliAlongLineTarget K) :
    ConformalSchlaefliAlongLineTarget K hK := by
  intro ξ t
  rw [hExpand ξ t]
  have hτ : ∀ τ : Fin K.nT,
      (∑ f : Fin 6,
        Real.sqrt (conformalLocalSqEdge K (linePotential K ξ t) τ f) *
          deriv
            (fun s : ℝ =>
              tetDihedralAngleUnderConformal K (linePotential K ξ s) τ f) t) = 0 := by
    intro τ
    exact hLocal ξ t τ
  simp_rw [hτ]
  simp

theorem weightedDeficitDerivativeEventuallyZero_of_conformalSchlaefliAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSchlaefli : ConformalSchlaefliAlongLineTarget K hK) :
    WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat := by
  intro ξ
  have h_eq : (fun t : ℝ =>
      ∑ e : Fin K.nE,
        hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
          deficitLineDeriv K ξ e t) = fun _t : ℝ => 0 := by
    funext t
    exact hSchlaefli ξ t
  simp only [h_eq, Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Set.univ, Filter.univ_mem, fun _ _ => rfl⟩

theorem weightedDeficitDerivativeStationary_of_conformalSchlaefliAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSchlaefli : ConformalSchlaefliAlongLineTarget K hK) :
    WeightedDeficitDerivativeStationaryTarget K hK hFlat :=
  weightedDeficitDerivativeStationary_of_eventuallyZero K hK hFlat
    (weightedDeficitDerivativeEventuallyZero_of_conformalSchlaefliAlongLine
      K hK hFlat hSchlaefli)

theorem weightedDeficitDerivative_hasDerivAt_secondSchlaefliSum
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (ξ : VertexPotential K) :
    HasDerivAt
      (fun t : ℝ =>
        ∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t)
      (∑ e : Fin K.nE,
        (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
          hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
            deficitLineSecondDeriv K ξ e 0)) 0 := by
  have hSecond :=
    hingeDeficitSecondLineDifferentiabilityAtZero_of_flatConfiguration K hK hFlat
  have hEdge : ∀ e : Fin K.nE,
      HasDerivAt
        (fun t : ℝ =>
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t)
        (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
          hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
            deficitLineSecondDeriv K ξ e 0) 0 := by
    intro e
    have hHinge0 : DifferentiableAt ℝ
        (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e) 0 :=
      (hingeLine_contDiffAt_zero K hK ξ e).differentiableAt (by simp)
    have hHingeLine : HasDerivAt
        (fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e)
        (hingeLineDeriv K hK ξ e 0) 0 := by
      simpa [hingeLineDeriv] using hHinge0.hasDerivAt
    have hDefDeriv : HasDerivAt (fun t : ℝ => deficitLineDeriv K ξ e t)
        (deficitLineSecondDeriv K ξ e 0) 0 := by
      simpa [deficitLineSecondDeriv] using (hSecond ξ e).2.hasDerivAt
    simpa [mul_comm, mul_left_comm, mul_assoc] using hHingeLine.mul hDefDeriv
  have hsum := HasDerivAt.sum
    (u := Finset.univ)
    (A := fun e t => hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
      deficitLineDeriv K ξ e t)
    (A' := fun e => hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
      hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
        deficitLineSecondDeriv K ξ e 0)
    (x := 0)
    (fun e _ => hEdge e)
  rw [show
      (fun t : ℝ =>
        ∑ e : Fin K.nE,
          hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t) =
        (∑ e : Fin K.nE,
          fun t : ℝ => hingeMeasureUnderConformal K hK (linePotential K ξ t) e *
            deficitLineDeriv K ξ e t) by
      funext t
      simp [Finset.sum_apply]]
  simpa using hsum

theorem secondSchlaefliAlongLine_of_weightedStationary
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hStat : WeightedDeficitDerivativeStationaryTarget K hK hFlat) :
    SecondSchlaefliAlongLineTarget K hK hFlat := by
  intro ξ
  have hcalc := weightedDeficitDerivative_hasDerivAt_secondSchlaefliSum K hK hFlat ξ
  have hzero := hcalc.unique (hStat ξ)
  simpa using hzero

theorem weightedDeficitDerivativeStationary_of_secondSchlaefliAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSch : SecondSchlaefliAlongLineTarget K hK hFlat) :
    WeightedDeficitDerivativeStationaryTarget K hK hFlat := by
  intro ξ
  have hcalc := weightedDeficitDerivative_hasDerivAt_secondSchlaefliSum K hK hFlat ξ
  rw [hSch ξ] at hcalc
  exact hcalc

theorem weightedDeficitDerivativeStationaryTarget_iff_secondSchlaefliAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    WeightedDeficitDerivativeStationaryTarget K hK hFlat ↔
      SecondSchlaefliAlongLineTarget K hK hFlat :=
  ⟨secondSchlaefliAlongLine_of_weightedStationary K hK hFlat,
    weightedDeficitDerivativeStationary_of_secondSchlaefliAlongLine K hK hFlat⟩

theorem secondProductRuleEqualsCanonicalHessian_of_secondSchlaefli_and_mixed
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSch : SecondSchlaefliAlongLineTarget K hK hFlat)
    (hMixed : MixedHingeDeficitCanonicalHessianTarget K hK) :
    SecondProductRuleEqualsCanonicalHessianTarget K hK := by
  intro ξ
  have hzero : ∀ e : Fin K.nE,
      deficitAngle K (linePotential K ξ 0) e = 0 := by
    intro e
    simpa [linePotential_zero K ξ] using hFlat.flat_deficit_zero e
  have hsplit :
      reggeActionSecondProductRuleDerivative K hK ξ 0 =
        (∑ e : Fin K.nE,
          (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0)) +
        (∑ e : Fin K.nE,
          (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
            hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
              deficitLineSecondDeriv K ξ e 0)) := by
    unfold reggeActionSecondProductRuleDerivative
    calc
      (∑ e : Fin K.nE,
        (hingeLineSecondDeriv K hK ξ e 0 *
            deficitAngle K (linePotential K ξ 0) e +
          2 * hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
          hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
            deficitLineSecondDeriv K ξ e 0))
          = ∑ e : Fin K.nE,
              (0 + 2 * hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
                hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
                  deficitLineSecondDeriv K ξ e 0) := by
              refine Finset.sum_congr rfl ?_
              intro e _
              rw [hzero e]
              ring
      _ = ∑ e : Fin K.nE,
            (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
              (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
                hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
                  deficitLineSecondDeriv K ξ e 0)) := by
              refine Finset.sum_congr rfl ?_
              intro e _
              ring
      _ = (∑ e : Fin K.nE,
            (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0)) +
          (∑ e : Fin K.nE,
            (hingeLineDeriv K hK ξ e 0 * deficitLineDeriv K ξ e 0 +
              hingeMeasureUnderConformal K hK (linePotential K ξ 0) e *
                deficitLineSecondDeriv K ξ e 0)) := by
              rw [Finset.sum_add_distrib]
  rw [hsplit, hSch ξ, hMixed ξ]
  ring

theorem secondProductRuleEqualsCanonicalHessian_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    SecondProductRuleEqualsCanonicalHessianTarget K hK :=
  secondProductRuleEqualsCanonicalHessian_of_secondSchlaefli_and_mixed K hK hFlat
    (secondSchlaefliAlongLine_of_weightedStationary K hK hFlat
      (weightedDeficitDerivativeStationary_of_eventuallyZero K hK hFlat hZero))
    (mixedHingeDeficitCanonicalHessian_of_edgeStencil K hK D hEdge hStencil)

theorem secondProductRuleEqualsCanonicalHessian_of_weightedStationary_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hStat : WeightedDeficitDerivativeStationaryTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    SecondProductRuleEqualsCanonicalHessianTarget K hK :=
  secondProductRuleEqualsCanonicalHessian_of_secondSchlaefli_and_mixed K hK hFlat
    (secondSchlaefliAlongLine_of_weightedStationary K hK hFlat hStat)
    (mixedHingeDeficitCanonicalHessian_of_edgeStencil K hK D hEdge hStencil)

/-- Equivalent final geometric derivative target: the product-rule expression
itself has the canonical Hessian as its derivative at the flat point. -/
def ProductRuleDerivativeCanonicalHessianTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasDerivAt (reggeActionProductRuleDerivative K hK ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0

theorem productRuleDerivativeCanonicalHessian_of_secondProduct
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hSecond : HingeDeficitSecondLineDifferentiabilityAtZeroTarget K hK)
    (hGeom : SecondProductRuleEqualsCanonicalHessianTarget K hK) :
    ProductRuleDerivativeCanonicalHessianTarget K hK := by
  intro ξ
  rw [← hGeom ξ]
  exact productRule_hasDerivAt_secondProduct K hK hFlat hSecond ξ

theorem productRuleDerivativeCanonicalHessian_of_flat_secondProduct
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hGeom : SecondProductRuleEqualsCanonicalHessianTarget K hK) :
    ProductRuleDerivativeCanonicalHessianTarget K hK :=
  productRuleDerivativeCanonicalHessian_of_secondProduct K hK hFlat
    (hingeDeficitSecondLineDifferentiabilityAtZero_of_flatConfiguration K hK hFlat)
    hGeom

theorem productRuleDerivativeCanonicalHessian_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ProductRuleDerivativeCanonicalHessianTarget K hK :=
  productRuleDerivativeCanonicalHessian_of_flat_secondProduct K hK hFlat
    (secondProductRuleEqualsCanonicalHessian_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil)

theorem productRuleDerivativeCanonicalHessian_of_weightedStationary_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hStat : WeightedDeficitDerivativeStationaryTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ProductRuleDerivativeCanonicalHessianTarget K hK :=
  productRuleDerivativeCanonicalHessian_of_flat_secondProduct K hK hFlat
    (secondProductRuleEqualsCanonicalHessian_of_weightedStationary_and_edgeStencil
      K hK hFlat D hStat hEdge hStencil)

/-- After the product-rule expression is available, the remaining geometric
linearization is that expression's first-order tangency to the canonical
quadratic-line derivative. -/
def ProductRuleTangencyToQuadraticTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasDerivAt
      (fun t : ℝ =>
        reggeActionProductRuleDerivative K hK ξ t -
          deriv (canonicalQuadraticAlongLine K hK ξ) t)
      0 0

theorem productRuleTangencyToQuadratic_of_productRuleDerivativeCanonicalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hProdDeriv : ProductRuleDerivativeCanonicalHessianTarget K hK) :
    ProductRuleTangencyToQuadraticTarget K hK := by
  intro ξ
  have hQuad := canonicalQuadraticAlongLine_hasSecondDerivAt_zero K hK ξ
  have hsub := (hProdDeriv ξ).sub hQuad
  have hzero :
      hessianQuadratic (canonicalReggeHessian K hK) ξ -
        hessianQuadratic (canonicalReggeHessian K hK) ξ = 0 := by
    ring
  simpa [Pi.sub_apply, hzero] using hsub

theorem actionDerivativeTangencyToQuadratic_of_productRule
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hProd : ActionDerivativeProductRuleNearZeroTarget K hK)
    (hTan : ProductRuleTangencyToQuadraticTarget K hK) :
    ActionDerivativeTangencyToQuadraticTarget K hK := by
  intro ξ
  refine (hTan ξ).congr_of_eventuallyEq ?_
  filter_upwards [hProd ξ] with t ht
  rw [ht]

theorem actionDerivativeTangencyToQuadratic_of_flat_productRuleDerivativeCanonicalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hProdDeriv : ProductRuleDerivativeCanonicalHessianTarget K hK) :
    ActionDerivativeTangencyToQuadraticTarget K hK :=
  actionDerivativeTangencyToQuadratic_of_productRule K hK
    (actionDerivativeProductRuleNearZero_of_flatConfiguration K hK hFlat)
    (productRuleTangencyToQuadratic_of_productRuleDerivativeCanonicalHessian K hK hProdDeriv)

theorem nonlinearDirectionalHessian_of_actionDerivativeTangencyToQuadratic
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hTan : ActionDerivativeTangencyToQuadraticTarget K hK) :
    NonlinearReggeDirectionalHessianTheorem K hK :=
  nonlinearDirectionalHessian_of_actionDerivativeFirstOrderTangency K hK
    (actionDerivativeFirstOrderTangency_of_quadraticTangency K hK hTan)

theorem actionDerivativeTangencyToQuadratic_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ActionDerivativeTangencyToQuadraticTarget K hK :=
  actionDerivativeTangencyToQuadratic_of_flat_productRuleDerivativeCanonicalHessian K hK
    hFlat
    (productRuleDerivativeCanonicalHessian_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil)

theorem actionDerivativeTangencyToQuadratic_of_weightedStationary_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hStat : WeightedDeficitDerivativeStationaryTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ActionDerivativeTangencyToQuadraticTarget K hK :=
  actionDerivativeTangencyToQuadratic_of_flat_productRuleDerivativeCanonicalHessian K hK
    hFlat
    (productRuleDerivativeCanonicalHessian_of_weightedStationary_and_edgeStencil
      K hK hFlat D hStat hEdge hStencil)

theorem nonlinearDirectionalHessian_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    NonlinearReggeDirectionalHessianTheorem K hK :=
  nonlinearDirectionalHessian_of_actionDerivativeTangencyToQuadratic K hK
    (actionDerivativeTangencyToQuadratic_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil)

theorem nonlinearDirectionalHessian_of_weightedStationary_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hStat : WeightedDeficitDerivativeStationaryTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    NonlinearReggeDirectionalHessianTheorem K hK :=
  nonlinearDirectionalHessian_of_actionDerivativeTangencyToQuadratic K hK
    (actionDerivativeTangencyToQuadratic_of_weightedStationary_and_edgeStencil
      K hK hFlat D hStat hEdge hStencil)

/-- The full nonlinear Hessian proof is reduced to proving zero second
variation for the canonical remainder line.  The remaining expansion is the
Cayley-Menger/arccos chain-rule calculation. -/
def NonlinearReggeHessianReducedToRemainder
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasSecondDerivAt (canonicalRemainderAlongLine K hK ξ) 0 0

/-- The remaining calculus glue between the explicit action split and the
remainder target.  This is not the geometric chain-rule calculation itself; it
is the exact derivative identity needed because `HasSecondDerivAt` is phrased
through `deriv`.  Closing it requires first-derivative existence for the
action, quadratic line, and subtraction-defined remainder near zero, supplied
by the smoothness chain. -/
def CanonicalRemainderDerivativeIdentityTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ => deriv (canonicalRemainderAlongLine K hK ξ) t) =
      fun t : ℝ =>
        deriv (actionAlongLine K hK ξ) t -
          deriv (canonicalQuadraticAlongLine K hK ξ) t

/-- Concrete differentiability condition sufficient for the derivative identity.
This is the target the smoothness chain should supply for the action line; the
quadratic line is elementary. -/
def CanonicalRemainderLineDifferentiabilityTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (t : ℝ),
    DifferentiableAt ℝ (actionAlongLine K hK ξ) t ∧
      DifferentiableAt ℝ (canonicalQuadraticAlongLine K hK ξ) t

def ActionLineDifferentiabilityTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ (ξ : VertexPotential K) (t : ℝ),
    DifferentiableAt ℝ (actionAlongLine K hK ξ) t

def ActionLineDifferentiabilityNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      DifferentiableAt ℝ (actionAlongLine K hK ξ) t

theorem linePotential_contDiffAt_zero
    (K : Triangulation3D) (ξ : VertexPotential K) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => linePotential K ξ t) (0 : ℝ) := by
  rw [contDiffAt_pi]
  intro i
  unfold linePotential
  fun_prop

theorem actionAlongLine_contDiffAt_zero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) (ξ : VertexPotential K) :
    ContDiffAt ℝ (⊤ : ℕ∞) (actionAlongLine K hK ξ) (0 : ℝ) := by
  have hline := linePotential_contDiffAt_zero K ξ
  have hActionAt : ContDiffAt ℝ (⊤ : ℕ∞)
      (reggeAction K hK) (linePotential K ξ 0) := by
    simpa [linePotential_zero K ξ] using hFlat.action_contDiff_at_zero
  unfold actionAlongLine
  have hcomp := ContDiffAt.comp (x := (0 : ℝ)) hActionAt hline
  simpa [Function.comp_def] using hcomp

theorem actionLineDifferentiabilityNearZero_of_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK) :
    ActionLineDifferentiabilityNearZeroTarget K hK := by
  intro ξ
  exact differentiableAt_eventually_of_contDiffAt_top
    (actionAlongLine K hK ξ) 0
    (actionAlongLine_contDiffAt_zero_of_flatConfiguration K hK hFlat ξ)

def CanonicalRemainderLineDifferentiabilityNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      DifferentiableAt ℝ (actionAlongLine K hK ξ) t ∧
        DifferentiableAt ℝ (canonicalQuadraticAlongLine K hK ξ) t

def CanonicalRemainderDerivativeIdentityNearZeroTarget
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    (fun t : ℝ => deriv (canonicalRemainderAlongLine K hK ξ) t) =ᶠ[nhds (0 : ℝ)]
      ((fun t : ℝ => deriv (actionAlongLine K hK ξ) t) -
        fun t : ℝ => deriv (canonicalQuadraticAlongLine K hK ξ) t)

theorem canonicalRemainderLineDifferentiability_of_actionLineDifferentiability
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hAction : ActionLineDifferentiabilityTarget K hK) :
    CanonicalRemainderLineDifferentiabilityTarget K hK := by
  intro ξ t
  exact ⟨hAction ξ t, canonicalQuadraticAlongLine_differentiableAt K hK ξ t⟩

theorem canonicalRemainderLineDifferentiabilityNearZero_of_actionLineDifferentiabilityNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hAction : ActionLineDifferentiabilityNearZeroTarget K hK) :
    CanonicalRemainderLineDifferentiabilityNearZeroTarget K hK := by
  intro ξ
  filter_upwards [hAction ξ] with t ht
  exact ⟨ht, canonicalQuadraticAlongLine_differentiableAt K hK ξ t⟩

theorem canonicalRemainderDerivativeIdentity_of_lineDifferentiability
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hDiff : CanonicalRemainderLineDifferentiabilityTarget K hK) :
    CanonicalRemainderDerivativeIdentityTarget K hK := by
  intro ξ
  funext t
  rw [canonicalRemainderAlongLine_eq_action_sub_quadratic K hK ξ]
  have hAction : DifferentiableAt ℝ (actionAlongLine K hK ξ) t := (hDiff ξ t).1
  have hQuad : DifferentiableAt ℝ (canonicalQuadraticAlongLine K hK ξ) t := (hDiff ξ t).2
  have hActionSubConst :
      DifferentiableAt ℝ
        (fun s : ℝ => actionAlongLine K hK ξ s -
          reggeAction K hK (zeroPotential K)) t :=
    hAction.sub (differentiableAt_const
      (c := reggeAction K hK (zeroPotential K)))
  have hSub := deriv_sub hActionSubConst hQuad
  calc
    deriv
        (fun s : ℝ =>
          actionAlongLine K hK ξ s - reggeAction K hK (zeroPotential K) -
            canonicalQuadraticAlongLine K hK ξ s) t
        = deriv
            (fun s : ℝ =>
              actionAlongLine K hK ξ s - reggeAction K hK (zeroPotential K)) t -
            deriv (canonicalQuadraticAlongLine K hK ξ) t := by
            simpa [sub_eq_add_neg] using hSub
    _ = deriv (actionAlongLine K hK ξ) t -
          deriv (canonicalQuadraticAlongLine K hK ξ) t := by
          rw [deriv_sub_const]

theorem canonicalRemainderDerivativeIdentityNearZero_of_lineDifferentiabilityNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hDiff : CanonicalRemainderLineDifferentiabilityNearZeroTarget K hK) :
    CanonicalRemainderDerivativeIdentityNearZeroTarget K hK := by
  intro ξ
  filter_upwards [hDiff ξ] with t ht
  rw [canonicalRemainderAlongLine_eq_action_sub_quadratic K hK ξ]
  have hAction : DifferentiableAt ℝ (actionAlongLine K hK ξ) t := ht.1
  have hQuad : DifferentiableAt ℝ (canonicalQuadraticAlongLine K hK ξ) t := ht.2
  have hActionSubConst :
      DifferentiableAt ℝ
        (fun s : ℝ => actionAlongLine K hK ξ s -
          reggeAction K hK (zeroPotential K)) t :=
    hAction.sub (differentiableAt_const
      (c := reggeAction K hK (zeroPotential K)))
  have hSub := deriv_sub hActionSubConst hQuad
  calc
    deriv
        (fun s : ℝ =>
          actionAlongLine K hK ξ s - reggeAction K hK (zeroPotential K) -
            canonicalQuadraticAlongLine K hK ξ s) t
        = deriv
            (fun s : ℝ =>
              actionAlongLine K hK ξ s - reggeAction K hK (zeroPotential K)) t -
            deriv (canonicalQuadraticAlongLine K hK ξ) t := by
            simpa [sub_eq_add_neg] using hSub
    _ = deriv (actionAlongLine K hK ξ) t -
          deriv (canonicalQuadraticAlongLine K hK ξ) t := by
          rw [deriv_sub_const]

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_derivIdentity
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hDeriv : CanonicalRemainderDerivativeIdentityTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK := by
  intro ξ
  unfold HasSecondDerivAt
  change HasDerivAt
    (fun t : ℝ => deriv (canonicalRemainderAlongLine K hK ξ) t) 0 0
  rw [hDeriv ξ]
  have hAction : HasDerivAt
      (fun t : ℝ => deriv (actionAlongLine K hK ξ) t)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := hHessian ξ
  have hQuadRaw := canonicalQuadraticAlongLine_hasSecondDerivAt_zero K hK ξ
  have hQuad : HasDerivAt
      (fun t : ℝ => deriv (canonicalQuadraticAlongLine K hK ξ) t)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := hQuadRaw
  have hSub := hAction.sub hQuad
  simpa using hSub

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_derivIdentityNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hDeriv : CanonicalRemainderDerivativeIdentityNearZeroTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK := by
  intro ξ
  unfold HasSecondDerivAt
  change HasDerivAt
    (fun t : ℝ => deriv (canonicalRemainderAlongLine K hK ξ) t) 0 0
  have hAction : HasDerivAt
      (fun t : ℝ => deriv (actionAlongLine K hK ξ) t)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := hHessian ξ
  have hQuadRaw := canonicalQuadraticAlongLine_hasSecondDerivAt_zero K hK ξ
  have hQuad : HasDerivAt
      (fun t : ℝ => deriv (canonicalQuadraticAlongLine K hK ξ) t)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 := hQuadRaw
  have hSub := hAction.sub hQuad
  simpa using hSub.congr_of_eventuallyEq (hDeriv ξ)

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_lineDiff
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hDiff : CanonicalRemainderLineDifferentiabilityTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_derivIdentity
    K hK hHessian
    (canonicalRemainderDerivativeIdentity_of_lineDifferentiability K hK hDiff)

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_actionLineDiff
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hAction : ActionLineDifferentiabilityTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_lineDiff
    K hK hHessian
    (canonicalRemainderLineDifferentiability_of_actionLineDifferentiability K hK hAction)

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_actionLineDiffNearZero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK)
    (hAction : ActionLineDifferentiabilityNearZeroTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_derivIdentityNearZero
    K hK hHessian
    (canonicalRemainderDerivativeIdentityNearZero_of_lineDifferentiabilityNearZero K hK
      (canonicalRemainderLineDifferentiabilityNearZero_of_actionLineDifferentiabilityNearZero
        K hK hAction))

theorem canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_flatConfiguration
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_actionLineDiffNearZero
    K hK hHessian
    (actionLineDifferentiabilityNearZero_of_flatConfiguration K hK hFlat)

theorem canonicalRemainderSecondVariationZero_of_actionDerivativeLinearizationNearZero_and_flat
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hLin : ActionDerivativeLinearizationNearZeroTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_flatConfiguration
    K hK hFlat
    (nonlinearDirectionalHessian_of_actionDerivativeLinearizationNearZero K hK hLin)

theorem canonicalRemainderSecondVariationZero_of_actionDerivativeTangency_and_flat
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTan : ActionDerivativeFirstOrderTangencyTarget K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_flatConfiguration
    K hK hFlat
    (nonlinearDirectionalHessian_of_actionDerivativeFirstOrderTangency K hK hTan)

def reggeActionRemainderSecondVariationInput_of_flat_nonlinearHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK) :
    ReggeActionRemainderSecondVariationInput K hK where
  remainder_secondVariation_zero :=
    canonicalRemainderSecondVariationZero_of_nonlinearHessian_and_flatConfiguration
      K hK hFlat hHessian

def reggeActionSecondVariationInput_of_flat_nonlinearHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hHessian : NonlinearReggeDirectionalHessianTheorem K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_directionalSecondVariation
    K hK hFlat hHessian

def reggeActionRemainderSecondVariationInput_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ReggeActionRemainderSecondVariationInput K hK :=
  reggeActionRemainderSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
    (nonlinearDirectionalHessian_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil)

def reggeActionSecondVariationInput_of_eventuallyZero_and_edgeStencil
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (D : ReggeActionFirstVariation.DeficitAngleDirectionalDerivativePackage K hK)
    (hZero : WeightedDeficitDerivativeEventuallyZeroTarget K hK hFlat)
    (hEdge : MixedHingeDeficitEdgeStencilTarget K hK D)
    (hStencil : CanonicalDirichletEqualsEdgeStencilTarget K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
    (nonlinearDirectionalHessian_of_eventuallyZero_and_edgeStencil
      K hK hFlat D hZero hEdge hStencil)

def reggeActionRemainderSecondVariationInput_of_flat_actionDerivativeLinearization
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hLin : ActionDerivativeLinearizationNearZeroTarget K hK) :
    ReggeActionRemainderSecondVariationInput K hK where
  remainder_secondVariation_zero :=
    canonicalRemainderSecondVariationZero_of_actionDerivativeLinearizationNearZero_and_flat
      K hK hFlat hLin

def reggeActionSecondVariationInput_of_flat_actionDerivativeLinearization
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hLin : ActionDerivativeLinearizationNearZeroTarget K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
    (nonlinearDirectionalHessian_of_actionDerivativeLinearizationNearZero K hK hLin)

def reggeActionRemainderSecondVariationInput_of_flat_actionDerivativeTangency
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTan : ActionDerivativeFirstOrderTangencyTarget K hK) :
    ReggeActionRemainderSecondVariationInput K hK where
  remainder_secondVariation_zero :=
    canonicalRemainderSecondVariationZero_of_actionDerivativeTangency_and_flat
      K hK hFlat hTan

def reggeActionSecondVariationInput_of_flat_actionDerivativeTangency
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTan : ActionDerivativeFirstOrderTangencyTarget K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_flat_nonlinearHessian K hK hFlat
    (nonlinearDirectionalHessian_of_actionDerivativeFirstOrderTangency K hK hTan)

def reggeActionRemainderSecondVariationInput_of_flat_actionDerivativeTangencyToQuadratic
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTan : ActionDerivativeTangencyToQuadraticTarget K hK) :
    ReggeActionRemainderSecondVariationInput K hK :=
  reggeActionRemainderSecondVariationInput_of_flat_actionDerivativeTangency
    K hK hFlat
    (actionDerivativeFirstOrderTangency_of_quadraticTangency K hK hTan)

def reggeActionSecondVariationInput_of_flat_actionDerivativeTangencyToQuadratic
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (hTan : ActionDerivativeTangencyToQuadraticTarget K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_flat_actionDerivativeTangency
    K hK hFlat
    (actionDerivativeFirstOrderTangency_of_quadraticTangency K hK hTan)

theorem remainder_reduction_eq_canonicalRemainderSecondVariation
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    NonlinearReggeHessianReducedToRemainder K hK ↔
      CanonicalRemainderSecondVariationZero K hK := by
  rfl

theorem canonicalRemainderSecondVariationZero_of_identically_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero :
      ∀ ξ : VertexPotential K,
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ = 0) :
    CanonicalRemainderSecondVariationZero K hK := by
  intro ξ
  unfold HasSecondDerivAt
  have hfun :
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t)) = fun _t : ℝ => (0 : ℝ) := by
    funext t
    exact hZero (linePotential K ξ t)
  rw [hfun]
  simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))

theorem nonlinearDirectionalHessian_of_remainder_identically_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hZero :
      ∀ ξ : VertexPotential K,
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ = 0) :
    NonlinearReggeDirectionalHessianTheorem K hK := by
  intro ξ
  have hsplit := actionAlongLine_canonical_split K hK ξ
  have haction :
      actionAlongLine K hK ξ =
        fun t : ℝ =>
          reggeAction K hK (zeroPotential K) +
            canonicalQuadraticAlongLine K hK ξ t := by
    funext t
    rw [congrFun hsplit t]
    simp [canonicalRemainderAlongLine, hZero]
  have hquad := canonicalQuadraticAlongLine_hasSecondDerivAt_zero K hK ξ
  have hconst :=
    hasSecondDerivAt_const_add
      (canonicalQuadraticAlongLine K hK ξ)
      (reggeAction K hK (zeroPotential K))
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0 hquad
  simpa [haction] using hconst

theorem canonicalHessianSecondVariation_of_nonlinearDirectionalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h : NonlinearReggeDirectionalHessianTheorem K hK) :
    CanonicalHessianSecondVariationAtZero K hK :=
  h

def reggeActionSecondVariationInput_of_nonlinearDirectionalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (hFlat : FlatConfiguration K hK)
    (h : NonlinearReggeDirectionalHessianTheorem K hK) :
    ReggeActionSecondVariationInput K hK hFlat :=
  reggeActionSecondVariationInput_of_directionalSecondVariation K hK hFlat
    (canonicalHessianSecondVariation_of_nonlinearDirectionalHessian K hK h)

/-- A convenient equivalent formulation in terms of the canonical nonlinear
remainder: if the canonical remainder has zero second variation in every
direction, then the nonlinear Hessian is canonical. -/
def CanonicalRemainderZeroSecondVariationTheorem
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  CanonicalRemainderSecondVariationZero K hK

def reggeActionRemainderSecondVariationInput_of_theorem
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h : CanonicalRemainderZeroSecondVariationTheorem K hK) :
    ReggeActionRemainderSecondVariationInput K hK where
  remainder_secondVariation_zero := h

end

end ReggeActionNonlinearHessianProof
end Geometry
end IndisputableMonolith
