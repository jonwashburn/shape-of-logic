import IndisputableMonolith.Gravity.Analysis.ReggeTTSymbolPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeTTDerivativeGate
import IndisputableMonolith.Gravity.Analysis.ReggeTTLocalSymbolExistence

/-!
# Regge TT flat second variation, Schläfli-reduced (Gate A2)

QG full-theory campaign, `ReggeTTContinuumSymbol` program, Crux-1(c) lane,
Gate A2 of the panel-locked protocol "Normalization-Gated Schläfli Two-Jet"
(Gate A0 is `ReggeTTSymbolSpecificationAudit`, Gate A1 is
`ReggeTTLocalSymbolExistence`; the first-derivative structure at flat is
`ReggeTTDerivativeGate`, reused here, never re-proved).

## What this module proves (all THEOREM)

* Regrouping bijection (`sum_edges_slotMatch`): for every cell/tet and
  every summand family, the edge-sum of `canonicalEdgeSlot?`-matched values
  equals the slot-sum over the tet's six local edges.  This is the
  incidence involution "edge-sum of incident-tet hits = tet-sum of slot
  values", proved from `canonicalEdgeSlot_eq_some_implies` +
  `canonicalPeriodicLocalEdgeNoDup`.
* Derivative of the profile at every good amplitude
  (`hasDerivAt_planeWaveActionProfile`): at every `t` where all edge values
  are positive and all tetrahedra are nondegenerate with interior cosines,
  `S'(t) = Σ_e [ (l'_e/(2√l_e))·δ_e + √l_e·δ'_e ]` with every primed object
  in explicit closed form (`edgeSqrtDeriv`, `deficitDeriv`,
  `slotAngleDeriv`).
* PATHWISE SCHLÄFLI KILL (`sum_sqrt_deficitDeriv_eq_zero`): at every good
  amplitude the ENTIRE second group `Σ_e √l_e·δ'_e` vanishes — regrouped
  per tetrahedron it is `−Σ_τ Σ_g v_g·(Σ_f √a_f·∂θ_f/∂a_g) = 0` by the
  proved tetrahedral Schläfli identity (`tetraSchlaefliSixEdgeClosedForm`)
  at the (nondegenerate) path point.  This holds IDENTICALLY near `0`, not
  just at `0`, and is what deletes every arccos second derivative from the
  second variation.
* GATE A2(a) (`trueReggeAction_firstVariation_flat_eq_zero`):
  `deriv (planeWaveActionProfile N E k) 0 = 0`.  At `t = 0` the first
  group dies (flat deficits vanish, Stage-1 kernel theorem) and the second
  group dies by the Schläfli kill at flat.
* GATE A2(b) (`trueReggeAction_secondVariation_flat_schlaefli`):
  `iteratedDeriv 2 (planeWaveActionProfile N E k) 0
     = −Σ_τ Σ_f L'_{τf}(0) · θ'_{τf}(0)`
  with `L'_{τf}(0) = v_{τf}/(2√a*_f)` (`flatSlotSqrtDeriv`) and
  `θ'_{τf}(0) = Σ_g v_{τg}·J_{fg}` the flat angle Jacobian contraction
  (`flatSlotAngleDeriv`, `J = flatAngleJacobian` of the derivative gate).
  NO second derivative of `arccos` appears anywhere: `S'` agrees near `0`
  with `Σ_e (l'_e/(2√l_e))·δ_e` alone (the `√l·δ'` group is identically
  zero near `0` by the pathwise Schläfli kill), so `S''(0)` is the
  `t`-derivative of the FIRST group only, and `δ_e(0) = 0` reduces it to
  `Σ_e L'_e(0)·δ'_e(0)`, regrouped per tetrahedron.
* GATE A2(c) (`axisReducedSecondVariation` +
  `axisReducedSecondVariation_applies`): the reduced formula instantiated
  at the preregistered axis direction `m = (1,0,0)` with polarization
  `axisTTPolarizationPlus` at `N = 3`, as a named `Finset`-sum expression
  and the kernel equation that the reduced formula computes that
  instance's `S''(0)`.  NO numeric value is claimed or evaluated.

## Consequence for the campaign (PASS report)

The explicit-G Hessian stage is deleted from the critical path: the
second variation of the TRUE nonlinear Regge action at flat is now a
kernel-checked finite sum of first-derivative data (flat sqrt-edge slopes
times flat angle-Jacobian contractions), with the arccos second-derivative
block eliminated by the proved Schläfli identity, not by any symbolic
differentiation of `arccos` compositions.

## What this module does NOT prove (binding scope disclosure)

* No VALUE of `S''(0)` and no continuum claim: the reduced formula is a
  kernel identity, not an evaluation.  The `-(1/4)` continuum target stays
  OPEN with status flag `false`; the C10 probe remains NUMERICAL EVIDENCE
  and is never cited as proof.
* Combined with Gate A1's bridge, the fixed-`N` symbol equals
  `(2/N³)·S''(0)` with `S''(0)` given by the reduced formula here; the
  remaining OPEN work toward the continuum target is the evaluation of the
  reduced finite sum and its `N → ∞` limit.

## Inherited axiom footprint (disclosure)

Gate A2(a) uses the Stage-1 flat-deficit theorem
(`deficitOfField_flatEdgeField`), which rides the certified periodic
angle-sum chain and therefore carries `Lean.ofReduceBool` /
`Lean.trustCompiler` in addition to the standard trio — inherited
disclosure, not new axioms.  Gate A2(b) also passes through the flat
point (`δ_e(0) = 0`), so it carries the same inherited pair.  No new
axioms; no `sorry`, no `admit`, no `native_decide` in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTFlatSecondVariation

open Geometry.PeriodicFreudenthalTorus
open Geometry.CayleyMengerPolynomial (SqEdges cm3)
open Geometry.DihedralCayleyMenger (dihedralCos3Sq)
open Geometry.DihedralDerivatives (dihedralAngle3Sq dihedralAngle3SqClosedFormDeriv)
open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges freudenthalTet)
open ReggeTTSymbolPreflight
open ReggeTTLocalSymbolExistence

noncomputable section

variable (N : ℕ) [NeZero N]

/-! ## §1. Edge-level closed-form derivative data -/

/-- The affine slope of a single plane-wave edge value:
`c_e = polEdgeCoeff E d_e · cos(k·x_mid(e))`.  On matched slots this is
definitionally `planeWaveTetVelocity`. -/
def edgeCoeff (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) : ℝ :=
  polEdgeCoeff E e.disp * Real.cos (edgeMidpointPhase N k e)

/-- The closed-form derivative of the sqrt hinge factor:
`L'_e(t) = c_e / (2·√(l_e(t)))`. -/
def edgeSqrtDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (t : ℝ) : ℝ :=
  edgeCoeff N E k e / (2 * Real.sqrt (planeWaveEdgeField N E k t e))

/-- Each plane-wave edge value is differentiable in the amplitude with
derivative its affine slope. -/
theorem hasDerivAt_edgeValue (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => planeWaveEdgeField N E k t e)
      (edgeCoeff N E k e) t₀ := by
  have h : (fun t : ℝ => planeWaveEdgeField N E k t e) =
      fun t : ℝ => periodicDispSqEdge e.disp + t * edgeCoeff N E k e := by
    funext t
    simp only [planeWaveEdgeField, edgeCoeff]
    ring
  rw [h]
  simpa using ((hasDerivAt_id t₀).mul_const (edgeCoeff N E k e)).const_add
    (periodicDispSqEdge e.disp)

/-- Derivative of the sqrt hinge factor at any amplitude where the edge
value is nonzero. -/
theorem hasDerivAt_sqrtEdge (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (t₀ : ℝ)
    (hne : planeWaveEdgeField N E k t₀ e ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sqrt (planeWaveEdgeField N E k t e))
      (edgeSqrtDeriv N E k e t₀) t₀ := by
  have hsq : HasDerivAt Real.sqrt
      (1 / (2 * Real.sqrt (planeWaveEdgeField N E k t₀ e)))
      (planeWaveEdgeField N E k t₀ e) :=
    Real.hasDerivAt_sqrt hne
  have hcomp := hsq.comp t₀ (hasDerivAt_edgeValue N E k e t₀)
  have hval : edgeSqrtDeriv N E k e t₀ =
      1 / (2 * Real.sqrt (planeWaveEdgeField N E k t₀ e)) * edgeCoeff N E k e := by
    unfold edgeSqrtDeriv
    ring
  rw [hval]
  exact hcomp

/-! ## §2. The directional angle derivative at a general nondegenerate point -/

/-- Directional derivative of one dihedral angle along an affine
squared-edge path through ANY nondegenerate tetrahedron with interior
cosine (generalization of the derivative gate's flat-point lemma; same
proof route: `C¹` Fréchet derivative + the six proved coordinate
partials). -/
theorem hasDerivAt_angle_directional
    (T : Geometry.ReggeRigorousFoundation.NonDegenerateTet) (f : Fin 6)
    (hEnd : dihedralCos3Sq T.sqEdge f ≠ -1 ∧ dihedralCos3Sq T.sqEdge f ≠ 1)
    (v : Fin 6 → ℝ) :
    HasDerivAt
      (fun t : ℝ => dihedralAngle3Sq (fun j : Fin 6 => T.sqEdge j + t * v j) f)
      (∑ g : Fin 6, v g * dihedralAngle3SqClosedFormDeriv T.sqEdge f g) 0 := by
  have hC : ContDiffAt ℝ 1 (fun x : SqEdges => dihedralAngle3Sq x f) T.sqEdge :=
    Geometry.ReggeActionFirstVariation.dihedralAngle3Sq_contDiffAt_nonDegenerate
      T f 1 hEnd
  have hDiff : DifferentiableAt ℝ (fun x : SqEdges => dihedralAngle3Sq x f)
      T.sqEdge :=
    hC.differentiableAt (by simp)
  have hF : HasFDerivAt (fun x : SqEdges => dihedralAngle3Sq x f)
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) T.sqEdge)
      T.sqEdge :=
    hDiff.hasFDerivAt
  have hγ : HasDerivAt
      (fun t : ℝ => (fun j : Fin 6 => T.sqEdge j + t * v j)) v 0 := by
    rw [hasDerivAt_pi]
    intro j
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (T.sqEdge j)
  have hF' : HasFDerivAt (fun x : SqEdges => dihedralAngle3Sq x f)
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) T.sqEdge)
      (fun j : Fin 6 => T.sqEdge j + (0 : ℝ) * v j) := by
    simpa using hF
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ))
    (f := fun t : ℝ => (fun j : Fin 6 => T.sqEdge j + t * v j))
    hF' hγ
  have hvalue :
      (fderiv ℝ (fun x : SqEdges => dihedralAngle3Sq x f) T.sqEdge) v =
        ∑ g : Fin 6, v g * dihedralAngle3SqClosedFormDeriv T.sqEdge f g := by
    rw [Geometry.ReggeActionFirstVariation.continuousLinearMap_apply_eq_sum_single]
    refine Finset.sum_congr rfl fun g _ => ?_
    exact congrArg (fun z => v g * z)
      (Geometry.ReggeActionFirstVariation.fderiv_dihedralAngle3Sq_apply_single
        T f g hEnd)
  rw [hvalue] at hcomp
  simpa [Function.comp_def] using hcomp

/-! ## §3. Slot-level derivative data along the plane wave -/

/-- Closed-form slot angle derivative along the plane wave:
`θ'_{τf}(t) = Σ_g v_{τg} · ∂θ_f/∂a_g (a_τ(t))`. -/
def slotAngleDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (τ : PeriodicTet N N N) (f : Fin 6) (t : ℝ) : ℝ :=
  ∑ g : Fin 6,
    planeWaveTetVelocity N E k τ g *
      dihedralAngle3SqClosedFormDeriv
        (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) f g

/-- Derivative of one slot angle along the plane wave at any amplitude
where the tetrahedron is nondegenerate with interior cosine (shift of the
directional lemma to base point `t₀` — the path is affine, so it is the
same affine path re-based at `a_τ(t₀)`). -/
theorem hasDerivAt_slotAngle (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (τ : PeriodicTet N N N) (f : Fin 6) (t₀ : ℝ)
    (hpos : ∀ j : Fin 6,
      0 < tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ j)
    (hcm : 0 < cm3 (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ))
    (hEnd :
      dihedralCos3Sq (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ) f ≠ -1 ∧
      dihedralCos3Sq (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ) f ≠ 1) :
    HasDerivAt
      (fun t : ℝ => tetDihedralAngleOfField N (planeWaveEdgeField N E k t) τ f)
      (slotAngleDeriv N E k τ f t₀) t₀ := by
  set T : Geometry.ReggeRigorousFoundation.NonDegenerateTet :=
    ⟨tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ, hpos, hcm⟩ with hT
  have hgen := hasDerivAt_angle_directional T f hEnd
    (planeWaveTetVelocity N E k τ)
  have hshift : HasDerivAt (fun t : ℝ => t - t₀) 1 t₀ :=
    (hasDerivAt_id t₀).sub_const t₀
  have hcomp := HasDerivAt.comp_of_eq t₀ hgen hshift (sub_self t₀).symm
  have hfuneq :
      (fun t : ℝ => dihedralAngle3Sq
        (fun j : Fin 6 => T.sqEdge j + (t - t₀) * planeWaveTetVelocity N E k τ j) f)
        = fun t : ℝ =>
            tetDihedralAngleOfField N (planeWaveEdgeField N E k t) τ f := by
    funext t
    unfold tetDihedralAngleOfField
    congr 1
    funext j
    show tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ j +
        (t - t₀) * planeWaveTetVelocity N E k τ j =
      tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ j
    rw [planeWaveTetSqEdges_apply N E k τ t₀ j,
      planeWaveTetSqEdges_apply N E k τ t j]
    ring
  have hcomp' : HasDerivAt
      (fun t : ℝ => dihedralAngle3Sq
        (fun j : Fin 6 => T.sqEdge j + (t - t₀) * planeWaveTetVelocity N E k τ j) f)
      ((∑ g : Fin 6, planeWaveTetVelocity N E k τ g *
        dihedralAngle3SqClosedFormDeriv T.sqEdge f g) * 1) t₀ := by
    simpa [Function.comp_def] using hcomp
  rw [hfuneq] at hcomp'
  simpa [slotAngleDeriv, hT] using hcomp'

/-! ## §4. Contribution and deficit derivatives -/

/-- Closed-form derivative of one edge-tet angle contribution (the slot
match, `none` branch constant `0`). -/
def contribDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (τ : PeriodicTet N N N) (t : ℝ) : ℝ :=
  match canonicalEdgeSlot? e τ.1 τ.2 with
  | some f => slotAngleDeriv N E k τ f t
  | none => 0

/-- Derivative of one edge-tet angle contribution at a good amplitude. -/
theorem hasDerivAt_contrib (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (τ : PeriodicTet N N N) (t₀ : ℝ)
    (hpos : ∀ j : Fin 6,
      0 < tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ j)
    (hcm : 0 < cm3 (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ))
    (hEnd : ∀ f : Fin 6,
      dihedralCos3Sq (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ) f ≠ -1 ∧
      dihedralCos3Sq (tetSqEdgesOfField N (planeWaveEdgeField N E k t₀) τ) f ≠ 1) :
    HasDerivAt
      (fun t : ℝ =>
        edgeAngleContributionOfField N (planeWaveEdgeField N E k t) e τ)
      (contribDeriv N E k e τ t₀) t₀ := by
  unfold edgeAngleContributionOfField contribDeriv
  cases h : canonicalEdgeSlot? e τ.1 τ.2 with
  | none => simpa [h] using hasDerivAt_const t₀ (0 : ℝ)
  | some f =>
      simpa [h] using
        hasDerivAt_slotAngle N E k τ f t₀ hpos hcm (hEnd f)

/-- Closed-form deficit derivative:
`δ'_e(t) = −Σ_τ (matched θ'_{τf}(t))`. -/
def deficitDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (t : ℝ) : ℝ :=
  -∑ τ : PeriodicTet N N N, contribDeriv N E k e τ t

/-- The goodness predicate for an amplitude: all edge values positive, all
tetrahedra nondegenerate with strictly interior cosines. -/
def PathGoodAt (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) (t : ℝ) : Prop :=
  (∀ e : PeriodicEdge N N N, 0 < planeWaveEdgeField N E k t e) ∧
    ∀ τ : PeriodicTet N N N,
      0 < cm3 (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) ∧
        ∀ f : Fin 6,
          0 < tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ f ∧
            (-1 < dihedralCos3Sq
                (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) f ∧
              dihedralCos3Sq
                (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) f < 1)

/-- The flat amplitude is good: edge values are the positive displacement
classes, every tetrahedron is the Freudenthal tetrahedron (`cm3 = 8 > 0`),
and every flat cosine is strictly interior. -/
theorem pathGoodAt_zero (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    PathGoodAt N E k 0 := by
  constructor
  · intro e
    simp only [planeWaveEdgeField, zero_mul, add_zero]
    exact periodicDispSqEdge_pos e.disp
  · intro τ
    rw [planeWaveTetSqEdges_zero]
    refine ⟨?_, ?_⟩
    · rw [Geometry.FreudenthalCubeTriangulation.cm3_freudenthalTetSqEdges]
      norm_num
    · intro f
      exact ⟨freudenthalTet.sqEdge_pos f,
        ReggeTTDerivativeGate.flatCos_bounds f⟩

/-- Goodness persists on a neighborhood of the flat amplitude
(continuity of the affine paths + the derivative gate's flat neighborhood
nondegeneracy). -/
theorem eventually_pathGoodAt (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    ∀ᶠ t in nhds (0 : ℝ), PathGoodAt N E k t := by
  have hedges : ∀ᶠ t in nhds (0 : ℝ),
      ∀ e : PeriodicEdge N N N, 0 < planeWaveEdgeField N E k t e := by
    rw [Filter.eventually_all]
    intro e
    have hcont : Filter.Tendsto (fun t : ℝ => planeWaveEdgeField N E k t e)
        (nhds 0) (nhds (planeWaveEdgeField N E k 0 e)) :=
      ((planeWaveEdgeValue_contDiff N E k e 0).continuous).continuousAt
    have hpos : 0 < planeWaveEdgeField N E k 0 e :=
      (pathGoodAt_zero N E k).1 e
    exact hcont.eventually (eventually_gt_nhds hpos)
  have htets : ∀ᶠ t in nhds (0 : ℝ),
      ∀ τ : PeriodicTet N N N,
        0 < cm3 (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) ∧
          ∀ f : Fin 6,
            0 < tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ f ∧
              (-1 < dihedralCos3Sq
                  (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) f ∧
                dihedralCos3Sq
                  (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) f < 1) := by
    rw [Filter.eventually_all]
    intro τ
    have h0 : ContinuousAt
        (fun t : ℝ => tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ) 0 :=
      (planeWaveTetSqEdges_contDiff N E k τ 0).continuous.continuousAt
    have hcont : Filter.Tendsto
        (fun t : ℝ => tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ)
        (nhds 0)
        (nhds (tetSqEdgesOfField N (planeWaveEdgeField N E k 0) τ)) :=
      h0.tendsto
    rw [planeWaveTetSqEdges_zero] at hcont
    have hflat := ReggeTTDerivativeGate.flat_nondegeneracy_eventually
    have hev := hcont.eventually hflat
    refine hev.mono fun t ht => ⟨ht.1, fun f => ?_⟩
    exact ⟨(ht.2 f).1, (ht.2 f).2.2⟩
  filter_upwards [hedges, htets] with t h1 h2
  exact ⟨h1, h2⟩

/-- Derivative of one edge deficit at a good amplitude. -/
theorem hasDerivAt_deficit (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) (t₀ : ℝ) (hgood : PathGoodAt N E k t₀) :
    HasDerivAt (fun t : ℝ => deficitOfField N (planeWaveEdgeField N E k t) e)
      (deficitDeriv N E k e t₀) t₀ := by
  have hall : ∀ τ ∈ (Finset.univ : Finset (PeriodicTet N N N)),
      HasDerivAt
        (fun t : ℝ =>
          edgeAngleContributionOfField N (planeWaveEdgeField N E k t) e τ)
        (contribDeriv N E k e τ t₀) t₀ := by
    intro τ _
    exact hasDerivAt_contrib N E k e τ t₀
      (fun j => ((hgood.2 τ).2 j).1) (hgood.2 τ).1
      (fun f => ⟨ne_of_gt ((hgood.2 τ).2 f).2.1,
        ne_of_lt ((hgood.2 τ).2 f).2.2⟩)
  have hsum := HasDerivAt.fun_sum hall
  have h := hsum.const_sub (2 * Real.pi)
  unfold deficitOfField deficitDeriv
  exact h

/-! ## §5. The profile derivative at every good amplitude -/

/-- The explicit first-variation integrand:
`T(t) = Σ_e [ L'_e(t)·δ_e(t) + √l_e(t)·δ'_e(t) ]`. -/
def firstVariationIntegrand (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (t : ℝ) : ℝ :=
  ∑ e : PeriodicEdge N N N,
    (edgeSqrtDeriv N E k e t *
        deficitOfField N (planeWaveEdgeField N E k t) e +
      Real.sqrt (planeWaveEdgeField N E k t e) * deficitDeriv N E k e t)

/-- THE PROFILE DERIVATIVE (THEOREM): at every good amplitude,
`S'(t) = Σ_e [ (l'_e/(2√l_e))·δ_e + √l_e·δ'_e ]` — every primed object in
explicit closed form. -/
theorem hasDerivAt_planeWaveActionProfile (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t₀ : ℝ) (hgood : PathGoodAt N E k t₀) :
    HasDerivAt (planeWaveActionProfile N E k)
      (firstVariationIntegrand N E k t₀) t₀ := by
  have hfun : planeWaveActionProfile N E k =
      fun t : ℝ => ∑ e : PeriodicEdge N N N,
        Real.sqrt (planeWaveEdgeField N E k t e) *
          deficitOfField N (planeWaveEdgeField N E k t) e := by
    funext t
    rfl
  rw [hfun]
  unfold firstVariationIntegrand
  have hall : ∀ e ∈ (Finset.univ : Finset (PeriodicEdge N N N)),
      HasDerivAt
        (fun t : ℝ => Real.sqrt (planeWaveEdgeField N E k t e) *
          deficitOfField N (planeWaveEdgeField N E k t) e)
        (edgeSqrtDeriv N E k e t₀ *
            deficitOfField N (planeWaveEdgeField N E k t₀) e +
          Real.sqrt (planeWaveEdgeField N E k t₀ e) *
            deficitDeriv N E k e t₀) t₀ := by
    intro e _
    exact (hasDerivAt_sqrtEdge N E k e t₀ (ne_of_gt (hgood.1 e))).mul
      (hasDerivAt_deficit N E k e t₀ hgood)
  exact HasDerivAt.fun_sum hall

/-! ## §6. The regrouping bijection (edge-sum ↔ tet-slot-sum) -/

/-- Constant multiplication distributes through the slot match. -/
theorem slotMatch_mul (c : ℝ) (m : Option (Fin 6)) (G : Fin 6 → ℝ) :
    (c * match m with | some f => G f | none => 0) =
      match m with | some f => c * G f | none => 0 := by
  cases m with
  | none => simp
  | some f => rfl

/-- THE REGROUPING BIJECTION (THEOREM): for every cell/tet and every
family `F`, the edge-sum of `canonicalEdgeSlot?`-matched values equals the
slot-sum over the tet's six local edges.  This is the incidence
involution reused by every regrouped Regge sum. -/
theorem sum_edges_slotMatch (cell : Vertex N N N) (tet : Fin 6)
    (F : PeriodicEdge N N N → Fin 6 → ℝ) :
    (∑ e : PeriodicEdge N N N,
      match canonicalEdgeSlot? e cell tet with
      | some f => F e f
      | none => 0) =
      ∑ f : Fin 6, F (localEdgeOf cell tet f) f := by
  have hnodup : ∀ f g : Fin 6,
      localEdgeOf cell tet f = localEdgeOf cell tet g → f = g :=
    fun f g h => canonicalPeriodicLocalEdgeNoDup N N N cell tet f g h
  have hstep : ∀ e : PeriodicEdge N N N,
      (match canonicalEdgeSlot? e cell tet with
        | some f => F e f
        | none => 0) =
        ∑ f : Fin 6, if e = localEdgeOf cell tet f then F e f else 0 := by
    intro e
    cases h : canonicalEdgeSlot? e cell tet with
    | none =>
        symm
        refine Finset.sum_eq_zero fun f _ => ?_
        rw [if_neg]
        intro heq
        have hsome := canonicalEdgeSlot_eq_some_of_noDup hnodup heq
        rw [h] at hsome
        simp at hsome
    | some f0 =>
        have he : e = localEdgeOf cell tet f0 :=
          canonicalEdgeSlot_eq_some_implies h
        symm
        rw [Finset.sum_eq_single f0]
        · rw [if_pos he]
        · intro g _ hg
          rw [if_neg]
          intro heq
          apply hg
          have h2 : localEdgeOf cell tet g = localEdgeOf cell tet f0 := by
            rw [← heq, ← he]
          exact hnodup g f0 h2
        · intro hmem
          exact absurd (Finset.mem_univ f0) hmem
  calc
    (∑ e : PeriodicEdge N N N,
        match canonicalEdgeSlot? e cell tet with
        | some f => F e f
        | none => 0)
        = ∑ e : PeriodicEdge N N N, ∑ f : Fin 6,
            if e = localEdgeOf cell tet f then F e f else 0 :=
          Finset.sum_congr rfl fun e _ => hstep e
    _ = ∑ f : Fin 6, ∑ e : PeriodicEdge N N N,
            if e = localEdgeOf cell tet f then F e f else 0 :=
          Finset.sum_comm
    _ = ∑ f : Fin 6, F (localEdgeOf cell tet f) f := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_ite_eq' Finset.univ (localEdgeOf cell tet f)
            (fun e => F e f)]
          rw [if_pos (Finset.mem_univ _)]

/-! ## §7. The pathwise Schläfli kill -/

/-- Per-tet Schläfli against the affine velocity at any nondegenerate path
point: `Σ_f √(a_f(t)) · θ'_{τf}(t) = 0`.  The proved tetrahedral Schläfli
identity holds in every coordinate direction; contracting with the
velocity kills the whole block. -/
theorem sum_sqrt_slotAngleDeriv_eq_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (τ : PeriodicTet N N N) (t : ℝ)
    (hpos : ∀ j : Fin 6,
      0 < tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ j)
    (hcm : 0 < cm3 (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ)) :
    (∑ f : Fin 6,
      Real.sqrt (tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ f) *
        slotAngleDeriv N E k τ f t) = 0 := by
  set a : SqEdges := tetSqEdgesOfField N (planeWaveEdgeField N E k t) τ with ha
  have hschl : ∀ g : Fin 6,
      (∑ f : Fin 6,
        Real.sqrt (a f) * dihedralAngle3SqClosedFormDeriv a f g) = 0 :=
    fun g =>
      Geometry.SchlaefliTetrahedronProof.tetraSchlaefliSixEdgeClosedForm
        ⟨a, hpos, hcm⟩ g
  calc
    (∑ f : Fin 6, Real.sqrt (a f) * slotAngleDeriv N E k τ f t)
        = ∑ f : Fin 6, Real.sqrt (a f) *
            (∑ g : Fin 6, planeWaveTetVelocity N E k τ g *
              dihedralAngle3SqClosedFormDeriv a f g) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          unfold slotAngleDeriv
          rw [← ha]
    _ = ∑ g : Fin 6, planeWaveTetVelocity N E k τ g *
            (∑ f : Fin 6, Real.sqrt (a f) *
              dihedralAngle3SqClosedFormDeriv a f g) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          refine Finset.sum_congr rfl fun f _ => ?_
          ring
    _ = 0 := by
          refine Finset.sum_eq_zero fun g _ => ?_
          rw [hschl g, mul_zero]

/-- THE PATHWISE SCHLÄFLI KILL (THEOREM): at every good amplitude the
ENTIRE second group `Σ_e √l_e(t)·δ'_e(t)` vanishes.  Regrouped per
tetrahedron it is a sum of per-tet Schläfli contractions.  This holds
identically on the good neighborhood of flat — not just at flat — and is
what removes every arccos second derivative from the second variation. -/
theorem sum_sqrt_deficitDeriv_eq_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) (hgood : PathGoodAt N E k t) :
    (∑ e : PeriodicEdge N N N,
      Real.sqrt (planeWaveEdgeField N E k t e) * deficitDeriv N E k e t) = 0 := by
  have hstep : ∀ e : PeriodicEdge N N N,
      Real.sqrt (planeWaveEdgeField N E k t e) * deficitDeriv N E k e t =
        -∑ τ : PeriodicTet N N N,
          (match canonicalEdgeSlot? e τ.1 τ.2 with
            | some f => Real.sqrt (planeWaveEdgeField N E k t e) *
                slotAngleDeriv N E k τ f t
            | none => 0) := by
    intro e
    unfold deficitDeriv
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    unfold contribDeriv
    exact slotMatch_mul _ _ _
  calc
    (∑ e : PeriodicEdge N N N,
        Real.sqrt (planeWaveEdgeField N E k t e) * deficitDeriv N E k e t)
        = ∑ e : PeriodicEdge N N N,
            -∑ τ : PeriodicTet N N N,
              (match canonicalEdgeSlot? e τ.1 τ.2 with
                | some f => Real.sqrt (planeWaveEdgeField N E k t e) *
                    slotAngleDeriv N E k τ f t
                | none => 0) :=
          Finset.sum_congr rfl fun e _ => hstep e
    _ = -∑ e : PeriodicEdge N N N, ∑ τ : PeriodicTet N N N,
            (match canonicalEdgeSlot? e τ.1 τ.2 with
              | some f => Real.sqrt (planeWaveEdgeField N E k t e) *
                  slotAngleDeriv N E k τ f t
              | none => 0) := by
          rw [← Finset.sum_neg_distrib]
    _ = -∑ τ : PeriodicTet N N N, ∑ e : PeriodicEdge N N N,
            (match canonicalEdgeSlot? e τ.1 τ.2 with
              | some f => Real.sqrt (planeWaveEdgeField N E k t e) *
                  slotAngleDeriv N E k τ f t
              | none => 0) := by
          rw [Finset.sum_comm]
    _ = -∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
            Real.sqrt (planeWaveEdgeField N E k t (localEdgeOf τ.1 τ.2 f)) *
              slotAngleDeriv N E k τ f t := by
          congr 1
          refine Finset.sum_congr rfl fun τ _ => ?_
          exact sum_edges_slotMatch N τ.1 τ.2
            (fun e f => Real.sqrt (planeWaveEdgeField N E k t e) *
              slotAngleDeriv N E k τ f t)
    _ = 0 := by
          rw [neg_eq_zero]
          refine Finset.sum_eq_zero fun τ _ => ?_
          exact sum_sqrt_slotAngleDeriv_eq_zero N E k τ t
            (fun j => ((hgood.2 τ).2 j).1) (hgood.2 τ).1

/-! ## §8. Gate A2(a): the first variation vanishes at flat -/

/-- Flat deficits vanish along the plane-wave family at `t = 0`
(re-export of the Stage-1 kernel theorem through the family). -/
theorem deficit_planeWave_zero (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (e : PeriodicEdge N N N) :
    deficitOfField N (planeWaveEdgeField N E k 0) e = 0 := by
  rw [planeWaveEdgeField_zero_amplitude]
  exact deficitOfField_flatEdgeField N e

/-- The first-variation integrand vanishes at flat: the deficit group dies
because flat deficits vanish, the Schläfli group dies by the pathwise
kill. -/
theorem firstVariationIntegrand_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    firstVariationIntegrand N E k 0 = 0 := by
  unfold firstVariationIntegrand
  rw [Finset.sum_add_distrib]
  have h1 : (∑ e : PeriodicEdge N N N,
      edgeSqrtDeriv N E k e 0 *
        deficitOfField N (planeWaveEdgeField N E k 0) e) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [deficit_planeWave_zero, mul_zero]
  have h2 : (∑ e : PeriodicEdge N N N,
      Real.sqrt (planeWaveEdgeField N E k 0 e) * deficitDeriv N E k e 0) = 0 :=
    sum_sqrt_deficitDeriv_eq_zero N E k 0 (pathGoodAt_zero N E k)
  rw [h1, h2, add_zero]

/-- **GATE A2(a) (THEOREM): the first variation of the true Regge action
vanishes at the flat point along every plane-wave direction.**
`S'(0) = Σ_e (l'_e/(2√l_e))·δ_e(0) + Σ_e √l_e(0)·δ'_e(0)`; the first group
dies because every flat deficit is zero (Stage-1 kernel theorem), the
second regroups per tetrahedron and dies by the proved Schläfli
identity. -/
theorem trueReggeAction_firstVariation_flat_eq_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    deriv (planeWaveActionProfile N E k) 0 = 0 := by
  have hS := hasDerivAt_planeWaveActionProfile N E k 0 (pathGoodAt_zero N E k)
  rw [hS.deriv]
  exact firstVariationIntegrand_zero N E k

/-! ## §9. Gate A2(b): the Schläfli-reduced second variation -/

/-- Flat slot sqrt-edge derivative: `L'_{τf}(0) = v_{τf}/(2√a*_f)`. -/
def flatSlotSqrtDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (τ : PeriodicTet N N N) (f : Fin 6) : ℝ :=
  planeWaveTetVelocity N E k τ f / (2 * Real.sqrt (freudenthalTetSqEdges f))

/-- Flat slot angle derivative: `θ'_{τf}(0) = Σ_g v_{τg}·J_{fg}` with `J`
the shared flat angle Jacobian of the derivative gate. -/
def flatSlotAngleDeriv (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (τ : PeriodicTet N N N) (f : Fin 6) : ℝ :=
  ∑ g : Fin 6,
    planeWaveTetVelocity N E k τ g * ReggeTTDerivativeGate.flatAngleJacobian f g

/-- The edge sqrt-derivative at flat on a matched slot is the flat slot
sqrt-derivative. -/
theorem edgeSqrtDeriv_localEdge_zero (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (τ : PeriodicTet N N N) (f : Fin 6) :
    edgeSqrtDeriv N E k (localEdgeOf τ.1 τ.2 f) 0 =
      flatSlotSqrtDeriv N E k τ f := by
  unfold edgeSqrtDeriv flatSlotSqrtDeriv edgeCoeff planeWaveTetVelocity
  simp only [planeWaveEdgeField, zero_mul, add_zero]
  rw [show periodicDispSqEdge ((localEdgeOf τ.1 τ.2 f).disp) =
      freudenthalTetSqEdges f from
    (freudenthalTet_sqEdge_eq_periodicDispSqEdge_localEdgeOf τ.1 τ.2 f).symm]

/-- The slot angle derivative at flat is the flat Jacobian contraction. -/
theorem slotAngleDeriv_zero (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (τ : PeriodicTet N N N) (f : Fin 6) :
    slotAngleDeriv N E k τ f 0 = flatSlotAngleDeriv N E k τ f := by
  unfold slotAngleDeriv flatSlotAngleDeriv
  rw [planeWaveTetSqEdges_zero]
  rfl

/-- The deficit-group first variation regrouped at flat:
`Σ_e L'_e(0)·δ'_e(0) = −Σ_τ Σ_f L'_{τf}(0)·θ'_{τf}(0)`. -/
theorem sum_edgeSqrtDeriv_deficitDeriv_flat (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    (∑ e : PeriodicEdge N N N,
      edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0) =
      -∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
        flatSlotSqrtDeriv N E k τ f * flatSlotAngleDeriv N E k τ f := by
  have hstep : ∀ e : PeriodicEdge N N N,
      edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0 =
        -∑ τ : PeriodicTet N N N,
          (match canonicalEdgeSlot? e τ.1 τ.2 with
            | some f => edgeSqrtDeriv N E k e 0 * slotAngleDeriv N E k τ f 0
            | none => 0) := by
    intro e
    unfold deficitDeriv
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    unfold contribDeriv
    exact slotMatch_mul _ _ _
  calc
    (∑ e : PeriodicEdge N N N,
        edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0)
        = ∑ e : PeriodicEdge N N N,
            -∑ τ : PeriodicTet N N N,
              (match canonicalEdgeSlot? e τ.1 τ.2 with
                | some f => edgeSqrtDeriv N E k e 0 *
                    slotAngleDeriv N E k τ f 0
                | none => 0) :=
          Finset.sum_congr rfl fun e _ => hstep e
    _ = -∑ e : PeriodicEdge N N N, ∑ τ : PeriodicTet N N N,
            (match canonicalEdgeSlot? e τ.1 τ.2 with
              | some f => edgeSqrtDeriv N E k e 0 *
                  slotAngleDeriv N E k τ f 0
              | none => 0) := by
          rw [← Finset.sum_neg_distrib]
    _ = -∑ τ : PeriodicTet N N N, ∑ e : PeriodicEdge N N N,
            (match canonicalEdgeSlot? e τ.1 τ.2 with
              | some f => edgeSqrtDeriv N E k e 0 *
                  slotAngleDeriv N E k τ f 0
              | none => 0) := by
          rw [Finset.sum_comm]
    _ = -∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
            edgeSqrtDeriv N E k (localEdgeOf τ.1 τ.2 f) 0 *
              slotAngleDeriv N E k τ f 0 := by
          congr 1
          refine Finset.sum_congr rfl fun τ _ => ?_
          exact sum_edges_slotMatch N τ.1 τ.2
            (fun e f => edgeSqrtDeriv N E k e 0 * slotAngleDeriv N E k τ f 0)
    _ = -∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
            flatSlotSqrtDeriv N E k τ f * flatSlotAngleDeriv N E k τ f := by
          congr 1
          refine Finset.sum_congr rfl fun τ _ => ?_
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [edgeSqrtDeriv_localEdge_zero, slotAngleDeriv_zero]

/-- The reduced first-variation function: near flat, `S'` agrees with the
deficit group alone (the Schläfli group is identically zero on the good
neighborhood). -/
def reducedFirstVariation (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ)
    (t : ℝ) : ℝ :=
  ∑ e : PeriodicEdge N N N,
    edgeSqrtDeriv N E k e t *
      deficitOfField N (planeWaveEdgeField N E k t) e

/-- Near flat, the full first-variation integrand equals the reduced
(deficit-group-only) form. -/
theorem firstVariationIntegrand_eq_reduced (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (t : ℝ) (hgood : PathGoodAt N E k t) :
    firstVariationIntegrand N E k t = reducedFirstVariation N E k t := by
  unfold firstVariationIntegrand reducedFirstVariation
  rw [Finset.sum_add_distrib, sum_sqrt_deficitDeriv_eq_zero N E k t hgood,
    add_zero]

/-- `deriv S` agrees with the reduced first variation on a neighborhood of
flat. -/
theorem deriv_actionProfile_eventuallyEq_reduced (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    deriv (planeWaveActionProfile N E k) =ᶠ[nhds (0 : ℝ)]
      reducedFirstVariation N E k := by
  filter_upwards [eventually_pathGoodAt N E k] with t hgood
  rw [(hasDerivAt_planeWaveActionProfile N E k t hgood).deriv]
  exact firstVariationIntegrand_eq_reduced N E k t hgood

/-- The sqrt-derivative factor is differentiable at flat (needed only for
the product rule; its derivative value multiplies the vanishing flat
deficit and never appears in the reduced formula). -/
theorem edgeSqrtDeriv_differentiableAt (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) (e : PeriodicEdge N N N) :
    DifferentiableAt ℝ (fun t : ℝ => edgeSqrtDeriv N E k e t) 0 := by
  have hpos : 0 < planeWaveEdgeField N E k 0 e := (pathGoodAt_zero N E k).1 e
  have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (planeWaveEdgeField N E k t e))
      (edgeSqrtDeriv N E k e 0) 0 :=
    hasDerivAt_sqrtEdge N E k e 0 (ne_of_gt hpos)
  have hden : DifferentiableAt ℝ
      (fun t : ℝ => 2 * Real.sqrt (planeWaveEdgeField N E k t e)) 0 :=
    (hsq.differentiableAt).const_mul 2
  have hden_ne : 2 * Real.sqrt (planeWaveEdgeField N E k 0 e) ≠ 0 := by
    have : 0 < Real.sqrt (planeWaveEdgeField N E k 0 e) :=
      Real.sqrt_pos.mpr hpos
    positivity
  exact (differentiableAt_const (edgeCoeff N E k e)).div hden hden_ne

/-- Derivative of the reduced first variation at flat: only the
`L'_e(0)·δ'_e(0)` group survives (the other product-rule term carries the
vanishing flat deficit). -/
theorem hasDerivAt_reducedFirstVariation_flat (E : Fin 3 → Fin 3 → ℝ)
    (k : Fin 3 → ℝ) :
    HasDerivAt (reducedFirstVariation N E k)
      (∑ e : PeriodicEdge N N N,
        edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0) 0 := by
  have hterm : ∀ e : PeriodicEdge N N N,
      HasDerivAt
        (fun t : ℝ => edgeSqrtDeriv N E k e t *
          deficitOfField N (planeWaveEdgeField N E k t) e)
        (edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0) 0 := by
    intro e
    have hu : HasDerivAt (fun t : ℝ => edgeSqrtDeriv N E k e t)
        (deriv (fun t : ℝ => edgeSqrtDeriv N E k e t) 0) 0 :=
      (edgeSqrtDeriv_differentiableAt N E k e).hasDerivAt
    have hv : HasDerivAt
        (fun t : ℝ => deficitOfField N (planeWaveEdgeField N E k t) e)
        (deficitDeriv N E k e 0) 0 :=
      hasDerivAt_deficit N E k e 0 (pathGoodAt_zero N E k)
    have hprod := hu.mul hv
    have hδ0 : deficitOfField N (planeWaveEdgeField N E k 0) e = 0 :=
      deficit_planeWave_zero N E k e
    rw [hδ0, mul_zero, zero_add] at hprod
    exact hprod
  have hall : ∀ e ∈ (Finset.univ : Finset (PeriodicEdge N N N)),
      HasDerivAt
        (fun t : ℝ => edgeSqrtDeriv N E k e t *
          deficitOfField N (planeWaveEdgeField N E k t) e)
        (edgeSqrtDeriv N E k e 0 * deficitDeriv N E k e 0) 0 :=
    fun e _ => hterm e
  have hsum := HasDerivAt.fun_sum hall
  unfold reducedFirstVariation
  exact hsum

/-- **GATE A2(b) HEADLINE (THEOREM): the Schläfli-reduced second variation
of the true Regge action at flat, as a kernel equation.**

`S''(0) = −Σ_τ Σ_f L'_{τf}(0) · θ'_{τf}(0)`

with `L'_{τf}(0) = v_{τf}/(2√a*_f)` and `θ'_{τf}(0) = Σ_g v_{τg}·J_{fg}`
(flat angle Jacobian of the derivative gate).  NO second derivative of
`arccos` appears: near flat, `S'` equals the deficit group alone because
the Schläfli group vanishes identically on the good neighborhood
(pathwise Schläfli kill); differentiating the deficit group at flat and
using `δ_e(0) = 0` leaves exactly the displayed contraction.  The
explicit-G Hessian stage is thereby deleted from the critical path. -/
theorem trueReggeAction_secondVariation_flat_schlaefli
    (E : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    iteratedDeriv 2 (planeWaveActionProfile N E k) 0 =
      -∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
        flatSlotSqrtDeriv N E k τ f * flatSlotAngleDeriv N E k τ f := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [Filter.EventuallyEq.deriv_eq
    (deriv_actionProfile_eventuallyEq_reduced N E k)]
  rw [(hasDerivAt_reducedFirstVariation_flat N E k).deriv]
  exact sum_edgeSqrtDeriv_deficitDeriv_flat N E k

/-! ## §10. Gate A2(c): symbolic cross-check instantiation (axis direction)

The preregistered axis direction `m = (1,0,0)` with the `+`-polarization at
`N = 3`, stated as a named `Finset`-sum expression plus the kernel equation
that the reduced formula computes that instance.  NO numeric value is
claimed and nothing is evaluated. -/

/-- The reduced second-variation value for the axis instance at `N = 3`,
as a `Finset` sum expression (`#eval`-free; MODEL-level named quantity —
its VALUE is not computed or claimed anywhere in this development). -/
def axisReducedSecondVariation : ℝ :=
  -∑ τ : PeriodicTet 3 3 3, ∑ f : Fin 6,
    flatSlotSqrtDeriv 3 axisTTPolarizationPlus
        (commensurateMomentum 3 axisWaveVector) τ f *
      flatSlotAngleDeriv 3 axisTTPolarizationPlus
        (commensurateMomentum 3 axisWaveVector) τ f

/-- GATE A2(c) (THEOREM): the reduced formula applies verbatim to the
preregistered axis instance — its `S''(0)` IS the named `Finset` sum.
Cross-check hook for the (non-proof) numerics lane; no value claimed. -/
theorem axisReducedSecondVariation_applies :
    iteratedDeriv 2
      (planeWaveActionProfile 3 axisTTPolarizationPlus
        (commensurateMomentum 3 axisWaveVector)) 0 =
      axisReducedSecondVariation :=
  trueReggeAction_secondVariation_flat_schlaefli 3 axisTTPolarizationPlus
    (commensurateMomentum 3 axisWaveVector)

/-! ## §11. Combination with Gate A1: the symbol value in reduced form -/

/-- COMBINED COROLLARY (THEOREM): the fixed-`N` TT Bloch symbol value of
Gate A1 equals `(2/N³)` times the Schläfli-reduced contraction — existence
and reduced form together, still with no evaluation and no continuum
claim. -/
theorem planeWave_TTBlochSymbolIs_reduced (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) :
    TTBlochSymbolIs N E m
      ((2 / (N : ℝ) ^ (3 : ℕ)) *
        (-∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
          flatSlotSqrtDeriv N E (commensurateMomentum N m) τ f *
            flatSlotAngleDeriv N E (commensurateMomentum N m) τ f)) := by
  have h := planeWave_TTBlochSymbolIs_secondVariation N E m
  rwa [trueReggeAction_secondVariation_flat_schlaefli N E
    (commensurateMomentum N m)] at h

end

end ReggeTTFlatSecondVariation
end Analysis
end Gravity
end IndisputableMonolith
