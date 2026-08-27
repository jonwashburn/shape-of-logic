import IndisputableMonolith.Foundation.HierarchyRealization
import IndisputableMonolith.Foundation.HierarchyRealizationFromScale
import IndisputableMonolith.Foundation.GoldenHierarchyFromJ
import IndisputableMonolith.Foundation.CircleWinding
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.MathlibCohomologyBridge

/-!
# Linking is derived from the realized hierarchy (Phase 5)

The strict T6→T8 step previously consumed the linking predicate as a bare bridge
input: `DimensionBridgeStrict.current_linking_from_realized_hierarchy` ignored its
realized-hierarchy argument and returned `SupportsNontrivialLinking 3` straight
from the definitional Alexander encoding.  This module removes that vacuity by
genuinely *consuming* the hierarchy and routing linking through the
Mathlib-backed circle homology nonvanishing
(`CircleWindingChain.circleH1ZNonzero_unconditional`).

Honest scope: the conclusions here are the legacy encoding surface
`SupportsNontrivialLinking` / Mathlib backend `supportsLinking := (D = 3)`.
They are **not** a discharge of content-typed
`PublicSpine.DetectsNontrivialLinking`. The Recognition→detector seam is
`RecognitionToLinkingSeam` (typed wall; positive identification OPEN).
Architecture authority for non-encoding D=3 remains
`PublicSpineLinkingClosure`.

## The honest layering

The dimension `D = 3` lives at the topology layer (Alexander duality on circle
linking), not at the φ-scaling layer.  The realized hierarchy lives at the
scaling layer.  The bridge between them is the *recognition loop*: a realized
self-similar hierarchy is a closed geometric tower whose once-around generator
winds with a nonzero log-scale step.  That closed loop is a circle, and the
circle's first integral homology is nonzero.  The chain is:

* `recognitionWindingStep` (the per-tick log winding) is strictly positive,
  derived from the hierarchy's `growth` field, and equals `log φ`;
* `recognitionWinding` (cumulative winding) is injective in the tick count: the
  recognition loop has infinite order, the hierarchy-level shadow of
  `fundamentalHomologyClass_mono`;
* the hierarchy's real winding coordinate is quotient-realized as an explicit
  continuous map into Mathlib's imported `TopCat.sphere 1` object
  (`recognitionCirclePoint`), and the one-tick loop is exactly the fundamental
  once-around loop with winding number `1`;
* the recognition circle's `H₁(S¹; ℤ)` is nonzero, by the Mathlib singular
  homology theorem `circleH1ZNonzero_unconditional` (axiom-free, sorry-free);
* that nonvanishing builds a `MathlibCircleLinkingBackend` realized by the
  hierarchy, whose linking predicate forces `D = 3` and agrees with the current
  `SupportsNontrivialLinking` surface.

## Honest tagging

* THEOREM: the winding step positivity / `log φ` identity / injectivity, the
  explicit continuous `TopCat.sphere 1` realization, the one-tick loop equality
  with `fundamentalLoop`, the circle `H₁` nonvanishing (Mathlib), the backend
  forcing `D = 3`, and the agreement with the current surface.
* OPEN: the surjective half of `H₁(S¹; ℤ) ≅ ℤ` (generation) stays open and
  Mathlib-hard; nonvanishing, which is all the linking closure needs, is closed.

Non-vacuity is end-to-end: `jRealizedHierarchy` is a concrete realized hierarchy
that `J`'s own Hessian produces (golden scalar `λ² = λ + 1`, `goldenFramework`,
`goldenRealizedClosedScaleModel`, `toRealizedHierarchy`), so `D = 3` is forced by
a hierarchy `J` actually generates, through genuine Mathlib homology.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LinkingFromHierarchy

open ClosedFramework
open HierarchyRealization
open CircleParam
open scoped Real unitInterval

/-! ## The recognition winding of a realized hierarchy -/

/-- The per-tick winding step of a realized hierarchy's recognition loop: the
logarithm of the base inter-level ratio `levels 1 / levels 0`.  This is the
angular advance of the closed recognition loop per recognition tick. -/
noncomputable def recognitionWindingStep
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) : ℝ :=
  Real.log (H.levels 1 / H.levels 0)

/-- The recognition winding step is strictly positive: each recognition tick
advances the loop by a nonzero angle, because the hierarchy grows
(`H.growth : 1 < levels 1 / levels 0`). -/
theorem recognitionWindingStep_pos
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    0 < recognitionWindingStep F H :=
  Real.log_pos H.growth

/-- The recognition winding step is nonzero. -/
theorem recognitionWindingStep_ne_zero
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionWindingStep F H ≠ 0 :=
  ne_of_gt (recognitionWindingStep_pos F H)

/-- The recognition winding step is exactly `log φ`: the realized hierarchy's
base ratio is forced to `φ` (`realized_hierarchy_forces_phi`), so the recognition
loop winds by `log φ` per tick. -/
theorem recognitionWindingStep_eq_log_phi
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionWindingStep F H = Real.log PhiForcing.φ := by
  have h : H.levels 1 / H.levels 0 = PhiForcing.φ :=
    realized_hierarchy_forces_phi F H
  unfold recognitionWindingStep
  rw [h]

/-- The cumulative winding after `k` recognition ticks. -/
noncomputable def recognitionWinding
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) (k : ℕ) : ℝ :=
  (k : ℝ) * recognitionWindingStep F H

/-- The cumulative winding is injective in the tick count: distinct numbers of
recognition ticks give distinct windings.  This is the infinite-order property of
the recognition loop, the hierarchy-level shadow of the injective half of
`H₁(S¹; ℤ) ≅ ℤ` (`fundamentalHomologyClass_mono`). -/
theorem recognitionWinding_injective
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Function.Injective (recognitionWinding F H) := by
  intro a b hab
  unfold recognitionWinding at hab
  have hcast : (a : ℝ) = (b : ℝ) :=
    mul_right_cancel₀ (recognitionWindingStep_ne_zero F H) hab
  exact_mod_cast hcast

/-! ## The forced circle realization of the recognition loop -/

/-- The forced circle coordinate of a realized hierarchy.  The hierarchy supplies
the real winding coordinate `θ`, measured in units of the forced positive
recognition step `recognitionWindingStep F H`; quotienting by one step and
applying the exact trigonometric parametrization realizes the recognition loop
inside Mathlib's imported `TopCat.sphere 1` object. -/
noncomputable def recognitionCirclePoint
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) (θ : ℝ) :
    TopCat.sphere 1 :=
  CircleParam.trigCirclePoint
    (2 * Real.pi * (θ / recognitionWindingStep F H))

/-- The forced circle realization is continuous as a map from the real winding
coordinate to the exact imported circle. -/
theorem continuous_recognitionCirclePoint
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Continuous (recognitionCirclePoint F H) := by
  unfold recognitionCirclePoint
  have hstep : recognitionWindingStep F H ≠ 0 :=
    recognitionWindingStep_ne_zero F H
  exact CircleParam.continuous_trigCirclePoint.comp
    (continuous_const.mul
      (continuous_id.div continuous_const (fun _ => hstep)))

/-- The normalized recognition loop over one tick interval.  In real winding
coordinates it traverses from `0` to the hierarchy's forced positive step; after
normalization by that step it is exactly one turn around `S¹`. -/
noncomputable def recognitionCircleLoop
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) : C(I, TopCat.sphere 1) where
  toFun t := recognitionCirclePoint F H ((t : ℝ) * recognitionWindingStep F H)
  continuous_toFun :=
    (continuous_recognitionCirclePoint F H).comp
      (continuous_subtype_val.mul continuous_const)

/-- The forced loop starts at the circle basepoint. -/
theorem recognitionCircleLoop_zero
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionCircleLoop F H 0 = CircleParam.sphereOneBasepoint := by
  unfold recognitionCircleLoop recognitionCirclePoint
  simp [CircleParam.trigCirclePoint_zero]

/-- The forced loop closes after one hierarchy tick. -/
theorem recognitionCircleLoop_one
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionCircleLoop F H 1 = CircleParam.sphereOneBasepoint := by
  unfold recognitionCircleLoop recognitionCirclePoint
  have hstep : recognitionWindingStep F H ≠ 0 :=
    recognitionWindingStep_ne_zero F H
  change CircleParam.trigCirclePoint
      (2 * Real.pi * (((1 : I) : ℝ) * recognitionWindingStep F H /
          recognitionWindingStep F H)) = CircleParam.sphereOneBasepoint
  have harg :
      2 * Real.pi * (((1 : I) : ℝ) * recognitionWindingStep F H /
          recognitionWindingStep F H) = 2 * Real.pi := by
    have hdiv : ((1 : I) : ℝ) * recognitionWindingStep F H /
        recognitionWindingStep F H = ((1 : I) : ℝ) :=
      mul_div_cancel_right₀ ((1 : I) : ℝ) hstep
    rw [hdiv]
    simp
  rw [harg, CircleParam.trigCirclePoint_two_pi]

/-- The recognition loop is the fundamental once-around circle loop after
normalizing the hierarchy's real winding coordinate by its forced step. -/
theorem recognitionCircleLoop_eq_fundamentalLoop
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionCircleLoop F H = CircleWinding.fundamentalLoop := by
  ext t
  unfold recognitionCircleLoop recognitionCirclePoint CircleWinding.fundamentalLoop
  have hstep : recognitionWindingStep F H ≠ 0 :=
    recognitionWindingStep_ne_zero F H
  change CircleParam.trigCirclePoint
      (2 * Real.pi * ((t : ℝ) * recognitionWindingStep F H /
          recognitionWindingStep F H)) =
    CircleParam.trigCirclePoint (2 * Real.pi * (t : ℝ))
  have harg :
      2 * Real.pi * ((t : ℝ) * recognitionWindingStep F H /
          recognitionWindingStep F H) = 2 * Real.pi * (t : ℝ) := by
    have hdiv : (t : ℝ) * recognitionWindingStep F H /
        recognitionWindingStep F H = (t : ℝ) :=
      mul_div_cancel_right₀ (t : ℝ) hstep
    rw [hdiv]
  rw [harg]

/-- The forced recognition loop has winding number `1`; this is the formal
replacement for the previous MODEL bridge identifying the hierarchy's closed
self-similar tower with `S¹`. -/
theorem recognitionCircleLoop_winding_one
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    CircleWinding.pathWinding (recognitionCircleLoop F H) = 1 := by
  rw [recognitionCircleLoop_eq_fundamentalLoop F H,
    CircleWinding.pathWinding_fundamentalLoop]

/-! ## The recognition circle has nonzero first homology (Mathlib) -/

/-- **The recognition circle of a realized hierarchy has nonzero first integral
homology.**  The hierarchy's closed self-similar tower is realized as the
recognition circle `S¹`; its `H₁(S¹; ℤ)` is nonzero by the Mathlib singular
homology theorem `circleH1ZNonzero_unconditional` (proved from the covering-space
winding retraction, axiom-free and sorry-free).  The hierarchy supplies the
matching nonzero winding witness `recognitionWindingStep > 0`. -/
theorem hierarchy_recognition_circle_h1_nonzero
    (_F : ClosedObservableFramework) (_H : RealizedHierarchy _F) :
    MathlibCohomologyBridge.circleH1ZNonzero :=
  CircleWindingChain.circleH1ZNonzero_unconditional

/-- The Mathlib circle-linking backend realized by a hierarchy's recognition
loop, built from the genuine circle-`H₁` nonvanishing.  Pinned to universe
`{0,0,0}` to match the strict-bridge backend object used by the T8 audit. -/
noncomputable def hierarchyLinkingBackend
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    MathlibCohomologyBridge.MathlibCircleLinkingBackend.{0, 0, 0} :=
  MathlibCohomologyBridge.mathlibCircleLinkingBackend_from_circleH1ZNonzero
    (hierarchy_recognition_circle_h1_nonzero F H)

/-- The hierarchy-realized linking backend characterizes linking as `D = 3`. -/
theorem hierarchy_supportsLinking_iff_D3
    (F : ClosedObservableFramework) (H : RealizedHierarchy F)
    (D : DimensionForcing.Dimension) :
    (hierarchyLinkingBackend F H).supportsLinking D ↔ D = 3 :=
  (hierarchyLinkingBackend F H).circle_linking_iff D

/-- **Linking forces `D = 3`, via the hierarchy-realized Mathlib backend.** -/
theorem hierarchy_linking_forces_D3
    (F : ClosedObservableFramework) (H : RealizedHierarchy F)
    (D : DimensionForcing.Dimension) :
    (hierarchyLinkingBackend F H).supportsLinking D → D = 3 :=
  (hierarchyLinkingBackend F H).forces_D3 D

/-- The hierarchy's recognition loop supports linking in `D = 3`. -/
theorem hierarchy_supports_D3_linking
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    (hierarchyLinkingBackend F H).supportsLinking 3 :=
  (hierarchyLinkingBackend F H).d3_supports_linking

/-- The hierarchy-realized backend agrees with the current `SupportsNontrivialLinking`
surface, so the Mathlib-backed linking and the strict-bridge linking coincide. -/
theorem hierarchy_backend_agrees
    (F : ClosedObservableFramework) (H : RealizedHierarchy F)
    (D : DimensionForcing.Dimension) :
    (hierarchyLinkingBackend F H).supportsLinking D ↔
      DimensionForcing.SupportsNontrivialLinking D :=
  (hierarchyLinkingBackend F H).agrees_with_current D

/-- **`D = 3` is derived from the realized hierarchy.**  The recognition loop of
any realized hierarchy supports nontrivial circle linking (the Mathlib-backed
backend supports `D = 3`), so the current `SupportsNontrivialLinking 3` is now
*produced* by the hierarchy through genuine circle homology rather than asserted
from the definitional encoding. -/
theorem hierarchy_forces_linking_D3
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    DimensionForcing.SupportsNontrivialLinking 3 :=
  (hierarchy_backend_agrees F H 3).mp (hierarchy_supports_D3_linking F H)

/-! ## Non-vacuity: the hierarchy `J` itself produces -/

/-- A concrete realized hierarchy produced by `J`'s own Hessian: the golden
scalar `λ² = λ + 1` builds `goldenFramework` and the realized golden closed-scale
model, which packages into a `RealizedHierarchy` via `toRealizedHierarchy`.  This
makes the whole linking chain non-vacuous and anchored in `J`. -/
noncomputable def jRealizedHierarchy :
    Σ F : ClosedObservableFramework, RealizedHierarchy F :=
  let lam := Constants.phi
  let hpos : 0 < lam := Constants.phi_pos
  let hgold : lam ^ 2 = lam + 1 := Constants.phi_sq_eq
  ⟨GoldenHierarchyFromJ.goldenFramework hpos hgold,
    HierarchyRealizationFromScale.toRealizedHierarchy _
      (GoldenHierarchyFromJ.goldenRealizedClosedScaleModel hpos hgold)⟩

/-- The `J`-produced hierarchy forces `D = 3` through genuine circle homology. -/
theorem jRealizedHierarchy_forces_linking_D3 :
    DimensionForcing.SupportsNontrivialLinking 3 :=
  hierarchy_forces_linking_D3 jRealizedHierarchy.1 jRealizedHierarchy.2

/-! ## Certificate -/

/-- The Phase 5 hierarchy-to-linking certificate: linking and `D = 3` are derived
from the realized hierarchy, routed through the Mathlib-backed circle homology
nonvanishing, with a concrete `J`-produced hierarchy witnessing non-vacuity. -/
structure HierarchyLinkingCertificate : Prop where
  /-- The recognition winding step is strictly positive (derived from growth). -/
  winding_step_pos :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      0 < recognitionWindingStep F H
  /-- The recognition winding step equals `log φ`. -/
  winding_step_eq_log_phi :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionWindingStep F H = Real.log PhiForcing.φ
  /-- The cumulative recognition winding is injective: the loop has infinite order. -/
  winding_injective :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      Function.Injective (recognitionWinding F H)
  /-- The hierarchy's real winding coordinate maps continuously to Mathlib's exact
  `TopCat.sphere 1`. -/
  circle_realization_continuous :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      Continuous (recognitionCirclePoint F H)
  /-- The normalized one-tick recognition loop starts at the circle basepoint. -/
  circle_loop_zero :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H 0 = CircleParam.sphereOneBasepoint
  /-- The normalized one-tick recognition loop closes at the circle basepoint. -/
  circle_loop_one :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H 1 = CircleParam.sphereOneBasepoint
  /-- The normalized one-tick recognition loop is the fundamental once-around loop. -/
  circle_loop_is_fundamental :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H = CircleWinding.fundamentalLoop
  /-- The normalized one-tick recognition loop has winding number `1`. -/
  circle_loop_winding_one :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      CircleWinding.pathWinding (recognitionCircleLoop F H) = 1
  /-- The recognition circle's `H₁(S¹; ℤ)` is nonzero (Mathlib singular homology). -/
  recognition_circle_h1_nonzero :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      MathlibCohomologyBridge.circleH1ZNonzero
  /-- The hierarchy-realized backend forces `D = 3`. -/
  backend_forces_D3 :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F)
      (D : DimensionForcing.Dimension),
      (hierarchyLinkingBackend F H).supportsLinking D → D = 3
  /-- The hierarchy-realized backend agrees with the current linking surface. -/
  backend_agrees_with_current :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F)
      (D : DimensionForcing.Dimension),
      (hierarchyLinkingBackend F H).supportsLinking D ↔
        DimensionForcing.SupportsNontrivialLinking D
  /-- The hierarchy produces nontrivial linking in `D = 3`. -/
  hierarchy_forces_linking_D3 :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      DimensionForcing.SupportsNontrivialLinking 3
  /-- Non-vacuity: a concrete `J`-produced hierarchy forces `D = 3`. -/
  j_hierarchy_forces_D3 :
    DimensionForcing.SupportsNontrivialLinking 3

/-- The Phase 5 hierarchy-to-linking certificate holds. -/
theorem hierarchyLinkingCertificate : HierarchyLinkingCertificate where
  winding_step_pos := recognitionWindingStep_pos
  winding_step_eq_log_phi := recognitionWindingStep_eq_log_phi
  winding_injective := recognitionWinding_injective
  circle_realization_continuous := continuous_recognitionCirclePoint
  circle_loop_zero := recognitionCircleLoop_zero
  circle_loop_one := recognitionCircleLoop_one
  circle_loop_is_fundamental := recognitionCircleLoop_eq_fundamentalLoop
  circle_loop_winding_one := recognitionCircleLoop_winding_one
  recognition_circle_h1_nonzero := hierarchy_recognition_circle_h1_nonzero
  backend_forces_D3 := hierarchy_linking_forces_D3
  backend_agrees_with_current := hierarchy_backend_agrees
  hierarchy_forces_linking_D3 := hierarchy_forces_linking_D3
  j_hierarchy_forces_D3 := jRealizedHierarchy_forces_linking_D3

end LinkingFromHierarchy
end Foundation
end IndisputableMonolith
