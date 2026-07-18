import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.ZqContinuumBlocker
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplexWick
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D

/-!
# Seven Gaps, P2.5: metric-refinement carrier blocker

`PathSumMeasure.BoundedComplex B` contains only cardinalities and incidence
maps. Its quotient `TriangulationClass B` therefore identifies combinatorial
types, not metric geometries. This file gives a concrete kernel certificate
of the resulting P2.5 obstruction.

The existing nonempty simplicial witness `oneTetComplex` admits two positive,
nondegenerate metric decorations at the same cap and in the same quotient
class. Their edge lengths differ, and their Cayley-Menger observable differs.
Consequently no function on `TriangulationClass 6` alone can recover either
observable for both decorations. The forgetful map from metric-decorated
simplicial complexes to the current quotient is explicitly non-injective.

The final section supplies the missing carrier shape
`MetricRefinementFamily`. It has finite metric-decorated configuration spaces,
a genuine mesh tending to zero, coarse projections, and summable local
action-step control. It does not assume convergence of the path sum. With a
measure supplied separately, it is just enough to define the geometric
finite-level path sum and state its continuum-limit proposition.

Honesty boundary:
* THEOREM: all obstruction and witness results below.
* MODEL/API: `MetricDecoration`, `MetricDecoratedComplex`, and
  `MetricRefinementFamily` are the minimal proposed carrier interface.
* OPEN: construction of such a family from the recognition substrate,
  derivation of its measure and action, and the geometric continuum theorem.

No full-theory flag is changed. Complexity-cutoff convergence remains
different from metric mesh refinement.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace MetricRefinementCarrierBlocker

open PathSumMeasure
open ExactShellGaugeUV
open ZqContinuumBlocker
open Geometry.CayleyMengerPolynomial

noncomputable section

/-! ## 1. Metric data missing from `BoundedComplex` -/

/-- Positive squared-edge data decorating one combinatorial carrier. The
carrier itself remains exactly the existing `BoundedComplex`. -/
structure MetricDecoration {B : ℕ} (K : BoundedComplex B) where
  sqEdge : Fin K.nE → ℝ
  sqEdge_pos : ∀ e, 0 < sqEdge e

/-- A simplicial carrier together with metric data. This is the smallest
configuration object on which mesh-sensitive observables can be evaluated. -/
structure MetricDecoratedComplex (B : ℕ) where
  carrier : BoundedComplex B
  simplicial : IsSimplicial carrier
  metric : MetricDecoration carrier

/-- Forgetting the metric returns exactly the current combinatorial quotient
class. -/
def MetricDecoratedComplex.toClass {B : ℕ} (G : MetricDecoratedComplex B) :
    TriangulationClass B :=
  Quotient.mk (relabelSetoid B) G.carrier

/-! ## 2. Two metrics on the same admissible combinatorial class -/

/-- Unit squared-edge metric on the existing one-tetrahedron simplicial
carrier. -/
def unitDecoration : MetricDecoration oneTetComplex where
  sqEdge := fun _ => 1
  sqEdge_pos := fun _ => one_pos

/-- Squared-edge metric of a regular tetrahedron with edge length two, on the
same one-tetrahedron simplicial carrier. -/
def doubleDecoration : MetricDecoration oneTetComplex where
  sqEdge := fun _ => 4
  sqEdge_pos := fun _ => by norm_num

/-- The length of the first edge. This is a genuine metric observable because
it reads the square root of the stored squared-edge datum. -/
def firstEdgeLength (D : MetricDecoration oneTetComplex) : ℝ :=
  Real.sqrt (D.sqEdge (show Fin oneTetComplex.nE from (0 : Fin 6)))

/-- The Cayley-Menger observable of the decorated tetrahedron. It is
`288 * volume^2` on realizable tetrahedra and enters the Regge metric API. -/
def cayleyMengerObservable (D : MetricDecoration oneTetComplex) : ℝ :=
  cm3 D.sqEdge

theorem unitDecoration_firstEdgeLength :
    firstEdgeLength unitDecoration = 1 := by
  norm_num [firstEdgeLength, unitDecoration]

theorem doubleDecoration_firstEdgeLength :
    firstEdgeLength doubleDecoration = 2 := by
  norm_num [firstEdgeLength, doubleDecoration]

theorem unitDecoration_cayleyMenger :
    cayleyMengerObservable unitDecoration = 4 := by
  norm_num [cayleyMengerObservable, unitDecoration, cm3]

theorem doubleDecoration_cayleyMenger :
    cayleyMengerObservable doubleDecoration = 256 := by
  norm_num [cayleyMengerObservable, doubleDecoration, cm3]

/-- The two metric decorations are distinct, witnessed by their first edge
lengths. -/
theorem unitDecoration_ne_doubleDecoration :
    unitDecoration ≠ doubleDecoration := by
  intro h
  have hobs := congrArg firstEdgeLength h
  rw [unitDecoration_firstEdgeLength, doubleDecoration_firstEdgeLength] at hobs
  norm_num at hobs

/-- Both decorations live over one genuine simplicial carrier of exact
combinatorial complexity six, but have different edge and volume data. -/
theorem oneTetClass_has_two_metric_decorations :
    IsSimplicial oneTetComplex ∧
      complexity oneTetComplex = 6 ∧
      ∃ D₁ D₂ : MetricDecoration oneTetComplex,
        D₁ ≠ D₂ ∧
        firstEdgeLength D₁ = 1 ∧ firstEdgeLength D₂ = 2 ∧
        cayleyMengerObservable D₁ = 4 ∧
          cayleyMengerObservable D₂ = 256 := by
  refine ⟨oneTetComplex_isSimplicial, rfl,
    unitDecoration, doubleDecoration, unitDecoration_ne_doubleDecoration,
    unitDecoration_firstEdgeLength, doubleDecoration_firstEdgeLength,
    unitDecoration_cayleyMenger, doubleDecoration_cayleyMenger⟩

/-- The one-tetrahedron quotient class at cap six. -/
def oneTetClass : TriangulationClass 6 :=
  Quotient.mk (relabelSetoid 6) oneTetComplex

/-- **P2.5 MESH BLOCKER.** No function of the current combinatorial quotient
class alone can recover the first-edge length of both admissible metric
decorations. -/
theorem no_class_only_mesh_recovers_both
    (mesh : TriangulationClass 6 → ℝ) :
    ¬ (mesh oneTetClass = firstEdgeLength unitDecoration ∧
      mesh oneTetClass = firstEdgeLength doubleDecoration) := by
  rw [unitDecoration_firstEdgeLength, doubleDecoration_firstEdgeLength]
  rintro ⟨h₁, h₂⟩
  linarith

/-- The same obstruction holds for an action-relevant Cayley-Menger
observable, not only for a chosen edge coordinate. -/
theorem no_class_only_cayleyMenger_recovers_both
    (observable : TriangulationClass 6 → ℝ) :
    ¬ (observable oneTetClass = cayleyMengerObservable unitDecoration ∧
      observable oneTetClass = cayleyMengerObservable doubleDecoration) := by
  rw [unitDecoration_cayleyMenger, doubleDecoration_cayleyMenger]
  rintro ⟨h₁, h₂⟩
  linarith

/-- The unit metric packaged as a metric-decorated simplicial complex. -/
def unitMetricOneTet : MetricDecoratedComplex 6 where
  carrier := oneTetComplex
  simplicial := oneTetComplex_isSimplicial
  metric := unitDecoration

/-- The edge-length-two metric packaged over the identical carrier. -/
def doubleMetricOneTet : MetricDecoratedComplex 6 where
  carrier := oneTetComplex
  simplicial := oneTetComplex_isSimplicial
  metric := doubleDecoration

theorem unitMetricOneTet_ne_doubleMetricOneTet :
    unitMetricOneTet ≠ doubleMetricOneTet := by
  intro h
  have hsig := congrArg
    (fun G : MetricDecoratedComplex 6 =>
      (⟨G.carrier, G.metric⟩ : Σ K : BoundedComplex 6, MetricDecoration K)) h
  simp only [Sigma.mk.injEq] at hsig
  exact unitDecoration_ne_doubleDecoration (eq_of_heq hsig.2)

theorem unit_double_toClass_eq :
    unitMetricOneTet.toClass = doubleMetricOneTet.toClass := rfl

/-- **CARRIER BLOCKER.** The current `TriangulationClass` quotient forgets
physical metric data: its forgetful map from decorated simplicial geometries
is not injective. -/
theorem metricForget_not_injective :
    ¬ Function.Injective
      (MetricDecoratedComplex.toClass :
        MetricDecoratedComplex 6 → TriangulationClass 6) := by
  intro hinj
  exact unitMetricOneTet_ne_doubleMetricOneTet
    (hinj unit_double_toClass_eq)

/-! ## 3. Independent check against the causal four-simplex metric API -/

/-- The same combinatorial causal 4-simplex type has different 4-volume
observables at two lattice spacings. This is independent confirmation from
the 4D Cayley-Menger API that simplex type does not determine metric scale. -/
theorem causalPent_metric_observable_varies :
    CausalSimplex4D.cm4
        (CausalSimplex4D.euclideanSqEdges
          CausalSimplex4D.CausalPentType.fourOne 1 1) = 5 ∧
      CausalSimplex4D.cm4
        (CausalSimplex4D.euclideanSqEdges
          CausalSimplex4D.CausalPentType.fourOne 2 1) = 1280 := by
  constructor
  · rw [CausalSimplex4D.cm4_euclidean_fourOne]
    norm_num
  · rw [CausalSimplex4D.cm4_euclidean_fourOne]
    norm_num

/-! ## 4. The minimal missing geometric-refinement carrier

This interface deliberately assumes neither a path-sum limit nor an action
limit. It asks for finite metric-decorated levels, an actual mesh tending to
zero, a coarse projection between adjacent levels, and a summable local bound
on action changes. Those data are absent from `BoundedComplex`,
`TriangulationClass`, `ExactPathClass`, and `CapShellCompatibility`.
-/

/-- Minimal metric-refinement and action-control data needed to replace a
bare complexity cutoff by a geometric refinement sequence.

`Config n` is the finite metric-decorated configuration space at level `n`.
`coarsen` identifies the adjacent-level histories whose action increments are
controlled. `mesh_tendsto_zero` is geometric refinement; `cap_strictMono`
separately records increasing combinatorial capacity. The summable
`actionStepError` is a local quantitative premise, not the desired path-sum
convergence conclusion. -/
structure MetricRefinementFamily where
  Config : ℕ → Type
  finiteConfig : ∀ n, Fintype (Config n)
  cap : ℕ → ℕ
  cap_strictMono : StrictMono cap
  decorated : ∀ n, Config n → MetricDecoratedComplex (cap n)
  coarsen : ∀ n, Config (n + 1) → Config n
  mesh : ℕ → ℝ
  mesh_pos : ∀ n, 0 < mesh n
  edgeLength_le_mesh :
    ∀ n (c : Config n) (e : Fin (decorated n c).carrier.nE),
      Real.sqrt ((decorated n c).metric.sqEdge e) ≤ mesh n
  mesh_attained :
    ∀ n, ∃ c : Config n, ∃ e : Fin (decorated n c).carrier.nE,
      Real.sqrt ((decorated n c).metric.sqEdge e) = mesh n
  mesh_tendsto_zero :
    Filter.Tendsto mesh Filter.atTop (nhds 0)
  action : ∀ n, Config n → ℝ
  actionStepError : ℕ → ℝ
  actionStepError_nonneg : ∀ n, 0 ≤ actionStepError n
  actionStepError_summable : Summable actionStepError
  action_step_control :
    ∀ n (c : Config (n + 1)),
      |action (n + 1) c - action n (coarsen n c)| ≤ actionStepError n

/-- The finite-level path sum on the metric-decorated carrier. The measure is
an explicit argument because its substrate derivation is the separate P2.2
obligation. -/
noncomputable def metricZ (F : MetricRefinementFamily)
    (measure : ∀ n, F.Config n → ℝ) (n : ℕ) : ℂ := by
  letI := F.finiteConfig n
  exact ∑ c : F.Config n,
    (measure n c : ℂ) * Complex.exp (Complex.I * (F.action n c : ℂ))

/-- The geometric Z_RS continuum target that becomes well-typed only after a
`MetricRefinementFamily` and an explicit measure are supplied. This is a
definition of the OPEN target, not a theorem asserting it. -/
def HasGeometricZRSContinuumLimit (F : MetricRefinementFamily)
    (measure : ∀ n, F.Config n → ℝ) : Prop :=
  ∃ L : ℂ, Filter.Tendsto (fun n => metricZ F measure n)
    Filter.atTop (nhds L)

#print axioms oneTetClass_has_two_metric_decorations
#print axioms no_class_only_mesh_recovers_both
#print axioms no_class_only_cayleyMenger_recovers_both
#print axioms metricForget_not_injective
#print axioms causalPent_metric_observable_varies

end

end MetricRefinementCarrierBlocker
end SevenGaps
end Gravity
end IndisputableMonolith
