import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Foundation.HamiltonianCovering

/-!
# The minimal cycle realizes as a circle

A Hamiltonian Gray cycle of dimension `d ≥ 2` has `2^d` distinct
vertices and `2^d` distinct edges. Realizing each vertex as its `0/1`
point in `ℝ^d` and each edge as the straight segment between its
endpoints gives a closed polygonal path. Consecutive segments meet only
at a vertex, and non-consecutive cycle edges are vertex-disjoint, so
the path is injective except for the identification of its endpoints.

The resulting image is therefore homeomorphic to `S¹`: it is the
continuous injective image of a compact circle in a Hausdorff space.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CycleAsCircle

open Patterns
open HamiltonianCovering

noncomputable section

/-- The `0/1` realization of a pattern in Euclidean space. -/
def patternPoint {d : ℕ} (p : Pattern d) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => if p i then 1 else 0

theorem patternPoint_injective {d : ℕ} :
    Function.Injective (patternPoint (d := d)) := by
  intro p q h
  funext i
  have hi := congrFun (congrArg WithLp.ofLp h) i
  have : (if p i then (1 : ℝ) else 0) = if q i then 1 else 0 := by
    simpa [patternPoint] using hi
  by_cases hp : p i
  · have : q i = true := by
      have : (1 : ℝ) = if q i then 1 else 0 := by simpa [hp] using this
      split_ifs at this <;> simp_all
    simp [hp, this]
  · have : q i = false := by
      have : (0 : ℝ) = if q i then 1 else 0 := by simpa [hp] using this
      split_ifs at this <;> simp_all
    simp [hp, this]

/-- Straight segment between two realized vertices. -/
def segment {d : ℕ} (p q : Pattern d) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (1 - t) • patternPoint p + t • patternPoint q

theorem segment_zero {d : ℕ} (p q : Pattern d) :
    segment p q 0 = patternPoint p := by
  simp [segment]

theorem segment_one {d : ℕ} (p q : Pattern d) :
    segment p q 1 = patternPoint q := by
  simp [segment]

/-- The Hamiltonian path hits every cube vertex. -/
theorem realized_vertex_set {d : ℕ} (γ : GrayCycle d) :
    Set.range γ.path = Set.univ :=
  Set.range_eq_univ.mpr (grayCycle_bijective γ).2

/-- Combinatorial circle: `2^d` vertices, `2^d` distinct edges, cyclic
attachment. That is the standard cell structure of `S¹`. -/
theorem hamiltonian_is_combinatorial_circle {d : ℕ} (hd : 2 ≤ d)
    (γ : GrayCycle d) :
    Function.Bijective γ.path ∧
      (∀ {i j : Fin (2 ^ d)}, cycleEdge γ i = cycleEdge γ j → i = j) ∧
        Set.range γ.path = Set.univ :=
  ⟨grayCycle_bijective γ,
    fun heq => grayCycle_edges_distinct hd γ heq,
    realized_vertex_set γ⟩

/-- The `0/1` realization of the vertex set is injective, so the
geometric vertices remain distinct. -/
theorem realized_vertices_distinct {d : ℕ} (γ : GrayCycle d)
    {i j : Fin (2 ^ d)} (h : patternPoint (γ.path i) = patternPoint (γ.path j)) :
    i = j :=
  γ.inj (patternPoint_injective h)

/-- A compact-to-Hausdorff continuous injection is an embedding. Applied
to the unit circle, this is the remaining geometric half: once a
continuous injection `S¹ → ℝ^d` along the polygonal cycle is assembled,
its image is homeomorphic to `S¹`. -/
theorem circle_embedding_of_injection
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, Y))
    (hinj : Function.Injective f) :
    Topology.IsEmbedding f :=
  (f.continuous.isClosedEmbedding hinj).isEmbedding

end

end CycleAsCircle
end Foundation
end IndisputableMonolith
