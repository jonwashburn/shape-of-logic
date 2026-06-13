import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homotopy.Lifting
import IndisputableMonolith.Foundation.CircleCovering

/-!
# Lifting prerequisites for the circle winding invariant

The winding / degree invariant on singular `1`-chains of `TopCat.sphere 1` is
built by lifting singular simplices through the covering map
`CircleCovering.isCoveringMap_trigCirclePoint`.  Two ingredients are needed and
established here, both about the *exact imported* objects:

* **Simplex contractibility.**  The realization domain of an `n`-simplex is the
  topological standard simplex `stdSimplex ℝ (Fin (n+1))`, a nonempty convex set,
  hence contractible and (therefore) simply connected.  Mathlib's path-lifting
  monodromy invariance (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`)
  combined with `SimplyConnectedSpace.paths_homotopic` is what makes the winding
  number kill boundaries, so we register the contractibility instance once here.

* **Fiber structure of the covering.**  `trigCirclePoint a = trigCirclePoint b`
  iff `a` and `b` differ by an integer multiple of the period `2π`.  This is the
  deck-transformation description of the fiber and is the algebraic heart of both
  the well-definedness of the winding number and the value `w(fundamental) = 1`.

No axioms, `sorry`, or project-local `S¹` replacements are used.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleLifting

open Complex CircleParam CircleCovering
open scoped Real

noncomputable section

/-- The topological standard `n`-simplex (the realization domain of a singular
`(n-1)`-simplex) is contractible: it is a nonempty convex set. -/
instance stdSimplex_contractibleSpace (n : ℕ) [NeZero n] :
    ContractibleSpace (stdSimplex ℝ (Fin n)) :=
  (convex_stdSimplex ℝ (Fin n)).contractibleSpace
    ⟨_, single_mem_stdSimplex ℝ (0 : Fin n)⟩

/-- Consequently the standard simplex is simply connected; this is the precise
hypothesis consumed by the path-lifting monodromy invariance used to show the
winding number kills boundaries.  (Stated explicitly for discoverability; it is
also available by instance resolution.) -/
theorem stdSimplex_simplyConnectedSpace (n : ℕ) [NeZero n] :
    SimplyConnectedSpace (stdSimplex ℝ (Fin n)) :=
  inferInstance

/-- Two real parameters hit the same point of `TopCat.sphere 1` under the
trigonometric covering iff they have the same `Circle.exp`. -/
theorem trigCirclePoint_eq_iff_exp (a b : ℝ) :
    trigCirclePoint a = trigCirclePoint b ↔ Circle.exp a = Circle.exp b := by
  rw [← ulift_carrierCovering_eq_trig]
  simp only [Function.comp_apply, carrierCovering]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact circleHomeoCarrier.injective (Homeomorph.ulift.symm.injective h)
  · rw [h]

/-- **Fiber of the trigonometric covering.**  `trigCirclePoint a = trigCirclePoint b`
exactly when `a` and `b` differ by an integer number of full turns `2π`.  This is
the deck-transformation group `2π ℤ` of the universal cover `ℝ → S¹`. -/
theorem trigCirclePoint_eq_iff (a b : ℝ) :
    trigCirclePoint a = trigCirclePoint b ↔ ∃ m : ℤ, a = b + (m : ℝ) * (2 * Real.pi) := by
  rw [trigCirclePoint_eq_iff_exp, Circle.exp_eq_exp]

/-- The covering map of `TopCat.sphere 1`, repackaged as an
`IsCoveringMap` term for direct use with the path-lifting API. -/
theorem isCoveringMap_trig : IsCoveringMap CircleParam.trigCirclePoint :=
  isCoveringMap_trigCirclePoint

end

end CircleLifting
end Foundation
end IndisputableMonolith
