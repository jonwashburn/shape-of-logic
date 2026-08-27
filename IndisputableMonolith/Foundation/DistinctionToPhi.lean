import Mathlib
import IndisputableMonolith.Foundation.DistinctionToHierarchy

/-!
# Distinction to Phi (T6)

This module continues the distinction-threaded forcing path:

```
distinction h → T0-T4 on the forced quotient → T5 J uniqueness → T6 φ
```

The key rule for this module is that we do not call the global
`t5_holds` or `t6_holds` surfaces, and we do not route through the monolithic
`t5_to_t6_forced_bridge_holds`.  Instead, `DistinctionToHierarchy` constructs
the canonical hierarchy surface from the distinction-threaded T5 theorem and
proves that every uniform, growth-oriented, seed-closed hierarchy has base
ratio φ.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DistinctionToPhi

open DistinctionToJCost
open DistinctionToHierarchy

/-! ## T6 through the explicit hierarchy surface -/

/-- T6, threaded through the supplied distinction. -/
structure T6_FromDistinction
    {K : Type} (h : ∃ x y : K, x ≠ y) : Prop where
  /-- The explicit hierarchy surface already forced from the same distinction. -/
  hierarchy : HierarchyFromDistinction h
  /-- The canonical hierarchy object exists. -/
  hierarchy_exists : Nonempty HierarchyForcing.NontrivialMultilevelComposition
  /-- The canonical hierarchy is uniform. -/
  uniform : UnifiedForcingChain.CanonicalUniformScaleLaw canonicalPhiHierarchy
  /-- The canonical hierarchy grows. -/
  growth : UnifiedForcingChain.CanonicalGrowthOrientation canonicalPhiHierarchy
  /-- The canonical hierarchy is seed-closed. -/
  seed : UnifiedForcingChain.CanonicalSeedSizeLaw canonicalPhiHierarchy
  /-- φ satisfies the golden equation. -/
  phi_equation : PhiForcing.φ^2 = PhiForcing.φ + 1
  /-- φ is positive. -/
  phi_positive : PhiForcing.φ > 0
  /-- φ is the unique positive solution of the golden equation. -/
  phi_unique : ∀ r : ℝ, 0 < r → r^2 = r + 1 → r = PhiForcing.φ

/-- A distinction-threaded T5 surface forces T6. -/
theorem distinction_hierarchy_to_T6
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (hh : HierarchyFromDistinction h) :
    T6_FromDistinction h := by
  exact {
    hierarchy := hh
    hierarchy_exists := hh.hierarchy
    uniform := hh.uniform
    growth := hh.growth
    seed := hh.seed
    phi_equation := PhiForcing.phi_equation
    phi_positive := PhiForcing.phi_pos
    phi_unique := by
      intro r hr hgold
      exact PhiForcing.phi_unique_self_similar hr
        (by simpa [PhiForcing.satisfies_golden_constraint] using hgold)
  }

/-- A supplied distinction forces the current formal T6 surface. -/
theorem distinction_forces_T6
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T6_FromDistinction h :=
  distinction_hierarchy_to_T6 (DistinctionToHierarchy.distinction_forces_hierarchy h)

/-! ## Phase-3 bundle -/

/-- T−1 through T6 threaded through the supplied distinction. -/
structure DistinctionToT6_Spine
    (K : Type) (h : ∃ x y : K, x ≠ y) : Prop where
  /-- The already forced T0-T5 spine. -/
  t0_to_t5 : DistinctionToJCost.DistinctionToT5_Spine K h
  /-- The threaded T6 surface. -/
  t6 : T6_FromDistinction h

/-- A distinction witness forces T−1 through T6. -/
theorem distinction_forces_T0_to_T6
    (K : Type) (h : ∃ x y : K, x ≠ y) :
    DistinctionToT6_Spine K h where
  t0_to_t5 := DistinctionToJCost.distinction_forces_T0_to_T5 K h
  t6 := distinction_forces_T6 h

end DistinctionToPhi
end Foundation
end IndisputableMonolith
