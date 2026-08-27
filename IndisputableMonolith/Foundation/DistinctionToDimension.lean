import Mathlib
import IndisputableMonolith.Foundation.DistinctionToPhi

/-!
# Distinction to Dimension (T8) and Eight-Tick (T7)

This module continues the distinction-threaded forcing path:

```
distinction h → T0-T6 → T8 (D = 3) → T7 (2^3 = 8)
```

The route here is deliberately ordered:

* T8 is primary.  The topological linking predicate, via the
  Alexander-duality bridge already formalized in `DimensionForcing`, forces
  `D = 3`.
* T7 is downstream.  Once `D = 3`, the canonical period is `2^3 = 8`.

The module does not call `UnifiedForcingChain.t8_holds`, `t7_holds`,
`t6_to_t8_dimension_bridge_holds`, or `t8_to_t7_bridge_holds`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DistinctionToDimension

open DistinctionToPhi

/-! ## T8 from the distinction-threaded T6 surface -/

/-- Dimension forcing, threaded through the supplied distinction. -/
structure T8_FromDistinction
    {K : Type} (h : ∃ x y : K, x ≠ y) : Prop where
  /-- The T6 theorem surface already forced from the same distinction. -/
  t6 : T6_FromDistinction h
  /-- T6's phi uniqueness is available to downstream dimension/cosmology routes. -/
  phi_unique_available : ∀ r : ℝ, 0 < r → r ^ 2 = r + 1 → r = PhiForcing.φ
  /-- Ledger-compatible topological linking forces D = 3. -/
  linking_route :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.SupportsNontrivialLinking D → D = 3
  /-- The eight-tick equation forces D = 3.  This is a consistency route, not
      the primary dimension proof. -/
  eight_tick_route :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.EightTickFromDimension D = DimensionForcing.eight_tick →
        D = 3
  /-- The unique RS-compatible spatial dimension. -/
  unique_dimension : ∃! D : DimensionForcing.Dimension, DimensionForcing.RSCompatibleDimension D
  /-- The forced dimension is 3, by the linking route. -/
  dimension_three_from_linking :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.SupportsNontrivialLinking D → D = 3
  /-- D=3 carries the linking witness. -/
  d3_has_linking : DimensionForcing.SupportsNontrivialLinking 3
  /-- D=3 is RS-compatible. -/
  d3_compatible : DimensionForcing.RSCompatibleDimension 3

/-- A distinction-threaded T6 surface forces T8. -/
theorem distinction_T6_to_T8
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (h6 : T6_FromDistinction h) :
    T8_FromDistinction h where
  t6 := h6
  phi_unique_available := h6.phi_unique
  linking_route := DimensionForcing.linking_requires_D3
  eight_tick_route := DimensionForcing.eight_tick_forces_D3
  unique_dimension := DimensionForcing.dimension_forced
  dimension_three_from_linking := DimensionForcing.linking_requires_D3
  d3_has_linking := DimensionForcing.D3_has_linking
  d3_compatible := DimensionForcing.D3_compatible

/-- A supplied distinction forces T8. -/
theorem distinction_forces_T8
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T8_FromDistinction h :=
  distinction_T6_to_T8 (DistinctionToPhi.distinction_forces_T6 h)

/-! ## T7 downstream of T8 -/

/-- Eight-tick forcing, threaded through the supplied distinction and derived
from T8's `D = 3` result. -/
structure T7_FromDistinction
    {K : Type} (h : ∃ x y : K, x ≠ y) : Prop where
  /-- The T8 theorem surface already forced from the same distinction. -/
  t8 : T8_FromDistinction h
  /-- The canonical eight-tick value is `2^3`. -/
  eight_is_2_cubed : DimensionForcing.eight_tick = 2^3
  /-- At D=3, the canonical period is the eight-tick. -/
  from_dimension :
    DimensionForcing.EightTickFromDimension 3 = DimensionForcing.eight_tick
  /-- Every RS-compatible dimension carries the eight-tick equation. -/
  compatible_dimension_eight_tick :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.RSCompatibleDimension D →
        DimensionForcing.EightTickFromDimension D = DimensionForcing.eight_tick
  /-- Every RS-compatible dimension is D=3. -/
  compatible_dimension_three :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.RSCompatibleDimension D → D = 3

/-- T8 supplies T7: dimension forcing is primary, eight-tick is downstream. -/
theorem distinction_T8_to_T7
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (h8 : T8_FromDistinction h) :
    T7_FromDistinction h where
  t8 := h8
  eight_is_2_cubed := DimensionForcing.eight_tick_is_2_cubed
  from_dimension := rfl
  compatible_dimension_eight_tick := by
    intro D hD
    exact hD.eight_tick
  compatible_dimension_three := by
    intro D hD
    exact h8.linking_route D hD.linking

/-- A supplied distinction forces T7 after T8. -/
theorem distinction_forces_T7
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T7_FromDistinction h :=
  distinction_T8_to_T7 (distinction_forces_T8 h)

/-! ## Phase-4 bundle -/

/-- T−1 through T8, plus T7 downstream, threaded through the supplied distinction. -/
structure DistinctionToT8_Spine
    (K : Type) (h : ∃ x y : K, x ≠ y) : Prop where
  /-- The already forced T0-T6 spine. -/
  t0_to_t6 : DistinctionToPhi.DistinctionToT6_Spine K h
  /-- The dimension-forcing surface. -/
  t8 : T8_FromDistinction h
  /-- The eight-tick consequence of T8. -/
  t7 : T7_FromDistinction h

/-- A distinction witness forces T−1 through T8, with T7 derived downstream. -/
theorem distinction_forces_T0_to_T8
    (K : Type) (h : ∃ x y : K, x ≠ y) :
    DistinctionToT8_Spine K h where
  t0_to_t6 := DistinctionToPhi.distinction_forces_T0_to_T6 K h
  t8 := distinction_forces_T8 h
  t7 := distinction_forces_T7 h

/-! ## Compatibility with the legacy complete-chain record -/

/-- The legacy complete-chain record holds **unconditionally**.  It is a global
fact about the forcing chain, not parameterized by any carrier or distinction,
and in particular it is **not** a consequence of any supplied spine.  It is
named explicitly so the honest decomposition is visible: the genuinely
carrier/distinction-threaded result is `distinction_forces_T0_to_T8`; this is the
separate global legacy record. -/
theorem legacy_complete_chain_is_global :
    UnifiedForcingChain.CompleteForcingChain :=
  UnifiedForcingChain.complete_forcing_chain

/-- Backward-compatibility projection for older callers that expect a
`CompleteForcingChain` next to a threaded spine.  The spine argument is
**intentionally not consumed**: `CompleteForcingChain` is the global,
unparameterized record `legacy_complete_chain_is_global`, so no honest function
from the spine can make its fields depend on `K` or `h`.  The consuming,
distinction-threaded theorem is `distinction_forces_T0_to_T8`; cite that for the
carrier-dependent content and this only for the legacy record. -/
theorem threaded_spine_to_legacy_complete_chain
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (_spine : DistinctionToT8_Spine K h) :
    UnifiedForcingChain.CompleteForcingChain :=
  legacy_complete_chain_is_global

/-- Direct compatibility form from a supplied distinction.  Use
`distinction_forces_T0_to_T8` for the threaded theorem; this statement exists
only so older code expecting `CompleteForcingChain` can cite the new route. -/
theorem distinction_forces_legacy_complete_chain
    (K : Type) (h : ∃ x y : K, x ≠ y) :
    UnifiedForcingChain.CompleteForcingChain :=
  threaded_spine_to_legacy_complete_chain
    (distinction_forces_T0_to_T8 K h)

end DistinctionToDimension
end Foundation
end IndisputableMonolith
