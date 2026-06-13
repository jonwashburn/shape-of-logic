import Mathlib
import IndisputableMonolith.Foundation.HierarchyRealization

namespace IndisputableMonolith
namespace Foundation
namespace HierarchyRealizationFromScale

open ClosedFramework
open HierarchyRealization
open PhiForcingDerived

/-!
# Deriving Realized-Hierarchy Fields from Earlier Scale Primitives

This module isolates the strongest honest derivation currently supported
by the codebase.

If a `ClosedObservableFramework` orbit realizes an earlier
`GeometricScaleSequence` that is closed under `ledgerCompose`, then the
two target fields of `RealizedHierarchy`

* `ratio_self_similar`
* `additive_posting`

are theorems rather than assumptions.

What remains genuinely open is proving that such a realized closed scale
model exists from `ClosedObservableFramework` alone.
-/

/-- A `ClosedObservableFramework` orbit that realizes an earlier closed
geometric scale sequence. -/
structure RealizedClosedScaleModel (F : ClosedObservableFramework) where
  baseState : F.S
  amplitude : ℝ
  amplitude_pos : 0 < amplitude
  scales : GeometricScaleSequence
  scales_closed : scales.isClosed
  growth : 1 < scales.ratio
  realize : ∀ k, F.r (F.T^[k] baseState) = amplitude * scales.scale k

/-- In any geometric scale sequence, each adjacent ratio equals the
base ratio. -/
theorem scale_step_ratio (S : GeometricScaleSequence) (k : ℕ) :
    S.scale (k + 1) / S.scale k = S.ratio := by
  unfold GeometricScaleSequence.scale
  rw [pow_succ]
  have hr : S.ratio ≠ 0 := ne_of_gt S.ratio_pos
  have hk : S.ratio ^ k ≠ 0 := pow_ne_zero k hr
  simpa using (mul_div_cancel_left₀ S.ratio hk)

/-- The realized orbit has constant adjacent ratio. -/
theorem realized_closed_scale_ratio_step
    (F : ClosedObservableFramework) (H : RealizedClosedScaleModel F) (k : ℕ) :
    F.r (F.T^[k + 1] H.baseState) / F.r (F.T^[k] H.baseState) = H.scales.ratio := by
  rw [H.realize (k + 1), H.realize k]
  have ha : H.amplitude ≠ 0 := ne_of_gt H.amplitude_pos
  calc
    H.amplitude * H.scales.scale (k + 1) / (H.amplitude * H.scales.scale k)
      = H.scales.scale (k + 1) / H.scales.scale k := by
          rw [mul_div_mul_left _ _ ha]
    _ = H.scales.ratio := scale_step_ratio H.scales k

/-- Therefore the realized orbit satisfies ratio self-similarity. -/
theorem ratio_self_similar_of_realized_closed_scale
    (F : ClosedObservableFramework) (H : RealizedClosedScaleModel F) :
    ∀ k,
      F.r (F.T^[k + 2] H.baseState) / F.r (F.T^[k + 1] H.baseState) =
        F.r (F.T^[k + 1] H.baseState) / F.r (F.T^[k] H.baseState) := by
  intro k
  rw [realized_closed_scale_ratio_step F H (k + 1), realized_closed_scale_ratio_step F H k]

/-- Closure of the earlier geometric scale sequence yields additive
posting on the realized orbit. -/
theorem additive_posting_of_realized_closed_scale
    (F : ClosedObservableFramework) (H : RealizedClosedScaleModel F) :
    F.r (F.T^[2] H.baseState) =
      F.r (F.T^[1] H.baseState) + F.r (F.T^[0] H.baseState) := by
  have hclosed : H.scales.scale 0 + H.scales.scale 1 = H.scales.scale 2 := by
    simpa [GeometricScaleSequence.isClosed, ledgerCompose] using H.scales_closed
  have hclosed' : H.scales.scale 2 = H.scales.scale 1 + H.scales.scale 0 := by
    linarith
  rw [H.realize 2, H.realize 1, H.realize 0]
  rw [hclosed']
  ring

/-- The earlier closed-scale model packages into the later
`RealizedHierarchy` interface, with the two critical fields now proved
rather than assumed. -/
noncomputable def toRealizedHierarchy
    (F : ClosedObservableFramework) (H : RealizedClosedScaleModel F) :
    RealizedHierarchy F where
  baseState := H.baseState
  levels_eq := by
    intro k
    rfl
  levels_pos := by
    intro k
    exact F.r_pos _
  growth := by
    rw [realized_closed_scale_ratio_step F H 0]
    exact H.growth
  ratio_self_similar := ratio_self_similar_of_realized_closed_scale F H
  additive_posting := by
    simpa using additive_posting_of_realized_closed_scale F H

end HierarchyRealizationFromScale
end Foundation
end IndisputableMonolith
