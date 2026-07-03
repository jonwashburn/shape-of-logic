import Mathlib

/-!
# L1b Chamber Measure

The measure-of-one-tile step for the finite-to-boundary push-forward.

`L1bChamberBridge` proved the *combinatorial* tiling: the `48` signed-permutation
images of the fundamental cone cover real `3`-space and are unique on regular points.
This file proves the *measure* core that turns that tiling into the boundary density:
for any finite group acting measurably and measure-invariantly, a fundamental domain
intersected with any invariant set carries exactly `1 / |G|` of that set's measure.

Instantiated at `G = B3` (`|G| = 48`), the fundamental cone, and the unit ball
(orthogonally invariant), this gives `vol(ball ∩ cone) = vol(ball) / 48`, hence the
solid angle `Ω(cone) = 3 · vol(ball ∩ cone) = 4π / 48`, the geometric bridge tying the
finite weight `1/48` to the boundary `1/(4π)`.

What is proved here, axiom-clean and sorry-free:
* `finite_group_invariant_tile`: the abstract measure-of-one-tile identity
  `μ t = |G| • μ (t ∩ s)` for a finite group `G`, a fundamental domain `s`, and a
  `G`-invariant set `t`.
* `b3_card`: `|B3| = 48`.

The remaining geometric obligation (isolated as explicit hypotheses, not assumed
silently): that the cone is an `IsFundamentalDomain` for the `B3` action on `ℝ³` and
that the unit ball is invariant. That residual is the spherical-tiling fact, which is
the genuinely geometric content; everything measure-theoretic is closed here.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1bChamberMeasure

open MeasureTheory
open scoped Pointwise

/--
**Measure of one tile.** For a finite group `G` acting on a measure space by
measure-preserving, measurable maps, a fundamental domain `s` carries exactly
`1 / |G|` of the measure of any `G`-invariant set `t`:
`μ t = |G| • μ (t ∩ s)`.

This is the abstract heart of "area(one chamber) = total / 48": the equal-measure
tiling of an invariant set by the group images of a fundamental domain.
-/
theorem finite_group_invariant_tile
    {G : Type*} {α : Type*} [Group G] [Fintype G] [MulAction G α]
    [MeasurableSpace α] [MeasurableSpace G] [MeasurableSMul G α]
    {μ : Measure α} [SMulInvariantMeasure G α μ]
    {s t : Set α} (hfd : IsFundamentalDomain G s μ)
    (htinv : ∀ g : G, g • t = t) :
    μ t = Fintype.card G • μ (t ∩ s) := by
  rw [hfd.measure_eq_tsum t]
  have hstep : ∀ g : G, μ (g • t ∩ s) = μ (t ∩ s) := by
    intro g; rw [htinv g]
  simp_rw [hstep]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ]

/-- The signed-permutation group `B3 = S₃ × (Fin 3 → Bool)` has order `48 = 6 · 8`. -/
theorem b3_card : Fintype.card (Equiv.Perm (Fin 3) × (Fin 3 → Bool)) = 48 := by
  decide

/--
**Tile-measure corollary at `|G| = 48`.** Specialising `finite_group_invariant_tile`
to any finite group of order `48`: a fundamental domain `s` carries `1/48` of the
measure of any invariant set `t`, i.e. `μ t = 48 • μ (t ∩ s)`.

For the geometric bridge, take `t = unit ball` (orthogonally invariant), `s = cone`,
`μ = volume`; then `vol(ball) = 48 • vol(ball ∩ cone)`, and the solid-angle relation
`Ω = 3 · vol(ball ∩ cone)` gives `Ω(cone) = 3 · vol(ball)/48 = 4π/48`.
-/
theorem tile_measure_of_card48
    {G : Type*} {α : Type*} [Group G] [Fintype G] [MulAction G α]
    [MeasurableSpace α] [MeasurableSpace G] [MeasurableSMul G α]
    {μ : Measure α} [SMulInvariantMeasure G α μ]
    (hcard : Fintype.card G = 48)
    {s t : Set α} (hfd : IsFundamentalDomain G s μ)
    (htinv : ∀ g : G, g • t = t) :
    μ t = 48 • μ (t ∩ s) := by
  rw [finite_group_invariant_tile hfd htinv, hcard]

end L1bChamberMeasure
end Masses
end IndisputableMonolith
