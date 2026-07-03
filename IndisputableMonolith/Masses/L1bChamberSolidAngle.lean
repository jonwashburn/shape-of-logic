import Mathlib
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup
import IndisputableMonolith.Masses.L1bChamberMeasure
import IndisputableMonolith.Masses.L1bChamberFundamentalDomain

/-!
# L1b chamber solid-angle capstone

This file closes the geometric bridge tying the finite weight `1/48` to the boundary
`1/(4π)`. It composes the three banked pieces:

* `L1bHyperoctahedralGroup.card_eq_48`: `|SignedPerm| = 48`.
* `L1bChamberFundamentalDomain.cone_isFundamentalDomain`: the open positive sorted cone
  is a fundamental domain for the `SignedPerm` action on `ℝ³` with respect to `volume`.
* `L1bChamberMeasure.tile_measure_of_card48`: a fundamental domain of an order-`48` group
  carries `1/48` of the measure of any invariant set.

The remaining content here is the *invariance of the Euclidean ball*: the signed-permutation
action permutes coordinates and flips signs, so it preserves `∑ i, (v i)²`, hence preserves
the closed unit ball `{v | ∑ i, (v i)² ≤ 1}`. With that, the capstone

  `vol(ball) = 48 • vol(ball ∩ cone)`

is forced. This is the measure-of-one-chamber identity: the unit ball is tiled into `48`
isometric pieces by the group images of the cone, so the cone slice carries exactly `1/48`
of the ball's volume. The solid angle of the cone is `Ω = 3 · vol(ball ∩ cone)` (volume of a
cone over a spherical region is `(1/3) · solid angle · R³`, here `R = 1`), giving
`Ω(cone) = 3 · vol(ball) / 48 = 3 · (4π/3) / 48 = 4π / 48`.
-/

namespace IndisputableMonolith.Masses.L1bChamberSolidAngle

open MeasureTheory
open scoped Pointwise BigOperators
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup.SignedPerm
open IndisputableMonolith.Masses.L1bChamberFundamentalDomain

abbrev V := Fin 3 → ℝ

/-- The signed-permutation action preserves the sum of squares: it permutes coordinates
and flips signs, neither of which changes `∑ i, (v i)²`. -/
theorem signedAct_sq_sum (g : SignedPerm) (v : V) :
    ∑ i, (signedAct g v i) ^ 2 = ∑ i, (v i) ^ 2 := by
  have h1 : ∀ i, (signedAct g v i) ^ 2 = (v (g.perm i)) ^ 2 := by
    intro i
    rcases hs : g.sign i with _ | _ <;> simp [signedAct, hs]
  simp_rw [h1]
  exact Equiv.sum_comp g.perm (fun j => (v j) ^ 2)

/-- The closed Euclidean unit ball in `ℝ³` (sum-of-squares form). -/
def ball : Set V := {v | ∑ i, (v i) ^ 2 ≤ 1}

theorem signedAct_mem_ball {g : SignedPerm} {v : V} (hv : v ∈ ball) :
    signedAct g v ∈ ball := by
  show ∑ i, (signedAct g v i) ^ 2 ≤ 1
  rw [signedAct_sq_sum]; exact hv

/-- The unit ball is invariant under the signed-permutation action. -/
theorem ball_invariant (g : SignedPerm) : g • ball = ball := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    show signedAct g v ∈ ball
    exact signedAct_mem_ball hv
  · intro hw
    refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
    show signedAct g⁻¹ w ∈ ball
    exact signedAct_mem_ball hw

/--
**Measure-of-one-chamber capstone.** The unit ball is tiled into `48` isometric pieces by
the group images of the cone, so the cone slice carries exactly `1/48` of the ball's volume:

  `vol(ball) = 48 • vol(ball ∩ cone)`.

This is the geometric bridge: with the solid-angle relation `Ω(cone) = 3 · vol(ball ∩ cone)`
and `vol(ball) = 4π/3`, it gives `Ω(cone) = 4π/48`, tying the finite `1/48` to the boundary
`1/(4π)`.
-/
theorem ball_tile_measure :
    (volume : Measure V) ball = 48 • (volume : Measure V) (ball ∩ cone) :=
  L1bChamberMeasure.tile_measure_of_card48 card_eq_48 cone_isFundamentalDomain ball_invariant

end IndisputableMonolith.Masses.L1bChamberSolidAngle
