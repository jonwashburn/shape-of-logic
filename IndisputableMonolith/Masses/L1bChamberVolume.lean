import Mathlib
import IndisputableMonolith.Masses.L1bChamberSolidAngle

/-!
# L1b chamber volume: `vol(ball) = 4π/3` and the solid-angle bridge

This module discharges the last arithmetic link in the L1b geometric bridge.

`L1bChamberSolidAngle.ball_tile_measure` proves the finite-carrier tiling fact
`vol(ball) = 48 • vol(ball ∩ cone)` (the hyperoctahedral group `SignedPerm`
has card 48 and `cone` is a fundamental domain). Here we compute the absolute
volume `vol(ball) = 4π/3` from Mathlib's Euclidean ball volume, transferred from
`EuclideanSpace ℝ (Fin 3)` to the plain product space `Fin 3 → ℝ` (on which the
group action and fundamental domain live) by the measure-preserving unwrapping
`(MeasurableEquiv.toLp 2 _).symm`.

Combining the two gives the per-chamber volume `vol(ball ∩ cone) = π/36` and,
defining the solid angle as `solidAngle S := 3 • vol(ball ∩ S)` (so the total
solid angle of the full ball is `3 • (4π/3) = 4π`), the headline identity

  `solidAngleCone : solidAngle cone = 4π/48`

which ties the finite `1/48` to the boundary `1/(4π)` measure.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1bChamberVolume

open MeasureTheory
open IndisputableMonolith.Masses.L1bChamberSolidAngle
open IndisputableMonolith.Masses.L1bChamberFundamentalDomain

noncomputable section

/-- The L²-unit-ball in `Fin 3 → ℝ` is the preimage, under the measure-preserving
unwrapping `EuclideanSpace ℝ (Fin 3) ≃ (Fin 3 → ℝ)`, of the Euclidean closed unit
ball. -/
theorem ball_eq_preimage_closedBall :
    (⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) ⁻¹' ball
      = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  ext x
  simp only [ball, Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_one]
  have hsum :
      (∑ i, ((⇑(MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) x i) ^ 2)
        = ∑ i, ‖x i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  rw [hsum]

/-- `ball` is measurable. -/
theorem measurableSet_ball : MeasurableSet (ball : Set (Fin 3 → ℝ)) := by
  have hf : Measurable (fun v : Fin 3 → ℝ => ∑ i, (v i) ^ 2) := by
    apply Finset.measurable_sum
    intro i _
    exact (measurable_pi_apply i).pow_const 2
  exact measurableSet_le hf measurable_const

/-- Γ(5/2) = (3/4)·√π. -/
theorem Gamma_five_halves : Real.Gamma (5 / 2 : ℝ) = 3 / 4 * Real.sqrt Real.pi := by
  have h12 : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have h32 : Real.Gamma (3 / 2 : ℝ) = 1 / 2 * Real.sqrt Real.pi := by
    have h := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
    rw [show (1 / 2 + 1 : ℝ) = 3 / 2 by norm_num, h12] at h
    rw [h]
  have h52 := Real.Gamma_add_one (s := (3 / 2 : ℝ)) (by norm_num)
  rw [show (3 / 2 + 1 : ℝ) = 5 / 2 by norm_num, h32] at h52
  rw [h52]; ring

/-- The real number appearing in Mathlib's ball-volume formula at dimension 3
simplifies to `4π/3`. -/
theorem sqrt_pi_cubed_div_Gamma : Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2 : ℝ)
    = 4 * Real.pi / 3 := by
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt Real.pi_pos)
  have hcube : Real.sqrt Real.pi ^ 3 = Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi := by ring
  rw [Gamma_five_halves, hcube, hsq]
  field_simp

/-- **Volume of the L²-unit-ball in `Fin 3 → ℝ` is `4π/3`.** -/
theorem volume_ball_eq :
    (volume : Measure (Fin 3 → ℝ)) ball = ENNReal.ofReal (4 * Real.pi / 3) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  rw [← hmp.measure_preimage measurableSet_ball.nullMeasurableSet,
      ball_eq_preimage_closedBall,
      EuclideanSpace.volume_closedBall (Fin 3) 0 1]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul, Nat.cast_ofNat]
  rw [show ((3 : ℝ) / 2 + 1) = 5 / 2 by norm_num]
  congr 1
  exact sqrt_pi_cubed_div_Gamma

/-- Per-chamber volume: `vol(ball ∩ cone) = π/36`. -/
theorem volume_ball_inter_cone :
    (volume : Measure (Fin 3 → ℝ)) (ball ∩ cone) = ENNReal.ofReal (Real.pi / 36) := by
  have htile := ball_tile_measure
  rw [volume_ball_eq, nsmul_eq_mul, Nat.cast_ofNat] at htile
  -- htile : ofReal (4π/3) = 48 * vol(ball ∩ cone)
  have hv : (volume : Measure (Fin 3 → ℝ)) (ball ∩ cone)
      = ENNReal.ofReal (4 * Real.pi / 3) / 48 :=
    (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr htile.symm
  rw [hv, show (48 : ENNReal) = ENNReal.ofReal 48 from (ENNReal.ofReal_ofNat 48).symm,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring

/-- The solid angle subtended by a set `S`, normalized so the full ball gives `4π`:
`solidAngle S := 3 • vol(ball ∩ S)`. -/
def solidAngle (S : Set (Fin 3 → ℝ)) : ENNReal :=
  (3 : ℕ) • (volume : Measure (Fin 3 → ℝ)) (ball ∩ S)

/-- Sanity: the total solid angle of the ambient ball is `4π`
(`ball ∩ univ = ball`, `3 • (4π/3) = 4π`). -/
theorem solidAngle_univ : solidAngle Set.univ = ENNReal.ofReal (4 * Real.pi) := by
  unfold solidAngle
  rw [Set.inter_univ, volume_ball_eq, nsmul_eq_mul, Nat.cast_ofNat,
      show (3 : ENNReal) = ENNReal.ofReal 3 from (ENNReal.ofReal_ofNat 3).symm,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- **The geometric bridge: the solid angle of the positive sorted chamber is `4π/48`.**
This is the spherical-measure identity that ties the finite carrier's `1/48`
to the boundary `1/(4π)`. -/
theorem solidAngleCone : solidAngle cone = ENNReal.ofReal (4 * Real.pi / 48) := by
  unfold solidAngle
  rw [volume_ball_inter_cone, nsmul_eq_mul, Nat.cast_ofNat,
      show (3 : ENNReal) = ENNReal.ofReal 3 from (ENNReal.ofReal_ofNat 3).symm,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-- Restatement making the `1/48` of the full sphere explicit:
`solidAngle cone = (4π) / 48`. -/
theorem solidAngleCone_eq_total_div :
    solidAngle cone = solidAngle Set.univ / 48 := by
  rw [solidAngleCone, solidAngle_univ,
      show (48 : ENNReal) = ENNReal.ofReal 48 from (ENNReal.ofReal_ofNat 48).symm,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]

end

end L1bChamberVolume
end Masses
end IndisputableMonolith
