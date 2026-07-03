import Mathlib
open MeasureTheory
#check @EuclideanSpace.volume_closedBall
#check @EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
#check @MeasurePreserving.measure_preimage
#check @ENNReal.eq_div_iff
#check @Nat.cast_ofNat
-- the nat-smul shape coming out of ball_tile_measure
example (v : ENNReal) (h : ENNReal.ofReal (4*Real.pi/3) = (48:ℕ) • v) :
    v = ENNReal.ofReal (Real.pi / 36) := by
  rw [nsmul_eq_mul, Nat.cast_ofNat] at h
  have hv : v = ENNReal.ofReal (4 * Real.pi / 3) / 48 :=
    (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr h.symm
  rw [hv, show (48 : ENNReal) = ENNReal.ofReal 48 from (ENNReal.ofReal_ofNat 48).symm,
    ← ENNReal.ofReal_div_of_pos (by norm_num)]
  congr 1
  ring
