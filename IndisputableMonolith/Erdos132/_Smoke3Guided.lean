import Mathlib.Tactic
set_option maxHeartbeats 800000 in
theorem smoke (u v y0 y1 y2 : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (hY0 : y0 ^ 2 = u^2 - 1/4)
    (hY1 : y1 ^ 2 = u^2 - 1/4)
    (hY2 : y2 ^ 2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4)
    (hne0 : y0 ≠ 0) (hne1 : y1 ≠ 0) (hne2 : y2 ≠ 0)
    (hp01 : (0) ^ 2 + (y0 - y1) ^ 2 = u ^ 2)
    (hp02 : (-u^2/2 + v^2/2) ^ 2 + (y0 - y2) ^ 2 = u ^ 2)
    (hp12 : (-u^2/2 + v^2/2) ^ 2 + (y1 - y2) ^ 2 = u ^ 2)
    : False := by
  have hprod : 2 * (y0 * y1) = u^2 - 1/2 := by nlinarith [hp01, hY0, hY1]
  have hsq : (y0 * y1)^2 = (u^2 - 1/4)^2 := by nlinarith [hY0, hY1, sq_nonneg (y0*y1)]
  have hloc : u^2 * (3 * u^2 - 1) = 0 := by nlinarith [hprod, hsq]
  have hu2 : 3 * u^2 = 1 := by
    rcases mul_eq_zero.mp hloc with h | h
    · exact absurd (by nlinarith [h] : u = 0) (ne_of_gt hu0)
    · linarith
  have hsub : (y0 - y2)^2 = (y1 - y2)^2 := by nlinarith [hp02, hp12]
  have hy01 : y0 ≠ y1 := by intro h; rw [h] at hp01; nlinarith [hp01, hu0]
  have hmid : y0 + y1 = 2*y2 := by
    have hfac : (y0 - y1) * (y0 + y1 - 2*y2) = 0 := by nlinarith [hsub]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (sub_eq_zero.mp h) hy01
    · linarith
  have hy2sq : y2 ^ 2 = 0 := by
    linear_combination (1/4)*hY0 + (1/4)*hY1 + (1/4)*hprod + (1/4)*hu2 + (-(2*y2+y0+y1)/4)*hmid
  have hmm : y2 * y2 = 0 := by linear_combination hy2sq
  exact hne2 (mul_self_eq_zero.mp hmm)
