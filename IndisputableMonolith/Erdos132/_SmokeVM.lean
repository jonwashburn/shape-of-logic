import Mathlib.Tactic
set_option maxHeartbeats 8000000 in
theorem smoke (u v y0 y1 y2 y3 : ℝ)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≠ v)
    (hY0 : y0 ^ 2 = u^2 - 1/4)
    (hY1 : y1 ^ 2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4)
    (hY2 : y2 ^ 2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4)
    (hY3 : y3 ^ 2 = -u^4/4 + u^2*v^2/2 + u^2/2 - v^4/4 + v^2/2 - 1/4)
    (hne0 : y0 ≠ 0)
    (hne1 : y1 ≠ 0)
    (hne2 : y2 ≠ 0)
    (hne3 : y3 ≠ 0)
    (hp01 : (-u^2/2 + v^2/2) ^ 2 + (y0 - y1) ^ 2 = u ^ 2)
    (hp02 : (-u^2/2 + v^2/2) ^ 2 + (y0 - y2) ^ 2 = u ^ 2)
    (hp03 : (u^2/2 - v^2/2) ^ 2 + (y0 - y3) ^ 2 = u ^ 2)
    (hp12 : (0) ^ 2 + (y1 - y2) ^ 2 = v ^ 2)
    (hp13 : (u^2 - v^2) ^ 2 + (y1 - y3) ^ 2 = v ^ 2)
    (hp23 : (u^2 - v^2) ^ 2 + (y2 - y3) ^ 2 = v ^ 2)
    : False := by
  nlinarith [hY0, hY1, hY2, hY3, hp01, hp02, hp03, hp12, hp13, hp23, sq_nonneg y0, sq_nonneg y1, sq_nonneg y2, sq_nonneg y3, mul_self_nonneg (y0 - y1), mul_self_nonneg (y0 - y2), mul_self_nonneg (y0 - y3), mul_self_nonneg (y1 - y2), mul_self_nonneg (y1 - y3), mul_self_nonneg (y2 - y3), mul_pos hu0 hu0, mul_pos hv0 hv0, sq_nonneg (u - v), sq_nonneg (u + v), sq_nonneg (u*v)]
