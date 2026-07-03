import Mathlib

/-!
Smoke test: verify that the gen_solve-produced Nullstellensatz identity for a
real "EASY" triple core (extracted by `_certgen_emit_one.py` from subset #5,
core edges e1=(0,5), e2=(1,5), e3=(2,3), target combo (c1,c2,c3)=(1,a,1))
actually compiles in Lean via `linear_combination`.

This isolates the truly novel step (does gen_solve's certificate check out as
a Lean `linear_combination`?) from the already-validated geometric scaffolding
(d2 = c -> 2*y*y' = M - c -> E = 0), which mirrors the n=4 `SlotCerts.lean`
pattern exactly.
-/

-- Step 1: pure E-level check (the risky, novel step).
example (a b : ℝ)
    (hE1 : a ^ 2 - a * b - 2 * a + b ^ 2 - 2 * b + 1 = 0)
    (hE2 : a ^ 2 - 2 * a * b - 2 * a + b ^ 2 - b + 1 = 0)
    (hE3 : a ^ 2 - 4 * a + 1 = 0) : False := by
  have h : (1 : ℝ) = 0 := by
    linear_combination
      (-3 * a * b / 4 + 5 * a / 4 + 11 * b / 4 - 17 / 4) * hE1 +
      (3 * a * b / 4 - 7 * a / 4 - 11 * b / 4 + 25 / 4) * hE2 +
      (a / 2 + 3 * b ^ 2 / 4 - 9 * b / 4 - 1) * hE3
  exact one_ne_zero h

/-- Step 2: full geometric chain from d2 = c down to E = 0, then to False,
using the u,v-substituted (a=u^2,b=v^2) concrete node coordinates. -/
example (u v y0 y1 y2 y3 y5 : ℝ)
    (hy0 : y0 ^ 2 = 3 / 4)
    (hy1 : y1 ^ 2 = 3 / 4)
    (hy2 : y2 ^ 2 = -u ^ 4 / 4 + u ^ 2)
    (hy3 : y3 ^ 2 = -u ^ 4 / 4 + u ^ 2)
    (hy5 : y5 ^ 2 = -u ^ 4 / 4 + u ^ 2 * v ^ 2 / 2 + u ^ 2 / 2 - v ^ 4 / 4 + v ^ 2 / 2 - 1 / 4)
    -- edge1: node0=(1/2, y0) to node5=(u²/2-v²/2+1/2, y5), squared-dist = 1
    (hd1 : (1 / 2 - (u ^ 2 / 2 - v ^ 2 / 2 + 1 / 2)) ^ 2 + (y0 - y5) ^ 2 = 1)
    -- edge2: node1=(1/2, y1) to node5, squared-dist = u^2 (= a)
    (hd2 : (1 / 2 - (u ^ 2 / 2 - v ^ 2 / 2 + 1 / 2)) ^ 2 + (y1 - y5) ^ 2 = u ^ 2)
    -- edge3: node2=(1-u²/2, y2) to node3=(1-u²/2, y3), squared-dist = 1
    (hd3 : (1 - u ^ 2 / 2 - (1 - u ^ 2 / 2)) ^ 2 + (y2 - y3) ^ 2 = 1) : False := by
  -- hs steps: turn each d2 = c into 2*yi*yj = M - c
  have hs1 : 2 * y0 * y5 = (u ^ 2 / 2 + v ^ 2 / 2 + 1 / 2) - 1 := by
    linear_combination -hd1 + hy0 + hy5
  have hs2 : 2 * y1 * y5 = (u ^ 2 / 2 + v ^ 2 / 2 + 1 / 2) - u ^ 2 := by
    linear_combination -hd2 + hy1 + hy5
  have hs3 : 2 * y2 * y3 = (-u ^ 4 / 2 + 2 * u ^ 2) - 1 := by
    linear_combination -hd3 + hy2 + hy3
  -- hE steps: square each hs and substitute the known y^2 values in ONE
  -- deterministic `linear_combination` call each (no nlinarith search).
  -- Coefficients derived symbolically (see scripts/erdos132, residual = 0 check):
  -- for `hs : 2*yi*yj = K`, `hYi : yi^2 = Yi`, `hYj : yj^2 = Yj`, the target
  -- `K^2 - 4*Yi*Yj = 0` equals  -(2*yi*yj+K)*hs + 4*yj^2*hYi + 4*Yi*hYj.
  have hE1' : (u ^ 2) ^ 2 - (u ^ 2) * (v ^ 2) - 2 * (u ^ 2) + (v ^ 2) ^ 2 - 2 * (v ^ 2) + 1 = 0 := by
    linear_combination
      (-(2 * y0 * y5 + ((u ^ 2 / 2 + v ^ 2 / 2 + 1 / 2) - 1))) * hs1 +
      (4 * y5 ^ 2) * hy0 + 3 * hy5
  have hE2' : (u ^ 2) ^ 2 - 2 * (u ^ 2) * (v ^ 2) - 2 * (u ^ 2) + (v ^ 2) ^ 2 - (v ^ 2) + 1 = 0 := by
    linear_combination
      (-(2 * y1 * y5 + ((u ^ 2 / 2 + v ^ 2 / 2 + 1 / 2) - u ^ 2))) * hs2 +
      (4 * y5 ^ 2) * hy1 + 3 * hy5
  have hE3' : (u ^ 2) ^ 2 - 4 * (u ^ 2) + 1 = 0 := by
    linear_combination
      (-(2 * y2 * y3 + ((-u ^ 4 / 2 + 2 * u ^ 2) - 1))) * hs3 +
      (4 * y3 ^ 2) * hy2 + (-u ^ 4 + 4 * u ^ 2) * hy3
  have h : (1 : ℝ) = 0 := by
    linear_combination
      (-3 * (u^2) * (v^2) / 4 + 5 * (u^2) / 4 + 11 * (v^2) / 4 - 17 / 4) * hE1' +
      (3 * (u^2) * (v^2) / 4 - 7 * (u^2) / 4 - 11 * (v^2) / 4 + 25 / 4) * hE2' +
      ((u^2) / 2 + 3 * (v^2)^2 / 4 - 9 * (v^2) / 4 - 1) * hE3'
  exact one_ne_zero h
