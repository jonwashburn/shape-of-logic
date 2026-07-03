import Mathlib

/-!
Smoke test: verify that the gen_solve-produced Nullstellensatz identity for a
"HARDER_ROOTFREE" sign-pair (pmpair) core (extracted by
`_certgen_pmpair_one.py`: subset with a conjugate pair (p,q) sharing a
neighbor t, winning combo (cp,cq)=(1,b), resultant g(a) = -4a^2+12a =
4a(3-a) > 0 on (0,1)) compiles in Lean via `linear_combination` +
sign analysis, mirroring the EASY-triple template in `_SmokeEmitOne.lean`
but for the SUM/DIFF2 (`pm_pair_kill`) system instead of the plain
three-equation triple system.

Unlike the triple case (target = 1, a pure ideal-membership contradiction),
the pmpair case target is the *resultant* g(a): the two SUM/DIFF2 equations
eq1 = 2M-(cp+cq), eq2 = 16W-(cp-cq)^2 combine to g(a), and g(a)=0 (forced by
the case hyps) contradicts g(a)>0 (forced by 0<a<1), which is the standard
resultant-based root-freeness argument translated into `linear_combination`
+ `nlinarith`/`linarith` instead of a resultant computation in Lean.
-/

-- Step 1: pure eq1/eq2-level check (the risky, novel step for pmpair).
-- eq1 = a-b+1, eq2 = -3a^2+12a-b^2+2b-1 (cp=1, cq=b), g(a) = -4a^2+12a.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (heq1 : a - b + 1 = 0)
    (heq2 : -3 * a ^ 2 + 12 * a - b ^ 2 + 2 * b - 1 = 0) : False := by
  have hg0 : -4 * a ^ 2 + 12 * a = 0 := by
    linear_combination (-a - b + 1) * heq1 + heq2
  have hgpos : 0 < -4 * a ^ 2 + 12 * a := by nlinarith [ha0, ha1]
  linarith

-- Step 2: full geometric chain from the conjugate-pair hypotheses
-- (`hyq : yq = -yp` from the sign pair, `hyp2`/`hyt2` from the y^2 = Y
-- node facts, `hdp`/`hdq` from the two squared-distance case facts) down
-- through eq1=0/eq2=0 to `False`, using the u,v-substituted (a=u^2,b=v^2)
-- concrete node coordinates: xp=1/2, xt=1-u^2/2, yp^2=Ysq=3/4,
-- yt^2=Yt=u^2-u^4/4. This is the `pm_pair_kill` / SUM+DIFF2 template.
example (u v yp yq yt : ℝ)
    (ha0 : 0 < u ^ 2) (ha1 : u ^ 2 < 1)
    (hyq : yq = -yp)
    (hyp2 : yp ^ 2 = 3 / 4)
    (hyt2 : yt ^ 2 = u ^ 2 - u ^ 4 / 4)
    -- case fact: d2(t,p) = cp = 1
    (hdp : (1 - u ^ 2 / 2 - 1 / 2) ^ 2 + (yt - yp) ^ 2 = 1)
    -- case fact: d2(t,q) = cq = b = v^2
    (hdq : (1 - u ^ 2 / 2 - 1 / 2) ^ 2 + (yt - yq) ^ 2 = v ^ 2) : False := by
  -- eq1 = 2M-(cp+cq) = 0, derived from hdp,hdq,hyq,hyp2,hyt2 (SUM branch).
  have heq1 : u ^ 2 - v ^ 2 + 1 = 0 := by
    linear_combination hdp + hdq + (yp - yq + 2 * yt) * hyq - 2 * hyp2 - 2 * hyt2
  -- eq2 = 16W-(cp-cq)^2 = 0, derived from hdp,hdq,hyq,hyp2,hyt2 (DIFF2 branch).
  have heq2 : -3 * u ^ 4 + 12 * u ^ 2 - v ^ 4 + 2 * v ^ 2 - 1 = 0 := by
    linear_combination
      (-v ^ 2 + yp ^ 2 - 2 * yp * yt - yq ^ 2 + 2 * yq * yt + 1) * hdp +
      (v ^ 2 - yp ^ 2 + 2 * yp * yt + yq ^ 2 - 2 * yq * yt - 1) * hdq +
      (-yp ^ 3 + yp ^ 2 * yq + 4 * yp ^ 2 * yt + yp * yq ^ 2 - 8 * yp * yq * yt +
        12 * yp * yt ^ 2 - yq ^ 3 + 4 * yq ^ 2 * yt - 4 * yq * yt ^ 2) * hyq +
      (-16 * yt ^ 2) * hyp2 + (-12) * hyt2
  -- Nullstellensatz combo: g(u) = L1*eq1 + L2*eq2 = -4u^4+12u^2 = 4u^2(3-u^2).
  have hg0 : -4 * u ^ 4 + 12 * u ^ 2 = 0 := by
    linear_combination (-u ^ 2 - v ^ 2 + 1) * heq1 + heq2
  have hgpos : 0 < -4 * u ^ 4 + 12 * u ^ 2 := by nlinarith [ha0, ha1]
  linarith
