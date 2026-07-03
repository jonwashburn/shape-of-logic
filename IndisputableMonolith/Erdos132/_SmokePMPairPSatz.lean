import Mathlib

/-!
Smoke test: the division-free Positivstellensatz certificate template for the
"harder" pmpair cores, and the negative control that proves the old
resultant/divide route is UNSOUND on the domain-kill family.

Panel-greenlit uniform template (per instance): given the two SUM/DIFF2 edge
equations `heq1 : eq1 = 0`, `heq2 : eq2 = 0` and the open-square domain bounds
`0 < a < 1`, `0 < b < 1`, we exhibit a target polynomial `P` with a ring-checked
identity `P = Q1*eq1 + Q2*eq2` (verified by `linear_combination`), where `P` is
sign-definite on the open square (verified by `nlinarith`/`linarith` against the
domain bounds). `P = 0` (forced by the edges) then contradicts `P > 0` (forced by
the domain), giving `False`. lake is the sole judge of the positivity step.

Two routes produce the identity:
  * domain_kill  : `P = ±eq1` where the linear edge is itself sign-definite on the
                   open square (e.g. `2 - b > 0` from `b < 1`). Q on the other edge
                   is 0. Four of the five distinct shapes below.
  * divide       : `P = other_eq - quo*lin_eq` (exact division), the eliminant, when
                   the eliminant is genuinely root-free on `(0,1)`. One shape below
                   (`P = -12a^2+12a = 12a(1-a)`), with a nontrivial multiplier.

The soundness point (`_SmokePMPairNegControl` below): on the `2 - b` domain-kill
family, the DIVIDE route yields the eliminant `-4a^2+16a-4`, which has a root at
`a = 2 - sqrt 3 ~ 0.268` INSIDE `(0,1)`. So the divide route's positivity step is
FALSE there and Lean correctly cannot prove it; only the domain-kill route is
sound. This is exactly the v1 pipeline bug (missing extraneous-root filtering).
-/

namespace IndisputableMonolith.Erdos132.SmokePMPairPSatz

-- Shape 1 (domain_kill): eq1 = a - b + 1, P = a - b + 1.
-- a - b + 1 = 0 with a > 0 forces b = a + 1 > 1, contradicting b < 1.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (heq1 : a - b + 1 = 0)
    (heq2 : -3 * a ^ 2 + 12 * a - b ^ 2 + 2 * b - 1 = 0) : False := by
  have hP : a - b + 1 = 0 := by linear_combination heq1
  nlinarith [hP, ha0, hb1]

-- Shape 2 (domain_kill): eq1 = 2 - b, P = 2 - b.
-- 2 - b = 0 forces b = 2, contradicting b < 1.  THE SOUND route for this family.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (heq1 : 2 - b = 0)
    (heq2 : -4 * a ^ 2 + 2 * a * b + 12 * a - b ^ 2 = 0) : False := by
  have hP : 2 - b = 0 := by linear_combination heq1
  nlinarith [hP, hb1]

-- Shape 3 (divide): eq1 = a + b - 1, eq2 = -3a^2+6ab+6a-3b^2+6b-3,
-- P = -12a^2+12a = 12a(1-a) > 0 on (0,1), Q1 = -9a+3b-3, Q2 = 1.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (heq1 : a + b - 1 = 0)
    (heq2 : -3 * a ^ 2 + 6 * a * b + 6 * a - 3 * b ^ 2 + 6 * b - 3 = 0) : False := by
  have hP : -12 * a ^ 2 + 12 * a = 0 := by
    linear_combination (-9 * a + 3 * b - 3) * heq1 + heq2
  nlinarith [hP, ha0, ha1]

-- Shape 4 (domain_kill): eq1 = b, P = b.
-- b = 0 contradicts b > 0.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (heq1 : b = 0)
    (heq2 : -4 * a ^ 2 + 6 * a * b + 8 * a - 3 * b ^ 2 + 6 * b - 4 = 0) : False := by
  have hP : b = 0 := by linear_combination heq1
  nlinarith [hP, hb0]

-- Shape 5 (domain_kill): eq1 = -a + b + 1, P = -a + b + 1.
-- -a + b + 1 = 0 with b > 0 forces a = b + 1 > 1, contradicting a < 1.
example (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (heq1 : -a + b + 1 = 0)
    (heq2 : -3 * a ^ 2 + 6 * a * b + 6 * a - 3 * b ^ 2 + 6 * b - 3 = 0) : False := by
  have hP : -a + b + 1 = 0 := by linear_combination heq1
  nlinarith [hP, hb0, ha1]

/-! Negative control: the v1-bug soundness gap. -/

-- The DIVIDE route on the `2 - b` core: eq1 = 2 - b, eq2 = -4a^2+2ab+12a-b^2.
-- Exact division gives the eliminant P = -4a^2+16a-4 with Q1 = 2a-b-2, Q2 = 1.
-- The ring IDENTITY holds (this compiles):
example (a b : ℝ)
    (heq1 : 2 - b = 0)
    (heq2 : -4 * a ^ 2 + 2 * a * b + 12 * a - b ^ 2 = 0) :
    -4 * a ^ 2 + 16 * a - 4 = 0 := by
  linear_combination (2 * a - b - 2) * heq1 + heq2

-- ...but the divide route's POSITIVITY claim is FALSE: -4a^2+16a-4 has a root in
-- (0,1) (a = 2 - sqrt 3), so it is NOT positive throughout (0,1). We prove the
-- negation, exhibiting a = 1/10 where the eliminant is negative. This is why the
-- divide route must be REJECTED for this family and domain-kill (Shape 2) used.
example : ¬ (∀ a : ℝ, 0 < a → a < 1 → 0 < -4 * a ^ 2 + 16 * a - 4) := by
  intro h
  have := h (1 / 10) (by norm_num) (by norm_num)
  norm_num at this

end IndisputableMonolith.Erdos132.SmokePMPairPSatz
