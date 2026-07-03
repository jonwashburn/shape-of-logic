import Mathlib.Tactic

/-!
Sanity check for the "HARDER_ROOTFREE" g(a) sign-analysis strategy: every
irreducible quadratic factor of g(a) found by the wide `_certgen_gfactor_check.py`
scan (a^2-3a-1, a^2-a+1, 2a^2-2a+1) should have a fixed, provable sign on
`0 < a < 1`, closable by `nlinarith` with at most one `sq_nonneg` hint.
This validates the Lean-side half of the certificate template before building
the full emitter.
-/

-- a^2 - 3a - 1: negative on all of ℝ_{≥0} actually, since roots are
-- (3±√13)/2 ≈ -0.30, 3.30, both outside (0,1). Hand certificate:
-- -(a^2-3a-1) = a*(1-a) + 2a + 1, manifestly positive for 0<a<1.
example (a : ℝ) (ha : 0 < a) (ha' : a < 1) : a ^ 2 - 3 * a - 1 < 0 := by
  nlinarith [mul_pos ha (sub_pos.mpr ha')]

-- a^2 - a + 1: negative discriminant, positive for ALL real a (no interval needed).
-- 4*(a^2-a+1) = (2a-1)^2 + 3.
example (a : ℝ) : 0 < a ^ 2 - a + 1 := by
  nlinarith [sq_nonneg (2 * a - 1)]

-- 2a^2 - 2a + 1: negative discriminant, positive for ALL real a.
-- 2*(2a^2-2a+1) = (2a-1)^2 + 1.
example (a : ℝ) : 0 < 2 * a ^ 2 - 2 * a + 1 := by
  nlinarith [sq_nonneg (2 * a - 1)]

-- Also check the "EASY" combinator shape used by the certificate template:
-- given three squared-membership equations E1,E2,E3 (each of shape
-- (M-c)^2 - 4*W = 0) and a Nullstellensatz certificate 1 = Λ1*E1+Λ2*E2+Λ3*E3,
-- linear_combination should directly close `False` after deriving a
-- manifestly-false numeric identity. Toy shape (Λ's = polynomials in a,b):
example (a b E1 E2 E3 L1 L2 L3 : ℝ)
    (h1 : E1 = 0) (h2 : E2 = 0) (h3 : E3 = 0)
    (hcert : (1 : ℝ) = L1 * E1 + L2 * E2 + L3 * E3) : False := by
  have : (1 : ℝ) = 0 := by linear_combination hcert + L1 * h1 + L2 * h2 + L3 * h3
  norm_num at this
