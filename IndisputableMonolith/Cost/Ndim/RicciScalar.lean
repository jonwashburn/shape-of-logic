import IndisputableMonolith.Cost.Ndim.Core

/-!
# Ricci scalar equivalence for the 2D cost Hessian metric

The Levi-Civita connection on M_x (the Hessian manifold in positive
coordinates) has Ricci scalar curvature expressed two ways:

* **Z-form** (Section 4.5): rational in Z = x^{2a} y^{2b},
* **q-form** (Eq. 4.26): hyperbolic in q = a s + b t.

Under Z = e^{2q}, the identities coth q = (Z+1)/(Z−1) and
csch q = 2 Z^{1/2}/(Z−1) convert one into the other.

We prove the algebraic equivalence by reducing both to a common
rational form in w = exp q, then closing with `field_simp` + `ring`.

Reference: "Multidimensional Cost Geometry", Washburn–Zlatanović–Beltracchi,
Sections 4.5 and 4.6.2.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

noncomputable section

/-- The Ricci scalar in (q, r)-coordinates, Eq. (4.26).
    Written with sinh/cosh to avoid coth/csch. -/
def ricciQ (a b q : ℝ) : ℝ :=
  (a + b) * ((a + b) * Real.cosh q - 2 * Real.sinh q) /
    (2 * (Real.sinh q) ^ 2 * ((a + b) * Real.cosh q - Real.sinh q) ^ 2)

/-- The Ricci scalar in (x, y)-coordinates (Section 4.5),
    parametrised by q via Z = exp(2q), Z^{3/2} = exp(3q). -/
def ricciZexp (a b q : ℝ) : ℝ :=
  let Z := Real.exp (2 * q)
  4 * (a + b) * Real.exp (3 * q) *
    ((a + b - 2) * Z + (a + b + 2)) /
    ((Z - 1) ^ 2 * ((a + b - 1) * Z + (a + b + 1)) ^ 2)

/-- Canonical rational form of the Ricci scalar in w = exp q. -/
def ricciW (a b w : ℝ) : ℝ :=
  4 * (a + b) * w ^ 3 *
    ((a + b - 2) * w ^ 2 + (a + b + 2)) /
    ((w ^ 2 - 1) ^ 2 * ((a + b - 1) * w ^ 2 + (a + b + 1)) ^ 2)

private theorem exp_two_mul (q : ℝ) :
    Real.exp (2 * q) = (Real.exp q) ^ 2 := by
  rw [show (2 : ℝ) * q = q + q from by ring, Real.exp_add]; ring

private theorem exp_three_mul (q : ℝ) :
    Real.exp (3 * q) = (Real.exp q) ^ 3 := by
  rw [show (3 : ℝ) * q = q + (q + q) from by ring, Real.exp_add, Real.exp_add]; ring

/-- The Z-form is `ricciW` evaluated at w = exp q. -/
theorem ricciZexp_eq_ricciW (a b q : ℝ) :
    ricciZexp a b q = ricciW a b (Real.exp q) := by
  unfold ricciZexp ricciW; rw [exp_two_mul, exp_three_mul]

/-- The q-form is also `ricciW` at w = exp q. -/
theorem ricciQ_eq_ricciW (a b q : ℝ)
    (hq : q ≠ 0)
    (hLC : (a + b) * Real.cosh q - Real.sinh q ≠ 0) :
    ricciQ a b q = ricciW a b (Real.exp q) := by
  set w := Real.exp q with hw_def
  have hw_pos : 0 < w := Real.exp_pos q
  have hw_ne : w ≠ 0 := hw_pos.ne'
  have hsinh_ne : Real.sinh q ≠ 0 := Real.sinh_ne_zero.mpr hq
  have hcosh_w : Real.cosh q = (w ^ 2 + 1) / (2 * w) := by
    rw [Real.cosh_eq, Real.exp_neg]; field_simp; ring
  have hsinh_w : Real.sinh q = (w ^ 2 - 1) / (2 * w) := by
    rw [Real.sinh_eq, Real.exp_neg]; field_simp; ring
  have hw2m1 : w ^ 2 - 1 ≠ 0 := by
    intro h; exact hsinh_ne (by rw [hsinh_w, h, zero_div])
  have hLCw : (a + b - 1) * w ^ 2 + (a + b + 1) ≠ 0 := by
    intro h; apply hLC; rw [hcosh_w, hsinh_w]; field_simp; linarith
  show ricciQ a b q = ricciW a b w
  unfold ricciQ ricciW
  rw [hcosh_w, hsinh_w]
  field_simp [hw_ne, hw2m1, hLCw]
  ring

/-- **Main result**: the two coordinate forms of the Ricci scalar agree. -/
theorem ricci_scalar_equiv (a b q : ℝ)
    (hq : q ≠ 0)
    (hLC : (a + b) * Real.cosh q - Real.sinh q ≠ 0) :
    ricciQ a b q = ricciZexp a b q := by
  rw [ricciQ_eq_ricciW a b q hq hLC, ricciZexp_eq_ricciW]

end

end Ndim
end Cost
end IndisputableMonolith
