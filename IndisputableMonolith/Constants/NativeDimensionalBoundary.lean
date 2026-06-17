import Mathlib
import IndisputableMonolith.Foundation.SIBridgeClosure

/-!
# Native Constants and the Dimensional Boundary

This module records the honest boundary between first-principles native
constants and SI calibration.

The recognition framework can force dimensionless/native identities such as
`hbar_RS = phi^(-5)`, `G_RS * hbar_RS = 1/pi`, and `kappa_RS * hbar_RS = 8`.
It cannot, from pure dimensionless data alone, output the absolute SI value of
`hbar` or `G`.  A dimensional bridge needs a dimensional anchor.

This is not a weakness of RS; it is dimensional analysis.  The dimensions of
`c`, `hbar`, and `G` are independent, so no nontrivial monomial
`c^a hbar^b G^d` is dimensionless.

## Where the positive half lives (do not re-prove it here)

This module proves the negative half (an anchor is *required*). The positive
half (one anchor *suffices* and determines the whole bridge uniquely) is
already formalized, more completely, elsewhere:

* `Foundation.SIBridgeClosure.tau0_eq_sqrt_pi_planck_time` /
  `a_T_sq_eq`: given the `c, ℏ, G` constraints, the tick conversion factor is
  uniquely `a_T = √π · τ_Planck`.
* `Measurement.RSNative.Calibration.SingleAnchor`: from one scalar (`τ₀` in
  seconds) the full `ExternalCalibration` is derived (meters/voxel from SI `c`,
  joules/coh from SI `ℏ`).
* `Verification.FirstPrinciplesToSI.first_principles_to_SI_capstone`: T0–T8 plus
  the single anchor `τ₀` yields the electron mass in SI kilograms with the mass
  audit at 0 Hypothesis / 0 Open / 0 External.

Together: exactly one dimensional anchor, and it determines everything.
-/

namespace IndisputableMonolith
namespace Constants
namespace NativeDimensionalBoundary

open IndisputableMonolith.Foundation.SIBridgeClosure

noncomputable section

/-- Dimension exponents `(L,T,M)` of a monomial `c^a hbar^b G^d`.

`c` has dimensions `L T^-1`; `hbar` has dimensions `M L^2 T^-1`;
`G` has dimensions `L^3 M^-1 T^-2`. -/
def cHbarGDimension (a b d : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2 * b + 3 * d, -a - b - 2 * d, b - d)

/-- The `(c, hbar, G)` dimension matrix: columns are the `(L,T,M)` exponent
vectors of `c = (1,-1,0)`, `hbar = (2,-1,1)`, `G = (3,-2,-1)`. -/
def dimMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of ![![1, 2, 3], ![-1, -1, -2], ![0, 1, -1]]

/-- The determinant of the `(c, hbar, G)` dimension matrix is `-2` (a real
`Matrix.det`, not a free-floating numeral). The value `-2` (rather than `±1`)
also records that `(c, hbar, G)` span an index-`2` sublattice of the integer
dimension lattice, so the Planck system is a basis only up to half-integer
powers; but the only fact the boundary argument needs is `det ≠ 0`. -/
theorem dimMatrix_det : dimMatrix.det = -2 := by
  simp [dimMatrix, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one]

/-- The determinant of the `(c,hbar,G)` dimension matrix is nonzero, i.e. the
three dimension vectors are linearly independent. -/
theorem dimension_matrix_c_hbar_G_det_nonzero : dimMatrix.det ≠ 0 := by
  rw [dimMatrix_det]; norm_num

/-- No nontrivial monomial in `c`, `hbar`, and `G` is dimensionless. -/
theorem no_nontrivial_dimensionless_monomial {a b d : ℤ}
    (h : cHbarGDimension a b d = (0, 0, 0)) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  unfold cHbarGDimension at h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hL, hT, hM⟩
  omega

/-- A pure-number theory can fix only dimensionless/native relations among
`c`, `hbar`, and `G`; an absolute SI value needs a dimensional anchor. -/
theorem dimensionless_theory_needs_anchor {a b d : ℤ}
    (hDimensionless : cHbarGDimension a b d = (0, 0, 0)) :
    a = 0 ∧ b = 0 ∧ d = 0 :=
  no_nontrivial_dimensionless_monomial hDimensionless

/-- The squared tick scale that the SI bridge assigns after a positive supplied
value of Newton's constant.  This is the same algebraic shape as
`SIBridgeClosure.a_T_sq_eq`, but with `G_input` left variable to expose the
anchor dependence. -/
def calibratedTickSquare (G_input : ℝ) : ℝ :=
  Real.pi * hbar_SI * G_input / c_SI ^ 5

/-- Any positive supplied `G_input` gives a positive calibrated tick square. -/
theorem calibratedTickSquare_pos {G_input : ℝ} (hG : 0 < G_input) :
    0 < calibratedTickSquare G_input := by
  unfold calibratedTickSquare
  exact div_pos (mul_pos (mul_pos Real.pi_pos hbar_SI_pos) hG) (pow_pos c_SI_pos 5)

/-- Changing the supplied `G` changes the calibrated tick square.  Thus the SI
bridge depends on the dimensional anchor; it does not predict that anchor. -/
theorem calibratedTickSquare_injective :
    Function.Injective calibratedTickSquare := by
  intro G₁ G₂ h
  unfold calibratedTickSquare at h
  have hcoeff : Real.pi * hbar_SI / c_SI ^ 5 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hbar_SI_pos.ne') (pow_ne_zero 5 c_SI_pos.ne')
  have hlin : (Real.pi * hbar_SI / c_SI ^ 5) * G₁ =
      (Real.pi * hbar_SI / c_SI ^ 5) * G₂ := by
    calc
      (Real.pi * hbar_SI / c_SI ^ 5) * G₁
          = Real.pi * hbar_SI * G₁ / c_SI ^ 5 := by ring
      _ = Real.pi * hbar_SI * G₂ / c_SI ^ 5 := h
      _ = (Real.pi * hbar_SI / c_SI ^ 5) * G₂ := by ring
  exact (mul_left_cancel₀ hcoeff hlin)

/-- The SI bridge is a calibration map: for every positive supplied dimensional
anchor `G_input`, the bridge assigns a positive tick-square scale, and different
anchors give different scales. -/
theorem si_bridge_is_calibration_not_prediction :
    (∀ G_input : ℝ, 0 < G_input → 0 < calibratedTickSquare G_input) ∧
      Function.Injective calibratedTickSquare :=
  ⟨fun _ hG => calibratedTickSquare_pos hG, calibratedTickSquare_injective⟩

/-- Certificate packaging the dimensional-boundary audit. -/
structure NativeDimensionalBoundaryCert where
  determinant_nonzero : dimMatrix.det ≠ 0
  no_dimensionless_monomial :
    ∀ {a b d : ℤ}, cHbarGDimension a b d = (0, 0, 0) → a = 0 ∧ b = 0 ∧ d = 0
  bridge_calibrates :
    (∀ G_input : ℝ, 0 < G_input → 0 < calibratedTickSquare G_input) ∧
      Function.Injective calibratedTickSquare

/-- Native constants are first-principles objects only up to the dimensional
boundary; SI conversion is a uniquely constrained calibration once an anchor is
supplied. -/
theorem native_dimensional_boundary_cert : NativeDimensionalBoundaryCert where
  determinant_nonzero := dimension_matrix_c_hbar_G_det_nonzero
  no_dimensionless_monomial := fun h => no_nontrivial_dimensionless_monomial h
  bridge_calibrates := si_bridge_is_calibration_not_prediction

end

end NativeDimensionalBoundary
end Constants
end IndisputableMonolith
