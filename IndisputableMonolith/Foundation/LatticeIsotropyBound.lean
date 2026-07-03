import Mathlib

/-!
# Lattice Isotropy Bound — Beltracchi Response §6

Key structural bound: lattice dispersion is non-negative (0 ≤ ω²).
This follows from 1 - cos(y) ≥ 0.

Also: 1 - cos(y) ≤ 2 (bounded above).

Together these constrain the lattice Laplacian spectrum.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.LatticeIsotropyBound

theorem one_minus_cos_nonneg (y : ℝ) : 0 ≤ 1 - Real.cos y :=
  by linarith [Real.cos_le_one y]

theorem one_minus_cos_le_two (y : ℝ) : 1 - Real.cos y ≤ 2 :=
  by linarith [Real.neg_one_le_cos y]

theorem lattice_dispersion_bounded (y : ℝ) :
    0 ≤ 1 - Real.cos y ∧ 1 - Real.cos y ≤ 2 :=
  ⟨one_minus_cos_nonneg y, one_minus_cos_le_two y⟩

theorem lattice_3d_nonneg (a k1 k2 k3 : ℝ) (ha : 0 < a) :
    0 ≤ (2 / a ^ 2) * ((1 - Real.cos (a * k1)) +
                        (1 - Real.cos (a * k2)) +
                        (1 - Real.cos (a * k3))) :=
  mul_nonneg (by positivity)
    (by linarith [one_minus_cos_nonneg (a * k1), one_minus_cos_nonneg (a * k2),
                  one_minus_cos_nonneg (a * k3)])

structure LatticeIsotropyCert where
  dispersion_nonneg : ∀ y : ℝ, 0 ≤ 1 - Real.cos y
  dispersion_bounded : ∀ y : ℝ, 1 - Real.cos y ≤ 2
  lattice_3d_nonneg : ∀ (a k1 k2 k3 : ℝ), 0 < a →
    0 ≤ (2 / a ^ 2) * ((1 - Real.cos (a * k1)) + (1 - Real.cos (a * k2)) + (1 - Real.cos (a * k3)))

def latticeIsotropyCert : LatticeIsotropyCert where
  dispersion_nonneg := one_minus_cos_nonneg
  dispersion_bounded := one_minus_cos_le_two
  lattice_3d_nonneg := lattice_3d_nonneg

end IndisputableMonolith.Foundation.LatticeIsotropyBound
