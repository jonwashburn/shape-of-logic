import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Dimension-Parametric Cayley-Menger Matrix

This module starts the n-dimensional generalization after the 3D
tetrahedral closure: instead of expanding the determinant as a polynomial,
we define the full Cayley-Menger matrix for an arbitrary `n`-simplex using
Mathlib matrices and determinants.
-/

namespace IndisputableMonolith
namespace Geometry
namespace CayleyMengerN

noncomputable section

/-- Squared-distance data for an `n`-simplex with vertices `Fin (n+1)`. -/
structure SimplexSquaredDistances (n : ℕ) where
  distSq : Fin (n + 1) → Fin (n + 1) → ℝ
  symm : ∀ i j, distSq i j = distSq j i
  diag_zero : ∀ i, distSq i i = 0

/-- Convert a Cayley-Menger matrix index to an optional simplex vertex.
Index `0` is the leading Cayley-Menger row/column; index `k+1` represents
simplex vertex `k`. -/
def cmIndexVertex {n : ℕ} (i : Fin (n + 2)) : Option (Fin (n + 1)) :=
  if h : i.val = 0 then none
  else some ⟨i.val - 1, by omega⟩

/-- The full `(n+2) × (n+2)` Cayley-Menger matrix. -/
def cmMatrixN {n : ℕ} (D : SimplexSquaredDistances n) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  fun i j =>
    match cmIndexVertex i, cmIndexVertex j with
    | none, none => 0
    | none, some _ => 1
    | some _, none => 1
    | some vi, some vj => D.distSq vi vj

/-- The n-dimensional Cayley-Menger determinant. -/
def cmDetN {n : ℕ} (D : SimplexSquaredDistances n) : ℝ :=
  Matrix.det (cmMatrixN D)

/-- The formal squared-volume expression:

`V_n^2 = (-1)^(n+1) det(CM) / (2^n (n!)^2)`.
-/
def simplexVolumeSqN {n : ℕ} (D : SimplexSquaredDistances n) : ℝ :=
  ((-1 : ℝ) ^ (n + 1) * cmDetN D) /
    ((2 : ℝ) ^ n * ((Nat.factorial n : ℕ) : ℝ) ^ 2)

/-- The Cayley-Menger matrix is symmetric whenever the squared-distance
data is symmetric. -/
theorem cmMatrixN_symm {n : ℕ} (D : SimplexSquaredDistances n)
    (i j : Fin (n + 2)) :
    cmMatrixN D i j = cmMatrixN D j i := by
  unfold cmMatrixN
  cases cmIndexVertex i <;> cases cmIndexVertex j <;> simp
  exact D.symm _ _

end

end CayleyMengerN
end Geometry
end IndisputableMonolith
