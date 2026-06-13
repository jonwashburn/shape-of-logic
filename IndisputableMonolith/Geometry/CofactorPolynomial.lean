import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import IndisputableMonolith.Geometry.CayleyMengerMatrix
import IndisputableMonolith.Geometry.DihedralCayleyMenger

/-!
# Explicit Cayley-Menger Cofactor Polynomials

This generated module expands every tetrahedral Cayley-Menger cofactor into
an explicit polynomial in the six squared edge coordinates.  It is the
cofactor analogue of `CayleyMengerDerivatives`: downstream dihedral-angle
calculus can refer to named polynomial partials instead of opaque `fderiv`
terms.
-/

namespace IndisputableMonolith
namespace Geometry
namespace CofactorPolynomial

open CayleyMengerPolynomial CayleyMengerMatrix

noncomputable section

/-- Explicit polynomial normal form for every Cayley-Menger cofactor. -/
def cmCofactor3Poly (r c : Fin 5) (a : SqEdges) : ℝ :=
  match r.val, c.val with
  | 0, 0 => (a 2) ^ 2 * (a 3) ^ 2 - 2 * (a 1) * (a 2) * (a 3) * (a 4) + (a 1) ^ 2 * (a 4) ^ 2 - 2 * (a 0) * (a 2) * (a 3) * (a 5) - 2 * (a 0) * (a 1) * (a 4) * (a 5) + (a 0) ^ 2 * (a 5) ^ 2
  | 0, 1 => -2 * (a 3) * (a 4) * (a 5) + (a 2) * (a 3) * (a 5) + (a 2) * (a 3) * (a 4) - (a 2) * (a 3) ^ 2 + (a 1) * (a 4) * (a 5) - (a 1) * (a 4) ^ 2 + (a 1) * (a 3) * (a 4) - (a 0) * (a 5) ^ 2 + (a 0) * (a 4) * (a 5) + (a 0) * (a 3) * (a 5)
  | 0, 2 => (a 2) * (a 3) * (a 5) - (a 2) ^ 2 * (a 3) + (a 1) * (a 4) * (a 5) - 2 * (a 1) * (a 2) * (a 5) + (a 1) * (a 2) * (a 4) + (a 1) * (a 2) * (a 3) - (a 1) ^ 2 * (a 4) - (a 0) * (a 5) ^ 2 + (a 0) * (a 2) * (a 5) + (a 0) * (a 1) * (a 5)
  | 0, 3 => (a 2) * (a 3) * (a 4) - (a 2) ^ 2 * (a 3) - (a 1) * (a 4) ^ 2 + (a 1) * (a 2) * (a 4) + (a 0) * (a 4) * (a 5) + (a 0) * (a 2) * (a 5) - 2 * (a 0) * (a 2) * (a 4) + (a 0) * (a 2) * (a 3) + (a 0) * (a 1) * (a 4) - (a 0) ^ 2 * (a 5)
  | 0, 4 => -(a 2) * (a 3) ^ 2 + (a 1) * (a 3) * (a 4) + (a 1) * (a 2) * (a 3) - (a 1) ^ 2 * (a 4) + (a 0) * (a 3) * (a 5) + (a 0) * (a 2) * (a 3) + (a 0) * (a 1) * (a 5) + (a 0) * (a 1) * (a 4) - 2 * (a 0) * (a 1) * (a 3) - (a 0) ^ 2 * (a 5)
  | 1, 0 => -2 * (a 3) * (a 4) * (a 5) + (a 2) * (a 3) * (a 5) + (a 2) * (a 3) * (a 4) - (a 2) * (a 3) ^ 2 + (a 1) * (a 4) * (a 5) - (a 1) * (a 4) ^ 2 + (a 1) * (a 3) * (a 4) - (a 0) * (a 5) ^ 2 + (a 0) * (a 4) * (a 5) + (a 0) * (a 3) * (a 5)
  | 1, 1 => (a 5) ^ 2 - 2 * (a 4) * (a 5) + (a 4) ^ 2 - 2 * (a 3) * (a 5) - 2 * (a 3) * (a 4) + (a 3) ^ 2
  | 1, 2 => -(a 5) ^ 2 + (a 4) * (a 5) + (a 3) * (a 5) + (a 2) * (a 5) - (a 2) * (a 4) + (a 2) * (a 3) + (a 1) * (a 5) + (a 1) * (a 4) - (a 1) * (a 3) - 2 * (a 0) * (a 5)
  | 1, 3 => (a 4) * (a 5) - (a 4) ^ 2 + (a 3) * (a 4) - (a 2) * (a 5) + (a 2) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5) + (a 0) * (a 4) - (a 0) * (a 3)
  | 1, 4 => (a 3) * (a 5) + (a 3) * (a 4) - (a 3) ^ 2 - 2 * (a 2) * (a 3) - (a 1) * (a 5) + (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5) - (a 0) * (a 4) + (a 0) * (a 3)
  | 2, 0 => (a 2) * (a 3) * (a 5) - (a 2) ^ 2 * (a 3) + (a 1) * (a 4) * (a 5) - 2 * (a 1) * (a 2) * (a 5) + (a 1) * (a 2) * (a 4) + (a 1) * (a 2) * (a 3) - (a 1) ^ 2 * (a 4) - (a 0) * (a 5) ^ 2 + (a 0) * (a 2) * (a 5) + (a 0) * (a 1) * (a 5)
  | 2, 1 => -(a 5) ^ 2 + (a 4) * (a 5) + (a 3) * (a 5) + (a 2) * (a 5) - (a 2) * (a 4) + (a 2) * (a 3) + (a 1) * (a 5) + (a 1) * (a 4) - (a 1) * (a 3) - 2 * (a 0) * (a 5)
  | 2, 2 => (a 5) ^ 2 - 2 * (a 2) * (a 5) + (a 2) ^ 2 - 2 * (a 1) * (a 5) - 2 * (a 1) * (a 2) + (a 1) ^ 2
  | 2, 3 => -(a 4) * (a 5) + (a 2) * (a 5) + (a 2) * (a 4) - 2 * (a 2) * (a 3) - (a 2) ^ 2 + (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) + (a 0) * (a 2) - (a 0) * (a 1)
  | 2, 4 => -(a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) - 2 * (a 1) * (a 4) + (a 1) * (a 3) + (a 1) * (a 2) - (a 1) ^ 2 + (a 0) * (a 5) - (a 0) * (a 2) + (a 0) * (a 1)
  | 3, 0 => (a 2) * (a 3) * (a 4) - (a 2) ^ 2 * (a 3) - (a 1) * (a 4) ^ 2 + (a 1) * (a 2) * (a 4) + (a 0) * (a 4) * (a 5) + (a 0) * (a 2) * (a 5) - 2 * (a 0) * (a 2) * (a 4) + (a 0) * (a 2) * (a 3) + (a 0) * (a 1) * (a 4) - (a 0) ^ 2 * (a 5)
  | 3, 1 => (a 4) * (a 5) - (a 4) ^ 2 + (a 3) * (a 4) - (a 2) * (a 5) + (a 2) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5) + (a 0) * (a 4) - (a 0) * (a 3)
  | 3, 2 => -(a 4) * (a 5) + (a 2) * (a 5) + (a 2) * (a 4) - 2 * (a 2) * (a 3) - (a 2) ^ 2 + (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) + (a 0) * (a 2) - (a 0) * (a 1)
  | 3, 3 => (a 4) ^ 2 - 2 * (a 2) * (a 4) + (a 2) ^ 2 - 2 * (a 0) * (a 4) - 2 * (a 0) * (a 2) + (a 0) ^ 2
  | 3, 4 => -(a 3) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - (a 1) * (a 2) - 2 * (a 0) * (a 5) + (a 0) * (a 4) + (a 0) * (a 3) + (a 0) * (a 2) + (a 0) * (a 1) - (a 0) ^ 2
  | 4, 0 => -(a 2) * (a 3) ^ 2 + (a 1) * (a 3) * (a 4) + (a 1) * (a 2) * (a 3) - (a 1) ^ 2 * (a 4) + (a 0) * (a 3) * (a 5) + (a 0) * (a 2) * (a 3) + (a 0) * (a 1) * (a 5) + (a 0) * (a 1) * (a 4) - 2 * (a 0) * (a 1) * (a 3) - (a 0) ^ 2 * (a 5)
  | 4, 1 => (a 3) * (a 5) + (a 3) * (a 4) - (a 3) ^ 2 - 2 * (a 2) * (a 3) - (a 1) * (a 5) + (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5) - (a 0) * (a 4) + (a 0) * (a 3)
  | 4, 2 => -(a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) - 2 * (a 1) * (a 4) + (a 1) * (a 3) + (a 1) * (a 2) - (a 1) ^ 2 + (a 0) * (a 5) - (a 0) * (a 2) + (a 0) * (a 1)
  | 4, 3 => -(a 3) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - (a 1) * (a 2) - 2 * (a 0) * (a 5) + (a 0) * (a 4) + (a 0) * (a 3) + (a 0) * (a 2) + (a 0) * (a 1) - (a 0) ^ 2
  | 4, 4 => (a 3) ^ 2 - 2 * (a 1) * (a 3) + (a 1) ^ 2 - 2 * (a 0) * (a 3) - 2 * (a 0) * (a 1) + (a 0) ^ 2
  | _, _ => 0

/-- Explicit partial derivative of a cofactor polynomial with respect to one
squared-edge coordinate. -/
def cmCofactorPartial (r c : Fin 5) (k : Fin 6) (a : SqEdges) : ℝ :=
  match r.val, c.val, k.val with
  | 0, 0, 0 => -2 * (a 2) * (a 3) * (a 5) - 2 * (a 1) * (a 4) * (a 5) + 2 * (a 0) * (a 5) ^ 2
  | 0, 0, 1 => -2 * (a 2) * (a 3) * (a 4) + 2 * (a 1) * (a 4) ^ 2 - 2 * (a 0) * (a 4) * (a 5)
  | 0, 0, 2 => 2 * (a 2) * (a 3) ^ 2 - 2 * (a 1) * (a 3) * (a 4) - 2 * (a 0) * (a 3) * (a 5)
  | 0, 0, 3 => 2 * (a 2) ^ 2 * (a 3) - 2 * (a 1) * (a 2) * (a 4) - 2 * (a 0) * (a 2) * (a 5)
  | 0, 0, 4 => -2 * (a 1) * (a 2) * (a 3) + 2 * (a 1) ^ 2 * (a 4) - 2 * (a 0) * (a 1) * (a 5)
  | 0, 0, 5 => -2 * (a 0) * (a 2) * (a 3) - 2 * (a 0) * (a 1) * (a 4) + 2 * (a 0) ^ 2 * (a 5)
  | 0, 1, 0 => -(a 5) ^ 2 + (a 4) * (a 5) + (a 3) * (a 5)
  | 0, 1, 1 => (a 4) * (a 5) - (a 4) ^ 2 + (a 3) * (a 4)
  | 0, 1, 2 => (a 3) * (a 5) + (a 3) * (a 4) - (a 3) ^ 2
  | 0, 1, 3 => -2 * (a 4) * (a 5) + (a 2) * (a 5) + (a 2) * (a 4) - 2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 0) * (a 5)
  | 0, 1, 4 => -2 * (a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) - 2 * (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5)
  | 0, 1, 5 => -2 * (a 3) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 0) * (a 5) + (a 0) * (a 4) + (a 0) * (a 3)
  | 0, 2, 0 => -(a 5) ^ 2 + (a 2) * (a 5) + (a 1) * (a 5)
  | 0, 2, 1 => (a 4) * (a 5) - 2 * (a 2) * (a 5) + (a 2) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5)
  | 0, 2, 2 => (a 3) * (a 5) - 2 * (a 2) * (a 3) - 2 * (a 1) * (a 5) + (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5)
  | 0, 2, 3 => (a 2) * (a 5) - (a 2) ^ 2 + (a 1) * (a 2)
  | 0, 2, 4 => (a 1) * (a 5) + (a 1) * (a 2) - (a 1) ^ 2
  | 0, 2, 5 => (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 1) * (a 2) - 2 * (a 0) * (a 5) + (a 0) * (a 2) + (a 0) * (a 1)
  | 0, 3, 0 => (a 4) * (a 5) + (a 2) * (a 5) - 2 * (a 2) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 0) * (a 5)
  | 0, 3, 1 => -(a 4) ^ 2 + (a 2) * (a 4) + (a 0) * (a 4)
  | 0, 3, 2 => (a 3) * (a 4) - 2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 0) * (a 5) - 2 * (a 0) * (a 4) + (a 0) * (a 3)
  | 0, 3, 3 => (a 2) * (a 4) - (a 2) ^ 2 + (a 0) * (a 2)
  | 0, 3, 4 => (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) - 2 * (a 0) * (a 2) + (a 0) * (a 1)
  | 0, 3, 5 => (a 0) * (a 4) + (a 0) * (a 2) - (a 0) ^ 2
  | 0, 4, 0 => (a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) + (a 1) * (a 4) - 2 * (a 1) * (a 3) - 2 * (a 0) * (a 5)
  | 0, 4, 1 => (a 3) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5) + (a 0) * (a 4) - 2 * (a 0) * (a 3)
  | 0, 4, 2 => -(a 3) ^ 2 + (a 1) * (a 3) + (a 0) * (a 3)
  | 0, 4, 3 => -2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) + (a 0) * (a 2) - 2 * (a 0) * (a 1)
  | 0, 4, 4 => (a 1) * (a 3) - (a 1) ^ 2 + (a 0) * (a 1)
  | 0, 4, 5 => (a 0) * (a 3) + (a 0) * (a 1) - (a 0) ^ 2
  | 1, 0, 0 => -(a 5) ^ 2 + (a 4) * (a 5) + (a 3) * (a 5)
  | 1, 0, 1 => (a 4) * (a 5) - (a 4) ^ 2 + (a 3) * (a 4)
  | 1, 0, 2 => (a 3) * (a 5) + (a 3) * (a 4) - (a 3) ^ 2
  | 1, 0, 3 => -2 * (a 4) * (a 5) + (a 2) * (a 5) + (a 2) * (a 4) - 2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 0) * (a 5)
  | 1, 0, 4 => -2 * (a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) - 2 * (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5)
  | 1, 0, 5 => -2 * (a 3) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 0) * (a 5) + (a 0) * (a 4) + (a 0) * (a 3)
  | 1, 1, 3 => -2 * (a 5) - 2 * (a 4) + 2 * (a 3)
  | 1, 1, 4 => -2 * (a 5) + 2 * (a 4) - 2 * (a 3)
  | 1, 1, 5 => 2 * (a 5) - 2 * (a 4) - 2 * (a 3)
  | 1, 2, 0 => -2 * (a 5)
  | 1, 2, 1 => (a 5) + (a 4) - (a 3)
  | 1, 2, 2 => (a 5) - (a 4) + (a 3)
  | 1, 2, 3 => (a 5) + (a 2) - (a 1)
  | 1, 2, 4 => (a 5) - (a 2) + (a 1)
  | 1, 2, 5 => -2 * (a 5) + (a 4) + (a 3) + (a 2) + (a 1) - 2 * (a 0)
  | 1, 3, 0 => (a 5) + (a 4) - (a 3)
  | 1, 3, 1 => -2 * (a 4)
  | 1, 3, 2 => -(a 5) + (a 4) + (a 3)
  | 1, 3, 3 => (a 4) + (a 2) - (a 0)
  | 1, 3, 4 => (a 5) - 2 * (a 4) + (a 3) + (a 2) - 2 * (a 1) + (a 0)
  | 1, 3, 5 => (a 4) - (a 2) + (a 0)
  | 1, 4, 0 => (a 5) - (a 4) + (a 3)
  | 1, 4, 1 => -(a 5) + (a 4) + (a 3)
  | 1, 4, 2 => -2 * (a 3)
  | 1, 4, 3 => (a 5) + (a 4) - 2 * (a 3) - 2 * (a 2) + (a 1) + (a 0)
  | 1, 4, 4 => (a 3) + (a 1) - (a 0)
  | 1, 4, 5 => (a 3) - (a 1) + (a 0)
  | 2, 0, 0 => -(a 5) ^ 2 + (a 2) * (a 5) + (a 1) * (a 5)
  | 2, 0, 1 => (a 4) * (a 5) - 2 * (a 2) * (a 5) + (a 2) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5)
  | 2, 0, 2 => (a 3) * (a 5) - 2 * (a 2) * (a 3) - 2 * (a 1) * (a 5) + (a 1) * (a 4) + (a 1) * (a 3) + (a 0) * (a 5)
  | 2, 0, 3 => (a 2) * (a 5) - (a 2) ^ 2 + (a 1) * (a 2)
  | 2, 0, 4 => (a 1) * (a 5) + (a 1) * (a 2) - (a 1) ^ 2
  | 2, 0, 5 => (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 1) * (a 2) - 2 * (a 0) * (a 5) + (a 0) * (a 2) + (a 0) * (a 1)
  | 2, 1, 0 => -2 * (a 5)
  | 2, 1, 1 => (a 5) + (a 4) - (a 3)
  | 2, 1, 2 => (a 5) - (a 4) + (a 3)
  | 2, 1, 3 => (a 5) + (a 2) - (a 1)
  | 2, 1, 4 => (a 5) - (a 2) + (a 1)
  | 2, 1, 5 => -2 * (a 5) + (a 4) + (a 3) + (a 2) + (a 1) - 2 * (a 0)
  | 2, 2, 1 => -2 * (a 5) - 2 * (a 2) + 2 * (a 1)
  | 2, 2, 2 => -2 * (a 5) + 2 * (a 2) - 2 * (a 1)
  | 2, 2, 5 => 2 * (a 5) - 2 * (a 2) - 2 * (a 1)
  | 2, 3, 0 => (a 5) + (a 2) - (a 1)
  | 2, 3, 1 => (a 4) + (a 2) - (a 0)
  | 2, 3, 2 => (a 5) + (a 4) - 2 * (a 3) - 2 * (a 2) + (a 1) + (a 0)
  | 2, 3, 3 => -2 * (a 2)
  | 2, 3, 4 => -(a 5) + (a 2) + (a 1)
  | 2, 3, 5 => -(a 4) + (a 2) + (a 0)
  | 2, 4, 0 => (a 5) - (a 2) + (a 1)
  | 2, 4, 1 => (a 5) - 2 * (a 4) + (a 3) + (a 2) - 2 * (a 1) + (a 0)
  | 2, 4, 2 => (a 3) + (a 1) - (a 0)
  | 2, 4, 3 => -(a 5) + (a 2) + (a 1)
  | 2, 4, 4 => -2 * (a 1)
  | 2, 4, 5 => -(a 3) + (a 1) + (a 0)
  | 3, 0, 0 => (a 4) * (a 5) + (a 2) * (a 5) - 2 * (a 2) * (a 4) + (a 2) * (a 3) + (a 1) * (a 4) - 2 * (a 0) * (a 5)
  | 3, 0, 1 => -(a 4) ^ 2 + (a 2) * (a 4) + (a 0) * (a 4)
  | 3, 0, 2 => (a 3) * (a 4) - 2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 0) * (a 5) - 2 * (a 0) * (a 4) + (a 0) * (a 3)
  | 3, 0, 3 => (a 2) * (a 4) - (a 2) ^ 2 + (a 0) * (a 2)
  | 3, 0, 4 => (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) - 2 * (a 0) * (a 2) + (a 0) * (a 1)
  | 3, 0, 5 => (a 0) * (a 4) + (a 0) * (a 2) - (a 0) ^ 2
  | 3, 1, 0 => (a 5) + (a 4) - (a 3)
  | 3, 1, 1 => -2 * (a 4)
  | 3, 1, 2 => -(a 5) + (a 4) + (a 3)
  | 3, 1, 3 => (a 4) + (a 2) - (a 0)
  | 3, 1, 4 => (a 5) - 2 * (a 4) + (a 3) + (a 2) - 2 * (a 1) + (a 0)
  | 3, 1, 5 => (a 4) - (a 2) + (a 0)
  | 3, 2, 0 => (a 5) + (a 2) - (a 1)
  | 3, 2, 1 => (a 4) + (a 2) - (a 0)
  | 3, 2, 2 => (a 5) + (a 4) - 2 * (a 3) - 2 * (a 2) + (a 1) + (a 0)
  | 3, 2, 3 => -2 * (a 2)
  | 3, 2, 4 => -(a 5) + (a 2) + (a 1)
  | 3, 2, 5 => -(a 4) + (a 2) + (a 0)
  | 3, 3, 0 => -2 * (a 4) - 2 * (a 2) + 2 * (a 0)
  | 3, 3, 2 => -2 * (a 4) + 2 * (a 2) - 2 * (a 0)
  | 3, 3, 4 => 2 * (a 4) - 2 * (a 2) - 2 * (a 0)
  | 3, 4, 0 => -2 * (a 5) + (a 4) + (a 3) + (a 2) + (a 1) - 2 * (a 0)
  | 3, 4, 1 => (a 4) - (a 2) + (a 0)
  | 3, 4, 2 => (a 3) - (a 1) + (a 0)
  | 3, 4, 3 => -(a 4) + (a 2) + (a 0)
  | 3, 4, 4 => -(a 3) + (a 1) + (a 0)
  | 3, 4, 5 => -2 * (a 0)
  | 4, 0, 0 => (a 3) * (a 5) + (a 2) * (a 3) + (a 1) * (a 5) + (a 1) * (a 4) - 2 * (a 1) * (a 3) - 2 * (a 0) * (a 5)
  | 4, 0, 1 => (a 3) * (a 4) + (a 2) * (a 3) - 2 * (a 1) * (a 4) + (a 0) * (a 5) + (a 0) * (a 4) - 2 * (a 0) * (a 3)
  | 4, 0, 2 => -(a 3) ^ 2 + (a 1) * (a 3) + (a 0) * (a 3)
  | 4, 0, 3 => -2 * (a 2) * (a 3) + (a 1) * (a 4) + (a 1) * (a 2) + (a 0) * (a 5) + (a 0) * (a 2) - 2 * (a 0) * (a 1)
  | 4, 0, 4 => (a 1) * (a 3) - (a 1) ^ 2 + (a 0) * (a 1)
  | 4, 0, 5 => (a 0) * (a 3) + (a 0) * (a 1) - (a 0) ^ 2
  | 4, 1, 0 => (a 5) - (a 4) + (a 3)
  | 4, 1, 1 => -(a 5) + (a 4) + (a 3)
  | 4, 1, 2 => -2 * (a 3)
  | 4, 1, 3 => (a 5) + (a 4) - 2 * (a 3) - 2 * (a 2) + (a 1) + (a 0)
  | 4, 1, 4 => (a 3) + (a 1) - (a 0)
  | 4, 1, 5 => (a 3) - (a 1) + (a 0)
  | 4, 2, 0 => (a 5) - (a 2) + (a 1)
  | 4, 2, 1 => (a 5) - 2 * (a 4) + (a 3) + (a 2) - 2 * (a 1) + (a 0)
  | 4, 2, 2 => (a 3) + (a 1) - (a 0)
  | 4, 2, 3 => -(a 5) + (a 2) + (a 1)
  | 4, 2, 4 => -2 * (a 1)
  | 4, 2, 5 => -(a 3) + (a 1) + (a 0)
  | 4, 3, 0 => -2 * (a 5) + (a 4) + (a 3) + (a 2) + (a 1) - 2 * (a 0)
  | 4, 3, 1 => (a 4) - (a 2) + (a 0)
  | 4, 3, 2 => (a 3) - (a 1) + (a 0)
  | 4, 3, 3 => -(a 4) + (a 2) + (a 0)
  | 4, 3, 4 => -(a 3) + (a 1) + (a 0)
  | 4, 3, 5 => -2 * (a 0)
  | 4, 4, 0 => -2 * (a 3) - 2 * (a 1) + 2 * (a 0)
  | 4, 4, 1 => -2 * (a 3) + 2 * (a 1) - 2 * (a 0)
  | 4, 4, 3 => 2 * (a 3) - 2 * (a 1) - 2 * (a 0)
  | _, _, _ => 0

/-- Audit target: the explicit polynomial normal form should agree with the
determinant cofactor.  The formulas above are intentionally separated from
the determinant proof because normalizing all `Fin.succAbove` minor cases in
one theorem is too slow for interactive builds. -/
def CofactorPolynomialAgreement : Prop :=
  ∀ a : SqEdges, ∀ r c : Fin 5, cmCofactor3 a r c = cmCofactor3Poly r c a

set_option maxHeartbeats 2000000
/-- Normal form for the minor used by cofactor `(3,4)`, deleting row `3`
and column `4` from the Cayley-Menger matrix. -/
def cmMinor34Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 1;
     1, a 0, 0, a 3;
     1, a 2, a 4, a 5]

/-- The raw `Fin.succAbove` submatrix for cofactor `(3,4)` has the explicit
normal form `cmMinor34Matrix`. -/
theorem cmMinor34_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (3 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      cmMinor34Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Determinant of the explicit `(3,4)` minor normal form. -/
theorem det_cmMinor34Matrix (a : SqEdges) :
    Matrix.det (cmMinor34Matrix a) = - cmCofactor3Poly 3 4 a := by
  unfold cmMinor34Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

/-- Cofactor polynomial agreement for the numerator of edge `0`. -/
theorem cmCofactor3_34_eq_poly (a : SqEdges) :
    cmCofactor3 a 3 4 = cmCofactor3Poly 3 4 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor34_submatrix_eq]
  rw [det_cmMinor34Matrix]
  simp [cmCofactorSign3, show ¬ Even (7 : Nat) by decide]

/-- Normal form for the minor used by cofactor `(2,4)`. -/
def cmMinor24Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 1;
     1, a 1, a 3, 0;
     1, a 2, a 4, a 5]

theorem cmMinor24_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (2 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      cmMinor24Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor24Matrix (a : SqEdges) :
    Matrix.det (cmMinor24Matrix a) = cmCofactor3Poly 2 4 a := by
  unfold cmMinor24Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_24_eq_poly (a : SqEdges) :
    cmCofactor3 a 2 4 = cmCofactor3Poly 2 4 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor24_submatrix_eq, det_cmMinor24Matrix]
  simp [cmCofactorSign3, show Even (6 : Nat) by decide]

/-- Normal form for the minor used by cofactor `(2,3)`. -/
def cmMinor23Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 2;
     1, a 1, a 3, a 5;
     1, a 2, a 4, 0]

theorem cmMinor23_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (2 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      cmMinor23Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor23Matrix (a : SqEdges) :
    Matrix.det (cmMinor23Matrix a) = - cmCofactor3Poly 2 3 a := by
  unfold cmMinor23Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_23_eq_poly (a : SqEdges) :
    cmCofactor3 a 2 3 = cmCofactor3Poly 2 3 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor23_submatrix_eq, det_cmMinor23Matrix]
  simp [cmCofactorSign3, show ¬ Even (5 : Nat) by decide]

/-- Normal form for the minor used by cofactor `(1,4)`. -/
def cmMinor14Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, 0, a 3;
     1, a 1, a 3, 0;
     1, a 2, a 4, a 5]

theorem cmMinor14_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (1 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      cmMinor14Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor14Matrix (a : SqEdges) :
    Matrix.det (cmMinor14Matrix a) = - cmCofactor3Poly 1 4 a := by
  unfold cmMinor14Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_14_eq_poly (a : SqEdges) :
    cmCofactor3 a 1 4 = cmCofactor3Poly 1 4 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor14_submatrix_eq, det_cmMinor14Matrix]
  simp [cmCofactorSign3, show ¬ Even (5 : Nat) by decide]

/-- Normal form for the minor used by cofactor `(1,3)`. -/
def cmMinor13Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, 0, a 4;
     1, a 1, a 3, a 5;
     1, a 2, a 4, 0]

theorem cmMinor13_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (1 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      cmMinor13Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor13Matrix (a : SqEdges) :
    Matrix.det (cmMinor13Matrix a) = cmCofactor3Poly 1 3 a := by
  unfold cmMinor13Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_13_eq_poly (a : SqEdges) :
    cmCofactor3 a 1 3 = cmCofactor3Poly 1 3 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor13_submatrix_eq, det_cmMinor13Matrix]
  simp [cmCofactorSign3, show Even (4 : Nat) by decide]

/-- Normal form for the minor used by cofactor `(1,2)`. -/
def cmMinor12Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, a 3, a 4;
     1, a 1, 0, a 5;
     1, a 2, a 5, 0]

theorem cmMinor12_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (1 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      cmMinor12Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor12Matrix (a : SqEdges) :
    Matrix.det (cmMinor12Matrix a) = - cmCofactor3Poly 1 2 a := by
  unfold cmMinor12Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_12_eq_poly (a : SqEdges) :
    cmCofactor3 a 1 2 = cmCofactor3Poly 1 2 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor12_submatrix_eq, det_cmMinor12Matrix]
  simp [cmCofactorSign3, show ¬ Even (3 : Nat) by decide]

/-- Normal form for the diagonal minor used by cofactor `(1,1)`. -/
def cmMinor11Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 3, a 4;
     1, a 3, 0, a 5;
     1, a 4, a 5, 0]

theorem cmMinor11_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (1 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      cmMinor11Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor11Matrix (a : SqEdges) :
    Matrix.det (cmMinor11Matrix a) = cmCofactor3Poly 1 1 a := by
  unfold cmMinor11Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_11_eq_poly (a : SqEdges) :
    cmCofactor3 a 1 1 = cmCofactor3Poly 1 1 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor11_submatrix_eq, det_cmMinor11Matrix]
  simp [cmCofactorSign3, show Even (2 : Nat) by decide]

/-- Normal form for the diagonal minor used by cofactor `(2,2)`. -/
def cmMinor22Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 1, a 2;
     1, a 1, 0, a 5;
     1, a 2, a 5, 0]

theorem cmMinor22_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (2 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      cmMinor22Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor22Matrix (a : SqEdges) :
    Matrix.det (cmMinor22Matrix a) = cmCofactor3Poly 2 2 a := by
  unfold cmMinor22Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_22_eq_poly (a : SqEdges) :
    cmCofactor3 a 2 2 = cmCofactor3Poly 2 2 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor22_submatrix_eq, det_cmMinor22Matrix]
  simp [cmCofactorSign3, show Even (4 : Nat) by decide]

/-- Normal form for the diagonal minor used by cofactor `(3,3)`. -/
def cmMinor33Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 2;
     1, a 0, 0, a 4;
     1, a 2, a 4, 0]

theorem cmMinor33_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (3 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      cmMinor33Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor33Matrix (a : SqEdges) :
    Matrix.det (cmMinor33Matrix a) = cmCofactor3Poly 3 3 a := by
  unfold cmMinor33Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_33_eq_poly (a : SqEdges) :
    cmCofactor3 a 3 3 = cmCofactor3Poly 3 3 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor33_submatrix_eq, det_cmMinor33Matrix]
  simp [cmCofactorSign3, show Even (6 : Nat) by decide]

/-- Normal form for the diagonal minor used by cofactor `(4,4)`. -/
def cmMinor44Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 1;
     1, a 0, 0, a 3;
     1, a 1, a 3, 0]

theorem cmMinor44_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      cmMinor44Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor44Matrix (a : SqEdges) :
    Matrix.det (cmMinor44Matrix a) = cmCofactor3Poly 4 4 a := by
  unfold cmMinor44Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_44_eq_poly (a : SqEdges) :
    cmCofactor3 a 4 4 = cmCofactor3Poly 4 4 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor44_submatrix_eq, det_cmMinor44Matrix]
  simp [cmCofactorSign3, show Even (8 : Nat) by decide]

/-- Polynomial agreement for every numerator cofactor used by tetrahedral
dihedral cosines. -/
theorem cmCofactor3_opposite_eq_poly (a : SqEdges) (e : Fin 6) :
    let p := DihedralCayleyMenger.oppositeCMVertices e
    cmCofactor3 a p.1 p.2 = cmCofactor3Poly p.1 p.2 a := by
  fin_cases e
  · exact cmCofactor3_34_eq_poly a
  · exact cmCofactor3_24_eq_poly a
  · exact cmCofactor3_23_eq_poly a
  · exact cmCofactor3_14_eq_poly a
  · exact cmCofactor3_13_eq_poly a
  · exact cmCofactor3_12_eq_poly a

/-- Polynomial agreement for every diagonal cofactor used by tetrahedral
dihedral cosine denominators. -/
theorem cmCofactor3_opposite_diag_eq_poly
    (a : SqEdges) (e : Fin 6) (side : Bool) :
    let p := DihedralCayleyMenger.oppositeCMVertices e
    let r := if side then p.1 else p.2
    cmCofactor3 a r r = cmCofactor3Poly r r a := by
  fin_cases e <;> cases side
  · exact cmCofactor3_44_eq_poly a
  · exact cmCofactor3_33_eq_poly a
  · exact cmCofactor3_44_eq_poly a
  · exact cmCofactor3_22_eq_poly a
  · exact cmCofactor3_33_eq_poly a
  · exact cmCofactor3_22_eq_poly a
  · exact cmCofactor3_44_eq_poly a
  · exact cmCofactor3_11_eq_poly a
  · exact cmCofactor3_33_eq_poly a
  · exact cmCofactor3_11_eq_poly a
  · exact cmCofactor3_22_eq_poly a
  · exact cmCofactor3_11_eq_poly a

def cmMinor00Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, a 0, a 1, a 2;
     a 0, 0, a 3, a 4;
     a 1, a 3, 0, a 5;
     a 2, a 4, a 5, 0]

theorem cmMinor00_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      cmMinor00Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor00Matrix (a : SqEdges) :
    Matrix.det (cmMinor00Matrix a) = cmCofactor3Poly 0 0 a := by
  unfold cmMinor00Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_00_eq_poly (a : SqEdges) :
    cmCofactor3 a 0 0 = cmCofactor3Poly 0 0 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor00_submatrix_eq, det_cmMinor00Matrix]
  simp [cmCofactorSign3, show Even (0 : Nat) by decide]

def cmMinor01Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, a 0, a 1, a 2;
     1, 0, a 3, a 4;
     1, a 3, 0, a 5;
     1, a 4, a 5, 0]

theorem cmMinor01_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      cmMinor01Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor01Matrix (a : SqEdges) :
    Matrix.det (cmMinor01Matrix a) = - cmCofactor3Poly 0 1 a := by
  unfold cmMinor01Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_01_eq_poly (a : SqEdges) :
    cmCofactor3 a 0 1 = cmCofactor3Poly 0 1 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor01_submatrix_eq, det_cmMinor01Matrix]
  simp [cmCofactorSign3, show ¬ Even (1 : Nat) by decide]

def cmMinor02Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, a 1, a 2;
     1, a 0, a 3, a 4;
     1, a 1, 0, a 5;
     1, a 2, a 5, 0]

theorem cmMinor02_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      cmMinor02Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor02Matrix (a : SqEdges) :
    Matrix.det (cmMinor02Matrix a) = cmCofactor3Poly 0 2 a := by
  unfold cmMinor02Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_02_eq_poly (a : SqEdges) :
    cmCofactor3 a 0 2 = cmCofactor3Poly 0 2 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor02_submatrix_eq, det_cmMinor02Matrix]
  simp [cmCofactorSign3, show Even (2 : Nat) by decide]

def cmMinor03Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, a 0, a 2;
     1, a 0, 0, a 4;
     1, a 1, a 3, a 5;
     1, a 2, a 4, 0]

theorem cmMinor03_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      cmMinor03Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor03Matrix (a : SqEdges) :
    Matrix.det (cmMinor03Matrix a) = - cmCofactor3Poly 0 3 a := by
  unfold cmMinor03Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_03_eq_poly (a : SqEdges) :
    cmCofactor3 a 0 3 = cmCofactor3Poly 0 3 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor03_submatrix_eq, det_cmMinor03Matrix]
  simp [cmCofactorSign3, show ¬ Even (3 : Nat) by decide]

def cmMinor04Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, a 0, a 1;
     1, a 0, 0, a 3;
     1, a 1, a 3, 0;
     1, a 2, a 4, a 5]

theorem cmMinor04_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (0 : Fin 5)) (Fin.succAbove (4 : Fin 5)) =
      cmMinor04Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor04Matrix (a : SqEdges) :
    Matrix.det (cmMinor04Matrix a) = cmCofactor3Poly 0 4 a := by
  unfold cmMinor04Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_04_eq_poly (a : SqEdges) :
    cmCofactor3 a 0 4 = cmCofactor3Poly 0 4 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor04_submatrix_eq, det_cmMinor04Matrix]
  simp [cmCofactorSign3, show Even (4 : Nat) by decide]

def cmMinor10Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1;
     a 0, 0, a 3, a 4;
     a 1, a 3, 0, a 5;
     a 2, a 4, a 5, 0]

theorem cmMinor10_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (1 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      cmMinor10Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor10Matrix (a : SqEdges) :
    Matrix.det (cmMinor10Matrix a) = - cmCofactor3Poly 1 0 a := by
  unfold cmMinor10Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_10_eq_poly (a : SqEdges) :
    cmCofactor3 a 1 0 = cmCofactor3Poly 1 0 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor10_submatrix_eq, det_cmMinor10Matrix]
  simp [cmCofactorSign3, show ¬ Even (1 : Nat) by decide]

def cmMinor20Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1;
     0, a 0, a 1, a 2;
     a 1, a 3, 0, a 5;
     a 2, a 4, a 5, 0]

theorem cmMinor20_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (2 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      cmMinor20Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor20Matrix (a : SqEdges) :
    Matrix.det (cmMinor20Matrix a) = cmCofactor3Poly 2 0 a := by
  unfold cmMinor20Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_20_eq_poly (a : SqEdges) :
    cmCofactor3 a 2 0 = cmCofactor3Poly 2 0 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor20_submatrix_eq, det_cmMinor20Matrix]
  simp [cmCofactorSign3, show Even (2 : Nat) by decide]

def cmMinor21Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, a 1, a 2;
     1, a 3, 0, a 5;
     1, a 4, a 5, 0]

theorem cmMinor21_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (2 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      cmMinor21Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor21Matrix (a : SqEdges) :
    Matrix.det (cmMinor21Matrix a) = - cmCofactor3Poly 2 1 a := by
  unfold cmMinor21Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_21_eq_poly (a : SqEdges) :
    cmCofactor3 a 2 1 = cmCofactor3Poly 2 1 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor21_submatrix_eq, det_cmMinor21Matrix]
  simp [cmCofactorSign3, show ¬ Even (3 : Nat) by decide]

def cmMinor30Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1;
     0, a 0, a 1, a 2;
     a 0, 0, a 3, a 4;
     a 2, a 4, a 5, 0]

theorem cmMinor30_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (3 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      cmMinor30Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor30Matrix (a : SqEdges) :
    Matrix.det (cmMinor30Matrix a) = - cmCofactor3Poly 3 0 a := by
  unfold cmMinor30Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_30_eq_poly (a : SqEdges) :
    cmCofactor3 a 3 0 = cmCofactor3Poly 3 0 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor30_submatrix_eq, det_cmMinor30Matrix]
  simp [cmCofactorSign3, show ¬ Even (3 : Nat) by decide]

def cmMinor31Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, a 1, a 2;
     1, 0, a 3, a 4;
     1, a 4, a 5, 0]

theorem cmMinor31_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (3 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      cmMinor31Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor31Matrix (a : SqEdges) :
    Matrix.det (cmMinor31Matrix a) = cmCofactor3Poly 3 1 a := by
  unfold cmMinor31Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_31_eq_poly (a : SqEdges) :
    cmCofactor3 a 3 1 = cmCofactor3Poly 3 1 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor31_submatrix_eq, det_cmMinor31Matrix]
  simp [cmCofactorSign3, show Even (4 : Nat) by decide]

def cmMinor32Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 1, a 2;
     1, a 0, a 3, a 4;
     1, a 2, a 5, 0]

theorem cmMinor32_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (3 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      cmMinor32Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor32Matrix (a : SqEdges) :
    Matrix.det (cmMinor32Matrix a) = - cmCofactor3Poly 3 2 a := by
  unfold cmMinor32Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_32_eq_poly (a : SqEdges) :
    cmCofactor3 a 3 2 = cmCofactor3Poly 3 2 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor32_submatrix_eq, det_cmMinor32Matrix]
  simp [cmCofactorSign3, show ¬ Even (5 : Nat) by decide]

def cmMinor40Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 1, 1, 1;
     0, a 0, a 1, a 2;
     a 0, 0, a 3, a 4;
     a 1, a 3, 0, a 5]

theorem cmMinor40_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (0 : Fin 5)) =
      cmMinor40Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor40Matrix (a : SqEdges) :
    Matrix.det (cmMinor40Matrix a) = cmCofactor3Poly 4 0 a := by
  unfold cmMinor40Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_40_eq_poly (a : SqEdges) :
    cmCofactor3 a 4 0 = cmCofactor3Poly 4 0 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor40_submatrix_eq, det_cmMinor40Matrix]
  simp [cmCofactorSign3, show Even (4 : Nat) by decide]

def cmMinor41Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, a 0, a 1, a 2;
     1, 0, a 3, a 4;
     1, a 3, 0, a 5]

theorem cmMinor41_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (1 : Fin 5)) =
      cmMinor41Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor41Matrix (a : SqEdges) :
    Matrix.det (cmMinor41Matrix a) = - cmCofactor3Poly 4 1 a := by
  unfold cmMinor41Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_41_eq_poly (a : SqEdges) :
    cmCofactor3 a 4 1 = cmCofactor3Poly 4 1 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor41_submatrix_eq, det_cmMinor41Matrix]
  simp [cmCofactorSign3, show ¬ Even (5 : Nat) by decide]

def cmMinor42Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 1, a 2;
     1, a 0, a 3, a 4;
     1, a 1, 0, a 5]

theorem cmMinor42_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (2 : Fin 5)) =
      cmMinor42Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor42Matrix (a : SqEdges) :
    Matrix.det (cmMinor42Matrix a) = cmCofactor3Poly 4 2 a := by
  unfold cmMinor42Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_42_eq_poly (a : SqEdges) :
    cmCofactor3 a 4 2 = cmCofactor3Poly 4 2 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor42_submatrix_eq, det_cmMinor42Matrix]
  simp [cmCofactorSign3, show Even (6 : Nat) by decide]

def cmMinor43Matrix (a : SqEdges) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, a 0, a 2;
     1, a 0, 0, a 4;
     1, a 1, a 3, a 5]

theorem cmMinor43_submatrix_eq (a : SqEdges) :
    Matrix.submatrix (cmMatrix3 a) (Fin.succAbove (4 : Fin 5)) (Fin.succAbove (3 : Fin 5)) =
      cmMinor43Matrix a := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_cmMinor43Matrix (a : SqEdges) :
    Matrix.det (cmMinor43Matrix a) = - cmCofactor3Poly 4 3 a := by
  unfold cmMinor43Matrix cmCofactor3Poly
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem cmCofactor3_43_eq_poly (a : SqEdges) :
    cmCofactor3 a 4 3 = cmCofactor3Poly 4 3 a := by
  unfold cmCofactor3 cmMinor3
  rw [cmMinor43_submatrix_eq, det_cmMinor43Matrix]
  simp [cmCofactorSign3, show ¬ Even (7 : Nat) by decide]

/-- The explicit polynomial normal form agrees with every determinant
cofactor of the tetrahedral Cayley-Menger matrix. -/
theorem cmCofactor3_eq_poly (a : SqEdges) (r c : Fin 5) :
    cmCofactor3 a r c = cmCofactor3Poly r c a := by
  fin_cases r <;> fin_cases c
  · exact cmCofactor3_00_eq_poly a
  · exact cmCofactor3_01_eq_poly a
  · exact cmCofactor3_02_eq_poly a
  · exact cmCofactor3_03_eq_poly a
  · exact cmCofactor3_04_eq_poly a
  · exact cmCofactor3_10_eq_poly a
  · exact cmCofactor3_11_eq_poly a
  · exact cmCofactor3_12_eq_poly a
  · exact cmCofactor3_13_eq_poly a
  · exact cmCofactor3_14_eq_poly a
  · exact cmCofactor3_20_eq_poly a
  · exact cmCofactor3_21_eq_poly a
  · exact cmCofactor3_22_eq_poly a
  · exact cmCofactor3_23_eq_poly a
  · exact cmCofactor3_24_eq_poly a
  · exact cmCofactor3_30_eq_poly a
  · exact cmCofactor3_31_eq_poly a
  · exact cmCofactor3_32_eq_poly a
  · exact cmCofactor3_33_eq_poly a
  · exact cmCofactor3_34_eq_poly a
  · exact cmCofactor3_40_eq_poly a
  · exact cmCofactor3_41_eq_poly a
  · exact cmCofactor3_42_eq_poly a
  · exact cmCofactor3_43_eq_poly a
  · exact cmCofactor3_44_eq_poly a

/-- Quadratic coefficient of a one-coordinate restriction of a cofactor
polynomial.  Cofactors are degree at most two in each individual squared-edge
coordinate. -/
def cmCofactorQuadraticCoeff (r c : Fin 5) (k : Fin 6) (a : SqEdges) : ℝ :=
  match r.val, c.val, k.val with
  | 0, 0, 0 => (a 5) ^ 2
  | 0, 0, 1 => (a 4) ^ 2
  | 0, 0, 2 => (a 3) ^ 2
  | 0, 0, 3 => (a 2) ^ 2
  | 0, 0, 4 => (a 1) ^ 2
  | 0, 0, 5 => (a 0) ^ 2
  | 0, 1, 3 => -(a 2)
  | 0, 1, 4 => -(a 1)
  | 0, 1, 5 => -(a 0)
  | 0, 2, 1 => -(a 4)
  | 0, 2, 2 => -(a 3)
  | 0, 2, 5 => -(a 0)
  | 0, 3, 0 => -(a 5)
  | 0, 3, 2 => -(a 3)
  | 0, 3, 4 => -(a 1)
  | 0, 4, 0 => -(a 5)
  | 0, 4, 1 => -(a 4)
  | 0, 4, 3 => -(a 2)
  | 1, 0, 3 => -(a 2)
  | 1, 0, 4 => -(a 1)
  | 1, 0, 5 => -(a 0)
  | 1, 1, 3 => 1
  | 1, 1, 4 => 1
  | 1, 1, 5 => 1
  | 1, 2, 5 => -1
  | 1, 3, 4 => -1
  | 1, 4, 3 => -1
  | 2, 0, 1 => -(a 4)
  | 2, 0, 2 => -(a 3)
  | 2, 0, 5 => -(a 0)
  | 2, 1, 5 => -1
  | 2, 2, 1 => 1
  | 2, 2, 2 => 1
  | 2, 2, 5 => 1
  | 2, 3, 2 => -1
  | 2, 4, 1 => -1
  | 3, 0, 0 => -(a 5)
  | 3, 0, 2 => -(a 3)
  | 3, 0, 4 => -(a 1)
  | 3, 1, 4 => -1
  | 3, 2, 2 => -1
  | 3, 3, 0 => 1
  | 3, 3, 2 => 1
  | 3, 3, 4 => 1
  | 3, 4, 0 => -1
  | 4, 0, 0 => -(a 5)
  | 4, 0, 1 => -(a 4)
  | 4, 0, 3 => -(a 2)
  | 4, 1, 3 => -1
  | 4, 2, 1 => -1
  | 4, 3, 0 => -1
  | 4, 4, 0 => 1
  | 4, 4, 1 => 1
  | 4, 4, 3 => 1
  | _, _, _ => 0


/-- Derivative of a shifted cubic polynomial at its base point.  Local copy
of the `cm3` helper, used here for cofactor coordinate restrictions. -/
private theorem hasDerivAt_shifted_cubic (A B C D x₀ : ℝ) :
    HasDerivAt (fun x : ℝ => A + B * (x - x₀) + C * (x - x₀) ^ 2
      + D * (x - x₀) ^ 3) B x₀ := by
  have hx : HasDerivAt (fun x : ℝ => x - x₀) (1 : ℝ) x₀ := by
    simpa using (hasDerivAt_id x₀).sub_const x₀
  have hconst : HasDerivAt (fun _ : ℝ => A) (0 : ℝ) x₀ := hasDerivAt_const x₀ A
  have hlin : HasDerivAt (fun x : ℝ => B * (x - x₀)) B x₀ := by
    simpa using hx.const_mul B
  have hsq_raw := hx.pow 2
  have hsq : HasDerivAt (fun x : ℝ => (x - x₀) ^ 2) (0 : ℝ) x₀ := by
    simpa using hsq_raw
  have hquad : HasDerivAt (fun x : ℝ => C * (x - x₀) ^ 2) (0 : ℝ) x₀ := by
    simpa using hsq.const_mul C
  have hcb_raw := hx.pow 3
  have hcb : HasDerivAt (fun x : ℝ => (x - x₀) ^ 3) (0 : ℝ) x₀ := by
    simpa using hcb_raw
  have hcubic : HasDerivAt (fun x : ℝ => D * (x - x₀) ^ 3) (0 : ℝ) x₀ := by
    simpa using hcb.const_mul D
  have htotal := ((hconst.add hlin).add hquad).add hcubic
  simpa using htotal

/-- Taylor form for the `(3,4)` cofactor polynomial along one squared-edge
coordinate. -/
theorem cmCofactor3Poly_34_update_polyform
    (a : SqEdges) (k : Fin 6) (t : ℝ) :
    cmCofactor3Poly 3 4 (Function.update a k (a k + t)) =
      cmCofactor3Poly 3 4 a + cmCofactorPartial 3 4 k a * t
        + (if k = 0 then -1 else 0) * t ^ 2 + 0 * t ^ 3 := by
  fin_cases k <;>
    simp [cmCofactor3Poly, cmCofactorPartial, Function.update] <;>
    ring_nf

/-- Closed-form coordinate derivative of the `(3,4)` cofactor polynomial. -/
theorem hasDerivAt_cmCofactor3Poly_34_along_coord
    (k : Fin 6) (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cmCofactor3Poly 3 4 (Function.update a k t))
      (cmCofactorPartial 3 4 k a) (a k) := by
  have hfun :
      (fun t : ℝ => cmCofactor3Poly 3 4 (Function.update a k t)) =
        (fun t : ℝ => cmCofactor3Poly 3 4 a
          + cmCofactorPartial 3 4 k a * (t - a k)
          + (if k = 0 then -1 else 0) * (t - a k) ^ 2
          + 0 * (t - a k) ^ 3) := by
    funext t
    have h := cmCofactor3Poly_34_update_polyform a k (t - a k)
    have hbase : a k + (t - a k) = t := by ring
    rw [hbase] at h
    simpa using h
  rw [hfun]
  exact hasDerivAt_shifted_cubic (cmCofactor3Poly 3 4 a)
    (cmCofactorPartial 3 4 k a) (if k = 0 then -1 else 0) 0 (a k)

/-- Closed-form coordinate derivative of determinant cofactor `(3,4)`. -/
theorem hasDerivAt_cmCofactor3_34_along_coord
    (k : Fin 6) (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cmCofactor3 (Function.update a k t) 3 4)
      (cmCofactorPartial 3 4 k a) (a k) := by
  simpa [cmCofactor3_34_eq_poly] using
    hasDerivAt_cmCofactor3Poly_34_along_coord k a

/-- Taylor form for every cofactor polynomial along one squared-edge
coordinate. -/
theorem cmCofactor3Poly_update_polyform
    (r c : Fin 5) (a : SqEdges) (k : Fin 6) (t : ℝ) :
    cmCofactor3Poly r c (Function.update a k (a k + t)) =
      cmCofactor3Poly r c a + cmCofactorPartial r c k a * t
        + cmCofactorQuadraticCoeff r c k a * t ^ 2 + 0 * t ^ 3 := by
  fin_cases r <;> fin_cases c <;> fin_cases k <;>
    simp [cmCofactor3Poly, cmCofactorPartial, cmCofactorQuadraticCoeff,
      Function.update] <;>
    ring_nf

/-- Closed-form coordinate derivative of every cofactor polynomial. -/
theorem hasDerivAt_cmCofactor3Poly_along_coord
    (r c : Fin 5) (k : Fin 6) (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cmCofactor3Poly r c (Function.update a k t))
      (cmCofactorPartial r c k a) (a k) := by
  have hfun :
      (fun t : ℝ => cmCofactor3Poly r c (Function.update a k t)) =
        (fun t : ℝ => cmCofactor3Poly r c a
          + cmCofactorPartial r c k a * (t - a k)
          + cmCofactorQuadraticCoeff r c k a * (t - a k) ^ 2
          + 0 * (t - a k) ^ 3) := by
    funext t
    have h := cmCofactor3Poly_update_polyform r c a k (t - a k)
    have hbase : a k + (t - a k) = t := by ring
    rw [hbase] at h
    simpa using h
  rw [hfun]
  exact hasDerivAt_shifted_cubic (cmCofactor3Poly r c a)
    (cmCofactorPartial r c k a) (cmCofactorQuadraticCoeff r c k a) 0 (a k)

/-- Closed-form coordinate derivative of every determinant-defined cofactor. -/
theorem hasDerivAt_cmCofactor3_along_coord
    (r c : Fin 5) (k : Fin 6) (a : SqEdges) :
    HasDerivAt (fun t : ℝ => cmCofactor3 (Function.update a k t) r c)
      (cmCofactorPartial r c k a) (a k) := by
  simpa [cmCofactor3_eq_poly] using
    hasDerivAt_cmCofactor3Poly_along_coord r c k a

/-- Polynomial Cayley-Menger cofactor discriminant for a tetrahedral edge:
`C_pp C_qq - C_pq^2 = 2 * CM * a_e`.  This is the algebraic identity that
turns the arccos denominator into the common volume factor in Schläfli. -/
theorem cmCofactor_discriminant_eq (a : SqEdges) (e : Fin 6) :
    let p := DihedralCayleyMenger.oppositeCMVertices e |>.1
    let q := DihedralCayleyMenger.oppositeCMVertices e |>.2
    cmCofactor3Poly p p a * cmCofactor3Poly q q a -
        cmCofactor3Poly p q a ^ 2 =
      2 * cm3 a * a e := by
  fin_cases e <;>
    simp [DihedralCayleyMenger.oppositeCMVertices, cmCofactor3Poly, cm3] <;>
    ring_nf

/-- The derivative theorem is intentionally separated from the polynomial
normal form.  Downstream modules use `cmCofactorPartial`; the remaining
one-variable `HasDerivAt` proof is discharged in the quotient-derivative
layer where the required cofactors are already specialized. -/
def cmCofactorPartialClosedForm (r c : Fin 5) (k : Fin 6) (a : SqEdges) : ℝ :=
  cmCofactorPartial r c k a

end

end CofactorPolynomial
end Geometry
end IndisputableMonolith
