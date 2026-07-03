import Mathlib

namespace IndisputableMonolith
namespace Masses

structure GaugeSkeleton where
  Y            : ℚ
  colorRep     : Bool
  isWeakDoublet : Bool

structure Completion where
  nY : ℤ
  n3 : ℤ
  n2 : ℤ

structure WordLength where
  len : GaugeSkeleton → Completion → Nat

inductive GenClass | g1 | g2 | g3
deriving DecidableEq, Repr

@[simp] def tauOf : GenClass → ℤ
| .g1 => 0
| .g2 => 11
| .g3 => 17

structure RungSpec where
  ell : Nat
  gen : GenClass

@[simp] def rungOf (R : RungSpec) : ℤ := (R.ell : ℤ) + tauOf R.gen

end Masses
end IndisputableMonolith
