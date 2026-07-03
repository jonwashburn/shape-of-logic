import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit

namespace IndisputableMonolith.PRCGrow.SignedOrbitMulBalancedZeroOfBalancedZeroRightChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus

theorem mul_balanced_zero_of_balanced_zero_right_cf
    (z w : SignedOrbit)
    (hw : w.balanced SignedOrbit.zero) :
    (z.mul w).balanced SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at hw ⊢
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, SignedOrbit.zero,
    DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_zero,
    Nat.add_zero, Nat.zero_add] at hw ⊢
  rw [hw]

end IndisputableMonolith.PRCGrow.SignedOrbitMulBalancedZeroOfBalancedZeroRightChoiceFree
