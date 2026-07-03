import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitLeCongrRightOfBalancedChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitLeOfProductRightFactorIffOfBalancedChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree

theorem mul_balanced_congr_right_cf {a b b' : SignedOrbit} (hb : SignedOrbit.balanced b b') : SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a b') := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at hb ⊢
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, DistinctionNat.toNat_add, DistinctionNat.toNat_mul]
  have hb2 : b.neg.toNat + b'.pos.toNat = b'.neg.toNat + b.pos.toNat := by omega
  have e1 : a.pos.toNat * b.pos.toNat + a.pos.toNat * b'.neg.toNat = a.pos.toNat * b'.pos.toNat + a.pos.toNat * b.neg.toNat := by rw [← Nat.mul_add, ← Nat.mul_add, hb]
  have e2 : a.neg.toNat * b.neg.toNat + a.neg.toNat * b'.pos.toNat = a.neg.toNat * b'.neg.toNat + a.neg.toNat * b.pos.toNat := by rw [← Nat.mul_add, ← Nat.mul_add, hb2]
  omega

theorem le_of_product_right_factor_iff_of_balanced_cf {c a b b' : SignedOrbit} (hb : SignedOrbit.balanced b b') : SignedOrbit.le c (SignedOrbit.mul a b) ↔ SignedOrbit.le c (SignedOrbit.mul a b') :=
  le_congr_right_of_balanced_cf (mul_balanced_congr_right_cf hb)

end IndisputableMonolith.PRCGrow.SignedOrbitLeOfProductRightFactorIffOfBalancedChoiceFree
