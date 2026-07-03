import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitArithmetic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitZeroLeIffNonnegFlagChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem zero_le_iff_nonnegFlag_cf (z : SignedOrbit) :
    SignedOrbit.le SignedOrbit.zero z ↔ z.nonnegFlag = true := by
  rw [le_iff_nonnegFlag_sub_cf]
  unfold SignedOrbit.nonnegFlag
  rw [leq_eq_true_iff_cf, leq_eq_true_iff_cf]
  have hp : (SignedOrbit.sub z SignedOrbit.zero).pos = z.pos + DistinctionNat.zero := rfl
  have hn : (SignedOrbit.sub z SignedOrbit.zero).neg = z.neg + DistinctionNat.zero := rfl
  rw [hp, hn, DistinctionNat.toNat_add, DistinctionNat.toNat_add,
      DistinctionNat.toNat_zero, Nat.add_zero, Nat.add_zero]

end IndisputableMonolith.PRCGrow.SignedOrbitZeroLeIffNonnegFlagChoiceFree
