import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem le_congr_left_of_balanced_cf {a a' b : SignedOrbit}
    (h : SignedOrbit.balanced a a') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  constructor
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega

end IndisputableMonolith.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree
