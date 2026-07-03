import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem le_congr_right_of_balanced_cf {a b b' : SignedOrbit}
    (h : b.balanced b') :
    a.le b ↔ a.le b' := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  constructor
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega

end IndisputableMonolith.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree
