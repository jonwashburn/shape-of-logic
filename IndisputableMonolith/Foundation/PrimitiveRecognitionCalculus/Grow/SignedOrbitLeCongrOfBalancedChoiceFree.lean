import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitLeCongrRightOfBalancedChoiceFree
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitLeCongrOfBalancedChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree
open IndisputableMonolith.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

theorem le_congr_of_balanced_cf {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b' :=
  (le_congr_left_of_balanced_cf ha).trans (le_congr_right_of_balanced_cf hb)

end IndisputableMonolith.PRCGrow.SignedOrbitLeCongrOfBalancedChoiceFree
