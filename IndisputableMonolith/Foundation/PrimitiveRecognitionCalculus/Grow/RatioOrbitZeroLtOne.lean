import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLtTrichotomy
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.RatioOrbitZeroLtOne

open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal
open IndisputableMonolith.PRCGrow.RatioOrbitLtTrichotomy
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree
open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus

theorem zero_ltQ_one : ltQ RatioOrbit.zero RatioOrbit.one := by
  unfold ltQ
  refine ⟨?_, ?_⟩
  · unfold leQ
    rw [le_iff_toNat_cf]
    decide
  · intro h
    have hf : ¬ RatioOrbit.crossEq RatioOrbit.zero RatioOrbit.one := by decide
    exact hf h

end IndisputableMonolith.PRCGrow.RatioOrbitZeroLtOne
