import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal

namespace IndisputableMonolith.PRCGrow.RatioOrbitLeNeg

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_neg_neg_iff (p q : RatioOrbit) :
    leQ (RatioOrbit.negate q) (RatioOrbit.negate p) ↔ leQ p q := by
  unfold leQ
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  simp only [RatioOrbit.negate, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    SignedOrbit.negate_toInt]
  constructor
  · intro h
    have e1 : -(q.num.toInt) * ↑(p.den.toNat) = -(q.num.toInt * ↑(p.den.toNat)) := by ring
    have e2 : -(p.num.toInt) * ↑(q.den.toNat) = -(p.num.toInt * ↑(q.den.toNat)) := by ring
    rw [e1, e2] at h
    omega
  · intro h
    have e1 : -(q.num.toInt) * ↑(p.den.toNat) = -(q.num.toInt * ↑(p.den.toNat)) := by ring
    have e2 : -(p.num.toInt) * ↑(q.den.toNat) = -(p.num.toInt * ↑(q.den.toNat)) := by ring
    rw [e1, e2]
    omega

end IndisputableMonolith.PRCGrow.RatioOrbitLeNeg
