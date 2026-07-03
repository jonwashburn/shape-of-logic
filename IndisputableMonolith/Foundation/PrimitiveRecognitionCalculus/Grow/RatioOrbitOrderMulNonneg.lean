import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal

namespace IndisputableMonolith.PRCGrow.RatioOrbitOrderMulNonneg

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal

/-- Choice-free characterization of nonnegativity in the `leQ` order:
    `zero ≤ r` iff the numerator's signed-orbit integer is nonnegative.
    Routed through the purified `SignedOrbit.le_iff_toInt_le` bridge; the
    zero side collapses because `RatioOrbit.zero` has numerator integer `0`
    and denominator `1`. -/
theorem zero_leQ_iff (r : RatioOrbit) :
    leQ RatioOrbit.zero r ↔ (0 : ℤ) ≤ r.num.toInt := by
  unfold leQ
  rw [SignedOrbit.le_iff_toInt_le]
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, RatioOrbit.zero,
    SignedOrbit.zero_toInt, DistinctionNat.toNat_succ, DistinctionNat.toNat_zero]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The ordered-ring law for the delta-native rational order: multiplying both
    sides of a `leQ` inequality on the right by a nonnegative ratio orbit
    preserves the order. Expand `RatioOrbit.mul` on representatives, reduce the
    cross-products to integer arithmetic through the choice-free `toInt`
    bridge (casts moved by the axiom-free `Int.natCast_mul`, never `push_cast`,
    which smuggles `Classical.choice` on this goal shape), and close with
    `Int.mul_le_mul_of_nonneg_right` after a `ring` regrouping that isolates
    the common nonnegative factor `r.num.toInt * r.den.toNat`. Choice-free:
    `#print axioms` is `{propext, Quot.sound}`. -/
theorem leQ_mul_nonneg_right (p q r : RatioOrbit)
    (hr : leQ RatioOrbit.zero r) (hpq : leQ p q) :
    leQ (RatioOrbit.mul p r) (RatioOrbit.mul q r) := by
  rw [zero_leQ_iff] at hr
  unfold leQ at hpq ⊢
  rw [SignedOrbit.le_iff_toInt_le] at hpq ⊢
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, RatioOrbit.mul,
    DistinctionNat.toNat_mul] at hpq ⊢
  -- hpq : p.num.toInt * q.den.toNat ≤ q.num.toInt * p.den.toNat
  -- goal: p.num.toInt * r.num.toInt * (q.den.toNat * r.den.toNat)
  --     ≤ q.num.toInt * r.num.toInt * (p.den.toNat * r.den.toNat)
  rw [Int.natCast_mul, Int.natCast_mul]
  have hrd : (0 : ℤ) ≤ (r.den.toNat : ℤ) := Int.natCast_nonneg _
  have hfac : (0 : ℤ) ≤ r.num.toInt * (r.den.toNat : ℤ) :=
    Int.mul_nonneg hr hrd
  have hstep : p.num.toInt * (q.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ))
      ≤ q.num.toInt * (p.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ)) :=
    Int.mul_le_mul_of_nonneg_right hpq hfac
  calc p.num.toInt * r.num.toInt * ((q.den.toNat : ℤ) * (r.den.toNat : ℤ))
      = p.num.toInt * (q.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ)) := by ring
    _ ≤ q.num.toInt * (p.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ)) := hstep
    _ = q.num.toInt * r.num.toInt * ((p.den.toNat : ℤ) * (r.den.toNat : ℤ)) := by ring

end IndisputableMonolith.PRCGrow.RatioOrbitOrderMulNonneg
