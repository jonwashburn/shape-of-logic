import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitNonnegFlagMulOfOrbitRightOfNeZeroChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem nonnegFlag_mul_ofOrbit_right_of_ne_zero_cf
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).nonnegFlag = z.nonnegFlag := by
  have hd' : d.toNat ≠ 0 := by
    intro h
    apply hd
    rw [← DistinctionNat.ofNat_toNat d, h, DistinctionNat.ofNat_zero]
  have hdpos : 0 < d.toNat := by omega
  have hpos : (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).pos.toNat = z.pos.toNat * d.toNat := by
    show (z.pos * (SignedOrbit.ofOrbit d).pos + z.neg * (SignedOrbit.ofOrbit d).neg).toNat = _
    have hp : (SignedOrbit.ofOrbit d).pos = d := rfl
    have hn : (SignedOrbit.ofOrbit d).neg = DistinctionNat.zero := rfl
    rw [hp, hn, DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_mul,
      DistinctionNat.toNat_zero]
    omega
  have hneg : (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).neg.toNat = z.neg.toNat * d.toNat := by
    show (z.pos * (SignedOrbit.ofOrbit d).neg + z.neg * (SignedOrbit.ofOrbit d).pos).toNat = _
    have hp : (SignedOrbit.ofOrbit d).pos = d := rfl
    have hn : (SignedOrbit.ofOrbit d).neg = DistinctionNat.zero := rfl
    rw [hp, hn, DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_mul,
      DistinctionNat.toNat_zero]
    omega
  have key : DistinctionNat.leq (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).neg
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).pos = true ↔
      DistinctionNat.leq z.neg z.pos = true := by
    rw [leq_eq_true_iff_cf, leq_eq_true_iff_cf, hpos, hneg]
    constructor
    · intro h
      exact Nat.le_of_mul_le_mul_right h hdpos
    · intro h
      exact Nat.mul_le_mul_right _ h
  show DistinctionNat.leq (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).neg
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).pos =
      DistinctionNat.leq z.neg z.pos
  cases hb : DistinctionNat.leq z.neg z.pos with
    | true => exact key.mpr hb
    | false =>
      cases hb2 : DistinctionNat.leq (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).neg
          (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).pos with
        | true =>
          rw [key.mp hb2] at hb
          exact absurd hb (by decide)
        | false => rfl

end IndisputableMonolith.PRCGrow.SignedOrbitNonnegFlagMulOfOrbitRightOfNeZeroChoiceFree
