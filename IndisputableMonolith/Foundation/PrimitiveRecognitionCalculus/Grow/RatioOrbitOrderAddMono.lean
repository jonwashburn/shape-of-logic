import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.RatioOrbitOrderAddMono

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

/-- Choice-free unfold of `toInt` to its pos/neg Nat-cast difference. -/
private lemma toInt_eq (a : SignedOrbit) :
    a.toInt = (a.pos.toNat : ℤ) - (a.neg.toNat : ℤ) := by
  cases a with
  | mk pos neg => exact SignedOrbit.toInt_mk pos neg

/-- Choice-free Int order bridge, routed through the CF Nat bridge `le_iff_toNat_cf`
    (never through the choice-tainted `SignedOrbit.le_iff_toInt_le`). -/
private lemma le_iff_toInt_le_cf (a b : SignedOrbit) :
    SignedOrbit.le a b ↔ a.toInt ≤ b.toInt := by
  rw [le_iff_toNat_cf, toInt_eq a, toInt_eq b]
  constructor
  · intro hh; omega
  · intro hh; omega

/-- Translation invariance of the delta-native ratio order: the order on `RatioOrbit`
    is compatible with addition. -/
theorem leQ_add_right (p q r : RatioOrbit) (h : leQ p q) :
    leQ (RatioOrbit.add p r) (RatioOrbit.add q r) := by
  unfold leQ at h ⊢
  rw [le_iff_toInt_le_cf] at h ⊢
  unfold RatioOrbit.add
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, SignedOrbit.scaleByNat_toInt,
             SignedOrbit.add_toInt, DistinctionNat.toNat_mul] at h ⊢
  push_cast at h ⊢
  rw [← Int.sub_nonneg] at h ⊢
  have hc : (0:ℤ) ≤ (r.den.toNat : ℤ) * (r.den.toNat : ℤ) :=
    Int.mul_nonneg (by omega) (by omega)
  have hprod := Int.mul_nonneg h hc
  convert hprod using 1 <;> ring

end IndisputableMonolith.PRCGrow.RatioOrbitOrderAddMono
