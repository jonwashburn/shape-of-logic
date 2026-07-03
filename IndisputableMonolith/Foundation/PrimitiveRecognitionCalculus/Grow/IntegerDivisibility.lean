import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder

namespace IndisputableMonolith.PRCGrow.IntegerDivisibility

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus

-- Choice-free bridges between `balanced` and the integer display, routed through
-- the Nat-level `balanced_iff_toNat_eq` (NOT the iff `balanced_iff_toInt_eq`),
-- so no order-typeclass / classical content leaks in.

theorem balanced_toInt_eq {x y : SignedOrbit} (h : SignedOrbit.balanced x y) :
    x.toInt = y.toInt := by
  have hn := (SignedOrbit.balanced_iff_toNat_eq x y).mp h
  unfold SignedOrbit.toInt
  omega

theorem balanced_of_toInt_eq {x y : SignedOrbit} (h : x.toInt = y.toInt) :
    SignedOrbit.balanced x y := by
  rw [SignedOrbit.balanced_iff_toNat_eq]
  unfold SignedOrbit.toInt at h
  omega

def dvdZ (a b : SignedOrbit) : Prop :=
  ∃ c : SignedOrbit, SignedOrbit.balanced (SignedOrbit.mul a c) b

theorem dvdZ_refl (a : SignedOrbit) : dvdZ a a := by
  refine ⟨SignedOrbit.one, balanced_of_toInt_eq ?_⟩
  rw [SignedOrbit.mul_toInt, SignedOrbit.one_toInt]
  omega

theorem dvdZ_trans (a b c : SignedOrbit) (hab : dvdZ a b) (hbc : dvdZ b c) : dvdZ a c := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨SignedOrbit.mul w v, balanced_of_toInt_eq ?_⟩
  have hw' := balanced_toInt_eq hw
  have hv' := balanced_toInt_eq hv
  rw [SignedOrbit.mul_toInt] at hw' hv'
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  linear_combination v.toInt * hw' + hv'

theorem dvdZ_add (a b c : SignedOrbit) (hab : dvdZ a b) (hac : dvdZ a c) :
    dvdZ a (SignedOrbit.add b c) := by
  obtain ⟨w, hw⟩ := hab
  obtain ⟨v, hv⟩ := hac
  refine ⟨SignedOrbit.add w v, balanced_of_toInt_eq ?_⟩
  have hw' := balanced_toInt_eq hw
  have hv' := balanced_toInt_eq hv
  rw [SignedOrbit.mul_toInt] at hw' hv'
  rw [SignedOrbit.mul_toInt, SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  linear_combination hw' + hv'

theorem one_dvdZ (a : SignedOrbit) : dvdZ SignedOrbit.one a := by
  refine ⟨a, balanced_of_toInt_eq ?_⟩
  rw [SignedOrbit.mul_toInt, SignedOrbit.one_toInt]
  omega

theorem dvdZ_zero (a : SignedOrbit) : dvdZ a SignedOrbit.zero := by
  refine ⟨SignedOrbit.zero, balanced_of_toInt_eq ?_⟩
  rw [SignedOrbit.mul_toInt, SignedOrbit.zero_toInt]
  omega

end IndisputableMonolith.PRCGrow.IntegerDivisibility
