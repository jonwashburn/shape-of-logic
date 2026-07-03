import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLtTrichotomy
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.RatioOrbitMulPos

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal
open IndisputableMonolith.PRCGrow.RatioOrbitLtTrichotomy
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem mul_strictpos_cf (a b : SignedOrbit) (ha : a.neg.toNat < a.pos.toNat) (hb : b.neg.toNat < b.pos.toNat) : (SignedOrbit.mul a b).neg.toNat < (SignedOrbit.mul a b).pos.toNat := by
  have hpos : (SignedOrbit.mul a b).pos.toNat = a.pos.toNat * b.pos.toNat + a.neg.toNat * b.neg.toNat := by
    show (a.pos * b.pos + a.neg * b.neg).toNat = _
    rw [DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
  have hneg : (SignedOrbit.mul a b).neg.toNat = a.pos.toNat * b.neg.toNat + a.neg.toNat * b.pos.toNat := by
    show (a.pos * b.neg + a.neg * b.pos).toNat = _
    rw [DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
  rw [hpos, hneg]; obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt ha; obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hb; rw [hs, ht]; ring_nf; omega

theorem zero_ltQ_iff_num (r : RatioOrbit) : ltQ RatioOrbit.zero r ↔ r.num.neg.toNat < r.num.pos.toNat := by
  unfold ltQ leQ RatioOrbit.crossEq
  constructor
  · rintro ⟨hle, hne⟩
    rw [le_iff_toNat_cf] at hle
    rw [SignedOrbit.balanced_iff_toNat_eq] at hne
    simp only [RatioOrbit.zero, SignedOrbit.mul, SignedOrbit.ofOrbit, SignedOrbit.zero, SignedOrbit.scaleByNat, DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_zero, DistinctionNat.toNat_succ] at hle hne
    omega
  · intro h
    refine ⟨?_, ?_⟩
    · rw [le_iff_toNat_cf]
      simp only [RatioOrbit.zero, SignedOrbit.mul, SignedOrbit.ofOrbit, SignedOrbit.zero, SignedOrbit.scaleByNat, DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_zero, DistinctionNat.toNat_succ]
      omega
    · intro hbal
      rw [SignedOrbit.balanced_iff_toNat_eq] at hbal
      simp only [RatioOrbit.zero, SignedOrbit.mul, SignedOrbit.ofOrbit, SignedOrbit.zero, SignedOrbit.scaleByNat, DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_zero, DistinctionNat.toNat_succ] at hbal
      omega

theorem ltQ_mul_pos (p q : RatioOrbit) (hp : ltQ RatioOrbit.zero p) (hq : ltQ RatioOrbit.zero q) : ltQ RatioOrbit.zero (RatioOrbit.mul p q) := by
  rw [zero_ltQ_iff_num] at hp hq ⊢
  have h : (RatioOrbit.mul p q).num = SignedOrbit.mul p.num q.num := rfl
  rw [h]
  exact mul_strictpos_cf p.num q.num hp hq

end IndisputableMonolith.PRCGrow.RatioOrbitMulPos
