import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLtTrichotomy
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.RatioOrbitDenseMediant

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal
open IndisputableMonolith.PRCGrow.RatioOrbitLtTrichotomy
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

def mediant (p q : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.add p.num q.num
  den := p.den + q.den
  den_ne_zero := by
    intro h
    have hp := RatioOrbit.den_toNat_ne_zero p
    have hq := RatioOrbit.den_toNat_ne_zero q
    have hadd : (p.den + q.den).toNat = p.den.toNat + q.den.toNat :=
      DistinctionNat.toNat_add p.den q.den
    have h2 : DistinctionNat.zero.toNat = p.den.toNat + q.den.toNat := by
      rw [← h]; exact hadd
    have h0 : DistinctionNat.zero.toNat = 0 := rfl
    rw [h0] at h2
    omega

theorem ltQ_iff_toNat (p q : RatioOrbit) :
    ltQ p q ↔
    p.num.pos.toNat * q.den.toNat + q.num.neg.toNat * p.den.toNat <
    q.num.pos.toNat * p.den.toNat + p.num.neg.toNat * q.den.toNat := by
  unfold ltQ leQ RatioOrbit.crossEq
  rw [le_iff_toNat_cf, SignedOrbit.balanced_iff_toNat_eq]
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, SignedOrbit.scaleByNat_pos,
             SignedOrbit.scaleByNat_neg, SignedOrbit.ofOrbit,
             DistinctionNat.toNat_add, DistinctionNat.toNat_mul]
  constructor
  · intro h
    have hz : DistinctionNat.zero.toNat = 0 := rfl
    simp only [hz, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at *
    obtain ⟨h1, h2⟩ := h
    omega
  · intro h
    have hz : DistinctionNat.zero.toNat = 0 := rfl
    simp only [hz, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at *
    refine ⟨?_, ?_⟩
    · omega
    · omega

theorem ltQ_mediant : ∀ p q, ltQ p q → ltQ p (mediant p q) ∧ ltQ (mediant p q) q := by
  intro p q h
  rw [ltQ_iff_toNat] at h
  refine ⟨?_, ?_⟩
  · rw [ltQ_iff_toNat]
    simp only [mediant, SignedOrbit.add_pos, SignedOrbit.add_neg,
               DistinctionNat.toNat_add, Nat.mul_add, Nat.add_mul]
    generalize p.num.pos.toNat * p.den.toNat = e1 at *
    generalize p.num.pos.toNat * q.den.toNat = e2 at *
    generalize p.num.neg.toNat * p.den.toNat = e3 at *
    generalize q.num.neg.toNat * p.den.toNat = e4 at *
    generalize q.num.pos.toNat * p.den.toNat = e5 at *
    generalize p.num.neg.toNat * q.den.toNat = e6 at *
    omega
  · rw [ltQ_iff_toNat]
    simp only [mediant, SignedOrbit.add_pos, SignedOrbit.add_neg,
               DistinctionNat.toNat_add, Nat.mul_add, Nat.add_mul]
    generalize p.num.pos.toNat * q.den.toNat = e2 at *
    generalize q.num.pos.toNat * q.den.toNat = e7 at *
    generalize q.num.neg.toNat * p.den.toNat = e4 at *
    generalize q.num.neg.toNat * q.den.toNat = e8 at *
    generalize q.num.pos.toNat * p.den.toNat = e5 at *
    generalize p.num.neg.toNat * q.den.toNat = e6 at *
    omega

end IndisputableMonolith.PRCGrow.RatioOrbitDenseMediant
