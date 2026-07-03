import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal

namespace IndisputableMonolith.PRCGrow.RatioOrbitLeTransAntisymm

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.RatioOrbitLeReflTotal

/-- Transitivity of the delta-native cross-multiplication order `leQ` on `RatioOrbit`.
    From the two cross-product inequalities, multiply through by the (positive) outer
    denominators, chain, and cancel the shared positive denominator `q.den`.
    Choice-free: routed through the purified `SignedOrbit.le_iff_toInt_le` bridge and
    `Int` cancellation lemmas only. -/
theorem leQ_trans (p q r : RatioOrbit) (hpq : leQ p q) (hqr : leQ q r) : leQ p r := by
  unfold leQ at hpq hqr ⊢
  rw [SignedOrbit.le_iff_toInt_le] at hpq hqr ⊢
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hpq hqr ⊢
  -- hpq : p.num.toInt * q.den.toNat ≤ q.num.toInt * p.den.toNat
  -- hqr : q.num.toInt * r.den.toNat ≤ r.num.toInt * q.den.toNat
  -- goal: p.num.toInt * r.den.toNat ≤ r.num.toInt * p.den.toNat
  have hq : (0 : ℤ) < (q.den.toNat : ℤ) := by
    have := q.den_toNat_ne_zero
    omega
  have hp : (0 : ℤ) ≤ (p.den.toNat : ℤ) := Int.natCast_nonneg _
  have hr : (0 : ℤ) ≤ (r.den.toNat : ℤ) := Int.natCast_nonneg _
  have hchain : p.num.toInt * (r.den.toNat : ℤ) * (q.den.toNat : ℤ)
      ≤ r.num.toInt * (p.den.toNat : ℤ) * (q.den.toNat : ℤ) := by
    calc p.num.toInt * (r.den.toNat : ℤ) * (q.den.toNat : ℤ)
        = p.num.toInt * (q.den.toNat : ℤ) * (r.den.toNat : ℤ) := by ring
      _ ≤ q.num.toInt * (p.den.toNat : ℤ) * (r.den.toNat : ℤ) :=
          Int.mul_le_mul_of_nonneg_right hpq hr
      _ = q.num.toInt * (r.den.toNat : ℤ) * (p.den.toNat : ℤ) := by ring
      _ ≤ r.num.toInt * (q.den.toNat : ℤ) * (p.den.toNat : ℤ) :=
          Int.mul_le_mul_of_nonneg_right hqr hp
      _ = r.num.toInt * (p.den.toNat : ℤ) * (q.den.toNat : ℤ) := by ring
  exact Int.le_of_mul_le_mul_right hchain hq

/-- Antisymmetry of `leQ` up to the rational equivalence `crossEq`: mutual `leQ`
    forces the cross products to be equal, which is exactly `crossEq` through the
    purified `crossEq_iff_toIntCross` bridge. Choice-free. -/
theorem leQ_antisymm (p q : RatioOrbit) (hpq : leQ p q) (hqp : leQ q p) :
    RatioOrbit.crossEq p q := by
  unfold leQ at hpq hqp
  rw [SignedOrbit.le_iff_toInt_le] at hpq hqp
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hpq hqp
  rw [RatioOrbit.crossEq_iff_toIntCross]
  exact Int.le_antisymm hpq hqp

end IndisputableMonolith.PRCGrow.RatioOrbitLeTransAntisymm
