import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.RatioOrbitLeReflTotal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitArithmetic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Grow.SignedOrbitOrderChoiceFree

namespace IndisputableMonolith.PRCGrow.SignedOrbitLeMulRightIffOfNonnegFlagOfNotBalancedZeroChoiceFree

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.PRCGrow.SignedOrbitOrderChoiceFree

theorem cross_le_iff (A B p n : Nat) (hnp : n < p) :
    (n * B + p * A ≤ p * B + n * A ↔ A ≤ B) := by
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hnp
  subst hc
  have e1 : (n + c + 1) * A = n * A + (c + 1) * A := by ring
  have e2 : (n + c + 1) * B = n * B + (c + 1) * B := by ring
  rw [e1, e2]
  constructor
  · intro h
    have h2 : (c + 1) * A ≤ (c + 1) * B := by omega
    exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos c)
  · intro h
    have h2 : (c + 1) * A ≤ (c + 1) * B := Nat.mul_le_mul (Nat.le_refl _) h
    omega

theorem le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero_cf :
    ∀ (a z w : SignedOrbit), a.nonnegFlag = true →
    ¬ a.balanced SignedOrbit.zero →
    ((z.mul a).le (w.mul a) ↔ z.le w) := by
  intro a z w hanonneg ha
  have han : a.neg.toNat ≤ a.pos.toNat := by
    have h := hanonneg
    unfold SignedOrbit.nonnegFlag at h
    rwa [leq_eq_true_iff_cf] at h
  have hlt : a.neg.toNat < a.pos.toNat := by
    rcases Nat.lt_or_ge a.neg.toNat a.pos.toNat with h | h
    · exact h
    · exfalso; apply ha
      rw [SignedOrbit.balanced_iff_toNat_eq]
      rw [show SignedOrbit.zero.neg.toNat = 0 from rfl,
          show SignedOrbit.zero.pos.toNat = 0 from rfl]
      omega
  rw [le_iff_toNat_cf, le_iff_toNat_cf]
  have eqL : (w.mul a).neg.toNat + (z.mul a).pos.toNat =
      a.neg.toNat * (w.pos.toNat + z.neg.toNat) + a.pos.toNat * (w.neg.toNat + z.pos.toNat) := by
    simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg,
              DistinctionNat.toNat_add, DistinctionNat.toNat_mul]
    ring
  have eqR : (w.mul a).pos.toNat + (z.mul a).neg.toNat =
      a.pos.toNat * (w.pos.toNat + z.neg.toNat) + a.neg.toNat * (w.neg.toNat + z.pos.toNat) := by
    simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg,
              DistinctionNat.toNat_add, DistinctionNat.toNat_mul]
    ring
  rw [eqL, eqR]
  exact cross_le_iff (w.neg.toNat + z.pos.toNat) (w.pos.toNat + z.neg.toNat)
      a.pos.toNat a.neg.toNat hlt

end IndisputableMonolith.PRCGrow.SignedOrbitLeMulRightIffOfNonnegFlagOfNotBalancedZeroChoiceFree
