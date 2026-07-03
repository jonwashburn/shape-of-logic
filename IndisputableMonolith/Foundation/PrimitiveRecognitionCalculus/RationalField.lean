/-
  PrimitiveRecognitionCalculus/RationalField.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 4: package the PRC rational quotient as the reusable
    field-like substrate needed by PRC real completion and cost.

  Strength: δ-only for the object operations and positivity predicate.
  Verifier `ℚ` appears only in display theorems and law proofs.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

namespace RatioOrbit

/-- PRC-native positivity for a ratio orbit: positive signed numerator over a
nonzero orbit denominator. The denominator is an orbit position, so nonzero
means positive in the verifier display but is not part of the object definition. -/
def positive (q : RatioOrbit) : Prop :=
  SignedOrbit.nonneg q.num ∧ ¬ SignedOrbit.balanced q.num SignedOrbit.zero

theorem positive_iff_toRat_pos (q : RatioOrbit) :
    positive q ↔ 0 < q.toRat := by
  unfold positive RatioOrbit.toRat
  have hdenNat : 0 < q.den.toNat := Nat.pos_of_ne_zero q.den_toNat_ne_zero
  have hdenQ : 0 < (q.den.toNat : ℚ) := by exact_mod_cast hdenNat
  constructor
  · intro h
    have hnum_nonneg : 0 ≤ q.num.toInt :=
      (SignedOrbit.nonneg_iff_toInt_nonneg q.num).mp h.1
    have hnum_ne : q.num.toInt ≠ 0 := by
      intro hz
      exact h.2 ((SignedOrbit.balanced_iff_toInt_eq q.num SignedOrbit.zero).mpr (by
        rw [hz, SignedOrbit.zero_toInt]))
    have hnum_pos : 0 < q.num.toInt := by omega
    have hnumQ : 0 < (q.num.toInt : ℚ) := by exact_mod_cast hnum_pos
    positivity
  · intro h
    have hnum_pos : 0 < q.num.toInt := by
      have hden_ne : (q.den.toNat : ℚ) ≠ 0 := q.den_cast_ne_zero
      have hmul : 0 < ((q.num.toInt : ℚ) / (q.den.toNat : ℚ)) * (q.den.toNat : ℚ) :=
        mul_pos h hdenQ
      have hnumQ : 0 < (q.num.toInt : ℚ) := by
        field_simp [hden_ne] at hmul
        exact hmul
      exact_mod_cast hnumQ
    constructor
    · exact (SignedOrbit.nonneg_iff_toInt_nonneg q.num).mpr (by omega)
    · intro hbal
      have hnum_zero : q.num.toInt = 0 := by
        have := (SignedOrbit.balanced_iff_toInt_eq q.num SignedOrbit.zero).mp hbal
        simpa using this
      omega

theorem positive_normalize {q : RatioOrbit}
    (h : positive q) : positive (DistinctionNat.normalizeRatio q) := by
  rw [positive_iff_toRat_pos, DistinctionNat.normalizeRatio_toRat]
  exact (positive_iff_toRat_pos q).mp h

theorem positive_not_zero {q : RatioOrbit}
    (h : positive q) : q.toRat ≠ 0 := by
  exact ne_of_gt ((positive_iff_toRat_pos q).mp h)

end RatioOrbit

namespace PRCRat

/-! ## Division and positive rationals -/

/-- Division on PRC rationals, defined from PRC multiplication and reciprocal. -/
def div (a b : PRCRat) : PRCRat :=
  a * b⁻¹

instance instDiv : Div PRCRat := ⟨div⟩

@[simp] theorem div_eq (a b : PRCRat) : a / b = div a b := rfl

theorem toRat_div (a b : PRCRat) :
    (a / b).toRat = a.toRat / b.toRat := by
  unfold HDiv.hDiv instHDiv Div.div instDiv div
  rw [toRat_mul', toRat_inv']
  rfl

/-- A PRC rational is positive if it has a positive ratio-orbit representative. -/
def positive (q : PRCRat) : Prop :=
  ∃ r : RatioOrbit, q = mk r ∧ RatioOrbit.positive r

theorem positive_iff_toRat_pos (q : PRCRat) :
    positive q ↔ 0 < q.toRat := by
  constructor
  · intro h
    rcases h with ⟨r, rfl, hr⟩
    rw [toRat_mk]
    exact (RatioOrbit.positive_iff_toRat_pos r).mp hr
  · refine Quot.induction_on q ?_
    intro r hr
    exact ⟨r, rfl, (RatioOrbit.positive_iff_toRat_pos r).mpr (by simpa using hr)⟩

theorem positive_ne_zero {q : PRCRat}
    (h : positive q) : q.toRat ≠ 0 :=
  ne_of_gt ((positive_iff_toRat_pos q).mp h)

/-! ## Operator-form field laws -/

theorem add_assoc' (a b c : PRCRat) :
    (a + b) + c = a + (b + c) :=
  add_assoc a b c

theorem zero_add' (a : PRCRat) :
    0 + a = a :=
  zero_add a

theorem add_zero' (a : PRCRat) :
    a + 0 = a :=
  add_zero a

theorem add_left_neg' (a : PRCRat) :
    -a + a = 0 :=
  negate_add a

theorem add_right_neg' (a : PRCRat) :
    a + -a = 0 :=
  add_negate a

theorem mul_assoc' (a b c : PRCRat) :
    (a * b) * c = a * (b * c) :=
  mul_assoc a b c

theorem one_mul' (a : PRCRat) :
    1 * a = a :=
  one_mul a

theorem mul_one' (a : PRCRat) :
    a * 1 = a :=
  mul_one a

theorem zero_mul' (a : PRCRat) :
    0 * a = 0 :=
  zero_mul a

theorem mul_zero' (a : PRCRat) :
    a * 0 = 0 :=
  mul_zero a

theorem right_distrib' (a b c : PRCRat) :
    (a + b) * c = a * c + b * c :=
  right_distrib a b c

theorem left_distrib' (a b c : PRCRat) :
    a * (b + c) = a * b + a * c :=
  left_distrib a b c

/- `zero_ne_one` is proved structurally (choice-free) in `IntegerRational.lean`
via the `isZero` discriminator; the operator-form statement `(0 : PRCRat) ≠ 1`
is definitionally the same proposition. -/

theorem inv_zero : (0 : PRCRat)⁻¹ = 0 :=
  recip_zero

theorem inv_mul_cancel {a : PRCRat} (h : a.toRat ≠ 0) :
    a⁻¹ * a = 1 := by
  apply recip_mul_cancel₀
  intro hz
  apply h
  rw [hz, zero_toRat]

theorem div_mul_cancel {a b : PRCRat} (h : b.toRat ≠ 0) :
    (a / b) * b = a := by
  apply toRat_injective
  rw [toRat_mul', toRat_div]
  field_simp [h]

theorem mul_div_cancel {a b : PRCRat} (h : b.toRat ≠ 0) :
    a * b / b = a := by
  apply toRat_injective
  rw [toRat_div, toRat_mul']
  field_simp [h]

end PRCRat

namespace PRCJCost

/-- PRC J-cost lifted from ratio-orbit representatives to the rational quotient. -/
def onPRCRat : PRCRat → PRCRat :=
  Quot.lift
    (fun q => PRCRat.mk (onRatioOrbit q))
    (by
      intro a b h
      apply PRCRat.toRat_injective
      rw [PRCRat.toRat_mk, PRCRat.toRat_mk, onRatioOrbit_toRat, onRatioOrbit_toRat]
      have hrat : a.toRat = b.toRat := (ratioOrbitEquiv_iff_toRat_eq a b).mp h
      rw [hrat])

@[simp] theorem onPRCRat_mk (q : RatioOrbit) :
    onPRCRat (PRCRat.mk q) = PRCRat.mk (onRatioOrbit q) := by
  rfl

theorem onPRCRat_toRat (q : PRCRat) :
    (onPRCRat q).toRat = (q.toRat + q.toRat⁻¹) / 2 - 1 := by
  refine Quot.induction_on q ?_
  intro r
  change (PRCRat.mk (onRatioOrbit r)).toRat =
    ((PRCRat.mk r).toRat + (PRCRat.mk r).toRat⁻¹) / 2 - 1
  rw [PRCRat.toRat_mk, PRCRat.toRat_mk, onRatioOrbit_toRat]

theorem onPRCRat_normalized_representative (q : RatioOrbit) :
    onPRCRat (PRCRat.mk q) =
      onPRCRat (PRCRat.mk (DistinctionNat.normalizeRatio q)) := by
  apply PRCRat.toRat_injective
  rw [onPRCRat_toRat, onPRCRat_toRat, PRCRat.toRat_mk, PRCRat.toRat_mk,
    DistinctionNat.normalizeRatio_toRat]

end PRCJCost

/-! ## Bundled certificate -/

structure RationalFieldCertificate : Prop where
  add_comm : ∀ a b : PRCRat, a + b = b + a
  add_assoc : ∀ a b c : PRCRat, (a + b) + c = a + (b + c)
  zero_add : ∀ a : PRCRat, 0 + a = a
  add_zero : ∀ a : PRCRat, a + 0 = a
  add_left_neg : ∀ a : PRCRat, -a + a = 0
  mul_comm : ∀ a b : PRCRat, a * b = b * a
  mul_assoc : ∀ a b c : PRCRat, (a * b) * c = a * (b * c)
  one_mul : ∀ a : PRCRat, 1 * a = a
  mul_one : ∀ a : PRCRat, a * 1 = a
  left_distrib : ∀ a b c : PRCRat, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : PRCRat, (a + b) * c = a * c + b * c
  zero_ne_one : (0 : PRCRat) ≠ 1
  inv_zero : (0 : PRCRat)⁻¹ = 0
  mul_inv_cancel : ∀ a : PRCRat, a.toRat ≠ 0 → a * a⁻¹ = 1
  inv_mul_cancel : ∀ a : PRCRat, a.toRat ≠ 0 → a⁻¹ * a = 1
  div_display : ∀ a b : PRCRat, (a / b).toRat = a.toRat / b.toRat
  positive_display : ∀ q : PRCRat, PRCRat.positive q ↔ 0 < q.toRat
  ratio_positive_display : ∀ q : RatioOrbit, RatioOrbit.positive q ↔ 0 < q.toRat
  jcost_display :
    ∀ q : PRCRat, (PRCJCost.onPRCRat q).toRat = (q.toRat + q.toRat⁻¹) / 2 - 1
  jcost_normalized_representative :
    ∀ q : RatioOrbit,
      PRCJCost.onPRCRat (PRCRat.mk q) =
        PRCJCost.onPRCRat (PRCRat.mk (DistinctionNat.normalizeRatio q))

theorem rational_field_certificate : RationalFieldCertificate where
  add_comm := PRCRat.add_comm
  add_assoc := PRCRat.add_assoc'
  zero_add := PRCRat.zero_add'
  add_zero := PRCRat.add_zero'
  add_left_neg := PRCRat.add_left_neg'
  mul_comm := PRCRat.mul_comm
  mul_assoc := PRCRat.mul_assoc'
  one_mul := PRCRat.one_mul'
  mul_one := PRCRat.mul_one'
  left_distrib := PRCRat.left_distrib'
  right_distrib := PRCRat.right_distrib'
  zero_ne_one := PRCRat.zero_ne_one
  inv_zero := PRCRat.inv_zero
  mul_inv_cancel := by
    intro a h
    exact PRCRat.mul_recip_cancel h
  inv_mul_cancel := by
    intro a h
    exact PRCRat.inv_mul_cancel h
  div_display := PRCRat.toRat_div
  positive_display := PRCRat.positive_iff_toRat_pos
  ratio_positive_display := RatioOrbit.positive_iff_toRat_pos
  jcost_display := PRCJCost.onPRCRat_toRat
  jcost_normalized_representative := PRCJCost.onPRCRat_normalized_representative

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
