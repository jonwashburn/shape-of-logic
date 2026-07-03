/-
  PrimitiveRecognitionCalculus/IntegerOrder.lean

  Round-trip sources:
    δ/PRC_Kernel_Spec_20260526.html
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchors:
    Build Order step 1: internal signed-orbit order and absolute value.

  This module is the named certificate surface for integer order. The core
  declarations live in `IntegerRational.lean` because `RatioOrbit.recipNonzero`
  needs `SignedOrbit.abs` and `SignedOrbit.nonnegFlag` without creating an
  import cycle.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

namespace SignedOrbit

/-! ## Closed order laws for the signed-orbit surface -/

theorem le_refl (a : SignedOrbit) : SignedOrbit.le a a :=
  (SignedOrbit.le_iff_toInt_le a a).mpr (by omega)

theorem le_trans {a b c : SignedOrbit}
    (hab : SignedOrbit.le a b) (hbc : SignedOrbit.le b c) :
    SignedOrbit.le a c := by
  rw [SignedOrbit.le_iff_toInt_le] at *
  omega

theorem le_antisymm_balanced {a b : SignedOrbit}
    (hab : SignedOrbit.le a b) (hba : SignedOrbit.le b a) :
    SignedOrbit.balanced a b := by
  rw [SignedOrbit.le_iff_toInt_le] at hab hba
  rw [SignedOrbit.balanced_iff_toInt_eq]
  omega

theorem le_total (a b : SignedOrbit) :
    SignedOrbit.le a b ∨ SignedOrbit.le b a := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  omega

theorem trichotomy (a b : SignedOrbit) :
    SignedOrbit.lt a b ∨
      SignedOrbit.balanced a b ∨
        SignedOrbit.lt b a := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.lt_iff_toInt_lt]
  omega

/-! ## Sign-flag complement laws -/

theorem negativeFlag_eq_true_iff_nonnegFlag_eq_false (z : SignedOrbit) :
    z.negativeFlag = true ↔ z.nonnegFlag = false := by
  unfold SignedOrbit.negativeFlag
  cases z.nonnegFlag <;> simp

theorem negativeFlag_eq_false_iff_nonnegFlag_eq_true (z : SignedOrbit) :
    z.negativeFlag = false ↔ z.nonnegFlag = true := by
  unfold SignedOrbit.negativeFlag
  cases z.nonnegFlag <;> simp

theorem signFlags_exclusive (z : SignedOrbit) :
    ¬ (z.nonnegFlag = true ∧ z.negativeFlag = true) := by
  intro h
  rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false] at h
  rcases h with ⟨hnonneg, hneg⟩
  rw [hnonneg] at hneg
  contradiction

theorem signFlags_exhaustive (z : SignedOrbit) :
    z.nonnegFlag = true ∨ z.negativeFlag = true := by
  cases h : z.nonnegFlag with
  | true => exact Or.inl rfl
  | false =>
      right
      rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
      exact h

theorem zero_le_iff_nonnegFlag (z : SignedOrbit) :
    SignedOrbit.le SignedOrbit.zero z ↔ z.nonnegFlag = true := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.zero_toInt,
    SignedOrbit.nonnegFlag_eq_true_iff]

theorem lt_zero_iff_negativeFlag (z : SignedOrbit) :
    SignedOrbit.lt z SignedOrbit.zero ↔ z.negativeFlag = true := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.zero_toInt,
    SignedOrbit.negativeFlag_eq_true_iff_toInt_neg]

theorem zero_lt_iff_nonnegFlag_and_not_balanced_zero (z : SignedOrbit) :
    SignedOrbit.lt SignedOrbit.zero z ↔
      z.nonnegFlag = true ∧
        ¬ SignedOrbit.balanced z SignedOrbit.zero := by
  unfold SignedOrbit.lt
  rw [SignedOrbit.zero_le_iff_nonnegFlag]
  constructor
  · intro h
    exact ⟨h.1, fun hz => h.2 (SignedOrbit.balanced_symm hz)⟩
  · intro h
    exact ⟨h.1, fun hz => h.2 (SignedOrbit.balanced_symm hz)⟩

theorem nonnegFlag_eq_of_balanced {z w : SignedOrbit}
    (h : SignedOrbit.balanced z w) :
    z.nonnegFlag = w.nonnegFlag := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at h
  cases hz : z.nonnegFlag <;> cases hw : w.nonnegFlag
  · rfl
  · have hzneg : z.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff z).mp hz
    have hwnonneg : 0 ≤ w.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff w).mp hw
    omega
  · have hznonneg : 0 ≤ z.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff z).mp hz
    have hwneg : w.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff w).mp hw
    omega
  · rfl

theorem negativeFlag_eq_of_balanced {z w : SignedOrbit}
    (h : SignedOrbit.balanced z w) :
    z.negativeFlag = w.negativeFlag := by
  unfold SignedOrbit.negativeFlag
  rw [SignedOrbit.nonnegFlag_eq_of_balanced h]

theorem nonneg_iff_of_balanced {z w : SignedOrbit}
    (h : SignedOrbit.balanced z w) :
    SignedOrbit.nonneg z ↔ SignedOrbit.nonneg w := by
  rw [SignedOrbit.nonneg_iff_toInt_nonneg, SignedOrbit.nonneg_iff_toInt_nonneg]
  exact ⟨fun hz => by
    rw [← (SignedOrbit.balanced_iff_toInt_eq z w).mp h]
    exact hz,
    fun hw => by
      rw [(SignedOrbit.balanced_iff_toInt_eq z w).mp h]
      exact hw⟩

/-! ## Balanced congruence for signed-orbit operations -/

theorem add_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.add a b) (SignedOrbit.add a' b') := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt, ha, hb]

theorem negate_congr_of_balanced {a a' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.negate a) (SignedOrbit.negate a') := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.negate_toInt, SignedOrbit.negate_toInt, ha]

theorem sub_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a' b') := by
  unfold SignedOrbit.sub
  exact SignedOrbit.add_congr_of_balanced ha
    (SignedOrbit.negate_congr_of_balanced hb)

theorem sub_congr_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a' b) := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.sub_congr_of_balanced ha hb

theorem sub_congr_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a b') := by
  have ha : SignedOrbit.balanced a a := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.sub_congr_of_balanced ha hb

theorem nonnegFlag_sub_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.sub a b).nonnegFlag =
      (SignedOrbit.sub a' b).nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem nonnegFlag_sub_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).nonnegFlag =
      (SignedOrbit.sub a b').nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem negativeFlag_sub_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.sub a b).negativeFlag =
      (SignedOrbit.sub a' b).negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem negativeFlag_sub_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).negativeFlag =
      (SignedOrbit.sub a b').negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem nonnegFlag_sub_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).nonnegFlag =
      (SignedOrbit.sub a' b').nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem negativeFlag_sub_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).negativeFlag =
      (SignedOrbit.sub a' b').negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem scaleByNat_congr_of_balanced {z w : SignedOrbit}
    (h : SignedOrbit.balanced z w) (d : DistinctionNat) :
    SignedOrbit.balanced (z.scaleByNat d) (w.scaleByNat d) := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt, h]

theorem scaleByNat_balanced_zero_of_balanced_zero {z : SignedOrbit}
    (h : SignedOrbit.balanced z SignedOrbit.zero) (d : DistinctionNat) :
    SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.zero_toInt, h]
  simp [SignedOrbit.zero_toInt]

theorem mul_ofOrbit_balanced_scaleByNat
    (z : SignedOrbit) (d : DistinctionNat) :
    SignedOrbit.balanced
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
      (z.scaleByNat d) := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.scaleByNat_toInt]

theorem ofOrbit_mul_balanced_scaleByNat
    (d : DistinctionNat) (z : SignedOrbit) :
    SignedOrbit.balanced
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
      (z.scaleByNat d) := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.scaleByNat_toInt]
  ring

theorem abs_mul (z w : SignedOrbit) :
    (SignedOrbit.mul z w).abs = z.abs * w.abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.mul_toInt, DistinctionNat.toNat_mul,
    SignedOrbit.abs_toNat, SignedOrbit.abs_toNat, Int.natAbs_mul]

theorem mul_balanced_zero_iff
    (z w : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero ∨
        SignedOrbit.balanced w SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.zero_toInt, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hw
    · exact Or.inl hz
    · exact Or.inr hw
  · intro h
    rcases h with hz | hw
    · rw [hz]
      ring
    · rw [hw]
      ring

theorem mul_not_balanced_zero_iff
    (z w : SignedOrbit) :
    ¬ SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
        ¬ SignedOrbit.balanced w SignedOrbit.zero := by
  rw [SignedOrbit.mul_balanced_zero_iff]
  constructor
  · intro h
    constructor
    · intro hz
      exact h (Or.inl hz)
    · intro hw
      exact h (Or.inr hw)
  · intro h hzprod
    rcases hzprod with hz | hw
    · exact h.1 hz
    · exact h.2 hw

theorem balanced_mul_left_iff_of_not_balanced_zero
    (a z w : SignedOrbit)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.balanced (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
      SignedOrbit.balanced z w := by
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor
  · intro h
    exact mul_left_cancel₀ haInt h
  · intro h
    rw [h]

theorem balanced_mul_right_iff_of_not_balanced_zero
    (a z w : SignedOrbit)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.balanced (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
      SignedOrbit.balanced z w := by
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor
  · intro h
    exact mul_right_cancel₀ haInt h
  · intro h
    rw [h]

theorem le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.le (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
      SignedOrbit.le z w := by
  have hanonnegInt : 0 ≤ a.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff a).mp hanonneg
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hapos : 0 < a.toInt := by omega
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.lt (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
      SignedOrbit.lt z w := by
  have hanonnegInt : 0 ≤ a.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff a).mp hanonneg
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hapos : 0 < a.toInt := by omega
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.le (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
      SignedOrbit.le z w := by
  have hanonnegInt : 0 ≤ a.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff a).mp hanonneg
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hapos : 0 < a.toInt := by omega
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.lt (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
      SignedOrbit.lt z w := by
  have hanonnegInt : 0 ≤ a.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff a).mp hanonneg
  have haInt : a.toInt ≠ 0 := by
    intro hzero
    exact ha (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hapos : 0 < a.toInt := by omega
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem le_mul_left_iff_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.le (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
      SignedOrbit.le w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem lt_mul_left_iff_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.lt (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
      SignedOrbit.lt w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem le_mul_right_iff_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.le (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
      SignedOrbit.le w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem lt_mul_right_iff_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.lt (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
      SignedOrbit.lt w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  constructor <;> intro h <;> nlinarith

theorem abs_mul_eq_zero_iff
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).abs = DistinctionNat.zero ↔
      z.abs = DistinctionNat.zero ∨ w.abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt,
    SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.abs_eq_zero_iff_toInt_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hw
    · exact Or.inl hz
    · exact Or.inr hw
  · intro h
    rcases h with hz | hw
    · rw [hz]
      ring
    · rw [hw]
      ring

theorem abs_mul_ne_zero_iff
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).abs ≠ DistinctionNat.zero ↔
      z.abs ≠ DistinctionNat.zero ∧ w.abs ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_eq_zero_iff z w
  constructor
  · intro h
    constructor
    · intro hz
      exact h (hzero.mpr (Or.inl hz))
    · intro hw
      exact h (hzero.mpr (Or.inr hw))
  · intro h hzprod
    rcases hzero.mp hzprod with hz | hw
    · exact h.1 hz
    · exact h.2 hw

theorem abs_mul_eq_zero_iff_balanced_zero
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).abs = DistinctionNat.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero ∨
        SignedOrbit.balanced w SignedOrbit.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt,
    SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.zero_toInt]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hw
    · exact Or.inl hz
    · exact Or.inr hw
  · intro h
    rcases h with hz | hw
    · rw [hz]
      ring
    · rw [hw]
      ring

theorem abs_mul_ne_zero_iff_not_balanced_zero
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).abs ≠ DistinctionNat.zero ↔
      ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
        ¬ SignedOrbit.balanced w SignedOrbit.zero := by
  have hzero := SignedOrbit.abs_mul_eq_zero_iff_balanced_zero z w
  constructor
  · intro h
    constructor
    · intro hz
      exact h (hzero.mpr (Or.inl hz))
    · intro hw
      exact h (hzero.mpr (Or.inr hw))
  · intro h hzprod
    rcases hzero.mp hzprod with hz | hw
    · exact h.1 hz
    · exact h.2 hw

theorem abs_scaleByNat (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).abs = z.abs * d := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.scaleByNat_toInt,
    DistinctionNat.toNat_mul, SignedOrbit.abs_toNat, Int.natAbs_mul,
    Int.natAbs_natCast]

theorem abs_mul_ofOrbit_right (z : SignedOrbit) (d : DistinctionNat) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs = z.abs * d := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    DistinctionNat.toNat_mul, SignedOrbit.abs_toNat, Int.natAbs_mul,
    Int.natAbs_natCast]

theorem abs_mul_ofOrbit_left (d : DistinctionNat) (z : SignedOrbit) :
    (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs = z.abs * d := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    DistinctionNat.toNat_mul, SignedOrbit.abs_toNat, Int.natAbs_mul,
    Int.natAbs_natCast]
  ring

theorem mul_ofOrbit_right_balanced_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d)) SignedOrbit.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.zero_toInt]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hd
    · left
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
  · intro h
    rcases h with hz | hd
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hz
      rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem mul_ofOrbit_left_balanced_zero_iff
    (d : DistinctionNat) (z : SignedOrbit) :
    SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z) SignedOrbit.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.zero_toInt]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hd | hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
    · left
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hz
  · intro h
    rcases h with hz | hd
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hz
      rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem mul_ofOrbit_right_not_balanced_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    ¬ SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d)) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero := by
  rw [SignedOrbit.mul_ofOrbit_right_balanced_zero_iff]
  constructor
  · intro h
    constructor
    · intro hz
      exact h (Or.inl hz)
    · intro hd
      exact h (Or.inr hd)
  · intro h hzprod
    rcases hzprod with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem mul_ofOrbit_left_not_balanced_zero_iff
    (d : DistinctionNat) (z : SignedOrbit) :
    ¬ SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero := by
  rw [SignedOrbit.mul_ofOrbit_left_balanced_zero_iff]
  constructor
  · intro h
    constructor
    · intro hz
      exact h (Or.inl hz)
    · intro hd
      exact h (Or.inr hd)
  · intro h hzprod
    rcases hzprod with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem nonnegFlag_scaleByNat_of_ne_zero
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    (z.scaleByNat d).nonnegFlag = z.nonnegFlag := by
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  cases hz : z.nonnegFlag
  · rw [SignedOrbit.nonnegFlag_eq_false_iff,
      SignedOrbit.scaleByNat_toInt]
    have hzneg : z.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff z).mp hz
    have hdpos : 0 < (d.toNat : ℤ) := by
      have : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
      exact_mod_cast this
    nlinarith
  · rw [SignedOrbit.nonnegFlag_eq_true_iff,
      SignedOrbit.scaleByNat_toInt]
    have hznonneg : 0 ≤ z.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff z).mp hz
    have hdnonneg : 0 ≤ (d.toNat : ℤ) := by exact_mod_cast Nat.zero_le d.toNat
    nlinarith

theorem negativeFlag_scaleByNat_of_ne_zero
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    (z.scaleByNat d).negativeFlag = z.negativeFlag := by
  unfold SignedOrbit.negativeFlag
  rw [SignedOrbit.nonnegFlag_scaleByNat_of_ne_zero z d hd]

theorem scaleByNat_balanced_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.scaleByNat_toInt,
    SignedOrbit.zero_toInt]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hd
    · left
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
  · intro h
    rcases h with hz | hd
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hz
      rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem scaleByNat_not_balanced_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    ¬ SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero := by
  rw [SignedOrbit.scaleByNat_balanced_zero_iff]
  constructor
  · intro h
    constructor
    · intro hz
      exact h (Or.inl hz)
    · intro hd
      exact h (Or.inr hd)
  · intro h hzscaled
    rcases hzscaled with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem abs_scaleByNat_eq_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).abs = DistinctionNat.zero ↔
      z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.scaleByNat_toInt, SignedOrbit.abs_eq_zero_iff_toInt_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hd
    · exact Or.inl hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
  · intro h
    rcases h with hz | hd
    · rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem abs_scaleByNat_ne_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).abs ≠ DistinctionNat.zero ↔
      z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_scaleByNat_eq_zero_iff z d
  constructor
  · intro h
    constructor
    · intro hz
      exact h (hzero.mpr (Or.inl hz))
    · intro hd
      exact h (hzero.mpr (Or.inr hd))
  · intro h hzscaled
    rcases hzero.mp hzscaled with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem abs_mul_ofOrbit_right_eq_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs = DistinctionNat.zero ↔
      z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_eq_zero_iff_toInt_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hz | hd
    · exact Or.inl hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
  · intro h
    rcases h with hz | hd
    · rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem abs_mul_ofOrbit_left_eq_zero_iff
    (d : DistinctionNat) (z : SignedOrbit) :
    (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs = DistinctionNat.zero ↔
      z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_eq_zero_iff_toInt_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hd | hz
    · right
      apply DistinctionNat.toNat_inj
      rw [DistinctionNat.toNat_zero]
      exact_mod_cast hd
    · exact Or.inl hz
  · intro h
    rcases h with hz | hd
    · rw [hz]
      ring
    · rw [hd, DistinctionNat.toNat_zero]
      ring

theorem abs_mul_ofOrbit_right_ne_zero_iff
    (z : SignedOrbit) (d : DistinctionNat) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs ≠ DistinctionNat.zero ↔
      z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_ofOrbit_right_eq_zero_iff z d
  constructor
  · intro h
    constructor
    · intro hz
      exact h (hzero.mpr (Or.inl hz))
    · intro hd
      exact h (hzero.mpr (Or.inr hd))
  · intro h hzprod
    rcases hzero.mp hzprod with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem abs_mul_ofOrbit_left_ne_zero_iff
    (d : DistinctionNat) (z : SignedOrbit) :
    (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs ≠ DistinctionNat.zero ↔
      z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_ofOrbit_left_eq_zero_iff d z
  constructor
  · intro h
    constructor
    · intro hz
      exact h (hzero.mpr (Or.inl hz))
    · intro hd
      exact h (hzero.mpr (Or.inr hd))
  · intro h hzprod
    rcases hzero.mp hzprod with hz | hd
    · exact h.1 hz
    · exact h.2 hd

theorem le_scaleByNat_of_le {z w : SignedOrbit}
    (h : SignedOrbit.le z w) (d : DistinctionNat) :
    SignedOrbit.le (z.scaleByNat d) (w.scaleByNat d) := by
  rw [SignedOrbit.le_iff_toInt_le] at h ⊢
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
  have hdnonneg : 0 ≤ (d.toNat : ℤ) := by exact_mod_cast Nat.zero_le d.toNat
  nlinarith

theorem le_scaleByNat_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.le (z.scaleByNat d) (w.scaleByNat d) ↔
      SignedOrbit.le z w := by
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hdpos : 0 < (d.toNat : ℤ) := by
    have hNatPos : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
    exact_mod_cast hNatPos
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
  constructor <;> intro h <;> nlinarith

theorem lt_scaleByNat_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.lt (z.scaleByNat d) (w.scaleByNat d) ↔
      SignedOrbit.lt z w := by
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hdpos : 0 < (d.toNat : ℤ) := by
    have hNatPos : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
    exact_mod_cast hNatPos
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt,
    SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
  constructor <;> intro h <;> nlinarith

theorem balanced_scaleByNat_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.balanced (z.scaleByNat d) (w.scaleByNat d) ↔
      SignedOrbit.balanced z w := by
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hdpos : 0 < (d.toNat : ℤ) := by
    have hNatPos : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
    exact_mod_cast hNatPos
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
  constructor <;> intro h <;> nlinarith

theorem le_congr_left_of_balanced {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  rw [(SignedOrbit.balanced_iff_toInt_eq a a').mp ha]

theorem le_congr_right_of_balanced {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le a b ↔ SignedOrbit.le a b' := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  rw [(SignedOrbit.balanced_iff_toInt_eq b b').mp hb]

theorem lt_congr_left_of_balanced {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.lt a b ↔ SignedOrbit.lt a' b := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt]
  rw [(SignedOrbit.balanced_iff_toInt_eq a a').mp ha]

theorem lt_congr_right_of_balanced {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt a b ↔ SignedOrbit.lt a b' := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt]
  rw [(SignedOrbit.balanced_iff_toInt_eq b b').mp hb]

theorem le_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b' := by
  exact (SignedOrbit.le_congr_left_of_balanced ha).trans
    (SignedOrbit.le_congr_right_of_balanced hb)

theorem lt_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt a b ↔ SignedOrbit.lt a' b' := by
  exact (SignedOrbit.lt_congr_left_of_balanced ha).trans
    (SignedOrbit.lt_congr_right_of_balanced hb)

/-- Internal comparison selector. It is defined from signed-orbit order and
balanced length, not from the verifier integer display. -/
def cmp (a b : SignedOrbit) : Ordering :=
  if SignedOrbit.balanced a b then
    Ordering.eq
  else if (SignedOrbit.sub b a).nonnegFlag then
    Ordering.lt
  else
    Ordering.gt

theorem cmp_eq_lt_of_lt {a b : SignedOrbit}
    (h : SignedOrbit.lt a b) :
    SignedOrbit.cmp a b = Ordering.lt := by
  have hnotbal : ¬ SignedOrbit.balanced a b := by
    rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.balanced_iff_toInt_eq] at *
    omega
  have hflag : (SignedOrbit.sub b a).nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.sub_toInt]
    rw [SignedOrbit.lt_iff_toInt_lt] at h
    omega
  simp [SignedOrbit.cmp, hnotbal, hflag]

theorem cmp_eq_eq_of_balanced {a b : SignedOrbit}
    (h : SignedOrbit.balanced a b) :
    SignedOrbit.cmp a b = Ordering.eq := by
  simp [SignedOrbit.cmp, h]

theorem cmp_eq_gt_of_gt {a b : SignedOrbit}
    (h : SignedOrbit.lt b a) :
    SignedOrbit.cmp a b = Ordering.gt := by
  have hflag : (SignedOrbit.sub b a).nonnegFlag = false := by
    rw [SignedOrbit.nonnegFlag_eq_false_iff, SignedOrbit.sub_toInt]
    rw [SignedOrbit.lt_iff_toInt_lt] at h
    omega
  have hnotbal : ¬ SignedOrbit.balanced a b := by
    rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.balanced_iff_toInt_eq] at *
    omega
  simp [SignedOrbit.cmp, hflag, hnotbal]

theorem cmp_eq_lt_iff (a b : SignedOrbit) :
    SignedOrbit.cmp a b = Ordering.lt ↔ SignedOrbit.lt a b := by
  constructor
  · intro hcmp
    unfold SignedOrbit.cmp at hcmp
    by_cases hbal : SignedOrbit.balanced a b
    · simp [hbal] at hcmp
    · by_cases hflag : (SignedOrbit.sub b a).nonnegFlag = true
      · rw [SignedOrbit.lt_iff_toInt_lt]
        rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.sub_toInt] at hflag
        rw [SignedOrbit.balanced_iff_toInt_eq] at hbal
        omega
      · simp [hbal, hflag] at hcmp
  · intro hlt
    exact SignedOrbit.cmp_eq_lt_of_lt hlt

theorem cmp_eq_eq_iff (a b : SignedOrbit) :
    SignedOrbit.cmp a b = Ordering.eq ↔ SignedOrbit.balanced a b := by
  constructor
  · intro hcmp
    unfold SignedOrbit.cmp at hcmp
    by_cases hbal : SignedOrbit.balanced a b
    · exact hbal
    · by_cases hflag : (SignedOrbit.sub b a).nonnegFlag = true
      · simp [hbal, hflag] at hcmp
      · simp [hbal, hflag] at hcmp
  · intro hbal
    exact SignedOrbit.cmp_eq_eq_of_balanced hbal

theorem cmp_eq_gt_iff (a b : SignedOrbit) :
    SignedOrbit.cmp a b = Ordering.gt ↔ SignedOrbit.lt b a := by
  constructor
  · intro hcmp
    unfold SignedOrbit.cmp at hcmp
    by_cases hbal : SignedOrbit.balanced a b
    · simp [hbal] at hcmp
    · by_cases hflag : (SignedOrbit.sub b a).nonnegFlag = true
      · simp [hbal, hflag] at hcmp
      · rw [SignedOrbit.lt_iff_toInt_lt]
        have hflagFalse : (SignedOrbit.sub b a).nonnegFlag = false := by
          cases hbranch : (SignedOrbit.sub b a).nonnegFlag with
          | false => rfl
          | true =>
              exfalso
              exact hflag hbranch
        rw [SignedOrbit.nonnegFlag_eq_false_iff, SignedOrbit.sub_toInt] at hflagFalse
        omega
  · intro hgt
    exact SignedOrbit.cmp_eq_gt_of_gt hgt

theorem cmp_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp a b = SignedOrbit.cmp a' b' := by
  cases hcmp : SignedOrbit.cmp a b with
  | lt =>
      have hlt : SignedOrbit.lt a b :=
        (SignedOrbit.cmp_eq_lt_iff a b).mp hcmp
      have hlt' : SignedOrbit.lt a' b' :=
        ((SignedOrbit.lt_congr_left_of_balanced ha).mp
          ((SignedOrbit.lt_congr_right_of_balanced hb).mp hlt))
      exact (SignedOrbit.cmp_eq_lt_of_lt hlt').symm
  | eq =>
      have hbal : SignedOrbit.balanced a b :=
        (SignedOrbit.cmp_eq_eq_iff a b).mp hcmp
      have hbal' : SignedOrbit.balanced a' b' := by
        exact SignedOrbit.balanced_trans
          (SignedOrbit.balanced_symm ha)
          (SignedOrbit.balanced_trans hbal hb)
      exact (SignedOrbit.cmp_eq_eq_of_balanced hbal').symm
  | gt =>
      have hgt : SignedOrbit.lt b a :=
        (SignedOrbit.cmp_eq_gt_iff a b).mp hcmp
      have hgt' : SignedOrbit.lt b' a' :=
        ((SignedOrbit.lt_congr_left_of_balanced hb).mp
          ((SignedOrbit.lt_congr_right_of_balanced ha).mp hgt))
      exact (SignedOrbit.cmp_eq_gt_of_gt hgt').symm

theorem cmp_scaleByNat_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.cmp (z.scaleByNat d) (w.scaleByNat d) =
      SignedOrbit.cmp z w := by
  cases hcmp : SignedOrbit.cmp z w with
  | lt =>
      have hlt : SignedOrbit.lt z w :=
        (SignedOrbit.cmp_eq_lt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_scaleByNat_iff_of_ne_zero z w d hd).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced z w :=
        (SignedOrbit.cmp_eq_eq_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        (SignedOrbit.scaleByNat_congr_of_balanced hbal d)
  | gt =>
      have hgt : SignedOrbit.lt w z :=
        (SignedOrbit.cmp_eq_gt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_scaleByNat_iff_of_ne_zero w z d hd).mpr hgt)

theorem le_mul_ofOrbit_right_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.le
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
      SignedOrbit.le z w := by
  exact (SignedOrbit.le_congr_of_balanced
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat z d)
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat w d)).trans
    (SignedOrbit.le_scaleByNat_iff_of_ne_zero z w d hd)

theorem lt_mul_ofOrbit_right_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.lt
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
      SignedOrbit.lt z w := by
  exact (SignedOrbit.lt_congr_of_balanced
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat z d)
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat w d)).trans
    (SignedOrbit.lt_scaleByNat_iff_of_ne_zero z w d hd)

theorem balanced_mul_ofOrbit_right_iff_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
      SignedOrbit.balanced z w := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt]
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hdpos : 0 < (d.toNat : ℤ) := by
    have hNatPos : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
    exact_mod_cast hNatPos
  constructor <;> intro h <;> nlinarith

theorem cmp_mul_ofOrbit_right_of_ne_zero
    (z w : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.cmp
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) =
      SignedOrbit.cmp z w := by
  exact (SignedOrbit.cmp_congr_of_balanced
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat z d)
      (SignedOrbit.mul_ofOrbit_balanced_scaleByNat w d)).trans
    (SignedOrbit.cmp_scaleByNat_of_ne_zero z w d hd)

theorem le_mul_ofOrbit_left_iff_of_ne_zero
    (d : DistinctionNat) (z w : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.le
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
      SignedOrbit.le z w := by
  exact (SignedOrbit.le_congr_of_balanced
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d z)
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d w)).trans
    (SignedOrbit.le_scaleByNat_iff_of_ne_zero z w d hd)

theorem lt_mul_ofOrbit_left_iff_of_ne_zero
    (d : DistinctionNat) (z w : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.lt
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
      SignedOrbit.lt z w := by
  exact (SignedOrbit.lt_congr_of_balanced
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d z)
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d w)).trans
    (SignedOrbit.lt_scaleByNat_iff_of_ne_zero z w d hd)

theorem balanced_mul_ofOrbit_left_iff_of_ne_zero
    (d : DistinctionNat) (z w : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
      SignedOrbit.balanced z w := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt]
  have hdNat : d.toNat ≠ 0 := by
    intro hzero
    apply hd
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  have hdpos : 0 < (d.toNat : ℤ) := by
    have hNatPos : 0 < d.toNat := Nat.pos_of_ne_zero hdNat
    exact_mod_cast hNatPos
  constructor <;> intro h <;> nlinarith

theorem cmp_mul_ofOrbit_left_of_ne_zero
    (d : DistinctionNat) (z w : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    SignedOrbit.cmp
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) =
      SignedOrbit.cmp z w := by
  exact (SignedOrbit.cmp_congr_of_balanced
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d z)
      (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d w)).trans
    (SignedOrbit.cmp_scaleByNat_of_ne_zero z w d hd)

theorem cmp_mul_left_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.cmp (SignedOrbit.mul a z) (SignedOrbit.mul a w) =
      SignedOrbit.cmp z w := by
  cases hcmp : SignedOrbit.cmp z w with
  | lt =>
      have hlt : SignedOrbit.lt z w :=
        (SignedOrbit.cmp_eq_lt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
          a z w hanonneg ha).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced z w :=
        (SignedOrbit.cmp_eq_eq_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_mul_left_iff_of_not_balanced_zero
          a z w ha).mpr hbal)
  | gt =>
      have hgt : SignedOrbit.lt w z :=
        (SignedOrbit.cmp_eq_gt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
          a w z hanonneg ha).mpr hgt)

theorem cmp_mul_right_of_nonnegFlag_of_not_balanced_zero
    (a z w : SignedOrbit)
    (hanonneg : a.nonnegFlag = true)
    (ha : ¬ SignedOrbit.balanced a SignedOrbit.zero) :
    SignedOrbit.cmp (SignedOrbit.mul z a) (SignedOrbit.mul w a) =
      SignedOrbit.cmp z w := by
  cases hcmp : SignedOrbit.cmp z w with
  | lt =>
      have hlt : SignedOrbit.lt z w :=
        (SignedOrbit.cmp_eq_lt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
          a z w hanonneg ha).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced z w :=
        (SignedOrbit.cmp_eq_eq_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_mul_right_iff_of_not_balanced_zero
          a z w ha).mpr hbal)
  | gt =>
      have hgt : SignedOrbit.lt w z :=
        (SignedOrbit.cmp_eq_gt_iff z w).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
          a w z hanonneg ha).mpr hgt)

theorem cmp_mul_left_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.cmp (SignedOrbit.mul a z) (SignedOrbit.mul a w) =
      SignedOrbit.cmp w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  have ha : ¬ SignedOrbit.balanced a SignedOrbit.zero := by
    intro hzero
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
    omega
  cases hcmp : SignedOrbit.cmp w z with
  | lt =>
      have hlt : SignedOrbit.lt w z :=
        (SignedOrbit.cmp_eq_lt_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_mul_left_iff_of_negativeFlag a z w haneg).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced w z :=
        (SignedOrbit.cmp_eq_eq_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_mul_left_iff_of_not_balanced_zero
          a z w ha).mpr (SignedOrbit.balanced_symm hbal))
  | gt =>
      have hgt : SignedOrbit.lt z w :=
        (SignedOrbit.cmp_eq_gt_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_mul_left_iff_of_negativeFlag a w z haneg).mpr hgt)

theorem cmp_mul_right_of_negativeFlag
    (a z w : SignedOrbit)
    (haneg : a.negativeFlag = true) :
    SignedOrbit.cmp (SignedOrbit.mul z a) (SignedOrbit.mul w a) =
      SignedOrbit.cmp w z := by
  have hanegInt : a.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg a).mp haneg
  have ha : ¬ SignedOrbit.balanced a SignedOrbit.zero := by
    intro hzero
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
    omega
  cases hcmp : SignedOrbit.cmp w z with
  | lt =>
      have hlt : SignedOrbit.lt w z :=
        (SignedOrbit.cmp_eq_lt_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_mul_right_iff_of_negativeFlag a z w haneg).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced w z :=
        (SignedOrbit.cmp_eq_eq_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_mul_right_iff_of_not_balanced_zero
          a z w ha).mpr (SignedOrbit.balanced_symm hbal))
  | gt =>
      have hgt : SignedOrbit.lt z w :=
        (SignedOrbit.cmp_eq_gt_iff w z).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_mul_right_iff_of_negativeFlag a w z haneg).mpr hgt)

theorem nonnegFlag_mul_of_nonnegFlag_of_nonnegFlag
    (z w : SignedOrbit)
    (hz : z.nonnegFlag = true) (hw : w.nonnegFlag = true) :
    (SignedOrbit.mul z w).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.mul_toInt]
  have hznonneg : 0 ≤ z.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff z).mp hz
  have hwnonneg : 0 ≤ w.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff w).mp hw
  nlinarith

theorem nonnegFlag_mul_of_negativeFlag_of_negativeFlag
    (z w : SignedOrbit)
    (hz : z.negativeFlag = true) (hw : w.negativeFlag = true) :
    (SignedOrbit.mul z w).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.mul_toInt]
  have hzneg : z.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg z).mp hz
  have hwneg : w.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg w).mp hw
  nlinarith

theorem negativeFlag_mul_of_nonnegFlag_of_not_balanced_zero_of_negativeFlag
    (z w : SignedOrbit)
    (hz : z.nonnegFlag = true)
    (hznz : ¬ SignedOrbit.balanced z SignedOrbit.zero)
    (hw : w.negativeFlag = true) :
    (SignedOrbit.mul z w).negativeFlag = true := by
  rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg, SignedOrbit.mul_toInt]
  have hznonneg : 0 ≤ z.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff z).mp hz
  have hznzInt : z.toInt ≠ 0 := by
    intro hzero
    exact hznz (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hzpos : 0 < z.toInt := by omega
  have hwneg : w.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg w).mp hw
  nlinarith

theorem negativeFlag_mul_of_negativeFlag_of_nonnegFlag_of_not_balanced_zero
    (z w : SignedOrbit)
    (hz : z.negativeFlag = true)
    (hw : w.nonnegFlag = true)
    (hwnz : ¬ SignedOrbit.balanced w SignedOrbit.zero) :
    (SignedOrbit.mul z w).negativeFlag = true := by
  rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg, SignedOrbit.mul_toInt]
  have hzneg : z.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg z).mp hz
  have hwnonneg : 0 ≤ w.toInt :=
    (SignedOrbit.nonnegFlag_eq_true_iff w).mp hw
  have hwnzInt : w.toInt ≠ 0 := by
    intro hzero
    exact hwnz (by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzero)
  have hwpos : 0 < w.toInt := by omega
  nlinarith

theorem negativeFlag_mul_iff
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).negativeFlag = true ↔
      (z.nonnegFlag = true ∧
          ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
          w.negativeFlag = true) ∨
        (z.negativeFlag = true ∧
          w.nonnegFlag = true ∧
          ¬ SignedOrbit.balanced w SignedOrbit.zero) := by
  constructor
  · intro hprod
    have hprodInt : z.toInt * w.toInt < 0 := by
      rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg,
        SignedOrbit.mul_toInt] at hprod
      exact hprod
    rcases SignedOrbit.signFlags_exhaustive z with hznonneg | hzneg
    · left
      have hzNonnegInt : 0 ≤ z.toInt :=
        (SignedOrbit.nonnegFlag_eq_true_iff z).mp hznonneg
      have hznz : ¬ SignedOrbit.balanced z SignedOrbit.zero := by
        intro hzero
        rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
        rw [hzero] at hprodInt
        nlinarith
      have hwNegInt : w.toInt < 0 := by nlinarith
      have hwneg : w.negativeFlag = true :=
        (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg w).mpr hwNegInt
      exact ⟨hznonneg, hznz, hwneg⟩
    · right
      have hzNegInt : z.toInt < 0 :=
        (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg z).mp hzneg
      have hwPosInt : 0 < w.toInt := by nlinarith
      have hwnonneg : w.nonnegFlag = true :=
        (SignedOrbit.nonnegFlag_eq_true_iff w).mpr (le_of_lt hwPosInt)
      have hwnz : ¬ SignedOrbit.balanced w SignedOrbit.zero := by
        intro hzero
        rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
        rw [hzero] at hprodInt
        nlinarith
      exact ⟨hzneg, hwnonneg, hwnz⟩
  · intro h
    rcases h with hleft | hright
    · exact SignedOrbit.negativeFlag_mul_of_nonnegFlag_of_not_balanced_zero_of_negativeFlag
        z w hleft.1 hleft.2.1 hleft.2.2
    · exact SignedOrbit.negativeFlag_mul_of_negativeFlag_of_nonnegFlag_of_not_balanced_zero
        z w hright.1 hright.2.1 hright.2.2

theorem nonnegFlag_mul_iff_not_strict_opposite_sign
    (z w : SignedOrbit) :
    (SignedOrbit.mul z w).nonnegFlag = true ↔
      ¬ ((z.nonnegFlag = true ∧
              ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
              w.negativeFlag = true) ∨
            (z.negativeFlag = true ∧
              w.nonnegFlag = true ∧
              ¬ SignedOrbit.balanced w SignedOrbit.zero)) := by
  constructor
  · intro hnonneg hstrict
    have hneg : (SignedOrbit.mul z w).negativeFlag = true :=
      (SignedOrbit.negativeFlag_mul_iff z w).mpr hstrict
    have hnonnegFalse : (SignedOrbit.mul z w).nonnegFlag = false :=
      (SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false
        (SignedOrbit.mul z w)).mp hneg
    rw [hnonneg] at hnonnegFalse
    contradiction
  · intro hnot
    cases hnonneg : (SignedOrbit.mul z w).nonnegFlag with
    | false =>
        have hneg : (SignedOrbit.mul z w).negativeFlag = true := by
          rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
          exact hnonneg
        exact False.elim (hnot ((SignedOrbit.negativeFlag_mul_iff z w).mp hneg))
    | true =>
        rfl

theorem nonnegFlag_mul_of_balanced_zero_left
    (z w : SignedOrbit)
    (hz : SignedOrbit.balanced z SignedOrbit.zero) :
    (SignedOrbit.mul z w).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hz
  rw [hz]
  omega

theorem nonnegFlag_mul_of_balanced_zero_right
    (z w : SignedOrbit)
    (hw : SignedOrbit.balanced w SignedOrbit.zero) :
    (SignedOrbit.mul z w).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hw
  rw [hw]
  omega

theorem negativeFlag_mul_eq_false_of_balanced_zero_left
    (z w : SignedOrbit)
    (hz : SignedOrbit.balanced z SignedOrbit.zero) :
    (SignedOrbit.mul z w).negativeFlag = false := by
  have hnonneg := SignedOrbit.nonnegFlag_mul_of_balanced_zero_left z w hz
  cases hneg : (SignedOrbit.mul z w).negativeFlag
  · rfl
  · have hnonnegFalse : (SignedOrbit.mul z w).nonnegFlag = false :=
      (SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false
        (SignedOrbit.mul z w)).mp hneg
    rw [hnonneg] at hnonnegFalse
    contradiction

theorem negativeFlag_mul_eq_false_of_balanced_zero_right
    (z w : SignedOrbit)
    (hw : SignedOrbit.balanced w SignedOrbit.zero) :
    (SignedOrbit.mul z w).negativeFlag = false := by
  have hnonneg := SignedOrbit.nonnegFlag_mul_of_balanced_zero_right z w hw
  cases hneg : (SignedOrbit.mul z w).negativeFlag
  · rfl
  · have hnonnegFalse : (SignedOrbit.mul z w).nonnegFlag = false :=
      (SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false
        (SignedOrbit.mul z w)).mp hneg
    rw [hnonneg] at hnonnegFalse
    contradiction

theorem mul_balanced_zero_of_balanced_zero_left
    (z w : SignedOrbit)
    (hz : SignedOrbit.balanced z SignedOrbit.zero) :
    SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero :=
  (SignedOrbit.mul_balanced_zero_iff z w).mpr (Or.inl hz)

theorem mul_balanced_zero_of_balanced_zero_right
    (z w : SignedOrbit)
    (hw : SignedOrbit.balanced w SignedOrbit.zero) :
    SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero :=
  (SignedOrbit.mul_balanced_zero_iff z w).mpr (Or.inr hw)

theorem abs_mul_eq_zero_of_balanced_zero_left
    (z w : SignedOrbit)
    (hz : SignedOrbit.balanced z SignedOrbit.zero) :
    (SignedOrbit.mul z w).abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hz
  rw [hz]
  ring

theorem abs_mul_eq_zero_of_balanced_zero_right
    (z w : SignedOrbit)
    (hw : SignedOrbit.balanced w SignedOrbit.zero) :
    (SignedOrbit.mul z w).abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hw
  rw [hw]
  ring

theorem mul_congr_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a' b') := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, ha, hb]

theorem mul_congr_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a' b) := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, ha]

theorem mul_congr_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a b') := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, hb]

theorem nonnegFlag_mul_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).nonnegFlag =
      (SignedOrbit.mul a' b').nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem nonnegFlag_mul_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.mul a b).nonnegFlag =
      (SignedOrbit.mul a' b).nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem nonnegFlag_mul_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).nonnegFlag =
      (SignedOrbit.mul a b').nonnegFlag :=
  SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem negativeFlag_mul_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).negativeFlag =
      (SignedOrbit.mul a' b').negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem negativeFlag_mul_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.mul a b).negativeFlag =
      (SignedOrbit.mul a' b).negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem negativeFlag_mul_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).negativeFlag =
      (SignedOrbit.mul a b').negativeFlag :=
  SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem abs_mul_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs = (SignedOrbit.mul a' b').abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb
  rw [ha, hb]

theorem abs_mul_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.mul a b).abs = (SignedOrbit.mul a' b).abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha
  rw [ha]

theorem abs_mul_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs = (SignedOrbit.mul a b').abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at hb
  rw [hb]

theorem mul_balanced_zero_iff_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.mul a' b) SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.zero_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha
  rw [ha]

theorem mul_balanced_zero_iff_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.mul a b') SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.zero_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at hb
  rw [hb]

theorem abs_mul_eq_zero_iff_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.mul a' b).abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha
  rw [ha]

theorem abs_mul_eq_zero_iff_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.mul a b').abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at hb
  rw [hb]

theorem abs_mul_ne_zero_iff_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.mul a' b).abs ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_eq_zero_iff_of_balanced_left
    (a := a) (a' := a') (b := b) ha
  constructor
  · intro h hright
    exact h (hzero.mpr hright)
  · intro h hleft
    exact h (hzero.mp hleft)

theorem abs_mul_ne_zero_iff_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.mul a b').abs ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_eq_zero_iff_of_balanced_right
    (a := a) (b := b) (b' := b') hb
  constructor
  · intro h hright
    exact h (hzero.mpr hright)
  · intro h hleft
    exact h (hzero.mp hleft)

theorem mul_balanced_zero_iff_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.mul a' b') SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.zero_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb
  rw [ha, hb]

theorem abs_mul_eq_zero_iff_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.mul a' b').abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb
  rw [ha, hb]

theorem abs_mul_ne_zero_iff_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.mul a' b').abs ≠ DistinctionNat.zero := by
  have hzero := SignedOrbit.abs_mul_eq_zero_iff_of_balanced ha hb
  constructor
  · intro h hright
    exact h (hzero.mpr hright)
  · intro h hleft
    exact h (hzero.mp hleft)

theorem le_product_left_factor_iff_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.le (SignedOrbit.mul a b) c ↔
      SignedOrbit.le (SignedOrbit.mul a' b) c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem le_product_right_factor_iff_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le (SignedOrbit.mul a b) c ↔
      SignedOrbit.le (SignedOrbit.mul a b') c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem le_of_product_left_factor_iff_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.le c (SignedOrbit.mul a b) ↔
      SignedOrbit.le c (SignedOrbit.mul a' b) :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem le_of_product_right_factor_iff_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le c (SignedOrbit.mul a b) ↔
      SignedOrbit.le c (SignedOrbit.mul a b') :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem lt_product_left_factor_iff_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.lt (SignedOrbit.mul a b) c ↔
      SignedOrbit.lt (SignedOrbit.mul a' b) c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem lt_product_right_factor_iff_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt (SignedOrbit.mul a b) c ↔
      SignedOrbit.lt (SignedOrbit.mul a b') c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem lt_of_product_left_factor_iff_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.lt c (SignedOrbit.mul a b) ↔
      SignedOrbit.lt c (SignedOrbit.mul a' b) :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem lt_of_product_right_factor_iff_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt c (SignedOrbit.mul a b) ↔
      SignedOrbit.lt c (SignedOrbit.mul a b') :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem cmp_product_left_factor_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.cmp (SignedOrbit.mul a b) c =
      SignedOrbit.cmp (SignedOrbit.mul a' b) c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced_left ha) hc

theorem cmp_product_right_factor_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp (SignedOrbit.mul a b) c =
      SignedOrbit.cmp (SignedOrbit.mul a b') c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced_right hb) hc

theorem cmp_of_product_left_factor_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.cmp c (SignedOrbit.mul a b) =
      SignedOrbit.cmp c (SignedOrbit.mul a' b) := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.mul_congr_of_balanced_left ha)

theorem cmp_of_product_right_factor_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp c (SignedOrbit.mul a b) =
      SignedOrbit.cmp c (SignedOrbit.mul a b') := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.mul_congr_of_balanced_right hb)

theorem le_product_factors_iff_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le (SignedOrbit.mul a b) c ↔
      SignedOrbit.le (SignedOrbit.mul a' b') c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem le_of_product_factors_iff_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le c (SignedOrbit.mul a b) ↔
      SignedOrbit.le c (SignedOrbit.mul a' b') :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem lt_product_factors_iff_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt (SignedOrbit.mul a b) c ↔
      SignedOrbit.lt (SignedOrbit.mul a' b') c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem lt_of_product_factors_iff_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt c (SignedOrbit.mul a b) ↔
      SignedOrbit.lt c (SignedOrbit.mul a' b') :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem cmp_product_factors_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp (SignedOrbit.mul a b) c =
      SignedOrbit.cmp (SignedOrbit.mul a' b') c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb) hc

theorem cmp_of_product_factors_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp c (SignedOrbit.mul a b) =
      SignedOrbit.cmp c (SignedOrbit.mul a' b') := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.mul_congr_of_balanced ha hb)

theorem le_products_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.le (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
      SignedOrbit.le (SignedOrbit.mul a' b') (SignedOrbit.mul c' d') :=
  SignedOrbit.le_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)
    (SignedOrbit.mul_congr_of_balanced hc hd)

theorem lt_products_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.lt (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
      SignedOrbit.lt (SignedOrbit.mul a' b') (SignedOrbit.mul c' d') :=
  SignedOrbit.lt_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)
    (SignedOrbit.mul_congr_of_balanced hc hd)

theorem cmp_products_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.cmp (SignedOrbit.mul a b) (SignedOrbit.mul c d) =
      SignedOrbit.cmp (SignedOrbit.mul a' b') (SignedOrbit.mul c' d') :=
  SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.mul_congr_of_balanced ha hb)
    (SignedOrbit.mul_congr_of_balanced hc hd)

theorem balanced_product_left_factor_iff_of_balanced
    {a a' b c : SignedOrbit} (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
      SignedOrbit.balanced (SignedOrbit.mul a' b) c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha
  rw [ha]

theorem balanced_product_right_factor_iff_of_balanced
    {a b b' c : SignedOrbit} (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
      SignedOrbit.balanced (SignedOrbit.mul a b') c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at hb
  rw [hb]

theorem balanced_product_factors_iff_of_balanced
    {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
      SignedOrbit.balanced (SignedOrbit.mul a' b') c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb
  rw [ha, hb]

theorem balanced_products_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
      SignedOrbit.balanced (SignedOrbit.mul a' b') (SignedOrbit.mul c' d') := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, SignedOrbit.mul_toInt,
    SignedOrbit.mul_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb hc hd
  rw [ha, hb, hc, hd]

theorem le_sub_left_input_iff_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.le (SignedOrbit.sub a b) c ↔
      SignedOrbit.le (SignedOrbit.sub a' b) c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem le_sub_right_input_iff_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le (SignedOrbit.sub a b) c ↔
      SignedOrbit.le (SignedOrbit.sub a b') c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem le_of_sub_left_input_iff_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.le c (SignedOrbit.sub a b) ↔
      SignedOrbit.le c (SignedOrbit.sub a' b) :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem le_of_sub_right_input_iff_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le c (SignedOrbit.sub a b) ↔
      SignedOrbit.le c (SignedOrbit.sub a b') :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem lt_sub_left_input_iff_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.lt (SignedOrbit.sub a b) c ↔
      SignedOrbit.lt (SignedOrbit.sub a' b) c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem lt_sub_right_input_iff_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt (SignedOrbit.sub a b) c ↔
      SignedOrbit.lt (SignedOrbit.sub a b') c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem lt_of_sub_left_input_iff_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.lt c (SignedOrbit.sub a b) ↔
      SignedOrbit.lt c (SignedOrbit.sub a' b) :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem lt_of_sub_right_input_iff_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt c (SignedOrbit.sub a b) ↔
      SignedOrbit.lt c (SignedOrbit.sub a b') :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem cmp_sub_left_input_of_balanced {a a' b c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.cmp (SignedOrbit.sub a b) c =
      SignedOrbit.cmp (SignedOrbit.sub a' b) c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha) hc

theorem cmp_sub_right_input_of_balanced {a b b' c : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp (SignedOrbit.sub a b) c =
      SignedOrbit.cmp (SignedOrbit.sub a b') c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb) hc

theorem cmp_of_sub_left_input_of_balanced {c a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    SignedOrbit.cmp c (SignedOrbit.sub a b) =
      SignedOrbit.cmp c (SignedOrbit.sub a' b) := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem cmp_of_sub_right_input_of_balanced {c a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp c (SignedOrbit.sub a b) =
      SignedOrbit.cmp c (SignedOrbit.sub a b') := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem le_sub_inputs_iff_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le (SignedOrbit.sub a b) c ↔
      SignedOrbit.le (SignedOrbit.sub a' b') c :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem le_of_sub_inputs_iff_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le c (SignedOrbit.sub a b) ↔
      SignedOrbit.le c (SignedOrbit.sub a' b') :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem lt_sub_inputs_iff_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt (SignedOrbit.sub a b) c ↔
      SignedOrbit.lt (SignedOrbit.sub a' b') c :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem lt_of_sub_inputs_iff_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.lt c (SignedOrbit.sub a b) ↔
      SignedOrbit.lt c (SignedOrbit.sub a' b') :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem cmp_sub_inputs_of_balanced {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp (SignedOrbit.sub a b) c =
      SignedOrbit.cmp (SignedOrbit.sub a' b') c := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb) hc

theorem cmp_of_sub_inputs_of_balanced {c a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.cmp c (SignedOrbit.sub a b) =
      SignedOrbit.cmp c (SignedOrbit.sub a' b') := by
  have hc : SignedOrbit.balanced c c := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hc
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem le_subtractions_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.le (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
      SignedOrbit.le (SignedOrbit.sub a' b') (SignedOrbit.sub c' d') :=
  SignedOrbit.le_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)
    (SignedOrbit.sub_congr_of_balanced hc hd)

theorem lt_subtractions_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.lt (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
      SignedOrbit.lt (SignedOrbit.sub a' b') (SignedOrbit.sub c' d') :=
  SignedOrbit.lt_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)
    (SignedOrbit.sub_congr_of_balanced hc hd)

theorem cmp_subtractions_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.cmp (SignedOrbit.sub a b) (SignedOrbit.sub c d) =
      SignedOrbit.cmp (SignedOrbit.sub a' b') (SignedOrbit.sub c' d') :=
  SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)
    (SignedOrbit.sub_congr_of_balanced hc hd)

theorem balanced_sub_left_input_iff_of_balanced
    {a a' b c : SignedOrbit} (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
      SignedOrbit.balanced (SignedOrbit.sub a' b) c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.sub_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha
  rw [ha]

theorem balanced_sub_right_input_iff_of_balanced
    {a b b' c : SignedOrbit} (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
      SignedOrbit.balanced (SignedOrbit.sub a b') c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.sub_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at hb
  rw [hb]

theorem balanced_sub_inputs_iff_of_balanced
    {a a' b b' c : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
      SignedOrbit.balanced (SignedOrbit.sub a' b') c := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.sub_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb
  rw [ha, hb]

theorem balanced_subtractions_iff_of_balanced
    {a a' b b' c c' d d' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b')
    (hc : SignedOrbit.balanced c c') (hd : SignedOrbit.balanced d d') :
    SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
      SignedOrbit.balanced (SignedOrbit.sub a' b') (SignedOrbit.sub c' d') := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.sub_toInt, SignedOrbit.sub_toInt,
    SignedOrbit.sub_toInt]
  rw [SignedOrbit.balanced_iff_toInt_eq] at ha hb hc hd
  rw [ha, hb, hc, hd]

theorem sub_balanced_zero_iff_of_balanced_left
    {a a' b : SignedOrbit} (ha : SignedOrbit.balanced a a') :
    SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.sub a' b) SignedOrbit.zero :=
  SignedOrbit.balanced_sub_left_input_iff_of_balanced
    (c := SignedOrbit.zero) ha

theorem sub_balanced_zero_iff_of_balanced_right
    {a b b' : SignedOrbit} (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.sub a b') SignedOrbit.zero :=
  SignedOrbit.balanced_sub_right_input_iff_of_balanced
    (c := SignedOrbit.zero) hb

theorem sub_balanced_zero_iff_of_balanced
    {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      SignedOrbit.balanced (SignedOrbit.sub a' b') SignedOrbit.zero :=
  SignedOrbit.balanced_sub_inputs_iff_of_balanced
    (c := SignedOrbit.zero) ha hb

theorem sub_not_balanced_zero_iff_of_balanced_left
    {a a' b : SignedOrbit} (ha : SignedOrbit.balanced a a') :
    ¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced (SignedOrbit.sub a' b) SignedOrbit.zero := by
  rw [SignedOrbit.sub_balanced_zero_iff_of_balanced_left ha]

theorem sub_not_balanced_zero_iff_of_balanced_right
    {a b b' : SignedOrbit} (hb : SignedOrbit.balanced b b') :
    ¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced (SignedOrbit.sub a b') SignedOrbit.zero := by
  rw [SignedOrbit.sub_balanced_zero_iff_of_balanced_right hb]

theorem sub_not_balanced_zero_iff_of_balanced
    {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    ¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced (SignedOrbit.sub a' b') SignedOrbit.zero := by
  rw [SignedOrbit.sub_balanced_zero_iff_of_balanced ha hb]

theorem sub_balanced_zero_iff_balanced (a b : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      SignedOrbit.balanced a b := by
  rw [SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.zero_toInt,
    SignedOrbit.balanced_iff_toInt_eq]
  omega

theorem sub_not_balanced_zero_iff_not_balanced (a b : SignedOrbit) :
    ¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced a b := by
  rw [SignedOrbit.sub_balanced_zero_iff_balanced a b]

theorem abs_sub_eq_zero_iff_balanced (a b : SignedOrbit) :
    (SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
      SignedOrbit.balanced a b := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.sub_toInt, SignedOrbit.balanced_iff_toInt_eq]
  omega

theorem abs_sub_ne_zero_iff_not_balanced (a b : SignedOrbit) :
    (SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
      ¬ SignedOrbit.balanced a b := by
  rw [← SignedOrbit.abs_sub_eq_zero_iff_balanced a b]

theorem sub_self_balanced_zero (a : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.sub a a) SignedOrbit.zero :=
  (SignedOrbit.sub_balanced_zero_iff_balanced a a).mpr (by
    rw [SignedOrbit.balanced_iff_toInt_eq])

theorem abs_sub_self_eq_zero (a : SignedOrbit) :
    (SignedOrbit.sub a a).abs = DistinctionNat.zero :=
  (SignedOrbit.abs_sub_eq_zero_iff_balanced a a).mpr (by
    rw [SignedOrbit.balanced_iff_toInt_eq])

theorem sub_zero_balanced (a : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.sub a SignedOrbit.zero) a := by
  rw [SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
  omega

theorem zero_sub_balanced_negate (a : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.sub SignedOrbit.zero a)
      (SignedOrbit.negate a) := by
  rw [SignedOrbit.balanced_iff_toInt_eq,
    SignedOrbit.sub_toInt, SignedOrbit.zero_toInt,
    SignedOrbit.negate_toInt]
  omega

theorem abs_sub_zero_eq (a : SignedOrbit) :
    (SignedOrbit.sub a SignedOrbit.zero).abs = a.abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
  simp

theorem abs_zero_sub_eq (a : SignedOrbit) :
    (SignedOrbit.sub SignedOrbit.zero a).abs = a.abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
  have h : 0 - a.toInt = -a.toInt := by omega
  rw [h, Int.natAbs_neg]

theorem le_sub_zero_left_iff (a b : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.sub a SignedOrbit.zero) b ↔
      SignedOrbit.le a b :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.sub_zero_balanced a)

theorem le_sub_zero_right_iff (a b : SignedOrbit) :
    SignedOrbit.le b (SignedOrbit.sub a SignedOrbit.zero) ↔
      SignedOrbit.le b a :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.sub_zero_balanced a)

theorem lt_sub_zero_left_iff (a b : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.sub a SignedOrbit.zero) b ↔
      SignedOrbit.lt a b :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.sub_zero_balanced a)

theorem lt_sub_zero_right_iff (a b : SignedOrbit) :
    SignedOrbit.lt b (SignedOrbit.sub a SignedOrbit.zero) ↔
      SignedOrbit.lt b a :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.sub_zero_balanced a)

theorem cmp_sub_zero_left (a b : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.sub a SignedOrbit.zero) b =
      SignedOrbit.cmp a b := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_zero_balanced a) hb

theorem cmp_sub_zero_right (a b : SignedOrbit) :
    SignedOrbit.cmp b (SignedOrbit.sub a SignedOrbit.zero) =
      SignedOrbit.cmp b a := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hb
    (SignedOrbit.sub_zero_balanced a)

theorem le_zero_sub_left_iff (a b : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.sub SignedOrbit.zero a) b ↔
      SignedOrbit.le (SignedOrbit.negate a) b :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.zero_sub_balanced_negate a)

theorem le_zero_sub_right_iff (a b : SignedOrbit) :
    SignedOrbit.le b (SignedOrbit.sub SignedOrbit.zero a) ↔
      SignedOrbit.le b (SignedOrbit.negate a) :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.zero_sub_balanced_negate a)

theorem lt_zero_sub_left_iff (a b : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.sub SignedOrbit.zero a) b ↔
      SignedOrbit.lt (SignedOrbit.negate a) b :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.zero_sub_balanced_negate a)

theorem lt_zero_sub_right_iff (a b : SignedOrbit) :
    SignedOrbit.lt b (SignedOrbit.sub SignedOrbit.zero a) ↔
      SignedOrbit.lt b (SignedOrbit.negate a) :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.zero_sub_balanced_negate a)

theorem cmp_zero_sub_left (a b : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.sub SignedOrbit.zero a) b =
      SignedOrbit.cmp (SignedOrbit.negate a) b := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.zero_sub_balanced_negate a) hb

theorem cmp_zero_sub_right (a b : SignedOrbit) :
    SignedOrbit.cmp b (SignedOrbit.sub SignedOrbit.zero a) =
      SignedOrbit.cmp b (SignedOrbit.negate a) := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hb
    (SignedOrbit.zero_sub_balanced_negate a)

theorem le_sub_self_left_iff (a b : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.sub a a) b ↔
      SignedOrbit.le SignedOrbit.zero b :=
  SignedOrbit.le_congr_left_of_balanced
    (SignedOrbit.sub_self_balanced_zero a)

theorem le_sub_self_right_iff (a b : SignedOrbit) :
    SignedOrbit.le b (SignedOrbit.sub a a) ↔
      SignedOrbit.le b SignedOrbit.zero :=
  SignedOrbit.le_congr_right_of_balanced
    (SignedOrbit.sub_self_balanced_zero a)

theorem lt_sub_self_left_iff (a b : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.sub a a) b ↔
      SignedOrbit.lt SignedOrbit.zero b :=
  SignedOrbit.lt_congr_left_of_balanced
    (SignedOrbit.sub_self_balanced_zero a)

theorem lt_sub_self_right_iff (a b : SignedOrbit) :
    SignedOrbit.lt b (SignedOrbit.sub a a) ↔
      SignedOrbit.lt b SignedOrbit.zero :=
  SignedOrbit.lt_congr_right_of_balanced
    (SignedOrbit.sub_self_balanced_zero a)

theorem cmp_sub_self_left (a b : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.sub a a) b =
      SignedOrbit.cmp SignedOrbit.zero b := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced
    (SignedOrbit.sub_self_balanced_zero a) hb

theorem cmp_sub_self_right (a b : SignedOrbit) :
    SignedOrbit.cmp b (SignedOrbit.sub a a) =
      SignedOrbit.cmp b SignedOrbit.zero := by
  have hb : SignedOrbit.balanced b b := by
    rw [SignedOrbit.balanced_iff_toInt_eq]
  exact SignedOrbit.cmp_congr_of_balanced hb
    (SignedOrbit.sub_self_balanced_zero a)

theorem nonnegFlag_sub_zero (a : SignedOrbit) :
    (SignedOrbit.sub a SignedOrbit.zero).nonnegFlag = a.nonnegFlag := by
  cases hflag : a.nonnegFlag
  · rw [SignedOrbit.nonnegFlag_eq_false_iff,
      SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
    have hneg : a.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff a).mp hflag
    omega
  · rw [SignedOrbit.nonnegFlag_eq_true_iff,
      SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
    have hnonneg : 0 ≤ a.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff a).mp hflag
    omega

theorem negativeFlag_sub_zero (a : SignedOrbit) :
    (SignedOrbit.sub a SignedOrbit.zero).negativeFlag = a.negativeFlag := by
  unfold SignedOrbit.negativeFlag
  rw [SignedOrbit.nonnegFlag_sub_zero a]

theorem nonnegFlag_zero_sub (a : SignedOrbit) :
    (SignedOrbit.sub SignedOrbit.zero a).nonnegFlag =
      (SignedOrbit.negate a).nonnegFlag := by
  cases hflag : (SignedOrbit.negate a).nonnegFlag
  · rw [SignedOrbit.nonnegFlag_eq_false_iff,
      SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
    have hneg : (SignedOrbit.negate a).toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff (SignedOrbit.negate a)).mp hflag
    rw [SignedOrbit.negate_toInt] at hneg
    omega
  · rw [SignedOrbit.nonnegFlag_eq_true_iff,
      SignedOrbit.sub_toInt, SignedOrbit.zero_toInt]
    have hnonneg : 0 ≤ (SignedOrbit.negate a).toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff (SignedOrbit.negate a)).mp hflag
    rw [SignedOrbit.negate_toInt] at hnonneg
    omega

theorem negativeFlag_zero_sub (a : SignedOrbit) :
    (SignedOrbit.sub SignedOrbit.zero a).negativeFlag =
      (SignedOrbit.negate a).negativeFlag := by
  unfold SignedOrbit.negativeFlag
  rw [SignedOrbit.nonnegFlag_zero_sub a]

theorem nonnegFlag_sub_self (a : SignedOrbit) :
    (SignedOrbit.sub a a).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.sub_toInt]
  omega

theorem negativeFlag_sub_self (a : SignedOrbit) :
    (SignedOrbit.sub a a).negativeFlag = false := by
  unfold SignedOrbit.negativeFlag
  rw [SignedOrbit.nonnegFlag_sub_self a]
  rfl

theorem nonnegFlag_sub_iff_le (a b : SignedOrbit) :
    (SignedOrbit.sub a b).nonnegFlag = true ↔
      SignedOrbit.le b a := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff,
    SignedOrbit.sub_toInt, SignedOrbit.le_iff_toInt_le]
  omega

theorem nonnegFlag_sub_eq_false_iff_lt (a b : SignedOrbit) :
    (SignedOrbit.sub a b).nonnegFlag = false ↔
      SignedOrbit.lt a b := by
  rw [SignedOrbit.nonnegFlag_eq_false_iff,
    SignedOrbit.sub_toInt, SignedOrbit.lt_iff_toInt_lt]
  omega

theorem negativeFlag_sub_iff_lt (a b : SignedOrbit) :
    (SignedOrbit.sub a b).negativeFlag = true ↔
      SignedOrbit.lt a b := by
  rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg,
    SignedOrbit.sub_toInt, SignedOrbit.lt_iff_toInt_lt]
  omega

theorem negativeFlag_sub_eq_false_iff_le (a b : SignedOrbit) :
    (SignedOrbit.sub a b).negativeFlag = false ↔
      SignedOrbit.le b a := by
  rw [SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true,
    SignedOrbit.nonnegFlag_sub_iff_le]

theorem le_iff_nonnegFlag_sub (a b : SignedOrbit) :
    SignedOrbit.le a b ↔
      (SignedOrbit.sub b a).nonnegFlag = true :=
  (SignedOrbit.nonnegFlag_sub_iff_le b a).symm

theorem lt_iff_nonnegFlag_sub_eq_false (a b : SignedOrbit) :
    SignedOrbit.lt a b ↔
      (SignedOrbit.sub a b).nonnegFlag = false :=
  (SignedOrbit.nonnegFlag_sub_eq_false_iff_lt a b).symm

theorem lt_iff_negativeFlag_sub (a b : SignedOrbit) :
    SignedOrbit.lt a b ↔
      (SignedOrbit.sub a b).negativeFlag = true :=
  (SignedOrbit.negativeFlag_sub_iff_lt a b).symm

theorem le_iff_negativeFlag_sub_eq_false (a b : SignedOrbit) :
    SignedOrbit.le a b ↔
      (SignedOrbit.sub b a).negativeFlag = false :=
  (SignedOrbit.negativeFlag_sub_eq_false_iff_le b a).symm

theorem nonnegFlag_mul_ofOrbit_right_of_ne_zero
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).nonnegFlag =
      z.nonnegFlag :=
  (SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.mul_ofOrbit_balanced_scaleByNat z d)).trans
      (SignedOrbit.nonnegFlag_scaleByNat_of_ne_zero z d hd)

theorem negativeFlag_mul_ofOrbit_right_of_ne_zero
    (z : SignedOrbit) (d : DistinctionNat) (hd : d ≠ DistinctionNat.zero) :
    (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).negativeFlag =
      z.negativeFlag :=
  (SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.mul_ofOrbit_balanced_scaleByNat z d)).trans
      (SignedOrbit.negativeFlag_scaleByNat_of_ne_zero z d hd)

theorem nonnegFlag_mul_ofOrbit_left_of_ne_zero
    (d : DistinctionNat) (z : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).nonnegFlag =
      z.nonnegFlag :=
  (SignedOrbit.nonnegFlag_eq_of_balanced
    (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d z)).trans
      (SignedOrbit.nonnegFlag_scaleByNat_of_ne_zero z d hd)

theorem negativeFlag_mul_ofOrbit_left_of_ne_zero
    (d : DistinctionNat) (z : SignedOrbit) (hd : d ≠ DistinctionNat.zero) :
    (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).negativeFlag =
      z.negativeFlag :=
  (SignedOrbit.negativeFlag_eq_of_balanced
    (SignedOrbit.ofOrbit_mul_balanced_scaleByNat d z)).trans
      (SignedOrbit.negativeFlag_scaleByNat_of_ne_zero z d hd)

/-! ## Order transport through signed-orbit operations -/

theorem balanced_add_left_iff (a b c : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
      SignedOrbit.balanced a b := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem balanced_add_right_iff (a b c : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
      SignedOrbit.balanced a b := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem balanced_negate_iff (a b : SignedOrbit) :
    SignedOrbit.balanced (SignedOrbit.negate a) (SignedOrbit.negate b) ↔
      SignedOrbit.balanced a b := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.negate_toInt, SignedOrbit.negate_toInt]
  omega

theorem le_add_left_iff (a b c : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
      SignedOrbit.le a b := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem le_add_right_iff (a b c : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
      SignedOrbit.le a b := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem lt_add_left_iff (a b c : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
      SignedOrbit.lt a b := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem lt_add_right_iff (a b c : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
      SignedOrbit.lt a b := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt]
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem add_le_add {a b c d : SignedOrbit}
    (hab : SignedOrbit.le a b) (hcd : SignedOrbit.le c d) :
    SignedOrbit.le (SignedOrbit.add a c) (SignedOrbit.add b d) := by
  rw [SignedOrbit.le_iff_toInt_le] at *
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt]
  omega

theorem add_lt_add_left {a b c : SignedOrbit}
    (h : SignedOrbit.lt a b) :
    SignedOrbit.lt (SignedOrbit.add c a) (SignedOrbit.add c b) := by
  exact (SignedOrbit.lt_add_left_iff a b c).mpr h

theorem add_lt_add_right {a b c : SignedOrbit}
    (h : SignedOrbit.lt a b) :
    SignedOrbit.lt (SignedOrbit.add a c) (SignedOrbit.add b c) := by
  exact (SignedOrbit.lt_add_right_iff a b c).mpr h

theorem negate_le_negate_iff (a b : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.negate b) (SignedOrbit.negate a) ↔
      SignedOrbit.le a b := by
  rw [SignedOrbit.le_iff_toInt_le, SignedOrbit.le_iff_toInt_le]
  rw [SignedOrbit.negate_toInt, SignedOrbit.negate_toInt]
  omega

theorem negate_lt_negate_iff (a b : SignedOrbit) :
    SignedOrbit.lt (SignedOrbit.negate b) (SignedOrbit.negate a) ↔
      SignedOrbit.lt a b := by
  rw [SignedOrbit.lt_iff_toInt_lt, SignedOrbit.lt_iff_toInt_lt]
  rw [SignedOrbit.negate_toInt, SignedOrbit.negate_toInt]
  omega

theorem cmp_add_left (a b c : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.add c a) (SignedOrbit.add c b) =
      SignedOrbit.cmp a b := by
  cases hcmp : SignedOrbit.cmp a b with
  | lt =>
      have hlt : SignedOrbit.lt a b :=
        (SignedOrbit.cmp_eq_lt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_add_left_iff a b c).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced a b :=
        (SignedOrbit.cmp_eq_eq_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_add_left_iff a b c).mpr hbal)
  | gt =>
      have hgt : SignedOrbit.lt b a :=
        (SignedOrbit.cmp_eq_gt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_add_left_iff b a c).mpr hgt)

theorem cmp_add_right (a b c : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.add a c) (SignedOrbit.add b c) =
      SignedOrbit.cmp a b := by
  cases hcmp : SignedOrbit.cmp a b with
  | lt =>
      have hlt : SignedOrbit.lt a b :=
        (SignedOrbit.cmp_eq_lt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.lt_add_right_iff a b c).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced a b :=
        (SignedOrbit.cmp_eq_eq_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_eq_of_balanced
        ((SignedOrbit.balanced_add_right_iff a b c).mpr hbal)
  | gt =>
      have hgt : SignedOrbit.lt b a :=
        (SignedOrbit.cmp_eq_gt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.lt_add_right_iff b a c).mpr hgt)

theorem cmp_negate_swap (a b : SignedOrbit) :
    SignedOrbit.cmp (SignedOrbit.negate b) (SignedOrbit.negate a) =
      SignedOrbit.cmp a b := by
  cases hcmp : SignedOrbit.cmp a b with
  | lt =>
      have hlt : SignedOrbit.lt a b :=
        (SignedOrbit.cmp_eq_lt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((SignedOrbit.negate_lt_negate_iff a b).mpr hlt)
  | eq =>
      have hbal : SignedOrbit.balanced a b :=
        (SignedOrbit.cmp_eq_eq_iff a b).mp hcmp
      have hbalNeg :
          SignedOrbit.balanced (SignedOrbit.negate b)
            (SignedOrbit.negate a) := by
        rw [SignedOrbit.balanced_negate_iff]
        exact SignedOrbit.balanced_symm hbal
      exact SignedOrbit.cmp_eq_eq_of_balanced hbalNeg
  | gt =>
      have hgt : SignedOrbit.lt b a :=
        (SignedOrbit.cmp_eq_gt_iff a b).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((SignedOrbit.negate_lt_negate_iff b a).mpr hgt)

/-! ## Absolute-value branch transport -/

theorem abs_eq_zero_iff_balanced_zero (z : SignedOrbit) :
    z.abs = DistinctionNat.zero ↔
      SignedOrbit.balanced z SignedOrbit.zero := by
  rw [SignedOrbit.abs_eq_zero_iff_toInt_eq_zero,
    SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]

theorem abs_toInt_of_nonnegFlag {z : SignedOrbit}
    (h : z.nonnegFlag = true) :
    (z.abs.toNat : ℤ) = z.toInt := by
  rw [SignedOrbit.abs_toNat]
  exact Int.ofNat_natAbs_of_nonneg
    ((SignedOrbit.nonnegFlag_eq_true_iff z).mp h)

theorem abs_toInt_of_negativeFlag {z : SignedOrbit}
    (h : z.negativeFlag = true) :
    (z.abs.toNat : ℤ) = -z.toInt := by
  have hzneg : z.toInt < 0 :=
    (SignedOrbit.negativeFlag_eq_true_iff_toInt_neg z).mp h
  rw [SignedOrbit.abs_toNat]
  exact Int.ofNat_natAbs_of_nonpos (le_of_lt hzneg)

theorem balanced_of_nonnegFlag {z : SignedOrbit}
    (h : z.nonnegFlag = true) :
    SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.ofOrbit_toInt]
  exact (SignedOrbit.abs_toInt_of_nonnegFlag h).symm

theorem balanced_of_negativeFlag {z : SignedOrbit}
    (h : z.negativeFlag = true) :
    SignedOrbit.balanced z
      (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt]
  have habs := SignedOrbit.abs_toInt_of_negativeFlag h
  omega

theorem balanced_sign_canonical (z : SignedOrbit) :
    (z.nonnegFlag = true ∧
      SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs)) ∨
      (z.negativeFlag = true ∧
        SignedOrbit.balanced z
          (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))) := by
  by_cases h : z.nonnegFlag = true
  · exact Or.inl ⟨h, SignedOrbit.balanced_of_nonnegFlag h⟩
  · have hneg : z.negativeFlag = true := by
      unfold SignedOrbit.negativeFlag
      cases hflag : z.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact h hflag
    exact Or.inr ⟨hneg, SignedOrbit.balanced_of_negativeFlag hneg⟩

theorem balanced_ofOrbit_abs_iff_nonnegFlag (z : SignedOrbit) :
    SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ↔
      z.nonnegFlag = true := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.ofOrbit_toInt]
  constructor
  · intro h
    rw [SignedOrbit.nonnegFlag_eq_true_iff]
    rw [h]
    exact Int.natCast_nonneg z.abs.toNat
  · intro h
    exact (SignedOrbit.abs_toInt_of_nonnegFlag h).symm

theorem balanced_negate_ofOrbit_abs_iff_negate_nonnegFlag (z : SignedOrbit) :
    SignedOrbit.balanced z
      (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
        (SignedOrbit.negate z).nonnegFlag = true := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt]
  constructor
  · intro h
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.negate_toInt]
    omega
  · intro h
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.negate_toInt] at h
    have hzle : z.toInt ≤ 0 := by omega
    have habs : ((Int.natAbs z.toInt : ℕ) : ℤ) = -z.toInt :=
      Int.ofNat_natAbs_of_nonpos hzle
    rw [← SignedOrbit.abs_toNat z] at habs
    omega

theorem balanced_negate_ofOrbit_abs_iff_negativeFlag_or_balanced_zero
    (z : SignedOrbit) :
    SignedOrbit.balanced z
      (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
        z.negativeFlag = true ∨
          SignedOrbit.balanced z SignedOrbit.zero := by
  constructor
  · intro h
    by_cases hneg : z.negativeFlag = true
    · exact Or.inl hneg
    · right
      have hnonneg : z.nonnegFlag = true :=
        (SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true z).mp (by
          cases hflag : z.negativeFlag with
          | false => rfl
          | true =>
              exfalso
              exact hneg hflag)
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
        SignedOrbit.ofOrbit_toInt] at h
      have habs : ((z.abs.toNat : ℕ) : ℤ) = z.toInt :=
        SignedOrbit.abs_toInt_of_nonnegFlag hnonneg
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      omega
  · intro h
    rcases h with hneg | hzero
    · exact SignedOrbit.balanced_of_negativeFlag hneg
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
        SignedOrbit.ofOrbit_toInt]
      have habs : ((z.abs.toNat : ℕ) : ℤ) = 0 := by
        rw [SignedOrbit.abs_toNat, hzero, Int.natAbs_zero]
        norm_num
      omega

theorem balanced_both_abs_representatives_iff_balanced_zero
    (z : SignedOrbit) :
    (SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ∧
      SignedOrbit.balanced z
        (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))) ↔
        SignedOrbit.balanced z SignedOrbit.zero := by
  constructor
  · intro h
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.ofOrbit_toInt] at h
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
      SignedOrbit.ofOrbit_toInt] at h
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
    omega
  · intro hzero
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt] at hzero
    constructor
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.ofOrbit_toInt]
      have habs : ((z.abs.toNat : ℕ) : ℤ) = 0 := by
        rw [SignedOrbit.abs_toNat, hzero, Int.natAbs_zero]
        norm_num
      omega
    · rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
        SignedOrbit.ofOrbit_toInt]
      have habs : ((z.abs.toNat : ℕ) : ℤ) = 0 := by
        rw [SignedOrbit.abs_toNat, hzero, Int.natAbs_zero]
        norm_num
      omega

theorem balanced_zero_of_both_abs_representatives {z : SignedOrbit}
    (hpos : SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs))
    (hneg : SignedOrbit.balanced z
      (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))) :
    SignedOrbit.balanced z SignedOrbit.zero :=
  (SignedOrbit.balanced_both_abs_representatives_iff_balanced_zero z).mp
    ⟨hpos, hneg⟩

theorem not_both_abs_representatives_of_not_balanced_zero {z : SignedOrbit}
    (hzero : ¬ SignedOrbit.balanced z SignedOrbit.zero) :
    ¬ (SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ∧
      SignedOrbit.balanced z
        (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))) := by
  intro h
  exact hzero
    ((SignedOrbit.balanced_both_abs_representatives_iff_balanced_zero z).mp h)

theorem not_balanced_ofOrbit_abs_of_negativeFlag {z : SignedOrbit}
    (hneg : z.negativeFlag = true) :
    ¬ SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) := by
  intro hbal
  have hnonneg : z.nonnegFlag = true :=
    (SignedOrbit.balanced_ofOrbit_abs_iff_nonnegFlag z).mp hbal
  exact SignedOrbit.signFlags_exclusive z ⟨hnonneg, hneg⟩

theorem balanced_negate_ofOrbit_abs_iff_balanced_zero_of_nonnegFlag
    {z : SignedOrbit} (hnonneg : z.nonnegFlag = true) :
    SignedOrbit.balanced z
      (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
        SignedOrbit.balanced z SignedOrbit.zero := by
  rw [SignedOrbit.balanced_negate_ofOrbit_abs_iff_negativeFlag_or_balanced_zero]
  constructor
  · intro h
    rcases h with hneg | hzero
    · exfalso
      exact SignedOrbit.signFlags_exclusive z ⟨hnonneg, hneg⟩
    · exact hzero
  · intro hzero
    exact Or.inr hzero

theorem abs_eq_of_balanced {z w : SignedOrbit}
    (h : SignedOrbit.balanced z w) :
    z.abs = w.abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat]
  rw [(SignedOrbit.balanced_iff_toInt_eq z w).mp h]

theorem abs_sub_eq_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.sub a b).abs = (SignedOrbit.sub a' b).abs :=
  SignedOrbit.abs_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_left ha)

theorem abs_sub_eq_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs = (SignedOrbit.sub a b').abs :=
  SignedOrbit.abs_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced_right hb)

theorem abs_sub_eq_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs = (SignedOrbit.sub a' b').abs :=
  SignedOrbit.abs_eq_of_balanced
    (SignedOrbit.sub_congr_of_balanced ha hb)

theorem abs_sub_eq_zero_iff_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.sub a' b).abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced_left ha]

theorem abs_sub_eq_zero_iff_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.sub a b').abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced_right hb]

theorem abs_sub_eq_zero_iff_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
      (SignedOrbit.sub a' b').abs = DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced ha hb]

theorem abs_sub_ne_zero_iff_of_balanced_left {a a' b : SignedOrbit}
    (ha : SignedOrbit.balanced a a') :
    (SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.sub a' b).abs ≠ DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced_left ha]

theorem abs_sub_ne_zero_iff_of_balanced_right {a b b' : SignedOrbit}
    (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.sub a b').abs ≠ DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced_right hb]

theorem abs_sub_ne_zero_iff_of_balanced {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    (SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
      (SignedOrbit.sub a' b').abs ≠ DistinctionNat.zero := by
  rw [SignedOrbit.abs_sub_eq_of_balanced ha hb]

theorem abs_negate (z : SignedOrbit) :
    (SignedOrbit.negate z).abs = z.abs := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.abs_toNat,
    SignedOrbit.negate_toInt, Int.natAbs_neg]

theorem abs_ofOrbit (n : DistinctionNat) :
    (SignedOrbit.ofOrbit n).abs = n := by
  apply DistinctionNat.toNat_inj
  rw [SignedOrbit.abs_toNat, SignedOrbit.ofOrbit_toInt]
  simp

theorem abs_negate_ofOrbit (n : DistinctionNat) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).abs = n := by
  rw [SignedOrbit.abs_negate, SignedOrbit.abs_ofOrbit]

theorem nonnegFlag_ofOrbit (n : DistinctionNat) :
    (SignedOrbit.ofOrbit n).nonnegFlag = true := by
  rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.ofOrbit_toInt]
  exact Int.natCast_nonneg n.toNat

theorem negativeFlag_ofOrbit (n : DistinctionNat) :
    (SignedOrbit.ofOrbit n).negativeFlag = false := by
  have hnonneg := SignedOrbit.nonnegFlag_ofOrbit n
  unfold SignedOrbit.negativeFlag
  rw [hnonneg]
  rfl

theorem nonnegFlag_negate_ofOrbit_of_ne_zero
    (n : DistinctionNat) (hn : n ≠ DistinctionNat.zero) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).nonnegFlag = false := by
  rw [SignedOrbit.nonnegFlag_eq_false_iff, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt]
  have hnNat : n.toNat ≠ 0 := by
    intro hzero
    apply hn
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  omega

theorem negativeFlag_negate_ofOrbit_of_ne_zero
    (n : DistinctionNat) (hn : n ≠ DistinctionNat.zero) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).negativeFlag = true := by
  rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg,
    SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt]
  have hnNat : n.toNat ≠ 0 := by
    intro hzero
    apply hn
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  omega

theorem negate_ofOrbit_not_balanced_zero_of_ne_zero
    (n : DistinctionNat) (hn : n ≠ DistinctionNat.zero) :
    ¬ SignedOrbit.balanced
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)) SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.zero_toInt]
  have hnNat : n.toNat ≠ 0 := by
    intro hzero
    apply hn
    apply DistinctionNat.toNat_inj
    rw [hzero, DistinctionNat.toNat_zero]
  omega

theorem nonnegFlag_negate_ofOrbit_eq_true_iff_zero (n : DistinctionNat) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).nonnegFlag = true ↔
      n = DistinctionNat.zero := by
  constructor
  · intro h
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.negate_toInt,
      SignedOrbit.ofOrbit_toInt] at h
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_zero]
    omega
  · intro h
    rw [h]
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.negate_toInt,
      SignedOrbit.ofOrbit_toInt, DistinctionNat.toNat_zero]
    norm_num

theorem negativeFlag_negate_ofOrbit_eq_true_iff_ne_zero (n : DistinctionNat) :
    (SignedOrbit.negate (SignedOrbit.ofOrbit n)).negativeFlag = true ↔
      n ≠ DistinctionNat.zero := by
  constructor
  · intro h hn
    rw [hn] at h
    rw [SignedOrbit.negativeFlag_eq_true_iff_toInt_neg,
      SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt,
      DistinctionNat.toNat_zero] at h
    norm_num at h
  · intro hn
    exact SignedOrbit.negativeFlag_negate_ofOrbit_of_ne_zero n hn

theorem negate_ofOrbit_balanced_zero_iff (n : DistinctionNat) :
    SignedOrbit.balanced
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)) SignedOrbit.zero ↔
        n = DistinctionNat.zero := by
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.negate_toInt,
    SignedOrbit.ofOrbit_toInt, SignedOrbit.zero_toInt]
  constructor
  · intro h
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_zero]
    omega
  · intro h
    rw [h, DistinctionNat.toNat_zero]
    norm_num

/-! ## Absolute-value order bounds -/

theorem abs_add_le_add_abs (z w : SignedOrbit) :
    DistinctionNat.leq (SignedOrbit.add z w).abs (z.abs + w.abs) = true := by
  rw [DistinctionNat.leq_eq_true_iff]
  rw [SignedOrbit.abs_toNat, SignedOrbit.add_toInt, DistinctionNat.toNat_add,
    SignedOrbit.abs_toNat, SignedOrbit.abs_toNat]
  exact Int.natAbs_add_le z.toInt w.toInt

theorem abs_sub_le_add_abs (z w : SignedOrbit) :
    DistinctionNat.leq (SignedOrbit.sub z w).abs (z.abs + w.abs) = true := by
  rw [DistinctionNat.leq_eq_true_iff]
  rw [SignedOrbit.abs_toNat, SignedOrbit.sub_toInt, DistinctionNat.toNat_add,
    SignedOrbit.abs_toNat, SignedOrbit.abs_toNat]
  simpa [sub_eq_add_neg, Int.natAbs_neg] using
    Int.natAbs_add_le z.toInt (-w.toInt)

theorem abs_le_iff_between (z : SignedOrbit) (n : DistinctionNat) :
    DistinctionNat.leq z.abs n = true ↔
      SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
        SignedOrbit.le z (SignedOrbit.ofOrbit n) := by
  rw [DistinctionNat.leq_eq_true_iff, SignedOrbit.le_iff_toInt_le,
    SignedOrbit.le_iff_toInt_le]
  simp [SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt,
    SignedOrbit.abs_toNat]
  constructor
  · intro h
    have hInt : ((Int.natAbs z.toInt : ℕ) : ℤ) ≤ (n.toNat : ℤ) := by
      exact_mod_cast h
    constructor
    · by_cases hz : 0 ≤ z.toInt
      · omega
      · have hzle : z.toInt ≤ 0 := by omega
        have habs : ((Int.natAbs z.toInt : ℕ) : ℤ) = -z.toInt :=
          Int.ofNat_natAbs_of_nonpos hzle
        omega
    · by_cases hz : 0 ≤ z.toInt
      · have habs : ((Int.natAbs z.toInt : ℕ) : ℤ) = z.toInt :=
          Int.ofNat_natAbs_of_nonneg hz
        omega
      · omega
  · intro h
    rcases h with ⟨hlo, hhi⟩
    have hInt : ((Int.natAbs z.toInt : ℕ) : ℤ) ≤ (n.toNat : ℤ) := by
      by_cases hz : 0 ≤ z.toInt
      · have habs : ((Int.natAbs z.toInt : ℕ) : ℤ) = z.toInt :=
          Int.ofNat_natAbs_of_nonneg hz
        omega
      · have hzle : z.toInt ≤ 0 := by omega
        have habs : ((Int.natAbs z.toInt : ℕ) : ℤ) = -z.toInt :=
          Int.ofNat_natAbs_of_nonpos hzle
        omega
    exact_mod_cast hInt

theorem between_of_abs_le {z : SignedOrbit} {n : DistinctionNat}
    (h : DistinctionNat.leq z.abs n = true) :
    SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
      SignedOrbit.le z (SignedOrbit.ofOrbit n) :=
  (SignedOrbit.abs_le_iff_between z n).mp h

theorem abs_le_of_between {z : SignedOrbit} {n : DistinctionNat}
    (hlo : SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z)
    (hhi : SignedOrbit.le z (SignedOrbit.ofOrbit n)) :
    DistinctionNat.leq z.abs n = true :=
  (SignedOrbit.abs_le_iff_between z n).mpr ⟨hlo, hhi⟩

theorem neg_abs_le_self (z : SignedOrbit) :
    SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) z :=
  ((SignedOrbit.abs_le_iff_between z z.abs).mp
    ((DistinctionNat.leq_eq_true_iff z.abs z.abs).mpr (Nat.le_refl _))).1

theorem self_le_abs (z : SignedOrbit) :
    SignedOrbit.le z (SignedOrbit.ofOrbit z.abs) :=
  ((SignedOrbit.abs_le_iff_between z z.abs).mp
    ((DistinctionNat.leq_eq_true_iff z.abs z.abs).mpr (Nat.le_refl _))).2

theorem abs_le_trans {z : SignedOrbit} {n m : DistinctionNat}
    (hzn : DistinctionNat.leq z.abs n = true)
    (hnm : DistinctionNat.leq n m = true) :
    DistinctionNat.leq z.abs m = true := by
  rw [DistinctionNat.leq_eq_true_iff] at *
  exact Nat.le_trans hzn hnm

theorem between_mono {z : SignedOrbit} {n m : DistinctionNat}
    (hbetween :
      SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
        SignedOrbit.le z (SignedOrbit.ofOrbit n))
    (hnm : DistinctionNat.leq n m = true) :
    SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit m)) z ∧
      SignedOrbit.le z (SignedOrbit.ofOrbit m) := by
  apply SignedOrbit.between_of_abs_le
  exact SignedOrbit.abs_le_trans (SignedOrbit.abs_le_of_between hbetween.1 hbetween.2) hnm

end SignedOrbit

namespace RatioOrbit

theorem recipNonzero_den_eq_abs (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recipNonzero a h).den = a.num.abs := by
  rfl

theorem recipNonzero_num_eq_of_nonnegFlag {a : RatioOrbit}
    {h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero}
    (hflag : a.num.nonnegFlag = true) :
    (RatioOrbit.recipNonzero a h).num = SignedOrbit.ofOrbit a.den := by
  simp [RatioOrbit.recipNonzero, hflag]

theorem recipNonzero_num_eq_of_negativeFlag {a : RatioOrbit}
    {h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero}
    (hflag : a.num.negativeFlag = true) :
    (RatioOrbit.recipNonzero a h).num =
      SignedOrbit.negate (SignedOrbit.ofOrbit a.den) := by
  have hnonnegFalse : a.num.nonnegFlag = false := by
    unfold SignedOrbit.negativeFlag at hflag
    cases hbranch : a.num.nonnegFlag with
    | false => rfl
    | true =>
        simp [hbranch] at hflag
  simp [RatioOrbit.recipNonzero, hnonnegFalse]

theorem recipNonzero_num_abs_eq_den (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recipNonzero a h).num.abs = a.den := by
  by_cases hnonneg : a.num.nonnegFlag = true
  · rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg,
      SignedOrbit.abs_ofOrbit]
  · have hneg : a.num.negativeFlag = true := by
      rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
      cases hflag : a.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hnonneg hflag
    rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg,
      SignedOrbit.abs_negate_ofOrbit]

theorem recipNonzero_num_not_balanced_zero (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced
      (RatioOrbit.recipNonzero a h).num SignedOrbit.zero := by
  intro hbal
  have habsZero :
      (RatioOrbit.recipNonzero a h).num.abs = DistinctionNat.zero :=
    (SignedOrbit.abs_eq_zero_iff_balanced_zero
      (RatioOrbit.recipNonzero a h).num).mpr hbal
  rw [RatioOrbit.recipNonzero_num_abs_eq_den a h] at habsZero
  exact a.den_ne_zero habsZero

theorem recipNonzero_num_nonnegFlag_eq (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recipNonzero a h).num.nonnegFlag = a.num.nonnegFlag := by
  by_cases hnonneg : a.num.nonnegFlag = true
  · rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg,
      SignedOrbit.nonnegFlag_ofOrbit, hnonneg]
  · have hnonnegFalse : a.num.nonnegFlag = false := by
      cases hflag : a.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hnonneg hflag
    have hneg : a.num.negativeFlag = true := by
      rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
      exact hnonnegFalse
    rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg,
      SignedOrbit.nonnegFlag_negate_ofOrbit_of_ne_zero a.den a.den_ne_zero,
      hnonnegFalse]

theorem recipNonzero_num_negativeFlag_eq (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recipNonzero a h).num.negativeFlag = a.num.negativeFlag := by
  by_cases hneg : a.num.negativeFlag = true
  · rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg,
      SignedOrbit.negativeFlag_negate_ofOrbit_of_ne_zero a.den a.den_ne_zero,
      hneg]
  · have hnegFalse : a.num.negativeFlag = false := by
      cases hflag : a.num.negativeFlag with
      | false => rfl
      | true =>
          exfalso
          exact hneg hflag
    have hnonneg : a.num.nonnegFlag = true :=
      (SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true a.num).mp hnegFalse
    rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg,
      SignedOrbit.negativeFlag_ofOrbit, hnegFalse]

theorem recipNonzero_num_zero_le_iff (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.le SignedOrbit.zero (RatioOrbit.recipNonzero a h).num ↔
      SignedOrbit.le SignedOrbit.zero a.num := by
  rw [SignedOrbit.zero_le_iff_nonnegFlag, SignedOrbit.zero_le_iff_nonnegFlag,
    RatioOrbit.recipNonzero_num_nonnegFlag_eq]

theorem recipNonzero_num_lt_zero_iff (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.lt (RatioOrbit.recipNonzero a h).num SignedOrbit.zero ↔
      SignedOrbit.lt a.num SignedOrbit.zero := by
  rw [SignedOrbit.lt_zero_iff_negativeFlag, SignedOrbit.lt_zero_iff_negativeFlag,
    RatioOrbit.recipNonzero_num_negativeFlag_eq]

theorem recipNonzero_num_zero_lt_iff (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.lt SignedOrbit.zero (RatioOrbit.recipNonzero a h).num ↔
      SignedOrbit.lt SignedOrbit.zero a.num := by
  rw [SignedOrbit.zero_lt_iff_nonnegFlag_and_not_balanced_zero,
    SignedOrbit.zero_lt_iff_nonnegFlag_and_not_balanced_zero,
    RatioOrbit.recipNonzero_num_nonnegFlag_eq]
  constructor
  · intro hrecip
    exact ⟨hrecip.1, h⟩
  · intro ha
    exact ⟨ha.1, RatioOrbit.recipNonzero_num_not_balanced_zero a h⟩

theorem recipNonzero_num_cmp_zero (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.cmp (RatioOrbit.recipNonzero a h).num SignedOrbit.zero =
      SignedOrbit.cmp a.num SignedOrbit.zero := by
  cases hcmp : SignedOrbit.cmp a.num SignedOrbit.zero with
  | lt =>
      have ha : SignedOrbit.lt a.num SignedOrbit.zero :=
        (SignedOrbit.cmp_eq_lt_iff a.num SignedOrbit.zero).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((RatioOrbit.recipNonzero_num_lt_zero_iff a h).mpr ha)
  | eq =>
      have hbal : SignedOrbit.balanced a.num SignedOrbit.zero :=
        (SignedOrbit.cmp_eq_eq_iff a.num SignedOrbit.zero).mp hcmp
      exact False.elim (h hbal)
  | gt =>
      have ha : SignedOrbit.lt SignedOrbit.zero a.num :=
        (SignedOrbit.cmp_eq_gt_iff a.num SignedOrbit.zero).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((RatioOrbit.recipNonzero_num_zero_lt_iff a h).mpr ha)

theorem recipNonzero_num_zero_cmp (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.cmp SignedOrbit.zero (RatioOrbit.recipNonzero a h).num =
      SignedOrbit.cmp SignedOrbit.zero a.num := by
  cases hcmp : SignedOrbit.cmp SignedOrbit.zero a.num with
  | lt =>
      have ha : SignedOrbit.lt SignedOrbit.zero a.num :=
        (SignedOrbit.cmp_eq_lt_iff SignedOrbit.zero a.num).mp hcmp
      exact SignedOrbit.cmp_eq_lt_of_lt
        ((RatioOrbit.recipNonzero_num_zero_lt_iff a h).mpr ha)
  | eq =>
      have hbal : SignedOrbit.balanced SignedOrbit.zero a.num :=
        (SignedOrbit.cmp_eq_eq_iff SignedOrbit.zero a.num).mp hcmp
      exact False.elim (h (SignedOrbit.balanced_symm hbal))
  | gt =>
      have ha : SignedOrbit.lt a.num SignedOrbit.zero :=
        (SignedOrbit.cmp_eq_gt_iff SignedOrbit.zero a.num).mp hcmp
      exact SignedOrbit.cmp_eq_gt_of_gt
        ((RatioOrbit.recipNonzero_num_lt_zero_iff a h).mpr ha)

theorem recipNonzero_num_balanced_ofOrbit_den_iff_nonnegFlag
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
        (RatioOrbit.recipNonzero a h).num (SignedOrbit.ofOrbit a.den) ↔
      a.num.nonnegFlag = true := by
  by_cases hnonneg : a.num.nonnegFlag = true
  · rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg]
    constructor
    · intro _
      exact hnonneg
    · intro _
      exact SignedOrbit.balanced_refl (SignedOrbit.ofOrbit a.den)
  · have hnonnegFalse : a.num.nonnegFlag = false := by
      cases hflag : a.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hnonneg hflag
    have hneg : a.num.negativeFlag = true := by
      rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
      exact hnonnegFalse
    rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg]
    constructor
    · intro hbal
      exfalso
      have hEq :=
        (SignedOrbit.balanced_iff_toInt_eq
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den))
          (SignedOrbit.ofOrbit a.den)).mp hbal
      rw [SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt] at hEq
      exact a.den_toNat_ne_zero (by omega)
    · intro htrue
      rw [hnonnegFalse] at htrue
      contradiction

theorem recipNonzero_num_balanced_negate_ofOrbit_den_iff_negativeFlag
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
        (RatioOrbit.recipNonzero a h).num
        (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
      a.num.negativeFlag = true := by
  by_cases hneg : a.num.negativeFlag = true
  · rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg]
    constructor
    · intro _
      exact hneg
    · intro _
      exact SignedOrbit.balanced_refl
        (SignedOrbit.negate (SignedOrbit.ofOrbit a.den))
  · have hnegFalse : a.num.negativeFlag = false := by
      cases hflag : a.num.negativeFlag with
      | false => rfl
      | true =>
          exfalso
          exact hneg hflag
    have hnonneg : a.num.nonnegFlag = true :=
      (SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true a.num).mp
        hnegFalse
    rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg]
    constructor
    · intro hbal
      exfalso
      have hEq :=
        (SignedOrbit.balanced_iff_toInt_eq
          (SignedOrbit.ofOrbit a.den)
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den))).mp hbal
      rw [SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt] at hEq
      exact a.den_toNat_ne_zero (by omega)
    · intro htrue
      rw [hnegFalse] at htrue
      contradiction

theorem recipNonzero_num_not_balanced_ofOrbit_den_iff_negativeFlag
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced
        (RatioOrbit.recipNonzero a h).num (SignedOrbit.ofOrbit a.den) ↔
      a.num.negativeFlag = true := by
  rw [RatioOrbit.recipNonzero_num_balanced_ofOrbit_den_iff_nonnegFlag a h]
  constructor
  · intro hnot
    rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
    cases hflag : a.num.nonnegFlag with
    | false => rfl
    | true =>
        exfalso
        exact hnot hflag
  · intro hneg hnonneg
    have hfalse :
        a.num.nonnegFlag = false :=
      (SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false a.num).mp hneg
    rw [hnonneg] at hfalse
    contradiction

theorem recipNonzero_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced
        (RatioOrbit.recipNonzero a h).num
        (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
      a.num.nonnegFlag = true := by
  rw [RatioOrbit.recipNonzero_num_balanced_negate_ofOrbit_den_iff_negativeFlag
    a h]
  constructor
  · intro hnot
    rw [← SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true]
    cases hflag : a.num.negativeFlag with
    | false => rfl
    | true =>
        exfalso
        exact hnot hflag
  · intro hnonneg hneg
    have hfalse :
        a.num.negativeFlag = false :=
      (SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true a.num).mpr
        hnonneg
    rw [hneg] at hfalse
    contradiction

theorem num_mul_recipNonzero_num_balanced_ofOrbit_den_mul_abs
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
      (SignedOrbit.mul a.num (RatioOrbit.recipNonzero a h).num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs)) := by
  by_cases hnonneg : a.num.nonnegFlag = true
  · have habs := SignedOrbit.abs_toInt_of_nonnegFlag (z := a.num) hnonneg
    rw [RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hnonneg]
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
      SignedOrbit.ofOrbit_toInt, SignedOrbit.ofOrbit_toInt,
      DistinctionNat.toNat_mul]
    rw [Nat.cast_mul, habs]
    ring
  · have hnonnegFalse : a.num.nonnegFlag = false := by
      cases hflag : a.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hnonneg hflag
    have hneg : a.num.negativeFlag = true := by
      rw [SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false]
      exact hnonnegFalse
    have habs := SignedOrbit.abs_toInt_of_negativeFlag (z := a.num) hneg
    rw [RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hneg]
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
      SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt,
      SignedOrbit.ofOrbit_toInt, DistinctionNat.toNat_mul]
    rw [Nat.cast_mul, habs]
    ring

theorem mul_recipNonzero_crossEq_one
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recipNonzero a h))
      RatioOrbit.one := by
  have hprod :=
    (SignedOrbit.balanced_iff_toInt_eq
      (SignedOrbit.mul a.num (RatioOrbit.recipNonzero a h).num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs))).mp
      (RatioOrbit.num_mul_recipNonzero_num_balanced_ofOrbit_den_mul_abs a h)
  unfold RatioOrbit.crossEq RatioOrbit.mul RatioOrbit.one
  rw [SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    DistinctionNat.toNat_mul] at hprod
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt,
    SignedOrbit.mul_toInt, SignedOrbit.one_toInt, DistinctionNat.toNat_mul]
  simp [RatioOrbit.recipNonzero_den_eq_abs a h, hprod]

theorem recipNonzero_num_mul_num_balanced_ofOrbit_den_mul_abs
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
      (SignedOrbit.mul (RatioOrbit.recipNonzero a h).num a.num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs)) := by
  have hprod :=
    (SignedOrbit.balanced_iff_toInt_eq
      (SignedOrbit.mul a.num (RatioOrbit.recipNonzero a h).num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs))).mp
      (RatioOrbit.num_mul_recipNonzero_num_balanced_ofOrbit_den_mul_abs a h)
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt,
    SignedOrbit.ofOrbit_toInt, DistinctionNat.toNat_mul]
  rw [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    DistinctionNat.toNat_mul] at hprod
  rw [← hprod]
  ring

theorem recipNonzero_mul_crossEq_one
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recipNonzero a h) a)
      RatioOrbit.one := by
  have hprod :=
    (SignedOrbit.balanced_iff_toInt_eq
      (SignedOrbit.mul (RatioOrbit.recipNonzero a h).num a.num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs))).mp
      (RatioOrbit.recipNonzero_num_mul_num_balanced_ofOrbit_den_mul_abs a h)
  unfold RatioOrbit.crossEq RatioOrbit.mul RatioOrbit.one
  rw [SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
    DistinctionNat.toNat_mul] at hprod
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt,
    SignedOrbit.mul_toInt, SignedOrbit.one_toInt, DistinctionNat.toNat_mul]
  simp [RatioOrbit.recipNonzero_den_eq_abs a h, hprod]
  ring

theorem recip_eq_recipNonzero_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.recip a = RatioOrbit.recipNonzero a h := by
  unfold RatioOrbit.recip
  simp [h]

theorem mul_recip_crossEq_one_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recip a))
      RatioOrbit.one := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.mul_recipNonzero_crossEq_one a h

theorem recip_mul_crossEq_one_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recip a) a)
      RatioOrbit.one := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_mul_crossEq_one a h

theorem recip_den_eq_abs_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recip a).den = a.num.abs := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_den_eq_abs a h

theorem recip_num_abs_eq_den_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recip a).num.abs = a.den := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_abs_eq_den a h

theorem recip_num_not_balanced_zero_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_not_balanced_zero a h

theorem recip_num_nonnegFlag_eq_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recip a).num.nonnegFlag = a.num.nonnegFlag := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_nonnegFlag_eq a h

theorem recip_num_negativeFlag_eq_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (RatioOrbit.recip a).num.negativeFlag = a.num.negativeFlag := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_negativeFlag_eq a h

theorem recip_num_zero_le_iff_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.le SignedOrbit.zero (RatioOrbit.recip a).num ↔
      SignedOrbit.le SignedOrbit.zero a.num := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_zero_le_iff a h

theorem recip_num_lt_zero_iff_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.lt (RatioOrbit.recip a).num SignedOrbit.zero ↔
      SignedOrbit.lt a.num SignedOrbit.zero := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_lt_zero_iff a h

theorem recip_num_zero_lt_iff_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.lt SignedOrbit.zero (RatioOrbit.recip a).num ↔
      SignedOrbit.lt SignedOrbit.zero a.num := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_zero_lt_iff a h

theorem recip_num_cmp_zero_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.cmp (RatioOrbit.recip a).num SignedOrbit.zero =
      SignedOrbit.cmp a.num SignedOrbit.zero := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_cmp_zero a h

theorem recip_num_zero_cmp_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.cmp SignedOrbit.zero (RatioOrbit.recip a).num =
      SignedOrbit.cmp SignedOrbit.zero a.num := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_zero_cmp a h

theorem recip_num_balanced_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
        (RatioOrbit.recip a).num (SignedOrbit.ofOrbit a.den) ↔
      a.num.nonnegFlag = true := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_balanced_ofOrbit_den_iff_nonnegFlag a h

theorem recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
        (RatioOrbit.recip a).num
        (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
      a.num.negativeFlag = true := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact
    RatioOrbit.recipNonzero_num_balanced_negate_ofOrbit_den_iff_negativeFlag
      a h

theorem recip_num_not_balanced_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced
        (RatioOrbit.recip a).num (SignedOrbit.ofOrbit a.den) ↔
      a.num.negativeFlag = true := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact
    RatioOrbit.recipNonzero_num_not_balanced_ofOrbit_den_iff_negativeFlag
      a h

theorem recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    ¬ SignedOrbit.balanced
        (RatioOrbit.recip a).num
        (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
      a.num.nonnegFlag = true := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact
    RatioOrbit.recipNonzero_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag
      a h

theorem recip_num_eq_of_nonnegFlag_of_not_balanced_zero
    {a : RatioOrbit}
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero)
    (hflag : a.num.nonnegFlag = true) :
    (RatioOrbit.recip a).num = SignedOrbit.ofOrbit a.den := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_eq_of_nonnegFlag (a := a) (h := h) hflag

theorem recip_num_eq_of_negativeFlag_of_not_balanced_zero
    {a : RatioOrbit}
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero)
    (hflag : a.num.negativeFlag = true) :
    (RatioOrbit.recip a).num =
      SignedOrbit.negate (SignedOrbit.ofOrbit a.den) := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_eq_of_negativeFlag (a := a) (h := h) hflag

theorem num_mul_recip_num_balanced_ofOrbit_den_mul_abs_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
      (SignedOrbit.mul a.num (RatioOrbit.recip a).num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs)) := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.num_mul_recipNonzero_num_balanced_ofOrbit_den_mul_abs a h

theorem recip_num_mul_num_balanced_ofOrbit_den_mul_abs_of_not_balanced_zero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    SignedOrbit.balanced
      (SignedOrbit.mul (RatioOrbit.recip a).num a.num)
      (SignedOrbit.ofOrbit (a.den * a.num.abs)) := by
  rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a h]
  exact RatioOrbit.recipNonzero_num_mul_num_balanced_ofOrbit_den_mul_abs a h

theorem recip_num_balanced_zero_iff (a : RatioOrbit) :
    SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero ↔
      SignedOrbit.balanced a.num SignedOrbit.zero := by
  by_cases hzero : SignedOrbit.balanced a.num SignedOrbit.zero
  · unfold RatioOrbit.recip
    simp [hzero, RatioOrbit.zero, SignedOrbit.balanced_refl]
  · rw [RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero a hzero]
    constructor
    · intro hrec
      exfalso
      exact RatioOrbit.recipNonzero_num_not_balanced_zero a hzero hrec
    · intro ha
      exfalso
      exact hzero ha

theorem recip_num_not_balanced_zero_iff (a : RatioOrbit) :
    ¬ SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero ↔
      ¬ SignedOrbit.balanced a.num SignedOrbit.zero := by
  rw [RatioOrbit.recip_num_balanced_zero_iff a]

theorem crossEq_zero_iff_num_balanced_zero (a : RatioOrbit) :
    RatioOrbit.crossEq a RatioOrbit.zero ↔
      SignedOrbit.balanced a.num SignedOrbit.zero := by
  unfold RatioOrbit.crossEq RatioOrbit.zero
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.scaleByNat_toInt,
    SignedOrbit.scaleByNat_toInt, SignedOrbit.zero_toInt,
    SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
  simp

theorem zero_crossEq_iff_num_balanced_zero (a : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.zero a ↔
      SignedOrbit.balanced a.num SignedOrbit.zero := by
  constructor
  · intro h
    exact (RatioOrbit.crossEq_zero_iff_num_balanced_zero a).mp
      (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.crossEq_zero_iff_num_balanced_zero a).mpr h)

theorem recip_crossEq_zero_iff_num_balanced_zero (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
      SignedOrbit.balanced a.num SignedOrbit.zero := by
  exact (RatioOrbit.crossEq_zero_iff_num_balanced_zero
      (RatioOrbit.recip a)).trans
    (RatioOrbit.recip_num_balanced_zero_iff a)

theorem zero_crossEq_recip_iff_num_balanced_zero (a : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
      SignedOrbit.balanced a.num SignedOrbit.zero := by
  exact (RatioOrbit.zero_crossEq_iff_num_balanced_zero
      (RatioOrbit.recip a)).trans
    (RatioOrbit.recip_num_balanced_zero_iff a)

theorem recip_crossEq_zero_iff_crossEq_zero (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
      RatioOrbit.crossEq a RatioOrbit.zero := by
  exact (RatioOrbit.recip_crossEq_zero_iff_num_balanced_zero a).trans
    (RatioOrbit.crossEq_zero_iff_num_balanced_zero a).symm

theorem zero_crossEq_recip_iff_zero_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
      RatioOrbit.crossEq RatioOrbit.zero a := by
  exact (RatioOrbit.zero_crossEq_recip_iff_num_balanced_zero a).trans
    (RatioOrbit.zero_crossEq_iff_num_balanced_zero a).symm

theorem recip_crossEq_zero_iff_zero_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
      RatioOrbit.crossEq RatioOrbit.zero a := by
  exact (RatioOrbit.recip_crossEq_zero_iff_num_balanced_zero a).trans
    (RatioOrbit.zero_crossEq_iff_num_balanced_zero a).symm

theorem zero_crossEq_recip_iff_crossEq_zero (a : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
      RatioOrbit.crossEq a RatioOrbit.zero := by
  exact (RatioOrbit.zero_crossEq_recip_iff_num_balanced_zero a).trans
    (RatioOrbit.crossEq_zero_iff_num_balanced_zero a).symm

theorem recip_not_crossEq_zero_iff_not_crossEq_zero (a : RatioOrbit) :
    ¬ RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero := by
  rw [RatioOrbit.recip_crossEq_zero_iff_crossEq_zero a]

theorem zero_not_crossEq_recip_iff_zero_not_crossEq (a : RatioOrbit) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
      ¬ RatioOrbit.crossEq RatioOrbit.zero a := by
  rw [RatioOrbit.zero_crossEq_recip_iff_zero_crossEq a]

theorem recip_not_crossEq_zero_iff_zero_not_crossEq (a : RatioOrbit) :
    ¬ RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
      ¬ RatioOrbit.crossEq RatioOrbit.zero a := by
  rw [RatioOrbit.recip_crossEq_zero_iff_zero_crossEq a]

theorem zero_not_crossEq_recip_iff_not_crossEq_zero (a : RatioOrbit) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero := by
  rw [RatioOrbit.zero_crossEq_recip_iff_crossEq_zero a]

theorem recip_recipNonzero_crossEq_self
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.recip (RatioOrbit.recipNonzero a h)) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.recipNonzero_toRat]
  simp

theorem self_crossEq_recip_recipNonzero
    (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    RatioOrbit.crossEq a (RatioOrbit.recip (RatioOrbit.recipNonzero a h)) := by
  exact RatioOrbit.crossEq_symm
    (RatioOrbit.recip_recipNonzero_crossEq_self a h)

theorem recip_recip_crossEq_self (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip (RatioOrbit.recip a)) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.recip_toRat]
  simp

theorem self_crossEq_recip_recip (a : RatioOrbit) :
    RatioOrbit.crossEq a (RatioOrbit.recip (RatioOrbit.recip a)) := by
  exact RatioOrbit.crossEq_symm (RatioOrbit.recip_recip_crossEq_self a)

theorem recip_crossEq_congr {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [RatioOrbit.recip_toRat, RatioOrbit.recip_toRat, h]

theorem recip_crossEq_iff (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b) ↔
      RatioOrbit.crossEq a b := by
  constructor
  · intro h
    have hrec := RatioOrbit.recip_crossEq_congr h
    exact RatioOrbit.crossEq_trans
      (RatioOrbit.crossEq_symm (RatioOrbit.recip_recip_crossEq_self a))
      (RatioOrbit.crossEq_trans hrec (RatioOrbit.recip_recip_crossEq_self b))
  · intro h
    exact RatioOrbit.recip_crossEq_congr h

theorem recip_crossEq_iff_crossEq_recip (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.recip a) b ↔
      RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.recip_toRat, RatioOrbit.recip_toRat]
  constructor
  · intro h
    calc
      a.toRat = ((a.toRat)⁻¹)⁻¹ := by simp
      _ = (b.toRat)⁻¹ := by rw [h]
  · intro h
    calc
      (a.toRat)⁻¹ = ((b.toRat)⁻¹)⁻¹ := by rw [h]
      _ = b.toRat := by simp

theorem crossEq_recip_iff_recip_crossEq (a b : RatioOrbit) :
    RatioOrbit.crossEq a (RatioOrbit.recip b) ↔
      RatioOrbit.crossEq (RatioOrbit.recip a) b := by
  exact (RatioOrbit.recip_crossEq_iff_crossEq_recip a b).symm

theorem mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero
    (a b : RatioOrbit)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.one_toRat, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.recip_toRat]
  have hbq : b.toRat ≠ 0 := by
    intro hzero
    exact hb ((RatioOrbit.crossEq_iff_toRat_eq b RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  constructor
  · intro h
    have hunit : b.toRat * (b.toRat)⁻¹ = 1 := by
      field_simp [hbq]
    calc
      a.toRat = a.toRat * 1 := by ring
      _ = a.toRat * (b.toRat * (b.toRat)⁻¹) := by rw [hunit]
      _ = (a.toRat * b.toRat) * (b.toRat)⁻¹ := by ring
      _ = 1 * (b.toRat)⁻¹ := by rw [h]
      _ = (b.toRat)⁻¹ := by ring
  · intro h
    rw [h]
    field_simp [hbq]

theorem mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      RatioOrbit.crossEq b (RatioOrbit.recip a) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.one_toRat, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.recip_toRat]
  have haq : a.toRat ≠ 0 := by
    intro hzero
    exact ha ((RatioOrbit.crossEq_iff_toRat_eq a RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  constructor
  · intro h
    have hunit : (a.toRat)⁻¹ * a.toRat = 1 := by
      field_simp [haq]
    calc
      b.toRat = 1 * b.toRat := by ring
      _ = ((a.toRat)⁻¹ * a.toRat) * b.toRat := by rw [hunit]
      _ = (a.toRat)⁻¹ * (a.toRat * b.toRat) := by ring
      _ = (a.toRat)⁻¹ * 1 := by rw [h]
      _ = (a.toRat)⁻¹ := by ring
  · intro h
    rw [h]
    field_simp [haq]

theorem mul_recip_cancel_right_crossEq_self_of_right_not_crossEq_zero
    (a b : RatioOrbit)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a b) (RatioOrbit.recip b)) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.recip_toRat]
  have hbq : b.toRat ≠ 0 := by
    intro hzero
    exact hb ((RatioOrbit.crossEq_iff_toRat_eq b RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : b.toRat * (b.toRat)⁻¹ = 1 := by
    field_simp [hbq]
  calc
    (a.toRat * b.toRat) * (b.toRat)⁻¹ =
        a.toRat * (b.toRat * (b.toRat)⁻¹) := by ring
    _ = a.toRat * 1 := by rw [hunit]
    _ = a.toRat := by ring

theorem recip_mul_cancel_left_crossEq_self_of_left_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.mul a b)) b := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.recip_toRat]
  have haq : a.toRat ≠ 0 := by
    intro hzero
    exact ha ((RatioOrbit.crossEq_iff_toRat_eq a RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : (a.toRat)⁻¹ * a.toRat = 1 := by
    field_simp [haq]
  calc
    (a.toRat)⁻¹ * (a.toRat * b.toRat) =
        ((a.toRat)⁻¹ * a.toRat) * b.toRat := by ring
    _ = 1 * b.toRat := by rw [hunit]
    _ = b.toRat := by ring

theorem mul_recip_cancel_right_assoc_crossEq_self_of_right_not_crossEq_zero
    (a b : RatioOrbit)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a (RatioOrbit.recip b)) b) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.recip_toRat]
  have hbq : b.toRat ≠ 0 := by
    intro hzero
    exact hb ((RatioOrbit.crossEq_iff_toRat_eq b RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : (b.toRat)⁻¹ * b.toRat = 1 := by
    field_simp [hbq]
  calc
    (a.toRat * (b.toRat)⁻¹) * b.toRat =
        a.toRat * ((b.toRat)⁻¹ * b.toRat) := by ring
    _ = a.toRat * 1 := by rw [hunit]
    _ = a.toRat := by ring

theorem recip_mul_cancel_left_assoc_crossEq_self_of_left_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul a (RatioOrbit.mul (RatioOrbit.recip a) b)) b := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.recip_toRat]
  have haq : a.toRat ≠ 0 := by
    intro hzero
    exact ha ((RatioOrbit.crossEq_iff_toRat_eq a RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : a.toRat * (a.toRat)⁻¹ = 1 := by
    field_simp [haq]
  calc
    a.toRat * ((a.toRat)⁻¹ * b.toRat) =
        (a.toRat * (a.toRat)⁻¹) * b.toRat := by ring
    _ = 1 * b.toRat := by rw [hunit]
    _ = b.toRat := by ring

theorem mul_right_crossEq_iff_of_not_crossEq_zero
    (a b c : RatioOrbit)
    (hc : ¬ RatioOrbit.crossEq c RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a c) (RatioOrbit.mul b c) ↔
      RatioOrbit.crossEq a b := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.crossEq_iff_toRat_eq]
  have hcq : c.toRat ≠ 0 := by
    intro hzero
    exact hc ((RatioOrbit.crossEq_iff_toRat_eq c RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : c.toRat * (c.toRat)⁻¹ = 1 := by
    field_simp [hcq]
  constructor
  · intro h
    calc
      a.toRat = a.toRat * 1 := by ring
      _ = a.toRat * (c.toRat * (c.toRat)⁻¹) := by rw [hunit]
      _ = (a.toRat * c.toRat) * (c.toRat)⁻¹ := by ring
      _ = (b.toRat * c.toRat) * (c.toRat)⁻¹ := by rw [h]
      _ = b.toRat * (c.toRat * (c.toRat)⁻¹) := by ring
      _ = b.toRat * 1 := by rw [hunit]
      _ = b.toRat := by ring
  · intro h
    rw [h]

theorem mul_left_crossEq_iff_of_not_crossEq_zero
    (a b c : RatioOrbit)
    (hc : ¬ RatioOrbit.crossEq c RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul c a) (RatioOrbit.mul c b) ↔
      RatioOrbit.crossEq a b := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.crossEq_iff_toRat_eq]
  have hcq : c.toRat ≠ 0 := by
    intro hzero
    exact hc ((RatioOrbit.crossEq_iff_toRat_eq c RatioOrbit.zero).mpr (by
      rw [hzero, RatioOrbit.zero_toRat]))
  have hunit : (c.toRat)⁻¹ * c.toRat = 1 := by
    field_simp [hcq]
  constructor
  · intro h
    calc
      a.toRat = 1 * a.toRat := by ring
      _ = ((c.toRat)⁻¹ * c.toRat) * a.toRat := by rw [hunit]
      _ = (c.toRat)⁻¹ * (c.toRat * a.toRat) := by ring
      _ = (c.toRat)⁻¹ * (c.toRat * b.toRat) := by rw [h]
      _ = ((c.toRat)⁻¹ * c.toRat) * b.toRat := by ring
      _ = 1 * b.toRat := by rw [hunit]
      _ = b.toRat := by ring
  · intro h
    rw [h]

theorem mul_crossEq_zero_iff (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero ↔
      RatioOrbit.crossEq a RatioOrbit.zero ∨
        RatioOrbit.crossEq b RatioOrbit.zero := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.zero_toRat, RatioOrbit.crossEq_iff_toRat_eq,
    RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.zero_toRat]
  exact mul_eq_zero

theorem zero_crossEq_mul_iff (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b) ↔
      RatioOrbit.crossEq a RatioOrbit.zero ∨
        RatioOrbit.crossEq b RatioOrbit.zero := by
  constructor
  · intro h
    exact (RatioOrbit.mul_crossEq_zero_iff a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm ((RatioOrbit.mul_crossEq_zero_iff a b).mpr h)

theorem mul_not_crossEq_zero_iff (a b : RatioOrbit) :
    ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero := by
  rw [RatioOrbit.mul_crossEq_zero_iff]
  constructor
  · intro h
    constructor
    · intro ha
      exact h (Or.inl ha)
    · intro hb
      exact h (Or.inr hb)
  · intro h hzero
    cases hzero with
    | inl ha => exact h.1 ha
    | inr hb => exact h.2 hb

theorem zero_not_crossEq_mul_iff (a b : RatioOrbit) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b) ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero := by
  rw [RatioOrbit.zero_crossEq_mul_iff]
  constructor
  · intro h
    constructor
    · intro ha
      exact h (Or.inl ha)
    · intro hb
      exact h (Or.inr hb)
  · intro h hzero
    cases hzero with
    | inl ha => exact h.1 ha
    | inr hb => exact h.2 hb

theorem mul_not_crossEq_zero_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero :=
  (RatioOrbit.mul_not_crossEq_zero_iff a b).mpr ⟨ha, hb⟩

theorem zero_not_crossEq_mul_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b) :=
  (RatioOrbit.zero_not_crossEq_mul_iff a b).mpr ⟨ha, hb⟩

theorem left_not_crossEq_zero_of_mul_not_crossEq_zero
    (a b : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq a RatioOrbit.zero :=
  ((RatioOrbit.mul_not_crossEq_zero_iff a b).mp h).1

theorem right_not_crossEq_zero_of_mul_not_crossEq_zero
    (a b : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq b RatioOrbit.zero :=
  ((RatioOrbit.mul_not_crossEq_zero_iff a b).mp h).2

theorem mul_crossEq_congr {a₁ a₂ b₁ b₂ : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂)
    (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.mul a₁ b₁) (RatioOrbit.mul a₂ b₂) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at ha hb ⊢
  rw [RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, ha, hb]

theorem mul_crossEq_congr_left {a₁ a₂ b : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂) :
    RatioOrbit.crossEq (RatioOrbit.mul a₁ b) (RatioOrbit.mul a₂ b) := by
  exact RatioOrbit.mul_crossEq_congr ha (RatioOrbit.crossEq_refl b)

theorem mul_crossEq_congr_right {a b₁ b₂ : RatioOrbit}
    (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.mul a b₁) (RatioOrbit.mul a b₂) := by
  exact RatioOrbit.mul_crossEq_congr (RatioOrbit.crossEq_refl a) hb

theorem mul_comm_crossEq (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) (RatioOrbit.mul b a) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat]
  ring

theorem mul_assoc_crossEq (a b c : RatioOrbit) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a b) c)
      (RatioOrbit.mul a (RatioOrbit.mul b c)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.mul_toRat]
  ring

theorem mul_one_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a RatioOrbit.one) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.one_toRat]
  ring

theorem one_mul_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.one a) a := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.one_toRat]
  ring

theorem mul_zero_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a RatioOrbit.zero) RatioOrbit.zero := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.zero_toRat]
  ring

theorem zero_mul_crossEq (a : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.zero a) RatioOrbit.zero := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.zero_toRat]
  ring

theorem one_not_crossEq_zero :
    ¬ RatioOrbit.crossEq RatioOrbit.one RatioOrbit.zero := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.one_toRat,
    RatioOrbit.zero_toRat]
  norm_num

theorem zero_not_crossEq_one :
    ¬ RatioOrbit.crossEq RatioOrbit.zero RatioOrbit.one := by
  intro h
  exact RatioOrbit.one_not_crossEq_zero (RatioOrbit.crossEq_symm h)

theorem recip_zero_crossEq_zero :
    RatioOrbit.crossEq (RatioOrbit.recip RatioOrbit.zero) RatioOrbit.zero := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.zero_toRat]
  norm_num

theorem zero_crossEq_recip_zero :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip RatioOrbit.zero) :=
  RatioOrbit.crossEq_symm RatioOrbit.recip_zero_crossEq_zero

theorem recip_one_crossEq_one :
    RatioOrbit.crossEq (RatioOrbit.recip RatioOrbit.one) RatioOrbit.one := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.one_toRat]
  norm_num

theorem one_crossEq_recip_one :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.recip RatioOrbit.one) :=
  RatioOrbit.crossEq_symm RatioOrbit.recip_one_crossEq_one

theorem factors_not_crossEq_zero_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
      ¬ RatioOrbit.crossEq b RatioOrbit.zero := by
  have hprod : ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero := by
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.zero_toRat]
    rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
      RatioOrbit.one_toRat] at h
    intro hzero
    rw [h] at hzero
    norm_num at hzero
  exact (RatioOrbit.mul_not_crossEq_zero_iff a b).mp hprod

theorem left_not_crossEq_zero_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    ¬ RatioOrbit.crossEq a RatioOrbit.zero :=
  (RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one a b h).1

theorem right_not_crossEq_zero_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    ¬ RatioOrbit.crossEq b RatioOrbit.zero :=
  (RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one a b h).2

theorem factors_not_crossEq_zero_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
      ¬ RatioOrbit.crossEq b RatioOrbit.zero :=
  RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one a b
    (RatioOrbit.crossEq_symm h)

theorem left_not_crossEq_zero_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    ¬ RatioOrbit.crossEq a RatioOrbit.zero :=
  (RatioOrbit.factors_not_crossEq_zero_of_one_crossEq_mul a b h).1

theorem right_not_crossEq_zero_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    ¬ RatioOrbit.crossEq b RatioOrbit.zero :=
  (RatioOrbit.factors_not_crossEq_zero_of_one_crossEq_mul a b h).2

theorem crossEq_recip_right_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    RatioOrbit.crossEq a (RatioOrbit.recip b) :=
  (RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero
    a b (RatioOrbit.right_not_crossEq_zero_of_mul_crossEq_one a b h)).mp h

theorem crossEq_recip_left_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    RatioOrbit.crossEq b (RatioOrbit.recip a) :=
  (RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero
    a b (RatioOrbit.left_not_crossEq_zero_of_mul_crossEq_one a b h)).mp h

theorem crossEq_recip_right_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    RatioOrbit.crossEq a (RatioOrbit.recip b) :=
  RatioOrbit.crossEq_recip_right_of_mul_crossEq_one a b
    (RatioOrbit.crossEq_symm h)

theorem crossEq_recip_left_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    RatioOrbit.crossEq b (RatioOrbit.recip a) :=
  RatioOrbit.crossEq_recip_left_of_mul_crossEq_one a b
    (RatioOrbit.crossEq_symm h)

theorem recip_mul_crossEq_mul_recip_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul a b))
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b)) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.recip_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.recip_toRat,
    RatioOrbit.recip_toRat]
  have haq : a.toRat ≠ 0 := by
    intro hzero
    exact ha ((RatioOrbit.crossEq_iff_toRat_eq a RatioOrbit.zero).mpr (by
      rw [RatioOrbit.zero_toRat]
      exact hzero))
  have hbq : b.toRat ≠ 0 := by
    intro hzero
    exact hb ((RatioOrbit.crossEq_iff_toRat_eq b RatioOrbit.zero).mpr (by
      rw [RatioOrbit.zero_toRat]
      exact hzero))
  have habq : a.toRat * b.toRat ≠ 0 := mul_ne_zero haq hbq
  field_simp [haq, hbq, habq]

theorem mul_recip_crossEq_recip_mul_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
      (RatioOrbit.recip (RatioOrbit.mul a b)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_mul_crossEq_mul_recip_of_not_crossEq_zero a b ha hb)

theorem recip_mul_crossEq_mul_recip_comm_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul a b))
      (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a)) :=
  RatioOrbit.crossEq_trans
    (RatioOrbit.recip_mul_crossEq_mul_recip_of_not_crossEq_zero a b ha hb)
    (RatioOrbit.mul_comm_crossEq (RatioOrbit.recip a) (RatioOrbit.recip b))

theorem mul_recip_comm_crossEq_recip_mul_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
      (RatioOrbit.recip (RatioOrbit.mul a b)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_mul_crossEq_mul_recip_comm_of_not_crossEq_zero
      a b ha hb)

theorem mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a b)
        (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b)))
      RatioOrbit.one := by
  rw [RatioOrbit.crossEq_iff_toRat_eq, RatioOrbit.mul_toRat,
    RatioOrbit.mul_toRat, RatioOrbit.mul_toRat, RatioOrbit.recip_toRat,
    RatioOrbit.recip_toRat, RatioOrbit.one_toRat]
  have haq : a.toRat ≠ 0 := by
    intro hzero
    exact ha ((RatioOrbit.crossEq_iff_toRat_eq a RatioOrbit.zero).mpr (by
      rw [RatioOrbit.zero_toRat]
      exact hzero))
  have hbq : b.toRat ≠ 0 := by
    intro hzero
    exact hb ((RatioOrbit.crossEq_iff_toRat_eq b RatioOrbit.zero).mpr (by
      rw [RatioOrbit.zero_toRat]
      exact hzero))
  field_simp [haq, hbq]

theorem recip_pair_mul_mul_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul
        (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
        (RatioOrbit.mul a b))
      RatioOrbit.one := by
  exact RatioOrbit.crossEq_trans
    (RatioOrbit.mul_comm_crossEq
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
      (RatioOrbit.mul a b))
    (RatioOrbit.mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero a b ha hb)

theorem mul_mul_recip_pair_comm_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a b)
        (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a)))
      RatioOrbit.one := by
  exact RatioOrbit.crossEq_trans
    (RatioOrbit.mul_crossEq_congr_right
      (RatioOrbit.mul_comm_crossEq (RatioOrbit.recip b) (RatioOrbit.recip a)))
    (RatioOrbit.mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero a b ha hb)

theorem recip_pair_comm_mul_mul_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul
        (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
        (RatioOrbit.mul a b))
      RatioOrbit.one := by
  exact RatioOrbit.crossEq_trans
    (RatioOrbit.mul_comm_crossEq
      (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
      (RatioOrbit.mul a b))
    (RatioOrbit.mul_mul_recip_pair_comm_crossEq_one_of_not_crossEq_zero
      a b ha hb)

theorem mul_recip_pair_not_crossEq_zero_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
      RatioOrbit.zero := by
  exact RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero
    (RatioOrbit.recip a) (RatioOrbit.recip b)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero a).mpr ha)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero b).mpr hb)

theorem zero_not_crossEq_mul_recip_pair_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero
      (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b)) := by
  exact RatioOrbit.zero_not_crossEq_mul_of_not_crossEq_zero
    (RatioOrbit.recip a) (RatioOrbit.recip b)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero a).mpr ha)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero b).mpr hb)

theorem mul_recip_pair_comm_not_crossEq_zero_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
      RatioOrbit.zero := by
  exact RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero
    (RatioOrbit.recip b) (RatioOrbit.recip a)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero b).mpr hb)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero a).mpr ha)

theorem zero_not_crossEq_mul_recip_pair_comm_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero
      (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a)) := by
  exact RatioOrbit.zero_not_crossEq_mul_of_not_crossEq_zero
    (RatioOrbit.recip b) (RatioOrbit.recip a)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero b).mpr hb)
    ((RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero a).mpr ha)

theorem mul_recip_crossEq_one_of_not_crossEq_zero
    (a : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recip a))
      RatioOrbit.one := by
  have hnum : ¬ SignedOrbit.balanced a.num SignedOrbit.zero := by
    intro hbal
    exact h ((RatioOrbit.crossEq_zero_iff_num_balanced_zero a).mpr hbal)
  exact RatioOrbit.mul_recip_crossEq_one_of_not_balanced_zero a hnum

theorem recip_mul_crossEq_one_of_not_crossEq_zero
    (a : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recip a) a)
      RatioOrbit.one := by
  have hnum : ¬ SignedOrbit.balanced a.num SignedOrbit.zero := by
    intro hbal
    exact h ((RatioOrbit.crossEq_zero_iff_num_balanced_zero a).mpr hbal)
  exact RatioOrbit.recip_mul_crossEq_one_of_not_balanced_zero a hnum

theorem one_crossEq_mul_recip_of_not_crossEq_zero
    (a : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul a (RatioOrbit.recip a)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.mul_recip_crossEq_one_of_not_crossEq_zero a h)

theorem one_crossEq_recip_mul_of_not_crossEq_zero
    (a : RatioOrbit)
    (h : ¬ RatioOrbit.crossEq a RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul (RatioOrbit.recip a) a) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_mul_crossEq_one_of_not_crossEq_zero a h)

theorem mul_product_recip_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul a b)
        (RatioOrbit.recip (RatioOrbit.mul a b)))
      RatioOrbit.one :=
  RatioOrbit.mul_recip_crossEq_one_of_not_crossEq_zero
    (RatioOrbit.mul a b)
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero a b ha hb)

theorem recip_product_mul_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul a b))
        (RatioOrbit.mul a b))
      RatioOrbit.one :=
  RatioOrbit.recip_mul_crossEq_one_of_not_crossEq_zero
    (RatioOrbit.mul a b)
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero a b ha hb)

theorem one_crossEq_mul_product_recip_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul (RatioOrbit.mul a b)
        (RatioOrbit.recip (RatioOrbit.mul a b))) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.mul_product_recip_crossEq_one_of_not_crossEq_zero a b ha hb)

theorem one_crossEq_recip_product_mul_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul a b))
        (RatioOrbit.mul a b)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_product_mul_crossEq_one_of_not_crossEq_zero a b ha hb)

theorem recip_product_not_crossEq_zero_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul a b)) RatioOrbit.zero :=
  (RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero
    (RatioOrbit.mul a b)).mpr
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero a b ha hb)

theorem zero_not_crossEq_recip_product_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero
      (RatioOrbit.recip (RatioOrbit.mul a b)) :=
  (RatioOrbit.zero_not_crossEq_recip_iff_not_crossEq_zero
    (RatioOrbit.mul a b)).mpr
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero a b ha hb)

theorem recip_product_comm_not_crossEq_zero_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul b a)) RatioOrbit.zero :=
  (RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero
    (RatioOrbit.mul b a)).mpr
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero b a hb ha)

theorem zero_not_crossEq_recip_product_comm_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    ¬ RatioOrbit.crossEq RatioOrbit.zero
      (RatioOrbit.recip (RatioOrbit.mul b a)) :=
  (RatioOrbit.zero_not_crossEq_recip_iff_not_crossEq_zero
    (RatioOrbit.mul b a)).mpr
    (RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero b a hb ha)

theorem recip_product_comm_crossEq_recip_product (a b : RatioOrbit) :
    RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul a b))
      (RatioOrbit.recip (RatioOrbit.mul b a)) := by
  exact RatioOrbit.recip_crossEq_congr (RatioOrbit.mul_comm_crossEq a b)

theorem recip_product_crossEq_recip_product_comm (a b : RatioOrbit) :
    RatioOrbit.crossEq
      (RatioOrbit.recip (RatioOrbit.mul b a))
      (RatioOrbit.recip (RatioOrbit.mul a b)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_product_comm_crossEq_recip_product a b)

theorem mul_product_comm_recip_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.mul b a)
        (RatioOrbit.recip (RatioOrbit.mul b a)))
      RatioOrbit.one :=
  RatioOrbit.mul_product_recip_crossEq_one_of_not_crossEq_zero b a hb ha

theorem recip_product_comm_mul_crossEq_one_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq
      (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul b a))
        (RatioOrbit.mul b a))
      RatioOrbit.one :=
  RatioOrbit.recip_product_mul_crossEq_one_of_not_crossEq_zero b a hb ha

theorem one_crossEq_mul_product_comm_recip_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul (RatioOrbit.mul b a)
        (RatioOrbit.recip (RatioOrbit.mul b a))) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.mul_product_comm_recip_crossEq_one_of_not_crossEq_zero
      a b ha hb)

theorem one_crossEq_recip_product_comm_mul_of_not_crossEq_zero
    (a b : RatioOrbit)
    (ha : ¬ RatioOrbit.crossEq a RatioOrbit.zero)
    (hb : ¬ RatioOrbit.crossEq b RatioOrbit.zero) :
    RatioOrbit.crossEq RatioOrbit.one
      (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul b a))
        (RatioOrbit.mul b a)) :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.recip_product_comm_mul_crossEq_one_of_not_crossEq_zero
      a b ha hb)

theorem recip_right_crossEq_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    RatioOrbit.crossEq (RatioOrbit.recip b) a :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.crossEq_recip_right_of_mul_crossEq_one a b h)

theorem recip_left_crossEq_of_mul_crossEq_one
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one) :
    RatioOrbit.crossEq (RatioOrbit.recip a) b :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.crossEq_recip_left_of_mul_crossEq_one a b h)

theorem recip_right_crossEq_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    RatioOrbit.crossEq (RatioOrbit.recip b) a :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.crossEq_recip_right_of_one_crossEq_mul a b h)

theorem recip_left_crossEq_of_one_crossEq_mul
    (a b : RatioOrbit)
    (h : RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b)) :
    RatioOrbit.crossEq (RatioOrbit.recip a) b :=
  RatioOrbit.crossEq_symm
    (RatioOrbit.crossEq_recip_left_of_one_crossEq_mul a b h)

theorem mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
        RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.right_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.crossEq_recip_right_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero
        a b h.1).mpr h.2

theorem mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        RatioOrbit.crossEq b (RatioOrbit.recip a) := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.left_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.crossEq_recip_left_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero
        a b h.1).mpr h.2

theorem one_crossEq_mul_iff_right_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
        RatioOrbit.crossEq a (RatioOrbit.recip b) := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
        a b).mpr h)

theorem one_crossEq_mul_iff_left_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        RatioOrbit.crossEq b (RatioOrbit.recip a) := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip
        a b).mpr h)

theorem mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
        RatioOrbit.crossEq (RatioOrbit.recip b) a := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.right_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.recip_right_crossEq_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
        a b).mpr ⟨h.1, RatioOrbit.crossEq_symm h.2⟩

theorem mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        RatioOrbit.crossEq (RatioOrbit.recip a) b := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.left_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.recip_left_crossEq_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip
        a b).mpr ⟨h.1, RatioOrbit.crossEq_symm h.2⟩

theorem one_crossEq_mul_iff_right_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
        RatioOrbit.crossEq (RatioOrbit.recip b) a := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq
        a b).mpr h)

theorem one_crossEq_mul_iff_left_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        RatioOrbit.crossEq (RatioOrbit.recip a) b := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq
        a b).mpr h)

theorem mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
        RatioOrbit.crossEq a (RatioOrbit.recip b) ∧
          RatioOrbit.crossEq b (RatioOrbit.recip a) := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.crossEq_recip_right_of_mul_crossEq_one a b h,
      RatioOrbit.crossEq_recip_left_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
        a b).mpr ⟨h.1.2, h.2.1⟩

theorem one_crossEq_mul_iff_factors_not_crossEq_zero_and_crossEq_recip
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
        RatioOrbit.crossEq a (RatioOrbit.recip b) ∧
          RatioOrbit.crossEq b (RatioOrbit.recip a) := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip
        a b).mpr h)

theorem mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
      (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
        RatioOrbit.crossEq (RatioOrbit.recip b) a ∧
          RatioOrbit.crossEq (RatioOrbit.recip a) b := by
  constructor
  · intro h
    exact ⟨
      RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one a b h,
      RatioOrbit.recip_right_crossEq_of_mul_crossEq_one a b h,
      RatioOrbit.recip_left_crossEq_of_mul_crossEq_one a b h⟩
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq
        a b).mpr ⟨h.1.2, h.2.1⟩

theorem one_crossEq_mul_iff_factors_not_crossEq_zero_and_recip_crossEq
    (a b : RatioOrbit) :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
      (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
        ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
        RatioOrbit.crossEq (RatioOrbit.recip b) a ∧
          RatioOrbit.crossEq (RatioOrbit.recip a) b := by
  constructor
  · intro h
    exact
      (RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq
        a b).mp (RatioOrbit.crossEq_symm h)
  · intro h
    exact RatioOrbit.crossEq_symm
      ((RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq
        a b).mpr h)

end RatioOrbit

/-- Step-1 certificate for internal signed-orbit order and absolute value. -/
structure IntegerOrderCertificate : Prop where
  truncated_sub_display :
    ∀ a b : DistinctionNat,
      (DistinctionNat.truncatedSub a b).toNat = a.toNat - b.toNat
  leq_display :
    ∀ a b : DistinctionNat,
      DistinctionNat.leq a b = true ↔ a.toNat ≤ b.toNat
  absdiff_display :
    ∀ a b : DistinctionNat,
      (DistinctionNat.absDiff a b).toNat =
        Int.natAbs ((a.toNat : ℤ) - (b.toNat : ℤ))
  signed_nonneg_display :
    ∀ z : SignedOrbit, SignedOrbit.nonneg z ↔ 0 ≤ z.toInt
  signed_nonneg_flag_display :
    ∀ z : SignedOrbit, z.nonnegFlag = true ↔ 0 ≤ z.toInt
  signed_abs_display :
    ∀ z : SignedOrbit, z.abs.toNat = Int.natAbs z.toInt
  signed_le_display :
    ∀ a b : SignedOrbit, SignedOrbit.le a b ↔ a.toInt ≤ b.toInt
  signed_lt_display :
    ∀ a b : SignedOrbit, SignedOrbit.lt a b ↔ a.toInt < b.toInt
  abs_nonzero_internal :
    ∀ z : SignedOrbit,
      (¬ SignedOrbit.balanced z SignedOrbit.zero) →
        z.abs ≠ DistinctionNat.zero
  signed_le_reflexive :
    ∀ a : SignedOrbit, SignedOrbit.le a a
  signed_le_transitive :
    ∀ {a b c : SignedOrbit},
      SignedOrbit.le a b → SignedOrbit.le b c → SignedOrbit.le a c
  signed_le_antisymmetric_balanced :
    ∀ {a b : SignedOrbit},
      SignedOrbit.le a b → SignedOrbit.le b a → SignedOrbit.balanced a b
  signed_le_total :
    ∀ a b : SignedOrbit, SignedOrbit.le a b ∨ SignedOrbit.le b a
  signed_order_trichotomy :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt a b ∨ SignedOrbit.balanced a b ∨ SignedOrbit.lt b a
  signed_negativeFlag_eq_true_iff_nonnegFlag_eq_false :
    ∀ z : SignedOrbit,
      z.negativeFlag = true ↔ z.nonnegFlag = false
  signed_negativeFlag_eq_false_iff_nonnegFlag_eq_true :
    ∀ z : SignedOrbit,
      z.negativeFlag = false ↔ z.nonnegFlag = true
  signed_flags_exclusive :
    ∀ z : SignedOrbit, ¬ (z.nonnegFlag = true ∧ z.negativeFlag = true)
  signed_flags_exhaustive :
    ∀ z : SignedOrbit, z.nonnegFlag = true ∨ z.negativeFlag = true
  signed_zero_le_iff_nonnegFlag :
    ∀ z : SignedOrbit,
      SignedOrbit.le SignedOrbit.zero z ↔ z.nonnegFlag = true
  signed_lt_zero_iff_negativeFlag :
    ∀ z : SignedOrbit,
      SignedOrbit.lt z SignedOrbit.zero ↔ z.negativeFlag = true
  signed_zero_lt_iff_nonnegFlag_and_not_balanced_zero :
    ∀ z : SignedOrbit,
      SignedOrbit.lt SignedOrbit.zero z ↔
        z.nonnegFlag = true ∧
          ¬ SignedOrbit.balanced z SignedOrbit.zero
  signed_nonnegFlag_eq_of_balanced :
    ∀ {z w : SignedOrbit}, SignedOrbit.balanced z w →
      z.nonnegFlag = w.nonnegFlag
  signed_negativeFlag_eq_of_balanced :
    ∀ {z w : SignedOrbit}, SignedOrbit.balanced z w →
      z.negativeFlag = w.negativeFlag
  signed_nonneg_iff_of_balanced :
    ∀ {z w : SignedOrbit}, SignedOrbit.balanced z w →
      (SignedOrbit.nonneg z ↔ SignedOrbit.nonneg w)
  signed_add_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced (SignedOrbit.add a b) (SignedOrbit.add a' b')
  signed_negate_congr_of_balanced :
    ∀ {a a' : SignedOrbit}, SignedOrbit.balanced a a' →
      SignedOrbit.balanced (SignedOrbit.negate a) (SignedOrbit.negate a')
  signed_sub_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a' b')
  signed_sub_congr_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a' b)
  signed_sub_congr_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub a b')
  signed_nonnegFlag_sub_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.sub a b).nonnegFlag =
          (SignedOrbit.sub a' b).nonnegFlag
  signed_nonnegFlag_sub_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).nonnegFlag =
          (SignedOrbit.sub a b').nonnegFlag
  signed_negativeFlag_sub_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.sub a b).negativeFlag =
          (SignedOrbit.sub a' b).negativeFlag
  signed_negativeFlag_sub_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).negativeFlag =
          (SignedOrbit.sub a b').negativeFlag
  signed_nonnegFlag_sub_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).nonnegFlag =
          (SignedOrbit.sub a' b').nonnegFlag
  signed_negativeFlag_sub_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).negativeFlag =
          (SignedOrbit.sub a' b').negativeFlag
  signed_scaleByNat_congr_of_balanced :
    ∀ {z w : SignedOrbit}, SignedOrbit.balanced z w →
      ∀ d : DistinctionNat,
        SignedOrbit.balanced (z.scaleByNat d) (w.scaleByNat d)
  signed_scaleByNat_balanced_zero_of_balanced_zero :
    ∀ {z : SignedOrbit}, SignedOrbit.balanced z SignedOrbit.zero →
      ∀ d : DistinctionNat,
        SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero
  signed_mul_ofOrbit_balanced_scaleByNat :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (z.scaleByNat d)
  signed_ofOrbit_mul_balanced_scaleByNat :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (z.scaleByNat d)
  signed_abs_mul :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).abs = z.abs * w.abs
  signed_mul_balanced_zero_iff :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero ↔
        SignedOrbit.balanced z SignedOrbit.zero ∨
          SignedOrbit.balanced w SignedOrbit.zero
  signed_mul_not_balanced_zero_iff :
    ∀ z w : SignedOrbit,
      ¬ SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero ↔
        ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
          ¬ SignedOrbit.balanced w SignedOrbit.zero
  signed_balanced_mul_left_iff_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      ¬ SignedOrbit.balanced a SignedOrbit.zero →
        (SignedOrbit.balanced (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
          SignedOrbit.balanced z w)
  signed_balanced_mul_right_iff_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      ¬ SignedOrbit.balanced a SignedOrbit.zero →
        (SignedOrbit.balanced (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
          SignedOrbit.balanced z w)
  signed_le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          (SignedOrbit.le (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
            SignedOrbit.le z w)
  signed_lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          (SignedOrbit.lt (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
            SignedOrbit.lt z w)
  signed_le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          (SignedOrbit.le (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
            SignedOrbit.le z w)
  signed_lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          (SignedOrbit.lt (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
            SignedOrbit.lt z w)
  signed_le_mul_left_iff_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        (SignedOrbit.le (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
          SignedOrbit.le w z)
  signed_lt_mul_left_iff_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        (SignedOrbit.lt (SignedOrbit.mul a z) (SignedOrbit.mul a w) ↔
          SignedOrbit.lt w z)
  signed_le_mul_right_iff_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        (SignedOrbit.le (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
          SignedOrbit.le w z)
  signed_lt_mul_right_iff_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        (SignedOrbit.lt (SignedOrbit.mul z a) (SignedOrbit.mul w a) ↔
          SignedOrbit.lt w z)
  signed_abs_mul_eq_zero_iff :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).abs = DistinctionNat.zero ↔
        z.abs = DistinctionNat.zero ∨ w.abs = DistinctionNat.zero
  signed_abs_mul_ne_zero_iff :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).abs ≠ DistinctionNat.zero ↔
        z.abs ≠ DistinctionNat.zero ∧ w.abs ≠ DistinctionNat.zero
  signed_abs_mul_eq_zero_iff_balanced_zero :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).abs = DistinctionNat.zero ↔
        SignedOrbit.balanced z SignedOrbit.zero ∨
          SignedOrbit.balanced w SignedOrbit.zero
  signed_abs_mul_ne_zero_iff_not_balanced_zero :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).abs ≠ DistinctionNat.zero ↔
        ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
          ¬ SignedOrbit.balanced w SignedOrbit.zero
  signed_abs_scaleByNat :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (z.scaleByNat d).abs = z.abs * d
  signed_abs_mul_ofOrbit_right :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs = z.abs * d
  signed_abs_mul_ofOrbit_left :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs = z.abs * d
  signed_mul_ofOrbit_right_balanced_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d)) SignedOrbit.zero ↔
          SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero
  signed_mul_ofOrbit_left_balanced_zero_iff :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z) SignedOrbit.zero ↔
          SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero
  signed_mul_ofOrbit_right_not_balanced_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      ¬ SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d)) SignedOrbit.zero ↔
          ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero
  signed_mul_ofOrbit_left_not_balanced_zero_iff :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      ¬ SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z) SignedOrbit.zero ↔
          ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero
  signed_nonnegFlag_scaleByNat_of_ne_zero :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (z.scaleByNat d).nonnegFlag = z.nonnegFlag
  signed_negativeFlag_scaleByNat_of_ne_zero :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (z.scaleByNat d).negativeFlag = z.negativeFlag
  signed_scaleByNat_balanced_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero ↔
        SignedOrbit.balanced z SignedOrbit.zero ∨ d = DistinctionNat.zero
  signed_scaleByNat_not_balanced_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      ¬ SignedOrbit.balanced (z.scaleByNat d) SignedOrbit.zero ↔
        ¬ SignedOrbit.balanced z SignedOrbit.zero ∧ d ≠ DistinctionNat.zero
  signed_abs_scaleByNat_eq_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (z.scaleByNat d).abs = DistinctionNat.zero ↔
        z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero
  signed_abs_scaleByNat_ne_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (z.scaleByNat d).abs ≠ DistinctionNat.zero ↔
        z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero
  signed_abs_mul_ofOrbit_right_eq_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs = DistinctionNat.zero ↔
        z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero
  signed_abs_mul_ofOrbit_left_eq_zero_iff :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs = DistinctionNat.zero ↔
        z.abs = DistinctionNat.zero ∨ d = DistinctionNat.zero
  signed_abs_mul_ofOrbit_right_ne_zero_iff :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat,
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).abs ≠ DistinctionNat.zero ↔
        z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero
  signed_abs_mul_ofOrbit_left_ne_zero_iff :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit,
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).abs ≠ DistinctionNat.zero ↔
        z.abs ≠ DistinctionNat.zero ∧ d ≠ DistinctionNat.zero
  signed_le_scaleByNat_of_le :
    ∀ {z w : SignedOrbit},
      SignedOrbit.le z w → ∀ d : DistinctionNat,
        SignedOrbit.le (z.scaleByNat d) (w.scaleByNat d)
  signed_le_scaleByNat_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.le (z.scaleByNat d) (w.scaleByNat d) ↔
        SignedOrbit.le z w)
  signed_lt_scaleByNat_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.lt (z.scaleByNat d) (w.scaleByNat d) ↔
        SignedOrbit.lt z w)
  signed_balanced_scaleByNat_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.balanced (z.scaleByNat d) (w.scaleByNat d) ↔
        SignedOrbit.balanced z w)
  signed_cmp_scaleByNat_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      SignedOrbit.cmp (z.scaleByNat d) (w.scaleByNat d) =
        SignedOrbit.cmp z w
  signed_le_mul_ofOrbit_right_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.le
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
          SignedOrbit.le z w)
  signed_lt_mul_ofOrbit_right_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.lt
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
          SignedOrbit.lt z w)
  signed_balanced_mul_ofOrbit_right_iff_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.balanced
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) ↔
          SignedOrbit.balanced z w)
  signed_cmp_mul_ofOrbit_right_of_ne_zero :
    ∀ z w : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      SignedOrbit.cmp
        (SignedOrbit.mul z (SignedOrbit.ofOrbit d))
        (SignedOrbit.mul w (SignedOrbit.ofOrbit d)) =
          SignedOrbit.cmp z w
  signed_le_mul_ofOrbit_left_iff_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z w : SignedOrbit, d ≠ DistinctionNat.zero →
      (SignedOrbit.le
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
          SignedOrbit.le z w)
  signed_lt_mul_ofOrbit_left_iff_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z w : SignedOrbit, d ≠ DistinctionNat.zero →
      (SignedOrbit.lt
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
          SignedOrbit.lt z w)
  signed_balanced_mul_ofOrbit_left_iff_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z w : SignedOrbit, d ≠ DistinctionNat.zero →
      (SignedOrbit.balanced
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) ↔
          SignedOrbit.balanced z w)
  signed_cmp_mul_ofOrbit_left_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z w : SignedOrbit, d ≠ DistinctionNat.zero →
      SignedOrbit.cmp
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) z)
        (SignedOrbit.mul (SignedOrbit.ofOrbit d) w) =
          SignedOrbit.cmp z w
  signed_cmp_mul_left_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          SignedOrbit.cmp (SignedOrbit.mul a z) (SignedOrbit.mul a w) =
            SignedOrbit.cmp z w
  signed_cmp_mul_right_of_nonnegFlag_of_not_balanced_zero :
    ∀ a z w : SignedOrbit,
      a.nonnegFlag = true →
        ¬ SignedOrbit.balanced a SignedOrbit.zero →
          SignedOrbit.cmp (SignedOrbit.mul z a) (SignedOrbit.mul w a) =
            SignedOrbit.cmp z w
  signed_cmp_mul_left_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        SignedOrbit.cmp (SignedOrbit.mul a z) (SignedOrbit.mul a w) =
          SignedOrbit.cmp w z
  signed_cmp_mul_right_of_negativeFlag :
    ∀ a z w : SignedOrbit,
      a.negativeFlag = true →
        SignedOrbit.cmp (SignedOrbit.mul z a) (SignedOrbit.mul w a) =
          SignedOrbit.cmp w z
  signed_nonnegFlag_mul_of_nonnegFlag_of_nonnegFlag :
    ∀ z w : SignedOrbit,
      z.nonnegFlag = true → w.nonnegFlag = true →
        (SignedOrbit.mul z w).nonnegFlag = true
  signed_nonnegFlag_mul_of_negativeFlag_of_negativeFlag :
    ∀ z w : SignedOrbit,
      z.negativeFlag = true → w.negativeFlag = true →
        (SignedOrbit.mul z w).nonnegFlag = true
  signed_negativeFlag_mul_of_nonnegFlag_of_not_balanced_zero_of_negativeFlag :
    ∀ z w : SignedOrbit,
      z.nonnegFlag = true →
        ¬ SignedOrbit.balanced z SignedOrbit.zero →
          w.negativeFlag = true →
            (SignedOrbit.mul z w).negativeFlag = true
  signed_negativeFlag_mul_of_negativeFlag_of_nonnegFlag_of_not_balanced_zero :
    ∀ z w : SignedOrbit,
      z.negativeFlag = true →
        w.nonnegFlag = true →
          ¬ SignedOrbit.balanced w SignedOrbit.zero →
            (SignedOrbit.mul z w).negativeFlag = true
  signed_negativeFlag_mul_iff :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).negativeFlag = true ↔
        (z.nonnegFlag = true ∧
            ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
            w.negativeFlag = true) ∨
          (z.negativeFlag = true ∧
            w.nonnegFlag = true ∧
            ¬ SignedOrbit.balanced w SignedOrbit.zero)
  signed_nonnegFlag_mul_iff_not_strict_opposite_sign :
    ∀ z w : SignedOrbit,
      (SignedOrbit.mul z w).nonnegFlag = true ↔
        ¬ ((z.nonnegFlag = true ∧
                ¬ SignedOrbit.balanced z SignedOrbit.zero ∧
                w.negativeFlag = true) ∨
              (z.negativeFlag = true ∧
                w.nonnegFlag = true ∧
                ¬ SignedOrbit.balanced w SignedOrbit.zero))
  signed_nonnegFlag_mul_of_balanced_zero_left :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced z SignedOrbit.zero →
        (SignedOrbit.mul z w).nonnegFlag = true
  signed_nonnegFlag_mul_of_balanced_zero_right :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced w SignedOrbit.zero →
        (SignedOrbit.mul z w).nonnegFlag = true
  signed_negativeFlag_mul_eq_false_of_balanced_zero_left :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced z SignedOrbit.zero →
        (SignedOrbit.mul z w).negativeFlag = false
  signed_negativeFlag_mul_eq_false_of_balanced_zero_right :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced w SignedOrbit.zero →
        (SignedOrbit.mul z w).negativeFlag = false
  signed_mul_balanced_zero_of_balanced_zero_left :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced z SignedOrbit.zero →
        SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero
  signed_mul_balanced_zero_of_balanced_zero_right :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced w SignedOrbit.zero →
        SignedOrbit.balanced (SignedOrbit.mul z w) SignedOrbit.zero
  signed_abs_mul_eq_zero_of_balanced_zero_left :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced z SignedOrbit.zero →
        (SignedOrbit.mul z w).abs = DistinctionNat.zero
  signed_abs_mul_eq_zero_of_balanced_zero_right :
    ∀ z w : SignedOrbit,
      SignedOrbit.balanced w SignedOrbit.zero →
        (SignedOrbit.mul z w).abs = DistinctionNat.zero
  signed_mul_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a' b')
  signed_mul_congr_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a' b)
  signed_mul_congr_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul a b')
  signed_nonnegFlag_mul_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).nonnegFlag =
          (SignedOrbit.mul a' b').nonnegFlag
  signed_nonnegFlag_mul_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.mul a b).nonnegFlag =
          (SignedOrbit.mul a' b).nonnegFlag
  signed_nonnegFlag_mul_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).nonnegFlag =
          (SignedOrbit.mul a b').nonnegFlag
  signed_negativeFlag_mul_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).negativeFlag =
          (SignedOrbit.mul a' b').negativeFlag
  signed_negativeFlag_mul_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.mul a b).negativeFlag =
          (SignedOrbit.mul a' b).negativeFlag
  signed_negativeFlag_mul_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).negativeFlag =
          (SignedOrbit.mul a b').negativeFlag
  signed_abs_mul_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).abs = (SignedOrbit.mul a' b').abs
  signed_abs_mul_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.mul a b).abs = (SignedOrbit.mul a' b).abs
  signed_abs_mul_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.mul a b).abs = (SignedOrbit.mul a b').abs
  signed_mul_balanced_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.mul a' b) SignedOrbit.zero)
  signed_mul_balanced_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.mul a b') SignedOrbit.zero)
  signed_abs_mul_eq_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        ((SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.mul a' b).abs = DistinctionNat.zero)
  signed_abs_mul_eq_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        ((SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.mul a b').abs = DistinctionNat.zero)
  signed_abs_mul_ne_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        ((SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.mul a' b).abs ≠ DistinctionNat.zero)
  signed_abs_mul_ne_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        ((SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.mul a b').abs ≠ DistinctionNat.zero)
  signed_mul_balanced_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.mul a' b') SignedOrbit.zero)
  signed_abs_mul_eq_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        ((SignedOrbit.mul a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.mul a' b').abs = DistinctionNat.zero)
  signed_abs_mul_ne_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        ((SignedOrbit.mul a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.mul a' b').abs ≠ DistinctionNat.zero)
  signed_le_product_left_factor_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.le (SignedOrbit.mul a b) c ↔
          SignedOrbit.le (SignedOrbit.mul a' b) c)
  signed_le_product_right_factor_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.le (SignedOrbit.mul a b) c ↔
          SignedOrbit.le (SignedOrbit.mul a b') c)
  signed_le_of_product_left_factor_iff_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.le c (SignedOrbit.mul a b) ↔
          SignedOrbit.le c (SignedOrbit.mul a' b))
  signed_le_of_product_right_factor_iff_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.le c (SignedOrbit.mul a b) ↔
          SignedOrbit.le c (SignedOrbit.mul a b'))
  signed_lt_product_left_factor_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.lt (SignedOrbit.mul a b) c ↔
          SignedOrbit.lt (SignedOrbit.mul a' b) c)
  signed_lt_product_right_factor_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.lt (SignedOrbit.mul a b) c ↔
          SignedOrbit.lt (SignedOrbit.mul a b') c)
  signed_lt_of_product_left_factor_iff_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.lt c (SignedOrbit.mul a b) ↔
          SignedOrbit.lt c (SignedOrbit.mul a' b))
  signed_lt_of_product_right_factor_iff_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.lt c (SignedOrbit.mul a b) ↔
          SignedOrbit.lt c (SignedOrbit.mul a b'))
  signed_cmp_product_left_factor_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.cmp (SignedOrbit.mul a b) c =
          SignedOrbit.cmp (SignedOrbit.mul a' b) c
  signed_cmp_product_right_factor_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.cmp (SignedOrbit.mul a b) c =
          SignedOrbit.cmp (SignedOrbit.mul a b') c
  signed_cmp_of_product_left_factor_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.cmp c (SignedOrbit.mul a b) =
          SignedOrbit.cmp c (SignedOrbit.mul a' b)
  signed_cmp_of_product_right_factor_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.cmp c (SignedOrbit.mul a b) =
          SignedOrbit.cmp c (SignedOrbit.mul a b')
  signed_le_product_factors_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.le (SignedOrbit.mul a b) c ↔
          SignedOrbit.le (SignedOrbit.mul a' b') c)
  signed_le_of_product_factors_iff_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.le c (SignedOrbit.mul a b) ↔
          SignedOrbit.le c (SignedOrbit.mul a' b'))
  signed_lt_product_factors_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.lt (SignedOrbit.mul a b) c ↔
          SignedOrbit.lt (SignedOrbit.mul a' b') c)
  signed_lt_of_product_factors_iff_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.lt c (SignedOrbit.mul a b) ↔
          SignedOrbit.lt c (SignedOrbit.mul a' b'))
  signed_cmp_product_factors_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.cmp (SignedOrbit.mul a b) c =
          SignedOrbit.cmp (SignedOrbit.mul a' b') c
  signed_cmp_of_product_factors_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.cmp c (SignedOrbit.mul a b) =
          SignedOrbit.cmp c (SignedOrbit.mul a' b')
  signed_le_products_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.le (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
            SignedOrbit.le (SignedOrbit.mul a' b') (SignedOrbit.mul c' d'))
  signed_lt_products_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.lt (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
            SignedOrbit.lt (SignedOrbit.mul a' b') (SignedOrbit.mul c' d'))
  signed_cmp_products_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          SignedOrbit.cmp (SignedOrbit.mul a b) (SignedOrbit.mul c d) =
            SignedOrbit.cmp (SignedOrbit.mul a' b') (SignedOrbit.mul c' d')
  signed_balanced_product_left_factor_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
          SignedOrbit.balanced (SignedOrbit.mul a' b) c)
  signed_balanced_product_right_factor_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
          SignedOrbit.balanced (SignedOrbit.mul a b') c)
  signed_balanced_product_factors_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.mul a b) c ↔
          SignedOrbit.balanced (SignedOrbit.mul a' b') c)
  signed_balanced_products_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.balanced (SignedOrbit.mul a b) (SignedOrbit.mul c d) ↔
            SignedOrbit.balanced (SignedOrbit.mul a' b') (SignedOrbit.mul c' d'))
  signed_le_sub_left_input_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.le (SignedOrbit.sub a b) c ↔
          SignedOrbit.le (SignedOrbit.sub a' b) c)
  signed_le_sub_right_input_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.le (SignedOrbit.sub a b) c ↔
          SignedOrbit.le (SignedOrbit.sub a b') c)
  signed_le_of_sub_left_input_iff_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.le c (SignedOrbit.sub a b) ↔
          SignedOrbit.le c (SignedOrbit.sub a' b))
  signed_le_of_sub_right_input_iff_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.le c (SignedOrbit.sub a b) ↔
          SignedOrbit.le c (SignedOrbit.sub a b'))
  signed_lt_sub_left_input_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.lt (SignedOrbit.sub a b) c ↔
          SignedOrbit.lt (SignedOrbit.sub a' b) c)
  signed_lt_sub_right_input_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.lt (SignedOrbit.sub a b) c ↔
          SignedOrbit.lt (SignedOrbit.sub a b') c)
  signed_lt_of_sub_left_input_iff_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.lt c (SignedOrbit.sub a b) ↔
          SignedOrbit.lt c (SignedOrbit.sub a' b))
  signed_lt_of_sub_right_input_iff_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.lt c (SignedOrbit.sub a b) ↔
          SignedOrbit.lt c (SignedOrbit.sub a b'))
  signed_cmp_sub_left_input_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.cmp (SignedOrbit.sub a b) c =
          SignedOrbit.cmp (SignedOrbit.sub a' b) c
  signed_cmp_sub_right_input_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.cmp (SignedOrbit.sub a b) c =
          SignedOrbit.cmp (SignedOrbit.sub a b') c
  signed_cmp_of_sub_left_input_of_balanced :
    ∀ {c a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        SignedOrbit.cmp c (SignedOrbit.sub a b) =
          SignedOrbit.cmp c (SignedOrbit.sub a' b)
  signed_cmp_of_sub_right_input_of_balanced :
    ∀ {c a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        SignedOrbit.cmp c (SignedOrbit.sub a b) =
          SignedOrbit.cmp c (SignedOrbit.sub a b')
  signed_le_sub_inputs_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.le (SignedOrbit.sub a b) c ↔
          SignedOrbit.le (SignedOrbit.sub a' b') c)
  signed_le_of_sub_inputs_iff_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.le c (SignedOrbit.sub a b) ↔
          SignedOrbit.le c (SignedOrbit.sub a' b'))
  signed_lt_sub_inputs_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.lt (SignedOrbit.sub a b) c ↔
          SignedOrbit.lt (SignedOrbit.sub a' b') c)
  signed_lt_of_sub_inputs_iff_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.lt c (SignedOrbit.sub a b) ↔
          SignedOrbit.lt c (SignedOrbit.sub a' b'))
  signed_cmp_sub_inputs_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.cmp (SignedOrbit.sub a b) c =
          SignedOrbit.cmp (SignedOrbit.sub a' b') c
  signed_cmp_of_sub_inputs_of_balanced :
    ∀ {c a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.cmp c (SignedOrbit.sub a b) =
          SignedOrbit.cmp c (SignedOrbit.sub a' b')
  signed_le_subtractions_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.le (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
            SignedOrbit.le (SignedOrbit.sub a' b') (SignedOrbit.sub c' d'))
  signed_lt_subtractions_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.lt (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
            SignedOrbit.lt (SignedOrbit.sub a' b') (SignedOrbit.sub c' d'))
  signed_cmp_subtractions_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          SignedOrbit.cmp (SignedOrbit.sub a b) (SignedOrbit.sub c d) =
            SignedOrbit.cmp (SignedOrbit.sub a' b') (SignedOrbit.sub c' d')
  signed_balanced_sub_left_input_iff_of_balanced :
    ∀ {a a' b c : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
          SignedOrbit.balanced (SignedOrbit.sub a' b) c)
  signed_balanced_sub_right_input_iff_of_balanced :
    ∀ {a b b' c : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
          SignedOrbit.balanced (SignedOrbit.sub a b') c)
  signed_balanced_sub_inputs_iff_of_balanced :
    ∀ {a a' b b' c : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) c ↔
          SignedOrbit.balanced (SignedOrbit.sub a' b') c)
  signed_balanced_subtractions_iff_of_balanced :
    ∀ {a a' b b' c c' d d' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.balanced c c' → SignedOrbit.balanced d d' →
          (SignedOrbit.balanced (SignedOrbit.sub a b) (SignedOrbit.sub c d) ↔
            SignedOrbit.balanced (SignedOrbit.sub a' b') (SignedOrbit.sub c' d'))
  signed_sub_balanced_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.sub a' b) SignedOrbit.zero)
  signed_sub_balanced_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.sub a b') SignedOrbit.zero)
  signed_sub_balanced_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          SignedOrbit.balanced (SignedOrbit.sub a' b') SignedOrbit.zero)
  signed_sub_not_balanced_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          ¬ SignedOrbit.balanced (SignedOrbit.sub a' b) SignedOrbit.zero)
  signed_sub_not_balanced_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          ¬ SignedOrbit.balanced (SignedOrbit.sub a b') SignedOrbit.zero)
  signed_sub_not_balanced_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
          ¬ SignedOrbit.balanced (SignedOrbit.sub a' b') SignedOrbit.zero)
  signed_sub_balanced_zero_iff_balanced :
    ∀ a b : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
        SignedOrbit.balanced a b
  signed_sub_not_balanced_zero_iff_not_balanced :
    ∀ a b : SignedOrbit,
      ¬ SignedOrbit.balanced (SignedOrbit.sub a b) SignedOrbit.zero ↔
        ¬ SignedOrbit.balanced a b
  signed_abs_sub_eq_zero_iff_balanced :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
        SignedOrbit.balanced a b
  signed_abs_sub_ne_zero_iff_not_balanced :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
        ¬ SignedOrbit.balanced a b
  signed_sub_self_balanced_zero :
    ∀ a : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.sub a a) SignedOrbit.zero
  signed_abs_sub_self_eq_zero :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a a).abs = DistinctionNat.zero
  signed_sub_zero_balanced :
    ∀ a : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.sub a SignedOrbit.zero) a
  signed_zero_sub_balanced_negate :
    ∀ a : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.sub SignedOrbit.zero a)
        (SignedOrbit.negate a)
  signed_abs_sub_zero_eq :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a SignedOrbit.zero).abs = a.abs
  signed_abs_zero_sub_eq :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub SignedOrbit.zero a).abs = a.abs
  signed_le_sub_zero_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le (SignedOrbit.sub a SignedOrbit.zero) b ↔
        SignedOrbit.le a b
  signed_le_sub_zero_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le b (SignedOrbit.sub a SignedOrbit.zero) ↔
        SignedOrbit.le b a
  signed_lt_sub_zero_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.sub a SignedOrbit.zero) b ↔
        SignedOrbit.lt a b
  signed_lt_sub_zero_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt b (SignedOrbit.sub a SignedOrbit.zero) ↔
        SignedOrbit.lt b a
  signed_cmp_sub_zero_left :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.sub a SignedOrbit.zero) b =
        SignedOrbit.cmp a b
  signed_cmp_sub_zero_right :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp b (SignedOrbit.sub a SignedOrbit.zero) =
        SignedOrbit.cmp b a
  signed_le_zero_sub_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le (SignedOrbit.sub SignedOrbit.zero a) b ↔
        SignedOrbit.le (SignedOrbit.negate a) b
  signed_le_zero_sub_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le b (SignedOrbit.sub SignedOrbit.zero a) ↔
        SignedOrbit.le b (SignedOrbit.negate a)
  signed_lt_zero_sub_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.sub SignedOrbit.zero a) b ↔
        SignedOrbit.lt (SignedOrbit.negate a) b
  signed_lt_zero_sub_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt b (SignedOrbit.sub SignedOrbit.zero a) ↔
        SignedOrbit.lt b (SignedOrbit.negate a)
  signed_cmp_zero_sub_left :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.sub SignedOrbit.zero a) b =
        SignedOrbit.cmp (SignedOrbit.negate a) b
  signed_cmp_zero_sub_right :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp b (SignedOrbit.sub SignedOrbit.zero a) =
        SignedOrbit.cmp b (SignedOrbit.negate a)
  signed_le_sub_self_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le (SignedOrbit.sub a a) b ↔
        SignedOrbit.le SignedOrbit.zero b
  signed_le_sub_self_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le b (SignedOrbit.sub a a) ↔
        SignedOrbit.le b SignedOrbit.zero
  signed_lt_sub_self_left_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.sub a a) b ↔
        SignedOrbit.lt SignedOrbit.zero b
  signed_lt_sub_self_right_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt b (SignedOrbit.sub a a) ↔
        SignedOrbit.lt b SignedOrbit.zero
  signed_cmp_sub_self_left :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.sub a a) b =
        SignedOrbit.cmp SignedOrbit.zero b
  signed_cmp_sub_self_right :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp b (SignedOrbit.sub a a) =
        SignedOrbit.cmp b SignedOrbit.zero
  signed_nonnegFlag_sub_zero :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a SignedOrbit.zero).nonnegFlag = a.nonnegFlag
  signed_negativeFlag_sub_zero :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a SignedOrbit.zero).negativeFlag = a.negativeFlag
  signed_nonnegFlag_zero_sub :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub SignedOrbit.zero a).nonnegFlag =
        (SignedOrbit.negate a).nonnegFlag
  signed_negativeFlag_zero_sub :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub SignedOrbit.zero a).negativeFlag =
        (SignedOrbit.negate a).negativeFlag
  signed_nonnegFlag_sub_self :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a a).nonnegFlag = true
  signed_negativeFlag_sub_self :
    ∀ a : SignedOrbit,
      (SignedOrbit.sub a a).negativeFlag = false
  signed_nonnegFlag_sub_iff_le :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).nonnegFlag = true ↔
        SignedOrbit.le b a
  signed_nonnegFlag_sub_eq_false_iff_lt :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).nonnegFlag = false ↔
        SignedOrbit.lt a b
  signed_negativeFlag_sub_iff_lt :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).negativeFlag = true ↔
        SignedOrbit.lt a b
  signed_negativeFlag_sub_eq_false_iff_le :
    ∀ a b : SignedOrbit,
      (SignedOrbit.sub a b).negativeFlag = false ↔
        SignedOrbit.le b a
  signed_le_iff_nonnegFlag_sub :
    ∀ a b : SignedOrbit,
      SignedOrbit.le a b ↔
        (SignedOrbit.sub b a).nonnegFlag = true
  signed_lt_iff_nonnegFlag_sub_eq_false :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt a b ↔
        (SignedOrbit.sub a b).nonnegFlag = false
  signed_lt_iff_negativeFlag_sub :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt a b ↔
        (SignedOrbit.sub a b).negativeFlag = true
  signed_le_iff_negativeFlag_sub_eq_false :
    ∀ a b : SignedOrbit,
      SignedOrbit.le a b ↔
        (SignedOrbit.sub b a).negativeFlag = false
  signed_nonnegFlag_mul_ofOrbit_right_of_ne_zero :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).nonnegFlag =
        z.nonnegFlag
  signed_negativeFlag_mul_ofOrbit_right_of_ne_zero :
    ∀ z : SignedOrbit, ∀ d : DistinctionNat, d ≠ DistinctionNat.zero →
      (SignedOrbit.mul z (SignedOrbit.ofOrbit d)).negativeFlag =
        z.negativeFlag
  signed_nonnegFlag_mul_ofOrbit_left_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit, d ≠ DistinctionNat.zero →
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).nonnegFlag =
        z.nonnegFlag
  signed_negativeFlag_mul_ofOrbit_left_of_ne_zero :
    ∀ d : DistinctionNat, ∀ z : SignedOrbit, d ≠ DistinctionNat.zero →
      (SignedOrbit.mul (SignedOrbit.ofOrbit d) z).negativeFlag =
        z.negativeFlag
  signed_le_congr_left_of_balanced :
    ∀ {a a' b : SignedOrbit}, SignedOrbit.balanced a a' →
      (SignedOrbit.le a b ↔ SignedOrbit.le a' b)
  signed_le_congr_right_of_balanced :
    ∀ {a b b' : SignedOrbit}, SignedOrbit.balanced b b' →
      (SignedOrbit.le a b ↔ SignedOrbit.le a b')
  signed_lt_congr_left_of_balanced :
    ∀ {a a' b : SignedOrbit}, SignedOrbit.balanced a a' →
      (SignedOrbit.lt a b ↔ SignedOrbit.lt a' b)
  signed_lt_congr_right_of_balanced :
    ∀ {a b b' : SignedOrbit}, SignedOrbit.balanced b b' →
      (SignedOrbit.lt a b ↔ SignedOrbit.lt a b')
  signed_le_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.le a b ↔ SignedOrbit.le a' b')
  signed_lt_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.lt a b ↔ SignedOrbit.lt a' b')
  signed_cmp_lt :
    ∀ {a b : SignedOrbit},
      SignedOrbit.lt a b → SignedOrbit.cmp a b = Ordering.lt
  signed_cmp_eq :
    ∀ {a b : SignedOrbit},
      SignedOrbit.balanced a b → SignedOrbit.cmp a b = Ordering.eq
  signed_cmp_gt :
    ∀ {a b : SignedOrbit},
      SignedOrbit.lt b a → SignedOrbit.cmp a b = Ordering.gt
  signed_cmp_lt_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp a b = Ordering.lt ↔ SignedOrbit.lt a b
  signed_cmp_eq_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp a b = Ordering.eq ↔ SignedOrbit.balanced a b
  signed_cmp_gt_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp a b = Ordering.gt ↔ SignedOrbit.lt b a
  signed_cmp_congr_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        SignedOrbit.cmp a b = SignedOrbit.cmp a' b'
  signed_balanced_add_left_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
        SignedOrbit.balanced a b
  signed_balanced_add_right_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
        SignedOrbit.balanced a b
  signed_balanced_negate_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.balanced (SignedOrbit.negate a) (SignedOrbit.negate b) ↔
        SignedOrbit.balanced a b
  signed_abs_zero_iff_balanced_zero :
    ∀ z : SignedOrbit,
      z.abs = DistinctionNat.zero ↔ SignedOrbit.balanced z SignedOrbit.zero
  signed_abs_nonnegative_branch :
    ∀ {z : SignedOrbit},
      z.nonnegFlag = true → (z.abs.toNat : ℤ) = z.toInt
  signed_abs_negative_branch :
    ∀ {z : SignedOrbit},
      z.negativeFlag = true → (z.abs.toNat : ℤ) = -z.toInt
  signed_balanced_of_nonnegFlag :
    ∀ {z : SignedOrbit},
      z.nonnegFlag = true →
        SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs)
  signed_balanced_of_negativeFlag :
    ∀ {z : SignedOrbit},
      z.negativeFlag = true →
        SignedOrbit.balanced z
          (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))
  signed_balanced_sign_canonical :
    ∀ z : SignedOrbit,
      (z.nonnegFlag = true ∧
        SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs)) ∨
        (z.negativeFlag = true ∧
          SignedOrbit.balanced z
            (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)))
  signed_balanced_ofOrbit_abs_iff_nonnegFlag :
    ∀ z : SignedOrbit,
      SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ↔
        z.nonnegFlag = true
  signed_balanced_negate_ofOrbit_abs_iff_negate_nonnegFlag :
    ∀ z : SignedOrbit,
      SignedOrbit.balanced z
        (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
          (SignedOrbit.negate z).nonnegFlag = true
  signed_balanced_negate_ofOrbit_abs_iff_negativeFlag_or_balanced_zero :
    ∀ z : SignedOrbit,
      SignedOrbit.balanced z
        (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
          z.negativeFlag = true ∨ SignedOrbit.balanced z SignedOrbit.zero
  signed_balanced_both_abs_representatives_iff_balanced_zero :
    ∀ z : SignedOrbit,
      (SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ∧
        SignedOrbit.balanced z
          (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs))) ↔
            SignedOrbit.balanced z SignedOrbit.zero
  signed_balanced_zero_of_both_abs_representatives :
    ∀ {z : SignedOrbit},
      SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) →
        SignedOrbit.balanced z
          (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) →
            SignedOrbit.balanced z SignedOrbit.zero
  signed_not_both_abs_representatives_of_not_balanced_zero :
    ∀ {z : SignedOrbit},
      ¬ SignedOrbit.balanced z SignedOrbit.zero →
        ¬ (SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs) ∧
          SignedOrbit.balanced z
            (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)))
  signed_not_balanced_ofOrbit_abs_of_negativeFlag :
    ∀ {z : SignedOrbit},
      z.negativeFlag = true →
        ¬ SignedOrbit.balanced z (SignedOrbit.ofOrbit z.abs)
  signed_balanced_negate_ofOrbit_abs_iff_balanced_zero_of_nonnegFlag :
    ∀ {z : SignedOrbit},
      z.nonnegFlag = true →
        (SignedOrbit.balanced z
          (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) ↔
            SignedOrbit.balanced z SignedOrbit.zero)
  signed_abs_balanced_invariant :
    ∀ {z w : SignedOrbit},
      SignedOrbit.balanced z w → z.abs = w.abs
  signed_abs_sub_eq_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        (SignedOrbit.sub a b).abs = (SignedOrbit.sub a' b).abs
  signed_abs_sub_eq_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).abs = (SignedOrbit.sub a b').abs
  signed_abs_sub_eq_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        (SignedOrbit.sub a b).abs = (SignedOrbit.sub a' b').abs
  signed_abs_sub_eq_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        ((SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.sub a' b).abs = DistinctionNat.zero)
  signed_abs_sub_eq_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        ((SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.sub a b').abs = DistinctionNat.zero)
  signed_abs_sub_eq_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        ((SignedOrbit.sub a b).abs = DistinctionNat.zero ↔
          (SignedOrbit.sub a' b').abs = DistinctionNat.zero)
  signed_abs_sub_ne_zero_iff_of_balanced_left :
    ∀ {a a' b : SignedOrbit},
      SignedOrbit.balanced a a' →
        ((SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.sub a' b).abs ≠ DistinctionNat.zero)
  signed_abs_sub_ne_zero_iff_of_balanced_right :
    ∀ {a b b' : SignedOrbit},
      SignedOrbit.balanced b b' →
        ((SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.sub a b').abs ≠ DistinctionNat.zero)
  signed_abs_sub_ne_zero_iff_of_balanced :
    ∀ {a a' b b' : SignedOrbit},
      SignedOrbit.balanced a a' → SignedOrbit.balanced b b' →
        ((SignedOrbit.sub a b).abs ≠ DistinctionNat.zero ↔
          (SignedOrbit.sub a' b').abs ≠ DistinctionNat.zero)
  signed_le_add_left_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.le (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
        SignedOrbit.le a b
  signed_le_add_right_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.le (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
        SignedOrbit.le a b
  signed_lt_add_left_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.add c a) (SignedOrbit.add c b) ↔
        SignedOrbit.lt a b
  signed_lt_add_right_iff :
    ∀ a b c : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.add a c) (SignedOrbit.add b c) ↔
        SignedOrbit.lt a b
  signed_add_le_add :
    ∀ {a b c d : SignedOrbit},
      SignedOrbit.le a b → SignedOrbit.le c d →
        SignedOrbit.le (SignedOrbit.add a c) (SignedOrbit.add b d)
  signed_add_lt_add_left :
    ∀ {a b c : SignedOrbit},
      SignedOrbit.lt a b →
        SignedOrbit.lt (SignedOrbit.add c a) (SignedOrbit.add c b)
  signed_add_lt_add_right :
    ∀ {a b c : SignedOrbit},
      SignedOrbit.lt a b →
        SignedOrbit.lt (SignedOrbit.add a c) (SignedOrbit.add b c)
  signed_negate_le_negate_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.le (SignedOrbit.negate b) (SignedOrbit.negate a) ↔
        SignedOrbit.le a b
  signed_negate_lt_negate_iff :
    ∀ a b : SignedOrbit,
      SignedOrbit.lt (SignedOrbit.negate b) (SignedOrbit.negate a) ↔
        SignedOrbit.lt a b
  signed_cmp_add_left :
    ∀ a b c : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.add c a) (SignedOrbit.add c b) =
        SignedOrbit.cmp a b
  signed_cmp_add_right :
    ∀ a b c : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.add a c) (SignedOrbit.add b c) =
        SignedOrbit.cmp a b
  signed_cmp_negate_swap :
    ∀ a b : SignedOrbit,
      SignedOrbit.cmp (SignedOrbit.negate b) (SignedOrbit.negate a) =
        SignedOrbit.cmp a b
  signed_abs_negate :
    ∀ z : SignedOrbit, (SignedOrbit.negate z).abs = z.abs
  signed_abs_ofOrbit :
    ∀ n : DistinctionNat, (SignedOrbit.ofOrbit n).abs = n
  signed_abs_negate_ofOrbit :
    ∀ n : DistinctionNat,
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).abs = n
  signed_nonnegFlag_ofOrbit :
    ∀ n : DistinctionNat, (SignedOrbit.ofOrbit n).nonnegFlag = true
  signed_negativeFlag_ofOrbit :
    ∀ n : DistinctionNat, (SignedOrbit.ofOrbit n).negativeFlag = false
  signed_nonnegFlag_negate_ofOrbit_of_ne_zero :
    ∀ n : DistinctionNat, n ≠ DistinctionNat.zero →
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).nonnegFlag = false
  signed_negativeFlag_negate_ofOrbit_of_ne_zero :
    ∀ n : DistinctionNat, n ≠ DistinctionNat.zero →
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).negativeFlag = true
  signed_negate_ofOrbit_not_balanced_zero_of_ne_zero :
    ∀ n : DistinctionNat, n ≠ DistinctionNat.zero →
      ¬ SignedOrbit.balanced
        (SignedOrbit.negate (SignedOrbit.ofOrbit n)) SignedOrbit.zero
  signed_nonnegFlag_negate_ofOrbit_eq_true_iff_zero :
    ∀ n : DistinctionNat,
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).nonnegFlag = true ↔
        n = DistinctionNat.zero
  signed_negativeFlag_negate_ofOrbit_eq_true_iff_ne_zero :
    ∀ n : DistinctionNat,
      (SignedOrbit.negate (SignedOrbit.ofOrbit n)).negativeFlag = true ↔
        n ≠ DistinctionNat.zero
  signed_negate_ofOrbit_balanced_zero_iff :
    ∀ n : DistinctionNat,
      SignedOrbit.balanced
        (SignedOrbit.negate (SignedOrbit.ofOrbit n)) SignedOrbit.zero ↔
          n = DistinctionNat.zero
  signed_abs_add_le_add_abs :
    ∀ z w : SignedOrbit,
      DistinctionNat.leq (SignedOrbit.add z w).abs (z.abs + w.abs) = true
  signed_abs_sub_le_add_abs :
    ∀ z w : SignedOrbit,
      DistinctionNat.leq (SignedOrbit.sub z w).abs (z.abs + w.abs) = true
  signed_abs_le_iff_between :
    ∀ z : SignedOrbit, ∀ n : DistinctionNat,
      DistinctionNat.leq z.abs n = true ↔
        SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
          SignedOrbit.le z (SignedOrbit.ofOrbit n)
  signed_between_of_abs_le :
    ∀ {z : SignedOrbit}, ∀ {n : DistinctionNat},
      DistinctionNat.leq z.abs n = true →
        SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
          SignedOrbit.le z (SignedOrbit.ofOrbit n)
  signed_abs_le_of_between :
    ∀ {z : SignedOrbit}, ∀ {n : DistinctionNat},
      SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z →
        SignedOrbit.le z (SignedOrbit.ofOrbit n) →
          DistinctionNat.leq z.abs n = true
  signed_neg_abs_le_self :
    ∀ z : SignedOrbit,
      SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit z.abs)) z
  signed_self_le_abs :
    ∀ z : SignedOrbit,
      SignedOrbit.le z (SignedOrbit.ofOrbit z.abs)
  signed_abs_le_trans :
    ∀ {z : SignedOrbit}, ∀ {n m : DistinctionNat},
      DistinctionNat.leq z.abs n = true →
        DistinctionNat.leq n m = true →
          DistinctionNat.leq z.abs m = true
  signed_between_mono :
    ∀ {z : SignedOrbit}, ∀ {n m : DistinctionNat},
      (SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit n)) z ∧
        SignedOrbit.le z (SignedOrbit.ofOrbit n)) →
          DistinctionNat.leq n m = true →
            SignedOrbit.le (SignedOrbit.negate (SignedOrbit.ofOrbit m)) z ∧
              SignedOrbit.le z (SignedOrbit.ofOrbit m)
  ratio_recip_den_internal :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recipNonzero a h).den = a.num.abs
  ratio_recip_num_nonnegative_branch :
    ∀ {a : RatioOrbit}
      {h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero},
      a.num.nonnegFlag = true →
        (RatioOrbit.recipNonzero a h).num = SignedOrbit.ofOrbit a.den
  ratio_recip_num_negative_branch :
    ∀ {a : RatioOrbit}
      {h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero},
      a.num.negativeFlag = true →
        (RatioOrbit.recipNonzero a h).num =
          SignedOrbit.negate (SignedOrbit.ofOrbit a.den)
  ratio_recip_num_abs_eq_den :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recipNonzero a h).num.abs = a.den
  ratio_recip_num_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced
        (RatioOrbit.recipNonzero a h).num SignedOrbit.zero
  ratio_recip_num_nonnegFlag_eq :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recipNonzero a h).num.nonnegFlag = a.num.nonnegFlag
  ratio_recip_num_negativeFlag_eq :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recipNonzero a h).num.negativeFlag = a.num.negativeFlag
  ratio_recip_num_zero_le_iff :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.le SignedOrbit.zero (RatioOrbit.recipNonzero a h).num ↔
        SignedOrbit.le SignedOrbit.zero a.num
  ratio_recip_num_lt_zero_iff :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.lt (RatioOrbit.recipNonzero a h).num SignedOrbit.zero ↔
        SignedOrbit.lt a.num SignedOrbit.zero
  ratio_recip_num_zero_lt_iff :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.lt SignedOrbit.zero (RatioOrbit.recipNonzero a h).num ↔
        SignedOrbit.lt SignedOrbit.zero a.num
  ratio_recip_num_cmp_zero :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.cmp (RatioOrbit.recipNonzero a h).num SignedOrbit.zero =
        SignedOrbit.cmp a.num SignedOrbit.zero
  ratio_recip_num_zero_cmp :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.cmp SignedOrbit.zero (RatioOrbit.recipNonzero a h).num =
        SignedOrbit.cmp SignedOrbit.zero a.num
  ratio_recip_num_balanced_ofOrbit_den_iff_nonnegFlag :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
          (RatioOrbit.recipNonzero a h).num (SignedOrbit.ofOrbit a.den) ↔
        a.num.nonnegFlag = true
  ratio_recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
          (RatioOrbit.recipNonzero a h).num
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
        a.num.negativeFlag = true
  ratio_recip_num_not_balanced_ofOrbit_den_iff_negativeFlag :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced
          (RatioOrbit.recipNonzero a h).num (SignedOrbit.ofOrbit a.den) ↔
        a.num.negativeFlag = true
  ratio_recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced
          (RatioOrbit.recipNonzero a h).num
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
        a.num.nonnegFlag = true
  ratio_num_mul_recip_num_balanced_den_mul_abs :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
        (SignedOrbit.mul a.num (RatioOrbit.recipNonzero a h).num)
        (SignedOrbit.ofOrbit (a.den * a.num.abs))
  ratio_mul_recipNonzero_crossEq_one :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recipNonzero a h))
        RatioOrbit.one
  ratio_recip_num_mul_num_balanced_den_mul_abs :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
        (SignedOrbit.mul (RatioOrbit.recipNonzero a h).num a.num)
        (SignedOrbit.ofOrbit (a.den * a.num.abs))
  ratio_recipNonzero_mul_crossEq_one :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recipNonzero a h) a)
        RatioOrbit.one
  ratio_recip_eq_recipNonzero_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.recip a = RatioOrbit.recipNonzero a h
  ratio_mul_recip_crossEq_one_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recip a))
        RatioOrbit.one
  ratio_recip_mul_crossEq_one_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recip a) a)
        RatioOrbit.one
  ratio_recip_den_eq_abs_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recip a).den = a.num.abs
  ratio_recip_num_abs_eq_den_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recip a).num.abs = a.den
  ratio_recip_num_not_balanced_zero_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero
  ratio_recip_num_nonnegFlag_eq_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recip a).num.nonnegFlag = a.num.nonnegFlag
  ratio_recip_num_negativeFlag_eq_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      (RatioOrbit.recip a).num.negativeFlag = a.num.negativeFlag
  ratio_recip_num_zero_le_iff_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.le SignedOrbit.zero (RatioOrbit.recip a).num ↔
        SignedOrbit.le SignedOrbit.zero a.num
  ratio_recip_num_lt_zero_iff_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.lt (RatioOrbit.recip a).num SignedOrbit.zero ↔
        SignedOrbit.lt a.num SignedOrbit.zero
  ratio_recip_num_zero_lt_iff_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.lt SignedOrbit.zero (RatioOrbit.recip a).num ↔
        SignedOrbit.lt SignedOrbit.zero a.num
  ratio_recip_num_cmp_zero_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.cmp (RatioOrbit.recip a).num SignedOrbit.zero =
        SignedOrbit.cmp a.num SignedOrbit.zero
  ratio_recip_num_zero_cmp_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.cmp SignedOrbit.zero (RatioOrbit.recip a).num =
        SignedOrbit.cmp SignedOrbit.zero a.num
  ratio_recip_num_balanced_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
          (RatioOrbit.recip a).num (SignedOrbit.ofOrbit a.den) ↔
        a.num.nonnegFlag = true
  ratio_recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
          (RatioOrbit.recip a).num
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
        a.num.negativeFlag = true
  ratio_recip_num_not_balanced_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced
          (RatioOrbit.recip a).num (SignedOrbit.ofOrbit a.den) ↔
        a.num.negativeFlag = true
  ratio_recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      ¬ SignedOrbit.balanced
          (RatioOrbit.recip a).num
          (SignedOrbit.negate (SignedOrbit.ofOrbit a.den)) ↔
        a.num.nonnegFlag = true
  ratio_recip_num_nonnegative_branch_of_not_balanced_zero :
    ∀ {a : RatioOrbit}
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      a.num.nonnegFlag = true →
        (RatioOrbit.recip a).num = SignedOrbit.ofOrbit a.den
  ratio_recip_num_negative_branch_of_not_balanced_zero :
    ∀ {a : RatioOrbit}
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      a.num.negativeFlag = true →
        (RatioOrbit.recip a).num =
          SignedOrbit.negate (SignedOrbit.ofOrbit a.den)
  ratio_num_mul_recip_num_balanced_den_mul_abs_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
        (SignedOrbit.mul a.num (RatioOrbit.recip a).num)
        (SignedOrbit.ofOrbit (a.den * a.num.abs))
  ratio_recip_num_mul_num_balanced_den_mul_abs_of_not_balanced_zero :
    ∀ (a : RatioOrbit)
      (_h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      SignedOrbit.balanced
        (SignedOrbit.mul (RatioOrbit.recip a).num a.num)
        (SignedOrbit.ofOrbit (a.den * a.num.abs))
  ratio_recip_num_balanced_zero_iff :
    ∀ a : RatioOrbit,
      SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero ↔
        SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_recip_num_not_balanced_zero_iff :
    ∀ a : RatioOrbit,
      ¬ SignedOrbit.balanced (RatioOrbit.recip a).num SignedOrbit.zero ↔
        ¬ SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_crossEq_zero_iff_num_balanced_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq a RatioOrbit.zero ↔
        SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_zero_crossEq_iff_num_balanced_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.zero a ↔
        SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_recip_crossEq_zero_iff_num_balanced_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
        SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_zero_crossEq_recip_iff_num_balanced_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
        SignedOrbit.balanced a.num SignedOrbit.zero
  ratio_recip_crossEq_zero_iff_crossEq_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
        RatioOrbit.crossEq a RatioOrbit.zero
  ratio_zero_crossEq_recip_iff_zero_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
        RatioOrbit.crossEq RatioOrbit.zero a
  ratio_recip_crossEq_zero_iff_zero_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
        RatioOrbit.crossEq RatioOrbit.zero a
  ratio_zero_crossEq_recip_iff_crossEq_zero :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
        RatioOrbit.crossEq a RatioOrbit.zero
  ratio_recip_not_crossEq_zero_iff_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero
  ratio_zero_not_crossEq_recip_iff_zero_not_crossEq :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
        ¬ RatioOrbit.crossEq RatioOrbit.zero a
  ratio_recip_not_crossEq_zero_iff_zero_not_crossEq :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq (RatioOrbit.recip a) RatioOrbit.zero ↔
        ¬ RatioOrbit.crossEq RatioOrbit.zero a
  ratio_zero_not_crossEq_recip_iff_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip a) ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero
  ratio_recip_recipNonzero_crossEq_self :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq (RatioOrbit.recip (RatioOrbit.recipNonzero a h)) a
  ratio_self_crossEq_recip_recipNonzero :
    ∀ (a : RatioOrbit)
      (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero),
      RatioOrbit.crossEq a (RatioOrbit.recip (RatioOrbit.recipNonzero a h))
  ratio_recip_recip_crossEq_self :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip (RatioOrbit.recip a)) a
  ratio_self_crossEq_recip_recip :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq a (RatioOrbit.recip (RatioOrbit.recip a))
  ratio_recip_crossEq_congr :
    ∀ {a b : RatioOrbit},
      RatioOrbit.crossEq a b →
        RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b)
  ratio_recip_crossEq_iff :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b) ↔
        RatioOrbit.crossEq a b
  ratio_recip_crossEq_iff_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.recip a) b ↔
        RatioOrbit.crossEq a (RatioOrbit.recip b)
  ratio_crossEq_recip_iff_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq a (RatioOrbit.recip b) ↔
        RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq b RatioOrbit.zero →
        (
        RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
          RatioOrbit.crossEq a (RatioOrbit.recip b))
  ratio_mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        (
        RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
          RatioOrbit.crossEq b (RatioOrbit.recip a))
  ratio_mul_recip_cancel_right_crossEq_self_of_right_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq b RatioOrbit.zero →
        RatioOrbit.crossEq
          (RatioOrbit.mul (RatioOrbit.mul a b) (RatioOrbit.recip b)) a
  ratio_recip_mul_cancel_left_crossEq_self_of_left_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq
          (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.mul a b)) b
  ratio_mul_recip_cancel_right_assoc_crossEq_self_of_right_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq b RatioOrbit.zero →
        RatioOrbit.crossEq
          (RatioOrbit.mul (RatioOrbit.mul a (RatioOrbit.recip b)) b) a
  ratio_recip_mul_cancel_left_assoc_crossEq_self_of_left_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq
          (RatioOrbit.mul a (RatioOrbit.mul (RatioOrbit.recip a) b)) b
  ratio_mul_right_crossEq_iff_of_not_crossEq_zero :
    ∀ a b c : RatioOrbit,
      ¬ RatioOrbit.crossEq c RatioOrbit.zero →
        (
        RatioOrbit.crossEq (RatioOrbit.mul a c) (RatioOrbit.mul b c) ↔
          RatioOrbit.crossEq a b)
  ratio_mul_left_crossEq_iff_of_not_crossEq_zero :
    ∀ a b c : RatioOrbit,
      ¬ RatioOrbit.crossEq c RatioOrbit.zero →
        (
        RatioOrbit.crossEq (RatioOrbit.mul c a) (RatioOrbit.mul c b) ↔
          RatioOrbit.crossEq a b)
  ratio_mul_crossEq_zero_iff :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero ↔
        RatioOrbit.crossEq a RatioOrbit.zero ∨
          RatioOrbit.crossEq b RatioOrbit.zero
  ratio_zero_crossEq_mul_iff :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b) ↔
        RatioOrbit.crossEq a RatioOrbit.zero ∨
          RatioOrbit.crossEq b RatioOrbit.zero
  ratio_mul_not_crossEq_zero_iff :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_zero_not_crossEq_mul_iff :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b) ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_mul_not_crossEq_zero_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero
  ratio_zero_not_crossEq_mul_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.mul a b)
  ratio_left_not_crossEq_zero_of_mul_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero →
        ¬ RatioOrbit.crossEq a RatioOrbit.zero
  ratio_right_not_crossEq_zero_of_mul_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_mul_crossEq_congr :
    ∀ {a₁ a₂ b₁ b₂ : RatioOrbit},
      RatioOrbit.crossEq a₁ a₂ →
        RatioOrbit.crossEq b₁ b₂ →
          RatioOrbit.crossEq (RatioOrbit.mul a₁ b₁) (RatioOrbit.mul a₂ b₂)
  ratio_mul_crossEq_congr_left :
    ∀ {a₁ a₂ b : RatioOrbit},
      RatioOrbit.crossEq a₁ a₂ →
        RatioOrbit.crossEq (RatioOrbit.mul a₁ b) (RatioOrbit.mul a₂ b)
  ratio_mul_crossEq_congr_right :
    ∀ {a b₁ b₂ : RatioOrbit},
      RatioOrbit.crossEq b₁ b₂ →
        RatioOrbit.crossEq (RatioOrbit.mul a b₁) (RatioOrbit.mul a b₂)
  ratio_mul_comm_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) (RatioOrbit.mul b a)
  ratio_mul_assoc_crossEq :
    ∀ a b c : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.mul (RatioOrbit.mul a b) c)
        (RatioOrbit.mul a (RatioOrbit.mul b c))
  ratio_mul_one_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a RatioOrbit.one) a
  ratio_one_mul_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.one a) a
  ratio_mul_zero_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a RatioOrbit.zero) RatioOrbit.zero
  ratio_zero_mul_crossEq :
    ∀ a : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul RatioOrbit.zero a) RatioOrbit.zero
  ratio_one_not_crossEq_zero :
    ¬ RatioOrbit.crossEq RatioOrbit.one RatioOrbit.zero
  ratio_zero_not_crossEq_one :
    ¬ RatioOrbit.crossEq RatioOrbit.zero RatioOrbit.one
  ratio_recip_zero_crossEq_zero :
    RatioOrbit.crossEq (RatioOrbit.recip RatioOrbit.zero) RatioOrbit.zero
  ratio_zero_crossEq_recip_zero :
    RatioOrbit.crossEq RatioOrbit.zero (RatioOrbit.recip RatioOrbit.zero)
  ratio_recip_one_crossEq_one :
    RatioOrbit.crossEq (RatioOrbit.recip RatioOrbit.one) RatioOrbit.one
  ratio_one_crossEq_recip_one :
    RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.recip RatioOrbit.one)
  ratio_factors_not_crossEq_zero_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_left_not_crossEq_zero_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        ¬ RatioOrbit.crossEq a RatioOrbit.zero
  ratio_right_not_crossEq_zero_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_factors_not_crossEq_zero_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_left_not_crossEq_zero_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        ¬ RatioOrbit.crossEq a RatioOrbit.zero
  ratio_right_not_crossEq_zero_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero
  ratio_crossEq_recip_right_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        RatioOrbit.crossEq a (RatioOrbit.recip b)
  ratio_crossEq_recip_left_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_crossEq_recip_right_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        RatioOrbit.crossEq a (RatioOrbit.recip b)
  ratio_crossEq_recip_left_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_recip_mul_crossEq_mul_recip_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.recip (RatioOrbit.mul a b))
            (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
  ratio_mul_recip_crossEq_recip_mul_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
            (RatioOrbit.recip (RatioOrbit.mul a b))
  ratio_recip_mul_crossEq_mul_recip_comm_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.recip (RatioOrbit.mul a b))
            (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
  ratio_mul_recip_comm_crossEq_recip_mul_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
            (RatioOrbit.recip (RatioOrbit.mul a b))
  ratio_mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul a b)
              (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b)))
            RatioOrbit.one
  ratio_recip_pair_mul_mul_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul
              (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
              (RatioOrbit.mul a b))
            RatioOrbit.one
  ratio_mul_mul_recip_pair_comm_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul a b)
              (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a)))
            RatioOrbit.one
  ratio_recip_pair_comm_mul_mul_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul
              (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
              (RatioOrbit.mul a b))
            RatioOrbit.one
  ratio_mul_recip_pair_not_crossEq_zero_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
            RatioOrbit.zero
  ratio_zero_not_crossEq_mul_recip_pair_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq RatioOrbit.zero
            (RatioOrbit.mul (RatioOrbit.recip a) (RatioOrbit.recip b))
  ratio_mul_recip_pair_comm_not_crossEq_zero_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
            RatioOrbit.zero
  ratio_zero_not_crossEq_mul_recip_pair_comm_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq RatioOrbit.zero
            (RatioOrbit.mul (RatioOrbit.recip b) (RatioOrbit.recip a))
  ratio_mul_recip_crossEq_one_of_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq (RatioOrbit.mul a (RatioOrbit.recip a))
          RatioOrbit.one
  ratio_recip_mul_crossEq_one_of_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq (RatioOrbit.mul (RatioOrbit.recip a) a)
          RatioOrbit.one
  ratio_one_crossEq_mul_recip_of_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq RatioOrbit.one
          (RatioOrbit.mul a (RatioOrbit.recip a))
  ratio_one_crossEq_recip_mul_of_not_crossEq_zero :
    ∀ a : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        RatioOrbit.crossEq RatioOrbit.one
          (RatioOrbit.mul (RatioOrbit.recip a) a)
  ratio_mul_product_recip_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul a b)
              (RatioOrbit.recip (RatioOrbit.mul a b)))
            RatioOrbit.one
  ratio_recip_product_mul_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul a b))
              (RatioOrbit.mul a b))
            RatioOrbit.one
  ratio_one_crossEq_mul_product_recip_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq RatioOrbit.one
            (RatioOrbit.mul (RatioOrbit.mul a b)
              (RatioOrbit.recip (RatioOrbit.mul a b)))
  ratio_one_crossEq_recip_product_mul_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq RatioOrbit.one
            (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul a b))
              (RatioOrbit.mul a b))
  ratio_recip_product_not_crossEq_zero_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq
            (RatioOrbit.recip (RatioOrbit.mul a b)) RatioOrbit.zero
  ratio_zero_not_crossEq_recip_product_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq RatioOrbit.zero
            (RatioOrbit.recip (RatioOrbit.mul a b))
  ratio_recip_product_comm_not_crossEq_zero_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq
            (RatioOrbit.recip (RatioOrbit.mul b a)) RatioOrbit.zero
  ratio_zero_not_crossEq_recip_product_comm_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          ¬ RatioOrbit.crossEq RatioOrbit.zero
            (RatioOrbit.recip (RatioOrbit.mul b a))
  ratio_recip_product_comm_crossEq_recip_product :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.recip (RatioOrbit.mul a b))
        (RatioOrbit.recip (RatioOrbit.mul b a))
  ratio_recip_product_crossEq_recip_product_comm :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq
        (RatioOrbit.recip (RatioOrbit.mul b a))
        (RatioOrbit.recip (RatioOrbit.mul a b))
  ratio_mul_product_comm_recip_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.mul b a)
              (RatioOrbit.recip (RatioOrbit.mul b a)))
            RatioOrbit.one
  ratio_recip_product_comm_mul_crossEq_one_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq
            (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul b a))
              (RatioOrbit.mul b a))
            RatioOrbit.one
  ratio_one_crossEq_mul_product_comm_recip_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq RatioOrbit.one
            (RatioOrbit.mul (RatioOrbit.mul b a)
              (RatioOrbit.recip (RatioOrbit.mul b a)))
  ratio_one_crossEq_recip_product_comm_mul_of_not_crossEq_zero :
    ∀ a b : RatioOrbit,
      ¬ RatioOrbit.crossEq a RatioOrbit.zero →
        ¬ RatioOrbit.crossEq b RatioOrbit.zero →
          RatioOrbit.crossEq RatioOrbit.one
            (RatioOrbit.mul (RatioOrbit.recip (RatioOrbit.mul b a))
              (RatioOrbit.mul b a))
  ratio_recip_right_crossEq_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        RatioOrbit.crossEq (RatioOrbit.recip b) a
  ratio_recip_left_crossEq_of_mul_crossEq_one :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one →
        RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_recip_right_crossEq_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        RatioOrbit.crossEq (RatioOrbit.recip b) a
  ratio_recip_left_crossEq_of_one_crossEq_mul :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) →
        RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
          RatioOrbit.crossEq a (RatioOrbit.recip b)
  ratio_mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_one_crossEq_mul_iff_right_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
          RatioOrbit.crossEq a (RatioOrbit.recip b)
  ratio_one_crossEq_mul_iff_left_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
          RatioOrbit.crossEq (RatioOrbit.recip b) a
  ratio_mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_one_crossEq_mul_iff_right_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        ¬ RatioOrbit.crossEq b RatioOrbit.zero ∧
          RatioOrbit.crossEq (RatioOrbit.recip b) a
  ratio_one_crossEq_mul_iff_left_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        ¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
          RatioOrbit.crossEq a (RatioOrbit.recip b) ∧
            RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_one_crossEq_mul_iff_factors_not_crossEq_zero_and_crossEq_recip :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
          RatioOrbit.crossEq a (RatioOrbit.recip b) ∧
            RatioOrbit.crossEq b (RatioOrbit.recip a)
  ratio_mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq (RatioOrbit.mul a b) RatioOrbit.one ↔
        (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
          RatioOrbit.crossEq (RatioOrbit.recip b) a ∧
            RatioOrbit.crossEq (RatioOrbit.recip a) b
  ratio_one_crossEq_mul_iff_factors_not_crossEq_zero_and_recip_crossEq :
    ∀ a b : RatioOrbit,
      RatioOrbit.crossEq RatioOrbit.one (RatioOrbit.mul a b) ↔
        (¬ RatioOrbit.crossEq a RatioOrbit.zero ∧
          ¬ RatioOrbit.crossEq b RatioOrbit.zero) ∧
          RatioOrbit.crossEq (RatioOrbit.recip b) a ∧
            RatioOrbit.crossEq (RatioOrbit.recip a) b

/-- The internal signed-orbit order surface is closed. -/
theorem integer_order_certificate : IntegerOrderCertificate where
  truncated_sub_display := DistinctionNat.toNat_truncatedSub
  leq_display := DistinctionNat.leq_eq_true_iff
  absdiff_display := DistinctionNat.toNat_absDiff
  signed_nonneg_display := SignedOrbit.nonneg_iff_toInt_nonneg
  signed_nonneg_flag_display := SignedOrbit.nonnegFlag_eq_true_iff
  signed_abs_display := SignedOrbit.abs_toNat
  signed_le_display := SignedOrbit.le_iff_toInt_le
  signed_lt_display := SignedOrbit.lt_iff_toInt_lt
  abs_nonzero_internal := by
    intro z h
    exact SignedOrbit.abs_ne_zero_of_not_balanced_zero h
  signed_le_reflexive := SignedOrbit.le_refl
  signed_le_transitive := by
    intro a b c
    exact SignedOrbit.le_trans
  signed_le_antisymmetric_balanced := by
    intro a b
    exact SignedOrbit.le_antisymm_balanced
  signed_le_total := SignedOrbit.le_total
  signed_order_trichotomy := SignedOrbit.trichotomy
  signed_negativeFlag_eq_true_iff_nonnegFlag_eq_false :=
    SignedOrbit.negativeFlag_eq_true_iff_nonnegFlag_eq_false
  signed_negativeFlag_eq_false_iff_nonnegFlag_eq_true :=
    SignedOrbit.negativeFlag_eq_false_iff_nonnegFlag_eq_true
  signed_flags_exclusive := SignedOrbit.signFlags_exclusive
  signed_flags_exhaustive := SignedOrbit.signFlags_exhaustive
  signed_zero_le_iff_nonnegFlag := SignedOrbit.zero_le_iff_nonnegFlag
  signed_lt_zero_iff_negativeFlag := SignedOrbit.lt_zero_iff_negativeFlag
  signed_zero_lt_iff_nonnegFlag_and_not_balanced_zero :=
    SignedOrbit.zero_lt_iff_nonnegFlag_and_not_balanced_zero
  signed_nonnegFlag_eq_of_balanced := by
    intro z w
    exact SignedOrbit.nonnegFlag_eq_of_balanced
  signed_negativeFlag_eq_of_balanced := by
    intro z w
    exact SignedOrbit.negativeFlag_eq_of_balanced
  signed_nonneg_iff_of_balanced := by
    intro z w
    exact SignedOrbit.nonneg_iff_of_balanced
  signed_add_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.add_congr_of_balanced
  signed_negate_congr_of_balanced := by
    intro a a'
    exact SignedOrbit.negate_congr_of_balanced
  signed_sub_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.sub_congr_of_balanced
  signed_sub_congr_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.sub_congr_of_balanced_left
  signed_sub_congr_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.sub_congr_of_balanced_right
  signed_nonnegFlag_sub_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.nonnegFlag_sub_eq_of_balanced_left
  signed_nonnegFlag_sub_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.nonnegFlag_sub_eq_of_balanced_right
  signed_negativeFlag_sub_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.negativeFlag_sub_eq_of_balanced_left
  signed_negativeFlag_sub_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.negativeFlag_sub_eq_of_balanced_right
  signed_nonnegFlag_sub_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.nonnegFlag_sub_eq_of_balanced
  signed_negativeFlag_sub_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.negativeFlag_sub_eq_of_balanced
  signed_scaleByNat_congr_of_balanced := by
    intro z w
    exact SignedOrbit.scaleByNat_congr_of_balanced
  signed_scaleByNat_balanced_zero_of_balanced_zero := by
    intro z
    exact SignedOrbit.scaleByNat_balanced_zero_of_balanced_zero
  signed_mul_ofOrbit_balanced_scaleByNat :=
    SignedOrbit.mul_ofOrbit_balanced_scaleByNat
  signed_ofOrbit_mul_balanced_scaleByNat :=
    SignedOrbit.ofOrbit_mul_balanced_scaleByNat
  signed_abs_mul := SignedOrbit.abs_mul
  signed_mul_balanced_zero_iff := SignedOrbit.mul_balanced_zero_iff
  signed_mul_not_balanced_zero_iff := SignedOrbit.mul_not_balanced_zero_iff
  signed_balanced_mul_left_iff_of_not_balanced_zero :=
    SignedOrbit.balanced_mul_left_iff_of_not_balanced_zero
  signed_balanced_mul_right_iff_of_not_balanced_zero :=
    SignedOrbit.balanced_mul_right_iff_of_not_balanced_zero
  signed_le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
  signed_lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.lt_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
  signed_le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
  signed_lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.lt_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
  signed_le_mul_left_iff_of_negativeFlag :=
    SignedOrbit.le_mul_left_iff_of_negativeFlag
  signed_lt_mul_left_iff_of_negativeFlag :=
    SignedOrbit.lt_mul_left_iff_of_negativeFlag
  signed_le_mul_right_iff_of_negativeFlag :=
    SignedOrbit.le_mul_right_iff_of_negativeFlag
  signed_lt_mul_right_iff_of_negativeFlag :=
    SignedOrbit.lt_mul_right_iff_of_negativeFlag
  signed_abs_mul_eq_zero_iff := SignedOrbit.abs_mul_eq_zero_iff
  signed_abs_mul_ne_zero_iff := SignedOrbit.abs_mul_ne_zero_iff
  signed_abs_mul_eq_zero_iff_balanced_zero :=
    SignedOrbit.abs_mul_eq_zero_iff_balanced_zero
  signed_abs_mul_ne_zero_iff_not_balanced_zero :=
    SignedOrbit.abs_mul_ne_zero_iff_not_balanced_zero
  signed_abs_scaleByNat := SignedOrbit.abs_scaleByNat
  signed_abs_mul_ofOrbit_right := SignedOrbit.abs_mul_ofOrbit_right
  signed_abs_mul_ofOrbit_left := SignedOrbit.abs_mul_ofOrbit_left
  signed_mul_ofOrbit_right_balanced_zero_iff :=
    SignedOrbit.mul_ofOrbit_right_balanced_zero_iff
  signed_mul_ofOrbit_left_balanced_zero_iff :=
    SignedOrbit.mul_ofOrbit_left_balanced_zero_iff
  signed_mul_ofOrbit_right_not_balanced_zero_iff :=
    SignedOrbit.mul_ofOrbit_right_not_balanced_zero_iff
  signed_mul_ofOrbit_left_not_balanced_zero_iff :=
    SignedOrbit.mul_ofOrbit_left_not_balanced_zero_iff
  signed_nonnegFlag_scaleByNat_of_ne_zero :=
    SignedOrbit.nonnegFlag_scaleByNat_of_ne_zero
  signed_negativeFlag_scaleByNat_of_ne_zero :=
    SignedOrbit.negativeFlag_scaleByNat_of_ne_zero
  signed_scaleByNat_balanced_zero_iff := SignedOrbit.scaleByNat_balanced_zero_iff
  signed_scaleByNat_not_balanced_zero_iff :=
    SignedOrbit.scaleByNat_not_balanced_zero_iff
  signed_abs_scaleByNat_eq_zero_iff := SignedOrbit.abs_scaleByNat_eq_zero_iff
  signed_abs_scaleByNat_ne_zero_iff := SignedOrbit.abs_scaleByNat_ne_zero_iff
  signed_abs_mul_ofOrbit_right_eq_zero_iff :=
    SignedOrbit.abs_mul_ofOrbit_right_eq_zero_iff
  signed_abs_mul_ofOrbit_left_eq_zero_iff :=
    SignedOrbit.abs_mul_ofOrbit_left_eq_zero_iff
  signed_abs_mul_ofOrbit_right_ne_zero_iff :=
    SignedOrbit.abs_mul_ofOrbit_right_ne_zero_iff
  signed_abs_mul_ofOrbit_left_ne_zero_iff :=
    SignedOrbit.abs_mul_ofOrbit_left_ne_zero_iff
  signed_le_scaleByNat_of_le := by
    intro z w
    exact SignedOrbit.le_scaleByNat_of_le
  signed_le_scaleByNat_iff_of_ne_zero :=
    SignedOrbit.le_scaleByNat_iff_of_ne_zero
  signed_lt_scaleByNat_iff_of_ne_zero :=
    SignedOrbit.lt_scaleByNat_iff_of_ne_zero
  signed_balanced_scaleByNat_iff_of_ne_zero :=
    SignedOrbit.balanced_scaleByNat_iff_of_ne_zero
  signed_cmp_scaleByNat_of_ne_zero :=
    SignedOrbit.cmp_scaleByNat_of_ne_zero
  signed_le_mul_ofOrbit_right_iff_of_ne_zero :=
    SignedOrbit.le_mul_ofOrbit_right_iff_of_ne_zero
  signed_lt_mul_ofOrbit_right_iff_of_ne_zero :=
    SignedOrbit.lt_mul_ofOrbit_right_iff_of_ne_zero
  signed_balanced_mul_ofOrbit_right_iff_of_ne_zero :=
    SignedOrbit.balanced_mul_ofOrbit_right_iff_of_ne_zero
  signed_cmp_mul_ofOrbit_right_of_ne_zero :=
    SignedOrbit.cmp_mul_ofOrbit_right_of_ne_zero
  signed_le_mul_ofOrbit_left_iff_of_ne_zero :=
    SignedOrbit.le_mul_ofOrbit_left_iff_of_ne_zero
  signed_lt_mul_ofOrbit_left_iff_of_ne_zero :=
    SignedOrbit.lt_mul_ofOrbit_left_iff_of_ne_zero
  signed_balanced_mul_ofOrbit_left_iff_of_ne_zero :=
    SignedOrbit.balanced_mul_ofOrbit_left_iff_of_ne_zero
  signed_cmp_mul_ofOrbit_left_of_ne_zero :=
    SignedOrbit.cmp_mul_ofOrbit_left_of_ne_zero
  signed_cmp_mul_left_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.cmp_mul_left_of_nonnegFlag_of_not_balanced_zero
  signed_cmp_mul_right_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.cmp_mul_right_of_nonnegFlag_of_not_balanced_zero
  signed_cmp_mul_left_of_negativeFlag :=
    SignedOrbit.cmp_mul_left_of_negativeFlag
  signed_cmp_mul_right_of_negativeFlag :=
    SignedOrbit.cmp_mul_right_of_negativeFlag
  signed_nonnegFlag_mul_of_nonnegFlag_of_nonnegFlag :=
    SignedOrbit.nonnegFlag_mul_of_nonnegFlag_of_nonnegFlag
  signed_nonnegFlag_mul_of_negativeFlag_of_negativeFlag :=
    SignedOrbit.nonnegFlag_mul_of_negativeFlag_of_negativeFlag
  signed_negativeFlag_mul_of_nonnegFlag_of_not_balanced_zero_of_negativeFlag :=
    SignedOrbit.negativeFlag_mul_of_nonnegFlag_of_not_balanced_zero_of_negativeFlag
  signed_negativeFlag_mul_of_negativeFlag_of_nonnegFlag_of_not_balanced_zero :=
    SignedOrbit.negativeFlag_mul_of_negativeFlag_of_nonnegFlag_of_not_balanced_zero
  signed_negativeFlag_mul_iff := SignedOrbit.negativeFlag_mul_iff
  signed_nonnegFlag_mul_iff_not_strict_opposite_sign :=
    SignedOrbit.nonnegFlag_mul_iff_not_strict_opposite_sign
  signed_nonnegFlag_mul_of_balanced_zero_left :=
    SignedOrbit.nonnegFlag_mul_of_balanced_zero_left
  signed_nonnegFlag_mul_of_balanced_zero_right :=
    SignedOrbit.nonnegFlag_mul_of_balanced_zero_right
  signed_negativeFlag_mul_eq_false_of_balanced_zero_left :=
    SignedOrbit.negativeFlag_mul_eq_false_of_balanced_zero_left
  signed_negativeFlag_mul_eq_false_of_balanced_zero_right :=
    SignedOrbit.negativeFlag_mul_eq_false_of_balanced_zero_right
  signed_mul_balanced_zero_of_balanced_zero_left :=
    SignedOrbit.mul_balanced_zero_of_balanced_zero_left
  signed_mul_balanced_zero_of_balanced_zero_right :=
    SignedOrbit.mul_balanced_zero_of_balanced_zero_right
  signed_abs_mul_eq_zero_of_balanced_zero_left :=
    SignedOrbit.abs_mul_eq_zero_of_balanced_zero_left
  signed_abs_mul_eq_zero_of_balanced_zero_right :=
    SignedOrbit.abs_mul_eq_zero_of_balanced_zero_right
  signed_mul_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.mul_congr_of_balanced
  signed_mul_congr_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.mul_congr_of_balanced_left
  signed_mul_congr_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.mul_congr_of_balanced_right
  signed_nonnegFlag_mul_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.nonnegFlag_mul_eq_of_balanced
  signed_nonnegFlag_mul_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.nonnegFlag_mul_eq_of_balanced_left
  signed_nonnegFlag_mul_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.nonnegFlag_mul_eq_of_balanced_right
  signed_negativeFlag_mul_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.negativeFlag_mul_eq_of_balanced
  signed_negativeFlag_mul_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.negativeFlag_mul_eq_of_balanced_left
  signed_negativeFlag_mul_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.negativeFlag_mul_eq_of_balanced_right
  signed_abs_mul_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_mul_eq_of_balanced
  signed_abs_mul_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_mul_eq_of_balanced_left
  signed_abs_mul_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_mul_eq_of_balanced_right
  signed_mul_balanced_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.mul_balanced_zero_iff_of_balanced_left
  signed_mul_balanced_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.mul_balanced_zero_iff_of_balanced_right
  signed_abs_mul_eq_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_mul_eq_zero_iff_of_balanced_left
  signed_abs_mul_eq_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_mul_eq_zero_iff_of_balanced_right
  signed_abs_mul_ne_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_mul_ne_zero_iff_of_balanced_left
  signed_abs_mul_ne_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_mul_ne_zero_iff_of_balanced_right
  signed_mul_balanced_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.mul_balanced_zero_iff_of_balanced
  signed_abs_mul_eq_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_mul_eq_zero_iff_of_balanced
  signed_abs_mul_ne_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_mul_ne_zero_iff_of_balanced
  signed_le_product_left_factor_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.le_product_left_factor_iff_of_balanced
  signed_le_product_right_factor_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.le_product_right_factor_iff_of_balanced
  signed_le_of_product_left_factor_iff_of_balanced := by
    intro c a a' b
    exact SignedOrbit.le_of_product_left_factor_iff_of_balanced
  signed_le_of_product_right_factor_iff_of_balanced := by
    intro c a b b'
    exact SignedOrbit.le_of_product_right_factor_iff_of_balanced
  signed_lt_product_left_factor_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.lt_product_left_factor_iff_of_balanced
  signed_lt_product_right_factor_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.lt_product_right_factor_iff_of_balanced
  signed_lt_of_product_left_factor_iff_of_balanced := by
    intro c a a' b
    exact SignedOrbit.lt_of_product_left_factor_iff_of_balanced
  signed_lt_of_product_right_factor_iff_of_balanced := by
    intro c a b b'
    exact SignedOrbit.lt_of_product_right_factor_iff_of_balanced
  signed_cmp_product_left_factor_of_balanced := by
    intro a a' b c
    exact SignedOrbit.cmp_product_left_factor_of_balanced
  signed_cmp_product_right_factor_of_balanced := by
    intro a b b' c
    exact SignedOrbit.cmp_product_right_factor_of_balanced
  signed_cmp_of_product_left_factor_of_balanced := by
    intro c a a' b
    exact SignedOrbit.cmp_of_product_left_factor_of_balanced
  signed_cmp_of_product_right_factor_of_balanced := by
    intro c a b b'
    exact SignedOrbit.cmp_of_product_right_factor_of_balanced
  signed_le_product_factors_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.le_product_factors_iff_of_balanced
  signed_le_of_product_factors_iff_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.le_of_product_factors_iff_of_balanced
  signed_lt_product_factors_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.lt_product_factors_iff_of_balanced
  signed_lt_of_product_factors_iff_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.lt_of_product_factors_iff_of_balanced
  signed_cmp_product_factors_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.cmp_product_factors_of_balanced
  signed_cmp_of_product_factors_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.cmp_of_product_factors_of_balanced
  signed_le_products_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.le_products_iff_of_balanced
  signed_lt_products_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.lt_products_iff_of_balanced
  signed_cmp_products_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.cmp_products_of_balanced
  signed_balanced_product_left_factor_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.balanced_product_left_factor_iff_of_balanced
  signed_balanced_product_right_factor_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.balanced_product_right_factor_iff_of_balanced
  signed_balanced_product_factors_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.balanced_product_factors_iff_of_balanced
  signed_balanced_products_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.balanced_products_iff_of_balanced
  signed_le_sub_left_input_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.le_sub_left_input_iff_of_balanced
  signed_le_sub_right_input_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.le_sub_right_input_iff_of_balanced
  signed_le_of_sub_left_input_iff_of_balanced := by
    intro c a a' b
    exact SignedOrbit.le_of_sub_left_input_iff_of_balanced
  signed_le_of_sub_right_input_iff_of_balanced := by
    intro c a b b'
    exact SignedOrbit.le_of_sub_right_input_iff_of_balanced
  signed_lt_sub_left_input_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.lt_sub_left_input_iff_of_balanced
  signed_lt_sub_right_input_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.lt_sub_right_input_iff_of_balanced
  signed_lt_of_sub_left_input_iff_of_balanced := by
    intro c a a' b
    exact SignedOrbit.lt_of_sub_left_input_iff_of_balanced
  signed_lt_of_sub_right_input_iff_of_balanced := by
    intro c a b b'
    exact SignedOrbit.lt_of_sub_right_input_iff_of_balanced
  signed_cmp_sub_left_input_of_balanced := by
    intro a a' b c
    exact SignedOrbit.cmp_sub_left_input_of_balanced
  signed_cmp_sub_right_input_of_balanced := by
    intro a b b' c
    exact SignedOrbit.cmp_sub_right_input_of_balanced
  signed_cmp_of_sub_left_input_of_balanced := by
    intro c a a' b
    exact SignedOrbit.cmp_of_sub_left_input_of_balanced
  signed_cmp_of_sub_right_input_of_balanced := by
    intro c a b b'
    exact SignedOrbit.cmp_of_sub_right_input_of_balanced
  signed_le_sub_inputs_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.le_sub_inputs_iff_of_balanced
  signed_le_of_sub_inputs_iff_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.le_of_sub_inputs_iff_of_balanced
  signed_lt_sub_inputs_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.lt_sub_inputs_iff_of_balanced
  signed_lt_of_sub_inputs_iff_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.lt_of_sub_inputs_iff_of_balanced
  signed_cmp_sub_inputs_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.cmp_sub_inputs_of_balanced
  signed_cmp_of_sub_inputs_of_balanced := by
    intro c a a' b b'
    exact SignedOrbit.cmp_of_sub_inputs_of_balanced
  signed_le_subtractions_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.le_subtractions_iff_of_balanced
  signed_lt_subtractions_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.lt_subtractions_iff_of_balanced
  signed_cmp_subtractions_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.cmp_subtractions_of_balanced
  signed_balanced_sub_left_input_iff_of_balanced := by
    intro a a' b c
    exact SignedOrbit.balanced_sub_left_input_iff_of_balanced
  signed_balanced_sub_right_input_iff_of_balanced := by
    intro a b b' c
    exact SignedOrbit.balanced_sub_right_input_iff_of_balanced
  signed_balanced_sub_inputs_iff_of_balanced := by
    intro a a' b b' c
    exact SignedOrbit.balanced_sub_inputs_iff_of_balanced
  signed_balanced_subtractions_iff_of_balanced := by
    intro a a' b b' c c' d d'
    exact SignedOrbit.balanced_subtractions_iff_of_balanced
  signed_sub_balanced_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.sub_balanced_zero_iff_of_balanced_left
  signed_sub_balanced_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.sub_balanced_zero_iff_of_balanced_right
  signed_sub_balanced_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.sub_balanced_zero_iff_of_balanced
  signed_sub_not_balanced_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.sub_not_balanced_zero_iff_of_balanced_left
  signed_sub_not_balanced_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.sub_not_balanced_zero_iff_of_balanced_right
  signed_sub_not_balanced_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.sub_not_balanced_zero_iff_of_balanced
  signed_sub_balanced_zero_iff_balanced := SignedOrbit.sub_balanced_zero_iff_balanced
  signed_sub_not_balanced_zero_iff_not_balanced :=
    SignedOrbit.sub_not_balanced_zero_iff_not_balanced
  signed_abs_sub_eq_zero_iff_balanced := SignedOrbit.abs_sub_eq_zero_iff_balanced
  signed_abs_sub_ne_zero_iff_not_balanced :=
    SignedOrbit.abs_sub_ne_zero_iff_not_balanced
  signed_sub_self_balanced_zero := SignedOrbit.sub_self_balanced_zero
  signed_abs_sub_self_eq_zero := SignedOrbit.abs_sub_self_eq_zero
  signed_sub_zero_balanced := SignedOrbit.sub_zero_balanced
  signed_zero_sub_balanced_negate := SignedOrbit.zero_sub_balanced_negate
  signed_abs_sub_zero_eq := SignedOrbit.abs_sub_zero_eq
  signed_abs_zero_sub_eq := SignedOrbit.abs_zero_sub_eq
  signed_le_sub_zero_left_iff := SignedOrbit.le_sub_zero_left_iff
  signed_le_sub_zero_right_iff := SignedOrbit.le_sub_zero_right_iff
  signed_lt_sub_zero_left_iff := SignedOrbit.lt_sub_zero_left_iff
  signed_lt_sub_zero_right_iff := SignedOrbit.lt_sub_zero_right_iff
  signed_cmp_sub_zero_left := SignedOrbit.cmp_sub_zero_left
  signed_cmp_sub_zero_right := SignedOrbit.cmp_sub_zero_right
  signed_le_zero_sub_left_iff := SignedOrbit.le_zero_sub_left_iff
  signed_le_zero_sub_right_iff := SignedOrbit.le_zero_sub_right_iff
  signed_lt_zero_sub_left_iff := SignedOrbit.lt_zero_sub_left_iff
  signed_lt_zero_sub_right_iff := SignedOrbit.lt_zero_sub_right_iff
  signed_cmp_zero_sub_left := SignedOrbit.cmp_zero_sub_left
  signed_cmp_zero_sub_right := SignedOrbit.cmp_zero_sub_right
  signed_le_sub_self_left_iff := SignedOrbit.le_sub_self_left_iff
  signed_le_sub_self_right_iff := SignedOrbit.le_sub_self_right_iff
  signed_lt_sub_self_left_iff := SignedOrbit.lt_sub_self_left_iff
  signed_lt_sub_self_right_iff := SignedOrbit.lt_sub_self_right_iff
  signed_cmp_sub_self_left := SignedOrbit.cmp_sub_self_left
  signed_cmp_sub_self_right := SignedOrbit.cmp_sub_self_right
  signed_nonnegFlag_sub_zero := SignedOrbit.nonnegFlag_sub_zero
  signed_negativeFlag_sub_zero := SignedOrbit.negativeFlag_sub_zero
  signed_nonnegFlag_zero_sub := SignedOrbit.nonnegFlag_zero_sub
  signed_negativeFlag_zero_sub := SignedOrbit.negativeFlag_zero_sub
  signed_nonnegFlag_sub_self := SignedOrbit.nonnegFlag_sub_self
  signed_negativeFlag_sub_self := SignedOrbit.negativeFlag_sub_self
  signed_nonnegFlag_sub_iff_le := SignedOrbit.nonnegFlag_sub_iff_le
  signed_nonnegFlag_sub_eq_false_iff_lt :=
    SignedOrbit.nonnegFlag_sub_eq_false_iff_lt
  signed_negativeFlag_sub_iff_lt := SignedOrbit.negativeFlag_sub_iff_lt
  signed_negativeFlag_sub_eq_false_iff_le :=
    SignedOrbit.negativeFlag_sub_eq_false_iff_le
  signed_le_iff_nonnegFlag_sub := SignedOrbit.le_iff_nonnegFlag_sub
  signed_lt_iff_nonnegFlag_sub_eq_false :=
    SignedOrbit.lt_iff_nonnegFlag_sub_eq_false
  signed_lt_iff_negativeFlag_sub := SignedOrbit.lt_iff_negativeFlag_sub
  signed_le_iff_negativeFlag_sub_eq_false :=
    SignedOrbit.le_iff_negativeFlag_sub_eq_false
  signed_nonnegFlag_mul_ofOrbit_right_of_ne_zero :=
    SignedOrbit.nonnegFlag_mul_ofOrbit_right_of_ne_zero
  signed_negativeFlag_mul_ofOrbit_right_of_ne_zero :=
    SignedOrbit.negativeFlag_mul_ofOrbit_right_of_ne_zero
  signed_nonnegFlag_mul_ofOrbit_left_of_ne_zero :=
    SignedOrbit.nonnegFlag_mul_ofOrbit_left_of_ne_zero
  signed_negativeFlag_mul_ofOrbit_left_of_ne_zero :=
    SignedOrbit.negativeFlag_mul_ofOrbit_left_of_ne_zero
  signed_le_congr_left_of_balanced := by
    intro a a' b
    exact SignedOrbit.le_congr_left_of_balanced
  signed_le_congr_right_of_balanced := by
    intro a b b'
    exact SignedOrbit.le_congr_right_of_balanced
  signed_lt_congr_left_of_balanced := by
    intro a a' b
    exact SignedOrbit.lt_congr_left_of_balanced
  signed_lt_congr_right_of_balanced := by
    intro a b b'
    exact SignedOrbit.lt_congr_right_of_balanced
  signed_le_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.le_congr_of_balanced
  signed_lt_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.lt_congr_of_balanced
  signed_cmp_lt := by
    intro a b
    exact SignedOrbit.cmp_eq_lt_of_lt
  signed_cmp_eq := by
    intro a b
    exact SignedOrbit.cmp_eq_eq_of_balanced
  signed_cmp_gt := by
    intro a b
    exact SignedOrbit.cmp_eq_gt_of_gt
  signed_cmp_lt_iff := SignedOrbit.cmp_eq_lt_iff
  signed_cmp_eq_iff := SignedOrbit.cmp_eq_eq_iff
  signed_cmp_gt_iff := SignedOrbit.cmp_eq_gt_iff
  signed_cmp_congr_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.cmp_congr_of_balanced
  signed_balanced_add_left_iff := SignedOrbit.balanced_add_left_iff
  signed_balanced_add_right_iff := SignedOrbit.balanced_add_right_iff
  signed_balanced_negate_iff := SignedOrbit.balanced_negate_iff
  signed_abs_zero_iff_balanced_zero := SignedOrbit.abs_eq_zero_iff_balanced_zero
  signed_abs_nonnegative_branch := by
    intro z
    exact SignedOrbit.abs_toInt_of_nonnegFlag
  signed_abs_negative_branch := by
    intro z
    exact SignedOrbit.abs_toInt_of_negativeFlag
  signed_balanced_of_nonnegFlag := by
    intro z
    exact SignedOrbit.balanced_of_nonnegFlag
  signed_balanced_of_negativeFlag := by
    intro z
    exact SignedOrbit.balanced_of_negativeFlag
  signed_balanced_sign_canonical := SignedOrbit.balanced_sign_canonical
  signed_balanced_ofOrbit_abs_iff_nonnegFlag :=
    SignedOrbit.balanced_ofOrbit_abs_iff_nonnegFlag
  signed_balanced_negate_ofOrbit_abs_iff_negate_nonnegFlag :=
    SignedOrbit.balanced_negate_ofOrbit_abs_iff_negate_nonnegFlag
  signed_balanced_negate_ofOrbit_abs_iff_negativeFlag_or_balanced_zero :=
    SignedOrbit.balanced_negate_ofOrbit_abs_iff_negativeFlag_or_balanced_zero
  signed_balanced_both_abs_representatives_iff_balanced_zero :=
    SignedOrbit.balanced_both_abs_representatives_iff_balanced_zero
  signed_balanced_zero_of_both_abs_representatives := by
    intro z
    exact SignedOrbit.balanced_zero_of_both_abs_representatives
  signed_not_both_abs_representatives_of_not_balanced_zero := by
    intro z
    exact SignedOrbit.not_both_abs_representatives_of_not_balanced_zero
  signed_not_balanced_ofOrbit_abs_of_negativeFlag := by
    intro z
    exact SignedOrbit.not_balanced_ofOrbit_abs_of_negativeFlag
  signed_balanced_negate_ofOrbit_abs_iff_balanced_zero_of_nonnegFlag := by
    intro z
    exact SignedOrbit.balanced_negate_ofOrbit_abs_iff_balanced_zero_of_nonnegFlag
  signed_abs_balanced_invariant := by
    intro z w
    exact SignedOrbit.abs_eq_of_balanced
  signed_abs_sub_eq_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_sub_eq_of_balanced_left
  signed_abs_sub_eq_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_sub_eq_of_balanced_right
  signed_abs_sub_eq_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_sub_eq_of_balanced
  signed_abs_sub_eq_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_sub_eq_zero_iff_of_balanced_left
  signed_abs_sub_eq_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_sub_eq_zero_iff_of_balanced_right
  signed_abs_sub_eq_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_sub_eq_zero_iff_of_balanced
  signed_abs_sub_ne_zero_iff_of_balanced_left := by
    intro a a' b
    exact SignedOrbit.abs_sub_ne_zero_iff_of_balanced_left
  signed_abs_sub_ne_zero_iff_of_balanced_right := by
    intro a b b'
    exact SignedOrbit.abs_sub_ne_zero_iff_of_balanced_right
  signed_abs_sub_ne_zero_iff_of_balanced := by
    intro a a' b b'
    exact SignedOrbit.abs_sub_ne_zero_iff_of_balanced
  signed_le_add_left_iff := SignedOrbit.le_add_left_iff
  signed_le_add_right_iff := SignedOrbit.le_add_right_iff
  signed_lt_add_left_iff := SignedOrbit.lt_add_left_iff
  signed_lt_add_right_iff := SignedOrbit.lt_add_right_iff
  signed_add_le_add := by
    intro a b c d
    exact SignedOrbit.add_le_add
  signed_add_lt_add_left := by
    intro a b c
    exact SignedOrbit.add_lt_add_left
  signed_add_lt_add_right := by
    intro a b c
    exact SignedOrbit.add_lt_add_right
  signed_negate_le_negate_iff := SignedOrbit.negate_le_negate_iff
  signed_negate_lt_negate_iff := SignedOrbit.negate_lt_negate_iff
  signed_cmp_add_left := SignedOrbit.cmp_add_left
  signed_cmp_add_right := SignedOrbit.cmp_add_right
  signed_cmp_negate_swap := SignedOrbit.cmp_negate_swap
  signed_abs_negate := SignedOrbit.abs_negate
  signed_abs_ofOrbit := SignedOrbit.abs_ofOrbit
  signed_abs_negate_ofOrbit := SignedOrbit.abs_negate_ofOrbit
  signed_nonnegFlag_ofOrbit := SignedOrbit.nonnegFlag_ofOrbit
  signed_negativeFlag_ofOrbit := SignedOrbit.negativeFlag_ofOrbit
  signed_nonnegFlag_negate_ofOrbit_of_ne_zero :=
    SignedOrbit.nonnegFlag_negate_ofOrbit_of_ne_zero
  signed_negativeFlag_negate_ofOrbit_of_ne_zero :=
    SignedOrbit.negativeFlag_negate_ofOrbit_of_ne_zero
  signed_negate_ofOrbit_not_balanced_zero_of_ne_zero :=
    SignedOrbit.negate_ofOrbit_not_balanced_zero_of_ne_zero
  signed_nonnegFlag_negate_ofOrbit_eq_true_iff_zero :=
    SignedOrbit.nonnegFlag_negate_ofOrbit_eq_true_iff_zero
  signed_negativeFlag_negate_ofOrbit_eq_true_iff_ne_zero :=
    SignedOrbit.negativeFlag_negate_ofOrbit_eq_true_iff_ne_zero
  signed_negate_ofOrbit_balanced_zero_iff :=
    SignedOrbit.negate_ofOrbit_balanced_zero_iff
  signed_abs_add_le_add_abs := SignedOrbit.abs_add_le_add_abs
  signed_abs_sub_le_add_abs := SignedOrbit.abs_sub_le_add_abs
  signed_abs_le_iff_between := SignedOrbit.abs_le_iff_between
  signed_between_of_abs_le := by
    intro z n
    exact SignedOrbit.between_of_abs_le
  signed_abs_le_of_between := by
    intro z n
    exact SignedOrbit.abs_le_of_between
  signed_neg_abs_le_self := SignedOrbit.neg_abs_le_self
  signed_self_le_abs := SignedOrbit.self_le_abs
  signed_abs_le_trans := by
    intro z n m
    exact SignedOrbit.abs_le_trans
  signed_between_mono := by
    intro z n m
    exact SignedOrbit.between_mono
  ratio_recip_den_internal := RatioOrbit.recipNonzero_den_eq_abs
  ratio_recip_num_nonnegative_branch := by
    intro a h
    exact RatioOrbit.recipNonzero_num_eq_of_nonnegFlag
  ratio_recip_num_negative_branch := by
    intro a h
    exact RatioOrbit.recipNonzero_num_eq_of_negativeFlag
  ratio_recip_num_abs_eq_den := RatioOrbit.recipNonzero_num_abs_eq_den
  ratio_recip_num_not_balanced_zero := RatioOrbit.recipNonzero_num_not_balanced_zero
  ratio_recip_num_nonnegFlag_eq := RatioOrbit.recipNonzero_num_nonnegFlag_eq
  ratio_recip_num_negativeFlag_eq := RatioOrbit.recipNonzero_num_negativeFlag_eq
  ratio_recip_num_zero_le_iff := RatioOrbit.recipNonzero_num_zero_le_iff
  ratio_recip_num_lt_zero_iff := RatioOrbit.recipNonzero_num_lt_zero_iff
  ratio_recip_num_zero_lt_iff := RatioOrbit.recipNonzero_num_zero_lt_iff
  ratio_recip_num_cmp_zero := RatioOrbit.recipNonzero_num_cmp_zero
  ratio_recip_num_zero_cmp := RatioOrbit.recipNonzero_num_zero_cmp
  ratio_recip_num_balanced_ofOrbit_den_iff_nonnegFlag :=
    RatioOrbit.recipNonzero_num_balanced_ofOrbit_den_iff_nonnegFlag
  ratio_recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag :=
    RatioOrbit.recipNonzero_num_balanced_negate_ofOrbit_den_iff_negativeFlag
  ratio_recip_num_not_balanced_ofOrbit_den_iff_negativeFlag :=
    RatioOrbit.recipNonzero_num_not_balanced_ofOrbit_den_iff_negativeFlag
  ratio_recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag :=
    RatioOrbit.recipNonzero_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag
  ratio_num_mul_recip_num_balanced_den_mul_abs :=
    RatioOrbit.num_mul_recipNonzero_num_balanced_ofOrbit_den_mul_abs
  ratio_mul_recipNonzero_crossEq_one :=
    RatioOrbit.mul_recipNonzero_crossEq_one
  ratio_recip_num_mul_num_balanced_den_mul_abs :=
    RatioOrbit.recipNonzero_num_mul_num_balanced_ofOrbit_den_mul_abs
  ratio_recipNonzero_mul_crossEq_one :=
    RatioOrbit.recipNonzero_mul_crossEq_one
  ratio_recip_eq_recipNonzero_of_not_balanced_zero :=
    RatioOrbit.recip_eq_recipNonzero_of_not_balanced_zero
  ratio_mul_recip_crossEq_one_of_not_balanced_zero :=
    RatioOrbit.mul_recip_crossEq_one_of_not_balanced_zero
  ratio_recip_mul_crossEq_one_of_not_balanced_zero :=
    RatioOrbit.recip_mul_crossEq_one_of_not_balanced_zero
  ratio_recip_den_eq_abs_of_not_balanced_zero :=
    RatioOrbit.recip_den_eq_abs_of_not_balanced_zero
  ratio_recip_num_abs_eq_den_of_not_balanced_zero :=
    RatioOrbit.recip_num_abs_eq_den_of_not_balanced_zero
  ratio_recip_num_not_balanced_zero_of_not_balanced_zero :=
    RatioOrbit.recip_num_not_balanced_zero_of_not_balanced_zero
  ratio_recip_num_nonnegFlag_eq_of_not_balanced_zero :=
    RatioOrbit.recip_num_nonnegFlag_eq_of_not_balanced_zero
  ratio_recip_num_negativeFlag_eq_of_not_balanced_zero :=
    RatioOrbit.recip_num_negativeFlag_eq_of_not_balanced_zero
  ratio_recip_num_zero_le_iff_of_not_balanced_zero :=
    RatioOrbit.recip_num_zero_le_iff_of_not_balanced_zero
  ratio_recip_num_lt_zero_iff_of_not_balanced_zero :=
    RatioOrbit.recip_num_lt_zero_iff_of_not_balanced_zero
  ratio_recip_num_zero_lt_iff_of_not_balanced_zero :=
    RatioOrbit.recip_num_zero_lt_iff_of_not_balanced_zero
  ratio_recip_num_cmp_zero_of_not_balanced_zero :=
    RatioOrbit.recip_num_cmp_zero_of_not_balanced_zero
  ratio_recip_num_zero_cmp_of_not_balanced_zero :=
    RatioOrbit.recip_num_zero_cmp_of_not_balanced_zero
  ratio_recip_num_balanced_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero :=
    RatioOrbit.recip_num_balanced_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero
  ratio_recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero :=
    RatioOrbit.recip_num_balanced_negate_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero
  ratio_recip_num_not_balanced_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero :=
    RatioOrbit.recip_num_not_balanced_ofOrbit_den_iff_negativeFlag_of_not_balanced_zero
  ratio_recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero :=
    RatioOrbit.recip_num_not_balanced_negate_ofOrbit_den_iff_nonnegFlag_of_not_balanced_zero
  ratio_recip_num_nonnegative_branch_of_not_balanced_zero := by
    intro a h
    exact RatioOrbit.recip_num_eq_of_nonnegFlag_of_not_balanced_zero h
  ratio_recip_num_negative_branch_of_not_balanced_zero := by
    intro a h
    exact RatioOrbit.recip_num_eq_of_negativeFlag_of_not_balanced_zero h
  ratio_num_mul_recip_num_balanced_den_mul_abs_of_not_balanced_zero :=
    RatioOrbit.num_mul_recip_num_balanced_ofOrbit_den_mul_abs_of_not_balanced_zero
  ratio_recip_num_mul_num_balanced_den_mul_abs_of_not_balanced_zero :=
    RatioOrbit.recip_num_mul_num_balanced_ofOrbit_den_mul_abs_of_not_balanced_zero
  ratio_recip_num_balanced_zero_iff :=
    RatioOrbit.recip_num_balanced_zero_iff
  ratio_recip_num_not_balanced_zero_iff :=
    RatioOrbit.recip_num_not_balanced_zero_iff
  ratio_crossEq_zero_iff_num_balanced_zero :=
    RatioOrbit.crossEq_zero_iff_num_balanced_zero
  ratio_zero_crossEq_iff_num_balanced_zero :=
    RatioOrbit.zero_crossEq_iff_num_balanced_zero
  ratio_recip_crossEq_zero_iff_num_balanced_zero :=
    RatioOrbit.recip_crossEq_zero_iff_num_balanced_zero
  ratio_zero_crossEq_recip_iff_num_balanced_zero :=
    RatioOrbit.zero_crossEq_recip_iff_num_balanced_zero
  ratio_recip_crossEq_zero_iff_crossEq_zero :=
    RatioOrbit.recip_crossEq_zero_iff_crossEq_zero
  ratio_zero_crossEq_recip_iff_zero_crossEq :=
    RatioOrbit.zero_crossEq_recip_iff_zero_crossEq
  ratio_recip_crossEq_zero_iff_zero_crossEq :=
    RatioOrbit.recip_crossEq_zero_iff_zero_crossEq
  ratio_zero_crossEq_recip_iff_crossEq_zero :=
    RatioOrbit.zero_crossEq_recip_iff_crossEq_zero
  ratio_recip_not_crossEq_zero_iff_not_crossEq_zero :=
    RatioOrbit.recip_not_crossEq_zero_iff_not_crossEq_zero
  ratio_zero_not_crossEq_recip_iff_zero_not_crossEq :=
    RatioOrbit.zero_not_crossEq_recip_iff_zero_not_crossEq
  ratio_recip_not_crossEq_zero_iff_zero_not_crossEq :=
    RatioOrbit.recip_not_crossEq_zero_iff_zero_not_crossEq
  ratio_zero_not_crossEq_recip_iff_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_recip_iff_not_crossEq_zero
  ratio_recip_recipNonzero_crossEq_self :=
    RatioOrbit.recip_recipNonzero_crossEq_self
  ratio_self_crossEq_recip_recipNonzero :=
    RatioOrbit.self_crossEq_recip_recipNonzero
  ratio_recip_recip_crossEq_self :=
    RatioOrbit.recip_recip_crossEq_self
  ratio_self_crossEq_recip_recip :=
    RatioOrbit.self_crossEq_recip_recip
  ratio_recip_crossEq_congr :=
    @RatioOrbit.recip_crossEq_congr
  ratio_recip_crossEq_iff :=
    RatioOrbit.recip_crossEq_iff
  ratio_recip_crossEq_iff_crossEq_recip :=
    RatioOrbit.recip_crossEq_iff_crossEq_recip
  ratio_crossEq_recip_iff_recip_crossEq :=
    RatioOrbit.crossEq_recip_iff_recip_crossEq
  ratio_mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero :=
    RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_right_not_crossEq_zero
  ratio_mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero :=
    RatioOrbit.mul_crossEq_one_iff_crossEq_recip_of_left_not_crossEq_zero
  ratio_mul_recip_cancel_right_crossEq_self_of_right_not_crossEq_zero :=
    RatioOrbit.mul_recip_cancel_right_crossEq_self_of_right_not_crossEq_zero
  ratio_recip_mul_cancel_left_crossEq_self_of_left_not_crossEq_zero :=
    RatioOrbit.recip_mul_cancel_left_crossEq_self_of_left_not_crossEq_zero
  ratio_mul_recip_cancel_right_assoc_crossEq_self_of_right_not_crossEq_zero :=
    RatioOrbit.mul_recip_cancel_right_assoc_crossEq_self_of_right_not_crossEq_zero
  ratio_recip_mul_cancel_left_assoc_crossEq_self_of_left_not_crossEq_zero :=
    RatioOrbit.recip_mul_cancel_left_assoc_crossEq_self_of_left_not_crossEq_zero
  ratio_mul_right_crossEq_iff_of_not_crossEq_zero :=
    RatioOrbit.mul_right_crossEq_iff_of_not_crossEq_zero
  ratio_mul_left_crossEq_iff_of_not_crossEq_zero :=
    RatioOrbit.mul_left_crossEq_iff_of_not_crossEq_zero
  ratio_mul_crossEq_zero_iff :=
    RatioOrbit.mul_crossEq_zero_iff
  ratio_zero_crossEq_mul_iff :=
    RatioOrbit.zero_crossEq_mul_iff
  ratio_mul_not_crossEq_zero_iff :=
    RatioOrbit.mul_not_crossEq_zero_iff
  ratio_zero_not_crossEq_mul_iff :=
    RatioOrbit.zero_not_crossEq_mul_iff
  ratio_mul_not_crossEq_zero_of_not_crossEq_zero :=
    RatioOrbit.mul_not_crossEq_zero_of_not_crossEq_zero
  ratio_zero_not_crossEq_mul_of_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_mul_of_not_crossEq_zero
  ratio_left_not_crossEq_zero_of_mul_not_crossEq_zero :=
    RatioOrbit.left_not_crossEq_zero_of_mul_not_crossEq_zero
  ratio_right_not_crossEq_zero_of_mul_not_crossEq_zero :=
    RatioOrbit.right_not_crossEq_zero_of_mul_not_crossEq_zero
  ratio_mul_crossEq_congr :=
    @RatioOrbit.mul_crossEq_congr
  ratio_mul_crossEq_congr_left :=
    @RatioOrbit.mul_crossEq_congr_left
  ratio_mul_crossEq_congr_right :=
    @RatioOrbit.mul_crossEq_congr_right
  ratio_mul_comm_crossEq :=
    RatioOrbit.mul_comm_crossEq
  ratio_mul_assoc_crossEq :=
    RatioOrbit.mul_assoc_crossEq
  ratio_mul_one_crossEq :=
    RatioOrbit.mul_one_crossEq
  ratio_one_mul_crossEq :=
    RatioOrbit.one_mul_crossEq
  ratio_mul_zero_crossEq :=
    RatioOrbit.mul_zero_crossEq
  ratio_zero_mul_crossEq :=
    RatioOrbit.zero_mul_crossEq
  ratio_one_not_crossEq_zero :=
    RatioOrbit.one_not_crossEq_zero
  ratio_zero_not_crossEq_one :=
    RatioOrbit.zero_not_crossEq_one
  ratio_recip_zero_crossEq_zero :=
    RatioOrbit.recip_zero_crossEq_zero
  ratio_zero_crossEq_recip_zero :=
    RatioOrbit.zero_crossEq_recip_zero
  ratio_recip_one_crossEq_one :=
    RatioOrbit.recip_one_crossEq_one
  ratio_one_crossEq_recip_one :=
    RatioOrbit.one_crossEq_recip_one
  ratio_factors_not_crossEq_zero_of_mul_crossEq_one :=
    RatioOrbit.factors_not_crossEq_zero_of_mul_crossEq_one
  ratio_left_not_crossEq_zero_of_mul_crossEq_one :=
    RatioOrbit.left_not_crossEq_zero_of_mul_crossEq_one
  ratio_right_not_crossEq_zero_of_mul_crossEq_one :=
    RatioOrbit.right_not_crossEq_zero_of_mul_crossEq_one
  ratio_factors_not_crossEq_zero_of_one_crossEq_mul :=
    RatioOrbit.factors_not_crossEq_zero_of_one_crossEq_mul
  ratio_left_not_crossEq_zero_of_one_crossEq_mul :=
    RatioOrbit.left_not_crossEq_zero_of_one_crossEq_mul
  ratio_right_not_crossEq_zero_of_one_crossEq_mul :=
    RatioOrbit.right_not_crossEq_zero_of_one_crossEq_mul
  ratio_crossEq_recip_right_of_mul_crossEq_one :=
    RatioOrbit.crossEq_recip_right_of_mul_crossEq_one
  ratio_crossEq_recip_left_of_mul_crossEq_one :=
    RatioOrbit.crossEq_recip_left_of_mul_crossEq_one
  ratio_crossEq_recip_right_of_one_crossEq_mul :=
    RatioOrbit.crossEq_recip_right_of_one_crossEq_mul
  ratio_crossEq_recip_left_of_one_crossEq_mul :=
    RatioOrbit.crossEq_recip_left_of_one_crossEq_mul
  ratio_recip_mul_crossEq_mul_recip_of_not_crossEq_zero :=
    RatioOrbit.recip_mul_crossEq_mul_recip_of_not_crossEq_zero
  ratio_mul_recip_crossEq_recip_mul_of_not_crossEq_zero :=
    RatioOrbit.mul_recip_crossEq_recip_mul_of_not_crossEq_zero
  ratio_recip_mul_crossEq_mul_recip_comm_of_not_crossEq_zero :=
    RatioOrbit.recip_mul_crossEq_mul_recip_comm_of_not_crossEq_zero
  ratio_mul_recip_comm_crossEq_recip_mul_of_not_crossEq_zero :=
    RatioOrbit.mul_recip_comm_crossEq_recip_mul_of_not_crossEq_zero
  ratio_mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.mul_mul_recip_pair_crossEq_one_of_not_crossEq_zero
  ratio_recip_pair_mul_mul_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.recip_pair_mul_mul_crossEq_one_of_not_crossEq_zero
  ratio_mul_mul_recip_pair_comm_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.mul_mul_recip_pair_comm_crossEq_one_of_not_crossEq_zero
  ratio_recip_pair_comm_mul_mul_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.recip_pair_comm_mul_mul_crossEq_one_of_not_crossEq_zero
  ratio_mul_recip_pair_not_crossEq_zero_of_not_crossEq_zero :=
    RatioOrbit.mul_recip_pair_not_crossEq_zero_of_not_crossEq_zero
  ratio_zero_not_crossEq_mul_recip_pair_of_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_mul_recip_pair_of_not_crossEq_zero
  ratio_mul_recip_pair_comm_not_crossEq_zero_of_not_crossEq_zero :=
    RatioOrbit.mul_recip_pair_comm_not_crossEq_zero_of_not_crossEq_zero
  ratio_zero_not_crossEq_mul_recip_pair_comm_of_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_mul_recip_pair_comm_of_not_crossEq_zero
  ratio_mul_recip_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.mul_recip_crossEq_one_of_not_crossEq_zero
  ratio_recip_mul_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.recip_mul_crossEq_one_of_not_crossEq_zero
  ratio_one_crossEq_mul_recip_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_mul_recip_of_not_crossEq_zero
  ratio_one_crossEq_recip_mul_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_recip_mul_of_not_crossEq_zero
  ratio_mul_product_recip_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.mul_product_recip_crossEq_one_of_not_crossEq_zero
  ratio_recip_product_mul_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.recip_product_mul_crossEq_one_of_not_crossEq_zero
  ratio_one_crossEq_mul_product_recip_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_mul_product_recip_of_not_crossEq_zero
  ratio_one_crossEq_recip_product_mul_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_recip_product_mul_of_not_crossEq_zero
  ratio_recip_product_not_crossEq_zero_of_not_crossEq_zero :=
    RatioOrbit.recip_product_not_crossEq_zero_of_not_crossEq_zero
  ratio_zero_not_crossEq_recip_product_of_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_recip_product_of_not_crossEq_zero
  ratio_recip_product_comm_not_crossEq_zero_of_not_crossEq_zero :=
    RatioOrbit.recip_product_comm_not_crossEq_zero_of_not_crossEq_zero
  ratio_zero_not_crossEq_recip_product_comm_of_not_crossEq_zero :=
    RatioOrbit.zero_not_crossEq_recip_product_comm_of_not_crossEq_zero
  ratio_recip_product_comm_crossEq_recip_product :=
    RatioOrbit.recip_product_comm_crossEq_recip_product
  ratio_recip_product_crossEq_recip_product_comm :=
    RatioOrbit.recip_product_crossEq_recip_product_comm
  ratio_mul_product_comm_recip_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.mul_product_comm_recip_crossEq_one_of_not_crossEq_zero
  ratio_recip_product_comm_mul_crossEq_one_of_not_crossEq_zero :=
    RatioOrbit.recip_product_comm_mul_crossEq_one_of_not_crossEq_zero
  ratio_one_crossEq_mul_product_comm_recip_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_mul_product_comm_recip_of_not_crossEq_zero
  ratio_one_crossEq_recip_product_comm_mul_of_not_crossEq_zero :=
    RatioOrbit.one_crossEq_recip_product_comm_mul_of_not_crossEq_zero
  ratio_recip_right_crossEq_of_mul_crossEq_one :=
    RatioOrbit.recip_right_crossEq_of_mul_crossEq_one
  ratio_recip_left_crossEq_of_mul_crossEq_one :=
    RatioOrbit.recip_left_crossEq_of_mul_crossEq_one
  ratio_recip_right_crossEq_of_one_crossEq_mul :=
    RatioOrbit.recip_right_crossEq_of_one_crossEq_mul
  ratio_recip_left_crossEq_of_one_crossEq_mul :=
    RatioOrbit.recip_left_crossEq_of_one_crossEq_mul
  ratio_mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_crossEq_recip
  ratio_mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_crossEq_recip
  ratio_one_crossEq_mul_iff_right_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.one_crossEq_mul_iff_right_not_crossEq_zero_and_crossEq_recip
  ratio_one_crossEq_mul_iff_left_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.one_crossEq_mul_iff_left_not_crossEq_zero_and_crossEq_recip
  ratio_mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.mul_crossEq_one_iff_right_not_crossEq_zero_and_recip_crossEq
  ratio_mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.mul_crossEq_one_iff_left_not_crossEq_zero_and_recip_crossEq
  ratio_one_crossEq_mul_iff_right_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.one_crossEq_mul_iff_right_not_crossEq_zero_and_recip_crossEq
  ratio_one_crossEq_mul_iff_left_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.one_crossEq_mul_iff_left_not_crossEq_zero_and_recip_crossEq
  ratio_mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_crossEq_recip
  ratio_one_crossEq_mul_iff_factors_not_crossEq_zero_and_crossEq_recip :=
    RatioOrbit.one_crossEq_mul_iff_factors_not_crossEq_zero_and_crossEq_recip
  ratio_mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.mul_crossEq_one_iff_factors_not_crossEq_zero_and_recip_crossEq
  ratio_one_crossEq_mul_iff_factors_not_crossEq_zero_and_recip_crossEq :=
    RatioOrbit.one_crossEq_mul_iff_factors_not_crossEq_zero_and_recip_crossEq

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
