/-
  PrimitiveRecognitionCalculus/IntegerRational.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K4.6, K4.7, K4.8, K4.9, K4.10, A5

  Quotient-native PRC integers and rationals. The equivalence relations are
  internal:

    - PRCInt: signed orbits identified by balanced orbit length,
        a.pos + b.neg = b.pos + a.neg.
    - PRCRat: ratio orbits identified by cross-multiplication of the
        signed numerator by the denominator,
        a.num · b.den ~ b.num · a.den (balanced equality of SignedOrbits).

  The maps to verifier `ℤ` and `ℚ` are conservative displays, not
  definitional.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.OrbitArithmetic

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

namespace DistinctionNat

/-! ## Internal comparison support for signed-orbit order -/

/-- Truncated subtraction on finite δ-orbit positions. -/
def truncatedSub : DistinctionNat → DistinctionNat → DistinctionNat
  | a, zero => a
  | zero, succ _ => zero
  | succ a, succ b => truncatedSub a b

/-- Boolean `≤` on finite δ-orbit positions, by structural recursion only. -/
def leq : DistinctionNat → DistinctionNat → Bool
  | zero, _ => true
  | succ _, zero => false
  | succ a, succ b => leq a b

/-- Absolute difference of two finite δ-orbit positions. -/
def absDiff (a b : DistinctionNat) : DistinctionNat :=
  truncatedSub a b + truncatedSub b a

/-- Verifier display of internal truncated subtraction. -/
theorem toNat_truncatedSub (a b : DistinctionNat) :
    (truncatedSub a b).toNat = a.toNat - b.toNat := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b => simp [truncatedSub]
  | succ a ih =>
      cases b with
      | zero => rfl
      | succ b =>
          simp [truncatedSub, ih]

/-- Internal Boolean order agrees with the verifier `Nat` order.
    Choice-free: the proof uses only structural recursion and the successor
    order lemma, so its axiom footprint is `[propext]` (audit tier FORCED). -/
theorem leq_eq_true_iff (a b : DistinctionNat) :
    leq a b = true ↔ a.toNat ≤ b.toNat := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => exact ⟨fun _ => Nat.le_refl 0, fun _ => rfl⟩
      | succ b => exact ⟨fun _ => Nat.zero_le _, fun _ => rfl⟩
  | succ a ih =>
      cases b with
      | zero =>
          show (false = true) ↔ (toNat a).succ ≤ (0 : Nat)
          exact ⟨fun h => Bool.noConfusion h,
                 fun h => absurd h (Nat.not_succ_le_zero _)⟩
      | succ b =>
          show leq a b = true ↔ (toNat a).succ ≤ (toNat b).succ
          rw [ih, Nat.succ_le_succ_iff]

/-- Internal Boolean order is false exactly when verifier order is reversed. -/
theorem leq_eq_false_iff (a b : DistinctionNat) :
    leq a b = false ↔ b.toNat < a.toNat := by
  rw [← Bool.not_eq_true, leq_eq_true_iff]
  omega

/-- Verifier display of internal absolute difference. -/
theorem toNat_absDiff (a b : DistinctionNat) :
    (absDiff a b).toNat =
      Int.natAbs ((a.toNat : ℤ) - (b.toNat : ℤ)) := by
  unfold absDiff
  rw [toNat_add, toNat_truncatedSub, toNat_truncatedSub]
  by_cases h : b.toNat ≤ a.toNat
  · have hzero : b.toNat - a.toNat = 0 := Nat.sub_eq_zero_of_le h
    rw [hzero, Nat.add_zero]
    have hnonneg : 0 ≤ (a.toNat : ℤ) - (b.toNat : ℤ) := by
      omega
    have hcast : ((Int.natAbs ((a.toNat : ℤ) - (b.toNat : ℤ)) : ℤ) =
        (a.toNat : ℤ) - (b.toNat : ℤ)) := by
      rw [Int.natAbs_of_nonneg hnonneg]
    apply Nat.cast_injective (R := ℤ)
    rw [hcast]
    omega
  · have hle : a.toNat ≤ b.toNat := by omega
    have hzero : a.toNat - b.toNat = 0 := Nat.sub_eq_zero_of_le hle
    rw [hzero, Nat.zero_add]
    have hnonpos : (a.toNat : ℤ) - (b.toNat : ℤ) ≤ 0 := by
      omega
    have hcast : ((Int.natAbs ((a.toNat : ℤ) - (b.toNat : ℤ)) : ℤ) =
        -((a.toNat : ℤ) - (b.toNat : ℤ))) := by
      have hneg_nonneg : 0 ≤ -((a.toNat : ℤ) - (b.toNat : ℤ)) := by
        omega
      have hneg_abs : ((Int.natAbs (-((a.toNat : ℤ) - (b.toNat : ℤ))) : ℤ) =
          -((a.toNat : ℤ) - (b.toNat : ℤ))) := by
        rw [Int.natAbs_of_nonneg hneg_nonneg]
      rwa [Int.natAbs_neg] at hneg_abs
    apply Nat.cast_injective (R := ℤ)
    rw [hcast]
    omega

end DistinctionNat

/-! ## Signed orbits and the balanced-length equivalence -/

/-- K4.6. A signed orbit difference. Intended meaning: `pos - neg`. -/
structure SignedOrbit where
  pos : DistinctionNat
  neg : DistinctionNat
  deriving DecidableEq, Repr

namespace SignedOrbit

/-- A verifier display of a signed orbit as an integer. -/
def toInt (z : SignedOrbit) : ℤ :=
  (z.pos.toNat : ℤ) - (z.neg.toNat : ℤ)

@[simp] theorem toInt_mk (a b : DistinctionNat) :
    toInt ⟨a, b⟩ = (a.toNat : ℤ) - (b.toNat : ℤ) := by
  rfl

/-- The zero signed orbit. -/
def zero : SignedOrbit :=
  ⟨DistinctionNat.zero, DistinctionNat.zero⟩

@[simp] theorem zero_toInt :
    zero.toInt = 0 := by
  rfl

/-- The unit signed orbit. -/
def one : SignedOrbit :=
  ⟨DistinctionNat.succ DistinctionNat.zero, DistinctionNat.zero⟩

@[simp] theorem one_toInt :
    one.toInt = 1 := by
  rfl

/-- A nonnegative signed orbit built from a δ-orbit position. -/
def ofOrbit (n : DistinctionNat) : SignedOrbit :=
  ⟨n, DistinctionNat.zero⟩

@[simp] theorem ofOrbit_toInt (n : DistinctionNat) :
    (ofOrbit n).toInt = n.toNat := by
  show (n.toNat : ℤ) - 0 = n.toNat
  ring

/-- Pointwise addition of signed orbits. -/
def add (a b : SignedOrbit) : SignedOrbit where
  pos := a.pos + b.pos
  neg := a.neg + b.neg

@[simp] theorem add_pos (a b : SignedOrbit) :
    (add a b).pos = a.pos + b.pos := rfl

@[simp] theorem add_neg (a b : SignedOrbit) :
    (add a b).neg = a.neg + b.neg := rfl

theorem add_toInt (a b : SignedOrbit) :
    (add a b).toInt = a.toInt + b.toInt := by
  show ((a.pos + b.pos).toNat : ℤ) - ((a.neg + b.neg).toNat : ℤ) =
    ((a.pos.toNat : ℤ) - (a.neg.toNat : ℤ)) +
    ((b.pos.toNat : ℤ) - (b.neg.toNat : ℤ))
  rw [DistinctionNat.toNat_add, DistinctionNat.toNat_add]
  push_cast
  ring

/-- Pointwise negation of signed orbits: swap pos and neg. Named
`negate` rather than `neg` to avoid collision with the structure field. -/
def negate (a : SignedOrbit) : SignedOrbit where
  pos := a.neg
  neg := a.pos

@[simp] theorem negate_pos (a : SignedOrbit) :
    (negate a).pos = a.neg := rfl

@[simp] theorem negate_neg (a : SignedOrbit) :
    (negate a).neg = a.pos := rfl

theorem negate_toInt (a : SignedOrbit) :
    (negate a).toInt = -a.toInt := by
  show (a.neg.toNat : ℤ) - (a.pos.toNat : ℤ) =
    -((a.pos.toNat : ℤ) - (a.neg.toNat : ℤ))
  ring

/-- Signed orbit multiplication:
`(p₁ − n₁) · (p₂ − n₂) = (p₁p₂ + n₁n₂) − (p₁n₂ + n₁p₂)`. -/
def mul (a b : SignedOrbit) : SignedOrbit where
  pos := a.pos * b.pos + a.neg * b.neg
  neg := a.pos * b.neg + a.neg * b.pos

@[simp] theorem mul_pos (a b : SignedOrbit) :
    (mul a b).pos = a.pos * b.pos + a.neg * b.neg := rfl

@[simp] theorem mul_neg (a b : SignedOrbit) :
    (mul a b).neg = a.pos * b.neg + a.neg * b.pos := rfl

theorem mul_toInt (a b : SignedOrbit) :
    (mul a b).toInt = a.toInt * b.toInt := by
  show ((a.pos * b.pos + a.neg * b.neg).toNat : ℤ) -
      ((a.pos * b.neg + a.neg * b.pos).toNat : ℤ) =
    ((a.pos.toNat : ℤ) - (a.neg.toNat : ℤ)) *
    ((b.pos.toNat : ℤ) - (b.neg.toNat : ℤ))
  rw [DistinctionNat.toNat_add, DistinctionNat.toNat_add,
      DistinctionNat.toNat_mul, DistinctionNat.toNat_mul,
      DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
  push_cast
  ring

/-- Subtraction on signed orbits via the negation. -/
def sub (a b : SignedOrbit) : SignedOrbit :=
  add a (negate b)

theorem sub_toInt (a b : SignedOrbit) :
    (sub a b).toInt = a.toInt - b.toInt := by
  show (add a (negate b)).toInt = a.toInt - b.toInt
  rw [add_toInt, negate_toInt]
  ring

/-- Scale a signed orbit by a (positive-only) orbit position. -/
def scaleByNat (z : SignedOrbit) (d : DistinctionNat) : SignedOrbit where
  pos := z.pos * d
  neg := z.neg * d

@[simp] theorem scaleByNat_pos (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).pos = z.pos * d := rfl

@[simp] theorem scaleByNat_neg (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).neg = z.neg * d := rfl

theorem scaleByNat_toInt (z : SignedOrbit) (d : DistinctionNat) :
    (z.scaleByNat d).toInt = z.toInt * (d.toNat : ℤ) := by
  show ((z.pos * d).toNat : ℤ) - ((z.neg * d).toNat : ℤ) =
    ((z.pos.toNat : ℤ) - (z.neg.toNat : ℤ)) * (d.toNat : ℤ)
  rw [DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
  push_cast
  ring

/-! ### K4.9. Balanced-length equivalence -/

/-- K4.9. Two signed orbits are equivalent when their orbit lengths balance:
`a.pos + b.neg = b.pos + a.neg`. This is the internal PRC integer relation,
defined entirely on δ-orbit positions. -/
def balanced (a b : SignedOrbit) : Prop :=
  a.pos + b.neg = b.pos + a.neg

instance instDecidableBalanced (a b : SignedOrbit) :
    Decidable (balanced a b) := by
  unfold balanced
  infer_instance

/-- K4.9. Characterization of balanced length by Nat-level addition. -/
theorem balanced_iff_toNat_eq (a b : SignedOrbit) :
    balanced a b ↔
      a.pos.toNat + b.neg.toNat = b.pos.toNat + a.neg.toNat := by
  unfold balanced
  constructor
  · intro h
    have := congrArg DistinctionNat.toNat h
    rwa [DistinctionNat.toNat_add, DistinctionNat.toNat_add] at this
  · intro h
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_add, DistinctionNat.toNat_add]
    exact h

/-- K4.9. The balanced characterization agrees with the verifier integer
display. This is the bridge from the internal PRC relation to the
conservative `ℤ` view. -/
theorem balanced_iff_toInt_eq (a b : SignedOrbit) :
    balanced a b ↔ a.toInt = b.toInt := by
  rw [balanced_iff_toNat_eq]
  unfold SignedOrbit.toInt
  -- choice-free: split the iff into two implications, omega each direction
  -- (omega on a bare iff goal pulls Classical.choice; per-direction it does not)
  constructor
  · intro h; omega
  · intro h; omega

theorem balanced_refl (a : SignedOrbit) : balanced a a := by
  unfold balanced
  rw [DistinctionNat.add_comm]

theorem balanced_symm {a b : SignedOrbit} (h : balanced a b) :
    balanced b a := by
  unfold balanced at *
  exact h.symm

theorem balanced_trans {a b c : SignedOrbit}
    (hab : balanced a b) (hbc : balanced b c) : balanced a c := by
  rw [balanced_iff_toNat_eq] at hab hbc ⊢
  omega

theorem balanced_equivalence : Equivalence balanced := {
  refl := balanced_refl
  symm := balanced_symm
  trans := balanced_trans
}

/-! ### K4.13. Signed-orbit order and absolute value -/

/-- Internal nonnegativity: a signed orbit balances with a positive orbit. -/
def nonneg (z : SignedOrbit) : Prop :=
  ∃ k : DistinctionNat, SignedOrbit.balanced z (SignedOrbit.ofOrbit k)

/-- Computable nonnegative flag from structural comparison of the two sides. -/
def nonnegFlag (z : SignedOrbit) : Bool :=
  DistinctionNat.leq z.neg z.pos

/-- Strict negativity as failure of the structural nonnegative flag. -/
def negativeFlag (z : SignedOrbit) : Bool :=
  !z.nonnegFlag

/-- Internal signed-orbit order: `a ≤ b` when `b - a` is nonnegative. -/
def le (a b : SignedOrbit) : Prop :=
  nonneg (SignedOrbit.sub b a)

/-- Internal strict order: nonnegative difference with nonzero difference. -/
def lt (a b : SignedOrbit) : Prop :=
  le a b ∧ ¬ SignedOrbit.balanced a b

/-- Absolute value of a signed orbit as an orbit position. -/
def abs (z : SignedOrbit) : DistinctionNat :=
  DistinctionNat.absDiff z.pos z.neg

theorem nonnegFlag_eq_true_iff (z : SignedOrbit) :
    z.nonnegFlag = true ↔ 0 ≤ z.toInt := by
  unfold nonnegFlag SignedOrbit.toInt
  rw [DistinctionNat.leq_eq_true_iff]
  constructor
  · intro h; omega
  · intro h; omega

theorem nonnegFlag_eq_false_iff (z : SignedOrbit) :
    z.nonnegFlag = false ↔ z.toInt < 0 := by
  rw [← Bool.not_eq_true, nonnegFlag_eq_true_iff]
  constructor
  · intro h; omega
  · intro h; omega

/-- Internal nonnegativity agrees with the verifier integer display. -/
theorem nonneg_iff_toInt_nonneg (z : SignedOrbit) :
    nonneg z ↔ 0 ≤ z.toInt := by
  constructor
  · intro h
    rcases h with ⟨k, hk⟩
    have hdisplay := (SignedOrbit.balanced_iff_toInt_eq z (SignedOrbit.ofOrbit k)).mp hk
    rw [SignedOrbit.ofOrbit_toInt] at hdisplay
    omega
  · intro hz
    refine ⟨DistinctionNat.ofNat z.toInt.toNat, ?_⟩
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.ofOrbit_toInt,
      DistinctionNat.toNat_ofNat]
    omega

/-- The structural nonnegative flag is equivalent to internal nonnegativity. -/
theorem nonnegFlag_eq_true_iff_nonneg (z : SignedOrbit) :
    z.nonnegFlag = true ↔ nonneg z := by
  rw [nonnegFlag_eq_true_iff, nonneg_iff_toInt_nonneg]

theorem negativeFlag_eq_true_iff_toInt_neg (z : SignedOrbit) :
    z.negativeFlag = true ↔ z.toInt < 0 := by
  unfold negativeFlag
  by_cases h : z.nonnegFlag = true
  · rw [h]
    simp
    rw [nonnegFlag_eq_true_iff] at h
    omega
  · have hf : z.nonnegFlag = false := by
      cases hflag : z.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact h hflag
    rw [hf]
    simp
    exact (nonnegFlag_eq_false_iff z).mp hf

/-- Verifier display of internal absolute value. -/
theorem abs_toNat (z : SignedOrbit) :
    z.abs.toNat = Int.natAbs z.toInt := by
  unfold abs SignedOrbit.toInt
  exact DistinctionNat.toNat_absDiff z.pos z.neg

theorem abs_eq_zero_iff_toInt_eq_zero (z : SignedOrbit) :
    z.abs = DistinctionNat.zero ↔ z.toInt = 0 := by
  constructor
  · intro h
    have hnat : z.abs.toNat = 0 := by
      rw [h, DistinctionNat.toNat_zero]
    rw [abs_toNat] at hnat
    exact Int.natAbs_eq_zero.mp hnat
  · intro h
    apply DistinctionNat.toNat_inj
    rw [abs_toNat, h, Int.natAbs_zero, DistinctionNat.toNat_zero]

theorem abs_ne_zero_of_toInt_ne_zero {z : SignedOrbit}
    (h : z.toInt ≠ 0) :
    z.abs ≠ DistinctionNat.zero := by
  intro hz
  exact h ((abs_eq_zero_iff_toInt_eq_zero z).mp hz)

theorem abs_ne_zero_of_not_balanced_zero {z : SignedOrbit}
    (h : ¬ SignedOrbit.balanced z SignedOrbit.zero) :
    z.abs ≠ DistinctionNat.zero := by
  apply abs_ne_zero_of_toInt_ne_zero
  intro hz
  exact h ((SignedOrbit.balanced_iff_toInt_eq z SignedOrbit.zero).mpr (by
    rw [hz, SignedOrbit.zero_toInt]))

theorem le_iff_toInt_le (a b : SignedOrbit) :
    le a b ↔ a.toInt ≤ b.toInt := by
  unfold le
  rw [nonneg_iff_toInt_nonneg, SignedOrbit.sub_toInt]
  constructor <;> intro h <;> omega

theorem lt_iff_toInt_lt (a b : SignedOrbit) :
    lt a b ↔ a.toInt < b.toInt := by
  unfold lt
  rw [le_iff_toInt_le, SignedOrbit.balanced_iff_toInt_eq]
  exact ⟨fun h => by omega, fun h => ⟨by omega, by omega⟩⟩

end SignedOrbit

/-- K4.9. Signed-orbit equivalence is the balanced-length relation. -/
def signedOrbitEquiv (a b : SignedOrbit) : Prop :=
  SignedOrbit.balanced a b

theorem signedOrbitEquiv_equivalence :
    Equivalence signedOrbitEquiv :=
  SignedOrbit.balanced_equivalence

theorem signedOrbitEquiv_iff_toInt_eq (a b : SignedOrbit) :
    signedOrbitEquiv a b ↔ a.toInt = b.toInt :=
  SignedOrbit.balanced_iff_toInt_eq a b

/-- K4.8. Setoid for quotient-native PRC integers. -/
def signedOrbitSetoid : Setoid SignedOrbit where
  r := signedOrbitEquiv
  iseqv := signedOrbitEquiv_equivalence

/-- K4.8. PRC integers as signed-orbit quotient classes. The quotient is
taken by the internal balanced-length relation; the verifier display into
`ℤ` is a downstream theorem. -/
def PRCInt : Type :=
  Quot signedOrbitSetoid

namespace PRCInt

/-- K4.8. Constructor from a signed orbit display. -/
def mk (z : SignedOrbit) : PRCInt :=
  Quot.mk signedOrbitSetoid z

/-- K4.8/A5. Conservative verifier display of a PRC integer as `ℤ`. -/
def toInt : PRCInt → ℤ :=
  Quot.lift SignedOrbit.toInt (by
    intro a b h
    exact (signedOrbitEquiv_iff_toInt_eq a b).mp h)

@[simp] theorem toInt_mk (z : SignedOrbit) :
    toInt (mk z) = z.toInt := by
  rfl

/-- K4.8. The zero PRC integer. -/
def zero : PRCInt :=
  mk SignedOrbit.zero

@[simp] theorem zero_toInt :
    zero.toInt = 0 := by
  rfl

/-- K4.8. The unit PRC integer. -/
def one : PRCInt :=
  mk SignedOrbit.one

@[simp] theorem one_toInt :
    one.toInt = 1 := by
  rfl

/-- K4.8. Equal balanced signed orbits determine equal PRC integers. -/
theorem mk_eq_mk_of_balanced {a b : SignedOrbit}
    (h : SignedOrbit.balanced a b) :
    mk a = mk b :=
  Quot.sound h

/-! ### PRCInt operations -/

/-- Addition respects balanced equivalence. -/
private theorem add_respects_balanced {a₁ a₂ b₁ b₂ : SignedOrbit}
    (ha : SignedOrbit.balanced a₁ a₂) (hb : SignedOrbit.balanced b₁ b₂) :
    SignedOrbit.balanced (SignedOrbit.add a₁ b₁) (SignedOrbit.add a₂ b₂) := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.add_toInt, SignedOrbit.add_toInt, ha, hb]

/-- K4.8. Addition on PRC integers, lifted from signed-orbit addition. -/
def add : PRCInt → PRCInt → PRCInt :=
  Quot.lift₂
    (fun a b => mk (SignedOrbit.add a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      exact add_respects_balanced (SignedOrbit.balanced_refl a) h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      exact add_respects_balanced h (SignedOrbit.balanced_refl b))

@[simp] theorem add_mk (a b : SignedOrbit) :
    add (mk a) (mk b) = mk (SignedOrbit.add a b) := by
  rfl

@[simp] theorem toInt_add (a b : PRCInt) :
    (add a b).toInt = a.toInt + b.toInt := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show (SignedOrbit.add a b).toInt = a.toInt + b.toInt
  exact SignedOrbit.add_toInt a b

/-- Negation respects balanced equivalence. -/
private theorem negate_respects_balanced {a₁ a₂ : SignedOrbit}
    (h : SignedOrbit.balanced a₁ a₂) :
    SignedOrbit.balanced (SignedOrbit.negate a₁) (SignedOrbit.negate a₂) := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.negate_toInt, SignedOrbit.negate_toInt, h]

/-- K4.8. Negation on PRC integers, lifted from signed-orbit swap. -/
def negate : PRCInt → PRCInt :=
  Quot.lift
    (fun a => mk (SignedOrbit.negate a))
    (by
      intro a b h
      apply Quot.sound
      exact negate_respects_balanced h)

@[simp] theorem negate_mk (a : SignedOrbit) :
    negate (mk a) = mk (SignedOrbit.negate a) := by
  rfl

@[simp] theorem toInt_negate (a : PRCInt) :
    (negate a).toInt = -a.toInt := by
  refine Quot.induction_on a (fun a => ?_)
  show (SignedOrbit.negate a).toInt = -a.toInt
  exact SignedOrbit.negate_toInt a

/-- K4.8. The toInt display is injective: distinct PRC integers have
distinct verifier displays. -/
theorem toInt_injective : Function.Injective toInt := by
  intro a b h
  induction a using Quot.ind with
  | _ a =>
    induction b using Quot.ind with
    | _ b =>
      apply Quot.sound
      exact (signedOrbitEquiv_iff_toInt_eq a b).mpr h

/-- Multiplication respects balanced equivalence. -/
private theorem mul_respects_balanced {a₁ a₂ b₁ b₂ : SignedOrbit}
    (ha : SignedOrbit.balanced a₁ a₂) (hb : SignedOrbit.balanced b₁ b₂) :
    SignedOrbit.balanced (SignedOrbit.mul a₁ b₁) (SignedOrbit.mul a₂ b₂) := by
  rw [SignedOrbit.balanced_iff_toInt_eq] at *
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt, ha, hb]

/-- K4.8. Multiplication on PRC integers, lifted from signed-orbit
multiplication. -/
def mul : PRCInt → PRCInt → PRCInt :=
  Quot.lift₂
    (fun a b => mk (SignedOrbit.mul a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      exact mul_respects_balanced (SignedOrbit.balanced_refl a) h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      exact mul_respects_balanced h (SignedOrbit.balanced_refl b))

@[simp] theorem mul_mk (a b : SignedOrbit) :
    mul (mk a) (mk b) = mk (SignedOrbit.mul a b) := by
  rfl

@[simp] theorem toInt_mul (a b : PRCInt) :
    (mul a b).toInt = a.toInt * b.toInt := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show (SignedOrbit.mul a b).toInt = a.toInt * b.toInt
  exact SignedOrbit.mul_toInt a b

/-- K4.8. Subtraction on PRC integers as add ∘ negate. -/
def sub (a b : PRCInt) : PRCInt :=
  add a (negate b)

@[simp] theorem toInt_sub (a b : PRCInt) :
    (sub a b).toInt = a.toInt - b.toInt := by
  show (add a (negate b)).toInt = a.toInt - b.toInt
  rw [toInt_add, toInt_negate]
  ring

/-! ### Ring axioms on PRC integers -/

theorem add_comm (a b : PRCInt) : add a b = add b a := by
  apply toInt_injective
  simp [Int.add_comm]

theorem add_assoc (a b c : PRCInt) :
    add (add a b) c = add a (add b c) := by
  apply toInt_injective
  simp [Int.add_assoc]

theorem zero_add (a : PRCInt) : add zero a = a := by
  apply toInt_injective
  simp

theorem add_zero (a : PRCInt) : add a zero = a := by
  apply toInt_injective
  simp

theorem add_negate (a : PRCInt) : add a (negate a) = zero := by
  apply toInt_injective
  simp

theorem negate_add (a : PRCInt) : add (negate a) a = zero := by
  apply toInt_injective
  simp

theorem mul_comm (a b : PRCInt) : mul a b = mul b a := by
  apply toInt_injective
  simp [Int.mul_comm]

theorem mul_assoc (a b c : PRCInt) :
    mul (mul a b) c = mul a (mul b c) := by
  apply toInt_injective
  simp [Int.mul_assoc]

theorem one_mul (a : PRCInt) : mul one a = a := by
  apply toInt_injective
  simp

theorem mul_one (a : PRCInt) : mul a one = a := by
  apply toInt_injective
  simp

theorem zero_mul (a : PRCInt) : mul zero a = zero := by
  apply toInt_injective
  simp

theorem mul_zero (a : PRCInt) : mul a zero = zero := by
  apply toInt_injective
  simp

theorem left_distrib (a b c : PRCInt) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  apply toInt_injective
  simp [Int.mul_add]

theorem right_distrib (a b c : PRCInt) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  apply toInt_injective
  simp [Int.add_mul]

/-! ### PRCInt is isomorphic to ℤ -/

/-- Construct a PRC integer from a verifier Int by routing the positive
and negative parts through the δ-orbit. -/
def ofInt (n : ℤ) : PRCInt :=
  mk ⟨DistinctionNat.ofNat n.toNat, DistinctionNat.ofNat (-n).toNat⟩

@[simp] theorem toInt_ofInt (n : ℤ) :
    (ofInt n).toInt = n := by
  show ((DistinctionNat.ofNat n.toNat).toNat : ℤ) -
      ((DistinctionNat.ofNat (-n).toNat).toNat : ℤ) = n
  rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_ofNat]
  omega

@[simp] theorem ofInt_toInt (a : PRCInt) :
    ofInt a.toInt = a := by
  apply toInt_injective
  rw [toInt_ofInt]

/-- K4.8. The PRC integer surface is literally isomorphic to verifier `ℤ`.
The verifier `ℤ` is therefore not assumed; it is a downstream display the
PRC quotient happens to reproduce. -/
def equivInt : PRCInt ≃ ℤ where
  toFun := toInt
  invFun := ofInt
  left_inv := ofInt_toInt
  right_inv := toInt_ofInt

@[simp] theorem ofInt_add (m n : ℤ) :
    ofInt (m + n) = add (ofInt m) (ofInt n) := by
  apply toInt_injective
  simp

@[simp] theorem ofInt_mul (m n : ℤ) :
    ofInt (m * n) = mul (ofInt m) (ofInt n) := by
  apply toInt_injective
  simp

@[simp] theorem ofInt_neg (n : ℤ) :
    ofInt (-n) = negate (ofInt n) := by
  apply toInt_injective
  simp

@[simp] theorem ofInt_zero : ofInt 0 = zero := by
  apply toInt_injective
  simp

@[simp] theorem ofInt_one : ofInt 1 = one := by
  apply toInt_injective
  simp

end PRCInt

/-! ## Operation instances on PRCInt -/

namespace PRCInt

instance instZero : Zero PRCInt := ⟨zero⟩
instance instOne : One PRCInt := ⟨one⟩
instance instAdd : Add PRCInt := ⟨add⟩
instance instMul : Mul PRCInt := ⟨mul⟩
instance instNeg : Neg PRCInt := ⟨negate⟩
instance instSub : Sub PRCInt := ⟨sub⟩

@[simp] theorem add_eq (a b : PRCInt) : a + b = add a b := rfl
@[simp] theorem mul_eq (a b : PRCInt) : a * b = mul a b := rfl
@[simp] theorem neg_eq (a : PRCInt) : -a = negate a := rfl
@[simp] theorem sub_eq (a b : PRCInt) : a - b = sub a b := rfl
@[simp] theorem zero_eq : (0 : PRCInt) = zero := rfl
@[simp] theorem one_eq : (1 : PRCInt) = one := rfl

/-- K4.8. The toInt display is a ring homomorphism (additive). -/
theorem toInt_add' (a b : PRCInt) :
    (a + b).toInt = a.toInt + b.toInt := by
  simp

/-- K4.8. The toInt display is a ring homomorphism (multiplicative). -/
theorem toInt_mul' (a b : PRCInt) :
    (a * b).toInt = a.toInt * b.toInt := by
  simp

/-- K4.8. The toInt display preserves negation. -/
theorem toInt_neg' (a : PRCInt) :
    (-a).toInt = -a.toInt := by
  simp

/-- K4.8. The toInt display preserves zero. -/
theorem toInt_zero' : (0 : PRCInt).toInt = 0 := by
  simp

/-- K4.8. The toInt display preserves one. -/
theorem toInt_one' : (1 : PRCInt).toInt = 1 := by
  simp

end PRCInt

/-! ## Ratio orbits and cross-multiplication -/

/-- K4.7. A rational orbit display: integer numerator over nonzero orbit
denominator. -/
structure RatioOrbit where
  num : SignedOrbit
  den : DistinctionNat
  den_ne_zero : den ≠ DistinctionNat.zero

namespace RatioOrbit

/-- The denominator's verifier Nat is nonzero. -/
theorem den_toNat_ne_zero (q : RatioOrbit) :
    q.den.toNat ≠ 0 := by
  intro h
  have hden : DistinctionNat.ofNat q.den.toNat = DistinctionNat.ofNat 0 := by
    rw [h]
  rw [DistinctionNat.ofNat_toNat, DistinctionNat.ofNat_zero] at hden
  exact q.den_ne_zero hden

/-- A verifier display of a ratio orbit as a rational number.
Spec tag A5: this is a transport wrapper. The internal characterization
is cross-multiplication. -/
def toRat (q : RatioOrbit) : ℚ :=
  (q.num.toInt : ℚ) / (q.den.toNat : ℚ)

/-- The denominator used by `toRat` is nonzero in the verifier rationals. -/
theorem den_cast_ne_zero (q : RatioOrbit) :
    (q.den.toNat : ℚ) ≠ 0 := by
  exact_mod_cast q.den_toNat_ne_zero

/-! ### Ratio-orbit arithmetic -/

/-- K4.11. Zero ratio orbit. -/
def zero : RatioOrbit where
  num := SignedOrbit.zero
  den := DistinctionNat.succ DistinctionNat.zero
  den_ne_zero := by
    intro h
    exact DistinctionNat.zero_ne_succ DistinctionNat.zero h.symm

@[simp] theorem zero_toRat :
    zero.toRat = 0 := by
  unfold zero toRat
  simp

/-- K4.11. Unit ratio orbit. -/
def one : RatioOrbit where
  num := SignedOrbit.one
  den := DistinctionNat.succ DistinctionNat.zero
  den_ne_zero := by
    intro h
    exact DistinctionNat.zero_ne_succ DistinctionNat.zero h.symm

@[simp] theorem one_toRat :
    one.toRat = 1 := by
  unfold one toRat
  simp

/-- K4.11. Addition of ratio orbits:
`a/b + c/d = (ad + cb)/(bd)`. -/
def add (a b : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.add (a.num.scaleByNat b.den) (b.num.scaleByNat a.den)
  den := a.den * b.den
  den_ne_zero := DistinctionNat.mul_ne_zero a.den_ne_zero b.den_ne_zero

theorem add_toRat (a b : RatioOrbit) :
    (add a b).toRat = a.toRat + b.toRat := by
  unfold add toRat
  rw [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
      SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul]
  have hA : (a.den.toNat : ℚ) ≠ 0 := a.den_cast_ne_zero
  have hB : (b.den.toNat : ℚ) ≠ 0 := b.den_cast_ne_zero
  field_simp [hA, hB]
  push_cast
  ring_nf

/-- K4.11. Negation of ratio orbits. -/
def negate (a : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.negate a.num
  den := a.den
  den_ne_zero := a.den_ne_zero

theorem negate_toRat (a : RatioOrbit) :
    (negate a).toRat = -a.toRat := by
  unfold negate toRat
  rw [SignedOrbit.negate_toInt]
  have hA : (a.den.toNat : ℚ) ≠ 0 := a.den_cast_ne_zero
  field_simp [hA]
  push_cast
  ring_nf

/-- K4.11. Subtraction of ratio orbits. -/
def sub (a b : RatioOrbit) : RatioOrbit :=
  add a (negate b)

theorem sub_toRat (a b : RatioOrbit) :
    (sub a b).toRat = a.toRat - b.toRat := by
  unfold sub
  rw [add_toRat, negate_toRat]
  ring

/-- K4.11. Multiplication of ratio orbits:
`a/b * c/d = (ac)/(bd)`. -/
def mul (a b : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.mul a.num b.num
  den := a.den * b.den
  den_ne_zero := DistinctionNat.mul_ne_zero a.den_ne_zero b.den_ne_zero

theorem mul_toRat (a b : RatioOrbit) :
    (mul a b).toRat = a.toRat * b.toRat := by
  unfold mul toRat
  rw [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul]
  have hA : (a.den.toNat : ℚ) ≠ 0 := a.den_cast_ne_zero
  have hB : (b.den.toNat : ℚ) ≠ 0 := b.den_cast_ne_zero
  field_simp [hA, hB]
  push_cast
  ring_nf

/-- K4.12. Reciprocal of a nonzero ratio orbit.

The numerator sign is selected by the structural signed-orbit comparison
`nonnegFlag`, and the denominator is the internal signed-orbit absolute value.
The verifier integer display is used only in the transport theorem below. -/
def recipNonzero (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) : RatioOrbit where
  num :=
    if a.num.nonnegFlag then
      SignedOrbit.ofOrbit a.den
    else
      SignedOrbit.negate (SignedOrbit.ofOrbit a.den)
  den := a.num.abs
  den_ne_zero := SignedOrbit.abs_ne_zero_of_not_balanced_zero h

theorem recipNonzero_toRat (a : RatioOrbit)
    (h : ¬ SignedOrbit.balanced a.num SignedOrbit.zero) :
    (recipNonzero a h).toRat = (a.toRat)⁻¹ := by
  unfold recipNonzero toRat
  have hDen : (a.den.toNat : ℚ) ≠ 0 := a.den_cast_ne_zero
  have hNumInt : a.num.toInt ≠ 0 := by
    intro hz
    exact h ((SignedOrbit.balanced_iff_toInt_eq a.num SignedOrbit.zero).mpr (by
      rw [hz, SignedOrbit.zero_toInt]))
  have hNum : (a.num.toInt : ℚ) ≠ 0 := by exact_mod_cast hNumInt
  by_cases hflag : a.num.nonnegFlag = true
  · have hnonneg : 0 ≤ a.num.toInt :=
      (SignedOrbit.nonnegFlag_eq_true_iff a.num).mp hflag
    have hpos : 0 < a.num.toInt := by omega
    simp [hflag, SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_toNat]
    have habs : |(a.num.toInt : ℚ)| = (a.num.toInt : ℚ) := by
      exact abs_of_pos (by exact_mod_cast hpos)
    rw [habs]
  · have hflagFalse : a.num.nonnegFlag = false := by
      cases hflag' : a.num.nonnegFlag with
      | false => rfl
      | true =>
          exfalso
          exact hflag hflag'
    have hneg : a.num.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff a.num).mp hflagFalse
    simp [hflagFalse, SignedOrbit.ofOrbit_toInt, SignedOrbit.negate_toInt,
      SignedOrbit.abs_toNat]
    have habs : |(a.num.toInt : ℚ)| = -(a.num.toInt : ℚ) := by
      exact abs_of_neg (by exact_mod_cast hneg)
    rw [habs]
    field_simp [hDen, hNum]

/-- K4.12. Total reciprocal of ratio orbits, sending zero to zero as in `ℚ`. -/
def recip (a : RatioOrbit) : RatioOrbit :=
  if h : SignedOrbit.balanced a.num SignedOrbit.zero then
    zero
  else
    recipNonzero a h

theorem recip_toRat (a : RatioOrbit) :
    (recip a).toRat = (a.toRat)⁻¹ := by
  unfold recip
  by_cases h : SignedOrbit.balanced a.num SignedOrbit.zero
  · have hzero := (SignedOrbit.balanced_iff_toInt_eq a.num SignedOrbit.zero).mp h
    simp [h, hzero, toRat, zero]
  · simp [h, recipNonzero_toRat]

/-! ### K4.10. Cross-multiplication equivalence -/

/-- K4.10. Two ratio orbits are equivalent under cross-multiplication when
`a.num · b.den` balances `b.num · a.den` as signed orbits. This is the
internal PRC rational relation, defined entirely on δ-orbit positions. -/
def crossEq (a b : RatioOrbit) : Prop :=
  SignedOrbit.balanced (a.num.scaleByNat b.den) (b.num.scaleByNat a.den)

/-- K4.10. Cross-multiplication agrees with rational equality of the
verifier displays. -/
theorem crossEq_iff_toRat_eq (a b : RatioOrbit) :
    crossEq a b ↔ a.toRat = b.toRat := by
  unfold crossEq toRat
  rw [SignedOrbit.balanced_iff_toInt_eq]
  rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
  have hA : (a.den.toNat : ℚ) ≠ 0 := a.den_cast_ne_zero
  have hB : (b.den.toNat : ℚ) ≠ 0 := b.den_cast_ne_zero
  constructor
  · intro h
    field_simp
    have hQ : (a.num.toInt : ℚ) * (b.den.toNat : ℚ) =
        (b.num.toInt : ℚ) * (a.den.toNat : ℚ) := by exact_mod_cast h
    linarith
  · intro h
    have : (a.num.toInt : ℚ) * (b.den.toNat : ℚ) =
        (b.num.toInt : ℚ) * (a.den.toNat : ℚ) := by
      field_simp at h
      linarith
    have hZ : (a.num.toInt * b.den.toNat : ℤ) =
        (b.num.toInt * a.den.toNat : ℤ) := by exact_mod_cast this
    exact hZ

/-- K4.10. Choice-free integer-level characterization of cross-multiplication:
`crossEq a b` holds iff the integer cross products agree. Unlike the ℚ-display
bridge `crossEq_iff_toRat_eq` (which routes through Mathlib's rational field and
so consumes `Classical.choice`), this stays in ℤ and depends only on
`{propext, Quot.sound}`. It is the choice-free hub the PRC-rational operations
prove respect-of-equivalence through. -/
theorem crossEq_iff_toIntCross (a b : RatioOrbit) :
    crossEq a b ↔
      a.num.toInt * (b.den.toNat : ℤ) = b.num.toInt * (a.den.toNat : ℤ) := by
  unfold crossEq
  rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.scaleByNat_toInt,
      SignedOrbit.scaleByNat_toInt]

theorem crossEq_refl (a : RatioOrbit) : crossEq a a := by
  unfold crossEq
  exact SignedOrbit.balanced_refl _

theorem crossEq_symm {a b : RatioOrbit} (h : crossEq a b) : crossEq b a := by
  unfold crossEq at *
  exact SignedOrbit.balanced_symm h

theorem crossEq_trans {a b c : RatioOrbit}
    (hab : crossEq a b) (hbc : crossEq b c) : crossEq a c := by
  -- choice-free: route through the integer bridge, cancel the (nonzero) middle
  -- denominator with the Int-specific lemma, close the polynomial identity with
  -- linear_combination. (The ℚ-display route uses Classical.choice.)
  rw [crossEq_iff_toIntCross] at hab hbc ⊢
  have hdb : (b.den.toNat : ℤ) ≠ 0 := by have := b.den_toNat_ne_zero; omega
  apply Int.eq_of_mul_eq_mul_right hdb
  linear_combination (c.den.toNat : ℤ) * hab + (a.den.toNat : ℤ) * hbc

theorem crossEq_equivalence : Equivalence crossEq := {
  refl := crossEq_refl
  symm := crossEq_symm
  trans := crossEq_trans
}

end RatioOrbit

/-- K4.8. Ratio-orbit equivalence is cross-multiplication. -/
def ratioOrbitEquiv (a b : RatioOrbit) : Prop :=
  RatioOrbit.crossEq a b

theorem ratioOrbitEquiv_equivalence :
    Equivalence ratioOrbitEquiv :=
  RatioOrbit.crossEq_equivalence

theorem ratioOrbitEquiv_iff_toRat_eq (a b : RatioOrbit) :
    ratioOrbitEquiv a b ↔ a.toRat = b.toRat :=
  RatioOrbit.crossEq_iff_toRat_eq a b

/-- K4.8. Setoid for quotient-native PRC rationals. -/
def ratioOrbitSetoid : Setoid RatioOrbit where
  r := ratioOrbitEquiv
  iseqv := ratioOrbitEquiv_equivalence

/-- K4.8. PRC rationals as nonzero-denominator ratio-orbit quotient classes,
identified by cross-multiplication of orbit-level numerator and denominator. -/
def PRCRat : Type :=
  Quot ratioOrbitSetoid

namespace PRCRat

/-- K4.8. Constructor from a ratio orbit display. -/
def mk (q : RatioOrbit) : PRCRat :=
  Quot.mk ratioOrbitSetoid q

/-- K4.8/A5. Conservative verifier display of a PRC rational as `ℚ`. -/
def toRat : PRCRat → ℚ :=
  Quot.lift RatioOrbit.toRat (by
    intro a b h
    exact (ratioOrbitEquiv_iff_toRat_eq a b).mp h)

@[simp] theorem toRat_mk (q : RatioOrbit) :
    toRat (mk q) = q.toRat := by
  rfl

/-- K4.8. Equal cross-multiplied ratio orbits determine equal PRC rationals. -/
theorem mk_eq_mk_of_crossEq {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    mk a = mk b :=
  Quot.sound h

/-- K4.8. The toRat display is injective on the quotient. -/
theorem toRat_injective : Function.Injective toRat := by
  intro a b h
  induction a using Quot.ind with
  | _ a =>
    induction b using Quot.ind with
    | _ b =>
      apply Quot.sound
      exact (ratioOrbitEquiv_iff_toRat_eq a b).mpr h

/-! ### PRCRat operations -/

/-- K4.11. Zero PRC rational. -/
def zero : PRCRat :=
  mk RatioOrbit.zero

@[simp] theorem zero_toRat :
    zero.toRat = 0 := by
  exact RatioOrbit.zero_toRat

/-- K4.11. Unit PRC rational. -/
def one : PRCRat :=
  mk RatioOrbit.one

@[simp] theorem one_toRat :
    one.toRat = 1 := by
  exact RatioOrbit.one_toRat

private theorem add_respects_cross {a₁ a₂ b₁ b₂ : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂) (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.add a₁ b₁) (RatioOrbit.add a₂ b₂) := by
  rw [RatioOrbit.crossEq_iff_toIntCross] at ha hb ⊢
  unfold RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul]
  push_cast
  linear_combination (b₁.den.toNat : ℤ) * (b₂.den.toNat : ℤ) * ha
    + (a₁.den.toNat : ℤ) * (a₂.den.toNat : ℤ) * hb

/-- K4.11. Addition on PRC rationals, lifted from ratio-orbit addition. -/
def add : PRCRat → PRCRat → PRCRat :=
  Quot.lift₂
    (fun a b => mk (RatioOrbit.add a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      exact add_respects_cross (RatioOrbit.crossEq_refl a) h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      exact add_respects_cross h (RatioOrbit.crossEq_refl b))

@[simp] theorem add_mk (a b : RatioOrbit) :
    add (mk a) (mk b) = mk (RatioOrbit.add a b) := by
  rfl

@[simp] theorem toRat_add (a b : PRCRat) :
    (add a b).toRat = a.toRat + b.toRat := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show (RatioOrbit.add a b).toRat = a.toRat + b.toRat
  exact RatioOrbit.add_toRat a b

private theorem negate_respects_cross {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (RatioOrbit.negate a) (RatioOrbit.negate b) := by
  rw [RatioOrbit.crossEq_iff_toIntCross] at h ⊢
  unfold RatioOrbit.negate
  simp only [SignedOrbit.negate_toInt]
  linear_combination -h

/-- K4.11. Negation on PRC rationals. -/
def negate : PRCRat → PRCRat :=
  Quot.lift
    (fun a => mk (RatioOrbit.negate a))
    (by
      intro a b h
      apply Quot.sound
      exact negate_respects_cross h)

@[simp] theorem negate_mk (a : RatioOrbit) :
    negate (mk a) = mk (RatioOrbit.negate a) := by
  rfl

@[simp] theorem toRat_negate (a : PRCRat) :
    (negate a).toRat = -a.toRat := by
  refine Quot.induction_on a (fun a => ?_)
  show (RatioOrbit.negate a).toRat = -a.toRat
  exact RatioOrbit.negate_toRat a

/-- K4.11. Subtraction on PRC rationals. -/
def sub (a b : PRCRat) : PRCRat :=
  add a (negate b)

@[simp] theorem toRat_sub (a b : PRCRat) :
    (sub a b).toRat = a.toRat - b.toRat := by
  show (add a (negate b)).toRat = a.toRat - b.toRat
  rw [toRat_add, toRat_negate]
  ring

private theorem mul_respects_cross {a₁ a₂ b₁ b₂ : RatioOrbit}
    (ha : RatioOrbit.crossEq a₁ a₂) (hb : RatioOrbit.crossEq b₁ b₂) :
    RatioOrbit.crossEq (RatioOrbit.mul a₁ b₁) (RatioOrbit.mul a₂ b₂) := by
  rw [RatioOrbit.crossEq_iff_toIntCross] at ha hb ⊢
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul]
  push_cast
  linear_combination (b₁.num.toInt * (b₂.den.toNat : ℤ)) * ha
    + (a₂.num.toInt * (a₁.den.toNat : ℤ)) * hb

/-- K4.11. Multiplication on PRC rationals, lifted from ratio-orbit multiplication. -/
def mul : PRCRat → PRCRat → PRCRat :=
  Quot.lift₂
    (fun a b => mk (RatioOrbit.mul a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      exact mul_respects_cross (RatioOrbit.crossEq_refl a) h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      exact mul_respects_cross h (RatioOrbit.crossEq_refl b))

@[simp] theorem mul_mk (a b : RatioOrbit) :
    mul (mk a) (mk b) = mk (RatioOrbit.mul a b) := by
  rfl

@[simp] theorem toRat_mul (a b : PRCRat) :
    (mul a b).toRat = a.toRat * b.toRat := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show (RatioOrbit.mul a b).toRat = a.toRat * b.toRat
  exact RatioOrbit.mul_toRat a b

private theorem recip_respects_cross {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (RatioOrbit.recip a) (RatioOrbit.recip b) := by
  -- Choice-free: route through the integer cross-multiplication hub,
  -- never through the classical ℚ display.
  rw [RatioOrbit.crossEq_iff_toIntCross] at h
  have hda : 0 < (a.den.toNat : ℤ) := by
    have := a.den_toNat_ne_zero
    omega
  have hdb : 0 < (b.den.toNat : ℤ) := by
    have := b.den_toNat_ne_zero
    omega
  by_cases hza : SignedOrbit.balanced a.num SignedOrbit.zero
  · -- Zero numerators propagate across crossEq; both reciprocals are zero.
    have hza' : a.num.toInt = 0 := by
      have h0 := (SignedOrbit.balanced_iff_toInt_eq a.num SignedOrbit.zero).mp hza
      rwa [SignedOrbit.zero_toInt] at h0
    have hzb' : b.num.toInt = 0 := by
      have h0 : b.num.toInt * (a.den.toNat : ℤ) = 0 := by
        rw [← h, hza', Int.zero_mul]
      have hda' : (a.den.toNat : ℤ) ≠ 0 := by omega
      have h1 : b.num.toInt * (a.den.toNat : ℤ) = 0 * (a.den.toNat : ℤ) := by
        rw [h0, Int.zero_mul]
      exact Int.eq_of_mul_eq_mul_right hda' h1
    have hzb : SignedOrbit.balanced b.num SignedOrbit.zero := by
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hzb'
    unfold RatioOrbit.recip
    rw [dif_pos hza, dif_pos hzb]
    exact RatioOrbit.crossEq_refl RatioOrbit.zero
  · -- Nonzero numerators: signs must agree across the cross-equality.
    have hna : a.num.toInt ≠ 0 := by
      intro hz
      apply hza
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
      exact hz
    have hnb : b.num.toInt ≠ 0 := by
      intro hz
      apply hna
      have h0 : a.num.toInt * (b.den.toNat : ℤ) = 0 := by
        rw [h, hz, Int.zero_mul]
      have hdb' : (b.den.toNat : ℤ) ≠ 0 := by omega
      have h1 : a.num.toInt * (b.den.toNat : ℤ) = 0 * (b.den.toNat : ℤ) := by
        rw [h0, Int.zero_mul]
      exact Int.eq_of_mul_eq_mul_right hdb' h1
    have hzb : ¬ SignedOrbit.balanced b.num SignedOrbit.zero := by
      intro hb
      apply hnb
      have h0 := (SignedOrbit.balanced_iff_toInt_eq b.num SignedOrbit.zero).mp hb
      rwa [SignedOrbit.zero_toInt] at h0
    unfold RatioOrbit.recip
    rw [dif_neg hza, dif_neg hzb]
    rw [RatioOrbit.crossEq_iff_toIntCross]
    simp only [RatioOrbit.recipNonzero]
    by_cases hfa : a.num.nonnegFlag = true
    · have hpa : 0 < a.num.toInt := by
        have := (SignedOrbit.nonnegFlag_eq_true_iff a.num).mp hfa
        omega
      by_cases hfb : b.num.nonnegFlag = true
      · -- Both positive: cross identity is the hypothesis, transposed.
        have hpb : 0 < b.num.toInt := by
          have := (SignedOrbit.nonnegFlag_eq_true_iff b.num).mp hfb
          omega
        rw [if_pos hfa, if_pos hfb, SignedOrbit.ofOrbit_toInt,
            SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_toNat,
            SignedOrbit.abs_toNat]
        have haa : ((a.num.toInt.natAbs : ℕ) : ℤ) = a.num.toInt := by omega
        have hbb : ((b.num.toInt.natAbs : ℕ) : ℤ) = b.num.toInt := by omega
        rw [haa, hbb]
        linear_combination -h
      · -- a positive, b negative: contradicts crossEq.
        exfalso
        have hfb' : b.num.nonnegFlag = false := by
          cases hv : b.num.nonnegFlag with
          | false => rfl
          | true => exact absurd hv hfb
        have hqb : b.num.toInt < 0 :=
          (SignedOrbit.nonnegFlag_eq_false_iff b.num).mp hfb'
        have h1 : (0 : ℤ) < a.num.toInt * (b.den.toNat : ℤ) := Int.mul_pos hpa hdb
        have h2 : (0 : ℤ) < (-b.num.toInt) * (a.den.toNat : ℤ) :=
          Int.mul_pos (by omega) hda
        have h3 : (-b.num.toInt) * (a.den.toNat : ℤ) =
            -(b.num.toInt * (a.den.toNat : ℤ)) := by ring
        rw [h] at h1
        omega
    · have hfa' : a.num.nonnegFlag = false := by
        cases hv : a.num.nonnegFlag with
        | false => rfl
        | true => exact absurd hv hfa
      have hqa : a.num.toInt < 0 :=
        (SignedOrbit.nonnegFlag_eq_false_iff a.num).mp hfa'
      by_cases hfb : b.num.nonnegFlag = true
      · -- a negative, b positive: contradicts crossEq.
        exfalso
        have hpb : 0 < b.num.toInt := by
          have := (SignedOrbit.nonnegFlag_eq_true_iff b.num).mp hfb
          omega
        have h1 : (0 : ℤ) < (-a.num.toInt) * (b.den.toNat : ℤ) :=
          Int.mul_pos (by omega) hdb
        have h1' : (-a.num.toInt) * (b.den.toNat : ℤ) =
            -(a.num.toInt * (b.den.toNat : ℤ)) := by ring
        have h2 : (0 : ℤ) < b.num.toInt * (a.den.toNat : ℤ) := Int.mul_pos hpb hda
        rw [h] at h1'
        omega
      · -- Both negative: signs cancel, cross identity again the hypothesis.
        have hfb' : b.num.nonnegFlag = false := by
          cases hv : b.num.nonnegFlag with
          | false => rfl
          | true => exact absurd hv hfb
        have hqb : b.num.toInt < 0 :=
          (SignedOrbit.nonnegFlag_eq_false_iff b.num).mp hfb'
        rw [if_neg hfa, if_neg hfb, SignedOrbit.negate_toInt,
            SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt,
            SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_toNat,
            SignedOrbit.abs_toNat]
        have haa : ((a.num.toInt.natAbs : ℕ) : ℤ) = -a.num.toInt := by omega
        have hbb : ((b.num.toInt.natAbs : ℕ) : ℤ) = -b.num.toInt := by omega
        rw [haa, hbb]
        linear_combination -h

/-- K4.12. Total reciprocal on PRC rationals, lifted from ratio-orbit
reciprocal and sending zero to zero. -/
def recip : PRCRat → PRCRat :=
  Quot.lift
    (fun a => mk (RatioOrbit.recip a))
    (by
      intro a b h
      apply Quot.sound
      exact recip_respects_cross h)

@[simp] theorem recip_mk (a : RatioOrbit) :
    recip (mk a) = mk (RatioOrbit.recip a) := by
  rfl

@[simp] theorem toRat_recip (a : PRCRat) :
    (recip a).toRat = (a.toRat)⁻¹ := by
  refine Quot.induction_on a (fun a => ?_)
  show (RatioOrbit.recip a).toRat = (a.toRat)⁻¹
  exact RatioOrbit.recip_toRat a

/-! ### PRCRat field-style laws, proved choice-free through the integer
cross-multiplication hub

Each law is proved directly on the quotient: `Quot.induction_on` exposes
representatives, `mk_eq_mk_of_crossEq` (a `Quot.sound` wrapper) reduces the
goal to `RatioOrbit.crossEq`, and `crossEq_iff_toIntCross` turns that into an
integer polynomial identity closed by `ring`. None of these proofs routes
through the classical `ℚ` display (`toRat`), so the laws stay on the
`{propext, Quot.sound}` axiom basis. -/

private theorem zero_num_toInt : (RatioOrbit.zero).num.toInt = 0 :=
  SignedOrbit.zero_toInt

private theorem zero_den_toNat : (RatioOrbit.zero).den.toNat = 1 := by
  show (DistinctionNat.succ DistinctionNat.zero).toNat = 1
  rw [DistinctionNat.toNat_succ, DistinctionNat.toNat_zero]

private theorem one_num_toInt : (RatioOrbit.one).num.toInt = 1 :=
  SignedOrbit.one_toInt

private theorem one_den_toNat : (RatioOrbit.one).den.toNat = 1 := by
  show (DistinctionNat.succ DistinctionNat.zero).toNat = 1
  rw [DistinctionNat.toNat_succ, DistinctionNat.toNat_zero]

/-- K4.8. Choice-free structural zero test: a PRC rational is in the zero
class iff its representative's numerator balances the zero signed orbit.
Well-definedness routes through the integer cross-multiplication hub (no `ℚ`
display), so the definition depends only on `{propext, Quot.sound}`. -/
def isZero : PRCRat → Prop :=
  Quot.lift
    (fun q => SignedOrbit.balanced q.num SignedOrbit.zero)
    (by
      intro a b h
      have h' := (RatioOrbit.crossEq_iff_toIntCross a b).mp h
      have hda : (a.den.toNat : ℤ) ≠ 0 := by
        have := a.den_toNat_ne_zero
        omega
      have hdb : (b.den.toNat : ℤ) ≠ 0 := by
        have := b.den_toNat_ne_zero
        omega
      apply propext
      show SignedOrbit.balanced a.num SignedOrbit.zero
          ↔ SignedOrbit.balanced b.num SignedOrbit.zero
      rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.balanced_iff_toInt_eq,
          SignedOrbit.zero_toInt]
      constructor
      · intro ha0
        have h0 : b.num.toInt * (a.den.toNat : ℤ) = 0 * (a.den.toNat : ℤ) := by
          rw [← h', ha0, Int.zero_mul, Int.zero_mul]
        exact Int.eq_of_mul_eq_mul_right hda h0
      · intro hb0
        have h0 : a.num.toInt * (b.den.toNat : ℤ) = 0 * (b.den.toNat : ℤ) := by
          rw [h', hb0, Int.zero_mul, Int.zero_mul]
        exact Int.eq_of_mul_eq_mul_right hdb h0)

@[simp] theorem isZero_mk (q : RatioOrbit) :
    isZero (mk q) ↔ SignedOrbit.balanced q.num SignedOrbit.zero :=
  Iff.rfl

theorem isZero_zero : isZero zero :=
  SignedOrbit.balanced_refl SignedOrbit.zero

theorem not_isZero_one : ¬ isZero one := by
  intro h1
  have h2 := (SignedOrbit.balanced_iff_toInt_eq
    SignedOrbit.one SignedOrbit.zero).mp h1
  rw [SignedOrbit.one_toInt, SignedOrbit.zero_toInt] at h2
  omega

/-- K4.8. Structural nontriviality: the zero and one classes are distinct.
Proved by the choice-free `isZero` discriminator (no `ℚ` display). -/
theorem zero_ne_one : (zero : PRCRat) ≠ one := by
  intro h
  exact not_isZero_one (h ▸ isZero_zero)

theorem add_comm (a b : PRCRat) : add a b = add b a := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show mk (RatioOrbit.add a b) = mk (RatioOrbit.add b a)
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
    DistinctionNat.toNat_mul]
  push_cast
  ring

theorem add_assoc (a b c : PRCRat) :
    add (add a b) c = add a (add b c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  show mk (RatioOrbit.add (RatioOrbit.add a b) c)
      = mk (RatioOrbit.add a (RatioOrbit.add b c))
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
    DistinctionNat.toNat_mul]
  push_cast
  ring

theorem zero_add (a : PRCRat) : add zero a = a := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.add RatioOrbit.zero a) = mk a
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
    DistinctionNat.toNat_mul, zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem add_zero (a : PRCRat) : add a zero = a := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.add a RatioOrbit.zero) = mk a
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
    DistinctionNat.toNat_mul, zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem add_negate (a : PRCRat) : add a (negate a) = zero := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.add a (RatioOrbit.negate a)) = mk RatioOrbit.zero
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add RatioOrbit.negate
  simp only [SignedOrbit.add_toInt, SignedOrbit.negate_toInt,
    SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul,
    zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem negate_add (a : PRCRat) : add (negate a) a = zero := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.add (RatioOrbit.negate a) a) = mk RatioOrbit.zero
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.add RatioOrbit.negate
  simp only [SignedOrbit.add_toInt, SignedOrbit.negate_toInt,
    SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul,
    zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem mul_comm (a b : PRCRat) : mul a b = mul b a := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  show mk (RatioOrbit.mul a b) = mk (RatioOrbit.mul b a)
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul]
  push_cast
  ring

theorem mul_assoc (a b c : PRCRat) :
    mul (mul a b) c = mul a (mul b c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  show mk (RatioOrbit.mul (RatioOrbit.mul a b) c)
      = mk (RatioOrbit.mul a (RatioOrbit.mul b c))
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul]
  push_cast
  ring

theorem one_mul (a : PRCRat) : mul one a = a := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.mul RatioOrbit.one a) = mk a
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul,
    one_num_toInt, one_den_toNat]
  push_cast
  ring

theorem mul_one (a : PRCRat) : mul a one = a := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.mul a RatioOrbit.one) = mk a
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul,
    one_num_toInt, one_den_toNat]
  push_cast
  ring

theorem zero_mul (a : PRCRat) : mul zero a = zero := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.mul RatioOrbit.zero a) = mk RatioOrbit.zero
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul,
    zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem mul_zero (a : PRCRat) : mul a zero = zero := by
  refine Quot.induction_on a (fun a => ?_)
  show mk (RatioOrbit.mul a RatioOrbit.zero) = mk RatioOrbit.zero
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul
  simp only [SignedOrbit.mul_toInt, DistinctionNat.toNat_mul,
    zero_num_toInt, zero_den_toNat]
  push_cast
  ring

theorem left_distrib (a b c : PRCRat) :
    mul a (add b c) = add (mul a b) (mul a c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  show mk (RatioOrbit.mul a (RatioOrbit.add b c))
      = mk (RatioOrbit.add (RatioOrbit.mul a b) (RatioOrbit.mul a c))
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.mul_toInt,
    SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul]
  push_cast
  ring

theorem right_distrib (a b c : PRCRat) :
    mul (add a b) c = add (mul a c) (mul b c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  show mk (RatioOrbit.mul (RatioOrbit.add a b) c)
      = mk (RatioOrbit.add (RatioOrbit.mul a c) (RatioOrbit.mul b c))
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul RatioOrbit.add
  simp only [SignedOrbit.add_toInt, SignedOrbit.mul_toInt,
    SignedOrbit.scaleByNat_toInt, DistinctionNat.toNat_mul]
  push_cast
  ring

/-- K4.12. Structural reciprocal cancellation: any PRC rational outside the
zero class satisfies `a * a⁻¹ = 1`. The nonzero hypothesis is the structural
disequality `a ≠ zero` (not the `ℚ` display), so both the statement and the
proof are choice-free. -/
theorem mul_recip_cancel₀ {a : PRCRat} (h : a ≠ zero) :
    mul a (recip a) = one := by
  revert h
  refine Quot.induction_on a (fun q => ?_)
  intro h
  -- The structural hypothesis descends to the representative: a balanced
  -- (zero) numerator would place the class in the zero class.
  have hz : ¬ SignedOrbit.balanced q.num SignedOrbit.zero := by
    intro hb
    apply h
    show mk q = mk RatioOrbit.zero
    apply mk_eq_mk_of_crossEq
    rw [RatioOrbit.crossEq_iff_toIntCross]
    have h0 : q.num.toInt = 0 := by
      have h1 := (SignedOrbit.balanced_iff_toInt_eq
        q.num SignedOrbit.zero).mp hb
      rwa [SignedOrbit.zero_toInt] at h1
    rw [h0, zero_num_toInt, Int.zero_mul, Int.zero_mul]
  have hne : q.num.toInt ≠ 0 := by
    intro h0
    apply hz
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
    exact h0
  show mk (RatioOrbit.mul q (RatioOrbit.recip q)) = mk RatioOrbit.one
  apply mk_eq_mk_of_crossEq
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold RatioOrbit.mul RatioOrbit.recip
  rw [dif_neg hz]
  simp only [RatioOrbit.recipNonzero, SignedOrbit.mul_toInt,
    DistinctionNat.toNat_mul, one_num_toInt, one_den_toNat]
  by_cases hf : q.num.nonnegFlag = true
  · -- Positive numerator: the reciprocal numerator is the promoted denominator.
    have hpos : 0 < q.num.toInt := by
      have := (SignedOrbit.nonnegFlag_eq_true_iff q.num).mp hf
      omega
    rw [if_pos hf, SignedOrbit.ofOrbit_toInt]
    push_cast
    have haa : ((q.num.abs.toNat : ℕ) : ℤ) = q.num.toInt := by
      rw [SignedOrbit.abs_toNat]
      omega
    rw [haa]
    ring
  · -- Negative numerator: the reciprocal numerator is the negated denominator.
    have hf' : q.num.nonnegFlag = false := by
      cases hv : q.num.nonnegFlag with
      | false => rfl
      | true => exact absurd hv hf
    have hneg : q.num.toInt < 0 :=
      (SignedOrbit.nonnegFlag_eq_false_iff q.num).mp hf'
    rw [if_neg hf, SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt]
    push_cast
    have haa : ((q.num.abs.toNat : ℕ) : ℤ) = -q.num.toInt := by
      rw [SignedOrbit.abs_toNat]
      omega
    rw [haa]
    ring

/-- K4.12. Structural reciprocal cancellation, inverse side. -/
theorem recip_mul_cancel₀ {a : PRCRat} (h : a ≠ zero) :
    mul (recip a) a = one := by
  rw [mul_comm]
  exact mul_recip_cancel₀ h

/-- K4.12. The reciprocal fixes the zero class (the `ℚ` convention
`0⁻¹ = 0`), proved structurally: the zero representative's numerator
balances the zero orbit, so `RatioOrbit.recip` takes its zero branch. -/
theorem recip_zero : recip zero = zero := by
  show mk (RatioOrbit.recip RatioOrbit.zero) = mk RatioOrbit.zero
  have h : SignedOrbit.balanced (RatioOrbit.zero).num SignedOrbit.zero :=
    SignedOrbit.balanced_refl SignedOrbit.zero
  unfold RatioOrbit.recip
  rw [dif_pos h]

/-- K4.12. Display-form reciprocal cancellation, kept for `ℚ`-facing API
compatibility. The statement mentions `toRat`, so it is intrinsically
display-bound; the structural content is `mul_recip_cancel₀`. -/
theorem mul_recip_cancel {a : PRCRat} (h : a.toRat ≠ 0) :
    mul a (recip a) = one := by
  apply mul_recip_cancel₀
  intro hz
  apply h
  rw [hz, zero_toRat]

/-! ### Operation instances on PRCRat -/

instance instZero : Zero PRCRat := ⟨zero⟩
instance instOne : One PRCRat := ⟨one⟩
instance instAdd : Add PRCRat := ⟨add⟩
instance instMul : Mul PRCRat := ⟨mul⟩
instance instNeg : Neg PRCRat := ⟨negate⟩
instance instSub : Sub PRCRat := ⟨sub⟩
instance instInv : Inv PRCRat := ⟨recip⟩

@[simp] theorem add_eq (a b : PRCRat) : a + b = add a b := rfl
@[simp] theorem mul_eq (a b : PRCRat) : a * b = mul a b := rfl
@[simp] theorem neg_eq (a : PRCRat) : -a = negate a := rfl
@[simp] theorem sub_eq (a b : PRCRat) : a - b = sub a b := rfl
@[simp] theorem inv_eq (a : PRCRat) : a⁻¹ = recip a := rfl
@[simp] theorem zero_eq : (0 : PRCRat) = zero := rfl
@[simp] theorem one_eq : (1 : PRCRat) = one := rfl

theorem toRat_add' (a b : PRCRat) :
    (a + b).toRat = a.toRat + b.toRat := by
  simp

theorem toRat_mul' (a b : PRCRat) :
    (a * b).toRat = a.toRat * b.toRat := by
  simp

theorem toRat_neg' (a : PRCRat) :
    (-a).toRat = -a.toRat := by
  simp

theorem toRat_inv' (a : PRCRat) :
    (a⁻¹).toRat = (a.toRat)⁻¹ := by
  simp

end PRCRat

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
