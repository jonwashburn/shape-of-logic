/-
  RationalsFromLogic.lean

  Recovery of the rationals from `LogicInt`, by field-of-fractions
  construction.

  A rational is a formal quotient `a/b` with `a : LogicInt`,
  `b : LogicInt`, `b ≠ 0`, modulo the equivalence
  `(a, b) ~ (c, d) ↔ a*d = c*b`. This is the field of fractions of
  the integral domain `LogicInt`.

  The recovery chain extends:

    Law of Logic
      ⊢ J
      ⊢ LogicNat ≃ Nat        (Foundation.ArithmeticFromLogic)
      ⊢ LogicInt ≃ Int        (Foundation.IntegersFromLogic)
      ⊢ LogicRat ≃ Rat        (this module)

  Status: Level 1. Defines the carrier, the equivalence relation, the
  setoid, the quotient, zero/one/negation/addition/multiplication, and
  the carrier-level equivalence with `Rat`. Field axioms (associativity
  of multiplication, distributivity, multiplicative inverse for
  non-zero elements) are mechanical extensions left for a follow-up.
-/

import Mathlib
import IndisputableMonolith.Foundation.IntegersFromLogic

namespace IndisputableMonolith
namespace Foundation
namespace RationalsFromLogic

open IntegersFromLogic IntegersFromLogic.LogicInt
open ArithmeticFromLogic ArithmeticFromLogic.LogicNat

/-! ## 1. Pre-rational structure: pairs with non-zero denominator -/

/-- A pre-rational is a pair `(num, den)` with `den ≠ 0`. -/
structure PreRat where
  num         : LogicInt
  den         : LogicInt
  den_nonzero : den ≠ 0

/-- The field-of-fractions equivalence: `(a, b) ~ (c, d)` iff
`a * d = c * b`. -/
def ratRel : PreRat → PreRat → Prop :=
  fun p q => p.num * q.den = q.num * p.den

theorem ratRel_refl : ∀ p : PreRat, ratRel p p := by
  intro p
  show p.num * p.den = p.num * p.den
  rfl

theorem ratRel_symm : ∀ {p q : PreRat}, ratRel p q → ratRel q p := by
  intro p q h
  show q.num * p.den = p.num * q.den
  exact h.symm

theorem ratRel_trans : ∀ {p q r : PreRat}, ratRel p q → ratRel q r → ratRel p r := by
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨e, f, hf⟩ hpq hqr
  -- hpq : a * d = c * b
  -- hqr : c * f = e * d
  -- goal: a * f = e * b
  -- Method: (a * f) * d = a * f * d = a * d * f = c * b * f = c * f * b = e * d * b = (e * b) * d.
  -- Cancel d ≠ 0.
  show a * f = e * b
  have key : (a * f) * d = (e * b) * d := by
    calc (a * f) * d
        = (a * d) * f := by rw [mul_assoc', mul_comm' f d, ← mul_assoc']
      _ = (c * b) * f := by rw [hpq]
      _ = (c * f) * b := by rw [mul_assoc', mul_comm' b f, ← mul_assoc']
      _ = (e * d) * b := by rw [hqr]
      _ = (e * b) * d := by rw [mul_assoc', mul_comm' d b, ← mul_assoc']
  exact mul_right_cancel hd key

instance setoid : Setoid PreRat := ⟨ratRel, ratRel_refl, ratRel_symm, ratRel_trans⟩

/-! ## 2. The Type of Logic-Native Rationals -/

/-- `LogicRat` is the field of fractions of `LogicInt`. -/
def LogicRat : Type := Quotient (setoid : Setoid PreRat)

namespace LogicRat

/-- Constructor: form a rational from a pair with non-zero denominator. -/
def mk (a b : LogicInt) (hb : b ≠ 0) : LogicRat :=
  Quotient.mk' ⟨a, b, hb⟩

theorem sound (a b c d : LogicInt) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * d = c * b) : mk a b hb = mk c d hd := by
  apply Quotient.sound
  show a * d = c * b
  exact h

/-! ## 3. Embedding LogicInt into LogicRat -/

/-- The natural injection `LogicInt ↪ LogicRat` sending `n` to `n/1`. -/
def ofLogicInt (n : LogicInt) : LogicRat :=
  mk n 1 (by
    intro h
    have : toInt (1 : LogicInt) = toInt (0 : LogicInt) := congrArg toInt h
    rw [toInt_one, toInt_zero] at this
    exact one_ne_zero this)

/-! ## 4. Zero, One, Negation, Addition, Multiplication -/

/-- Zero in `LogicRat`. -/
def zero : LogicRat :=
  mk 0 1 (by
    intro h
    have : toInt (1 : LogicInt) = toInt (0 : LogicInt) := congrArg toInt h
    rw [toInt_one, toInt_zero] at this
    exact one_ne_zero this)

/-- One in `LogicRat`. -/
def one : LogicRat :=
  mk 1 1 (by
    intro h
    have : toInt (1 : LogicInt) = toInt (0 : LogicInt) := congrArg toInt h
    rw [toInt_one, toInt_zero] at this
    exact one_ne_zero this)

instance : Zero LogicRat := ⟨zero⟩
instance : One LogicRat := ⟨one⟩

/-- Negation: `-(a/b) = (-a)/b`. -/
def neg : LogicRat → LogicRat :=
  Quotient.lift
    (fun (p : PreRat) => mk (-p.num) p.den p.den_nonzero)
    (by
      rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ h
      show mk (-a) b hb = mk (-c) d hd
      apply sound
      show -a * d = -c * b
      have h' : a * d = c * b := h
      rw [eq_iff_toInt_eq, toInt_mul, toInt_mul, toInt_neg, toInt_neg]
      have h'' : toInt a * toInt d = toInt c * toInt b := by
        have := congrArg toInt h'
        rwa [toInt_mul, toInt_mul] at this
      linarith)

instance : Neg LogicRat := ⟨neg⟩

/-- Addition: `(a/b) + (c/d) = (a*d + c*b) / (b*d)`. -/
def add : LogicRat → LogicRat → LogicRat :=
  Quotient.lift₂
    (fun (p q : PreRat) =>
       mk (p.num * q.den + q.num * p.den) (p.den * q.den)
         (fun h => p.den_nonzero ((mul_eq_zero.mp h).resolve_right q.den_nonzero)))
    (by
      rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨a', b', hb'⟩ ⟨c', d', hd'⟩ hab hcd
      show mk (a * d + c * b) (b * d) _
            = mk (a' * d' + c' * b') (b' * d') _
      apply sound
      show (a * d + c * b) * (b' * d') = (a' * d' + c' * b') * (b * d)
      rw [eq_iff_toInt_eq]
      simp only [toInt_add, toInt_mul]
      have hab' : toInt a * toInt b' = toInt a' * toInt b := by
        have := congrArg toInt hab
        rwa [toInt_mul, toInt_mul] at this
      have hcd' : toInt c * toInt d' = toInt c' * toInt d := by
        have := congrArg toInt hcd
        rwa [toInt_mul, toInt_mul] at this
      linear_combination (toInt d * toInt d') * hab' + (toInt b * toInt b') * hcd')

instance : Add LogicRat := ⟨add⟩

/-- Multiplication: `(a/b) * (c/d) = (a*c) / (b*d)`. -/
def mul : LogicRat → LogicRat → LogicRat :=
  Quotient.lift₂
    (fun (p q : PreRat) =>
       mk (p.num * q.num) (p.den * q.den)
         (fun h => p.den_nonzero ((mul_eq_zero.mp h).resolve_right q.den_nonzero)))
    (by
      rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ ⟨a', b', hb'⟩ ⟨c', d', hd'⟩ hab hcd
      show mk (a * c) (b * d) _ = mk (a' * c') (b' * d') _
      apply sound
      show a * c * (b' * d') = a' * c' * (b * d)
      rw [eq_iff_toInt_eq]
      simp only [toInt_mul]
      have hab' : toInt a * toInt b' = toInt a' * toInt b := by
        have := congrArg toInt hab
        rwa [toInt_mul, toInt_mul] at this
      have hcd' : toInt c * toInt d' = toInt c' * toInt d := by
        have := congrArg toInt hcd
        rwa [toInt_mul, toInt_mul] at this
      linear_combination (toInt c * toInt d') * hab' + (toInt a' * toInt b) * hcd')

instance : Mul LogicRat := ⟨mul⟩

/-! ## 5. Recovery Theorem: LogicRat ≃ Rat

Map a pre-rational `(a, b)` with `b ≠ 0` to the rational `(toInt a) / (toInt b)`
in `Rat`. Well-defined on the quotient because `a*d = c*b` implies the
two `Rat` values are equal. -/

/-- Map a `PreRat` to `Rat`. -/
def toRatCore : PreRat → ℚ :=
  fun p => (toInt p.num : ℚ) / (toInt p.den : ℚ)

theorem toRatCore_respects :
    ∀ p q : PreRat, p ≈ q → toRatCore p = toRatCore q := by
  rintro ⟨a, b, hb⟩ ⟨c, d, hd⟩ h
  show (toInt a : ℚ) / toInt b = (toInt c : ℚ) / toInt d
  have hb_int : (toInt b : ℚ) ≠ 0 := by
    intro habs
    apply hb
    rw [eq_iff_toInt_eq, toInt_zero]
    exact_mod_cast habs
  have hd_int : (toInt d : ℚ) ≠ 0 := by
    intro habs
    apply hd
    rw [eq_iff_toInt_eq, toInt_zero]
    exact_mod_cast habs
  have h' : toInt a * toInt d = toInt c * toInt b := by
    have := congrArg toInt (show a * d = c * b from h)
    rwa [toInt_mul, toInt_mul] at this
  rw [div_eq_div_iff hb_int hd_int]
  exact_mod_cast h'

/-- The recovery map `LogicRat → Rat`. -/
def toRat : LogicRat → ℚ := Quotient.lift toRatCore toRatCore_respects

/-- The inverse `Rat → LogicRat`. -/
noncomputable def fromRat (q : ℚ) : LogicRat :=
  let n : LogicInt := fromInt q.num
  let d : LogicInt := fromInt q.den
  mk n d (by
    intro h
    have : toInt d = toInt 0 := congrArg toInt h
    rw [toInt_zero] at this
    have : toInt (fromInt q.den) = 0 := this
    rw [toInt_fromInt] at this
    have hpos : (0 : Int) < q.den := by exact_mod_cast q.den_pos
    have : (q.den : Int) = 0 := this
    have hne : (q.den : Int) ≠ 0 := ne_of_gt hpos
    exact hne this)

@[simp] theorem toRat_mk (a b : LogicInt) (hb : b ≠ 0) :
    toRat (mk a b hb) = (toInt a : ℚ) / toInt b := rfl

theorem toRat_fromRat : ∀ q : ℚ, toRat (fromRat q) = q := by
  intro q
  show toRat (mk (fromInt q.num) (fromInt q.den) _) = q
  rw [toRat_mk, toInt_fromInt, toInt_fromInt]
  exact_mod_cast q.num_div_den

/-- The other round trip: every logic-native rational is recovered from
its image in Mathlib's `Rat`. This is the key injectivity theorem for
the transport API. -/
theorem fromRat_toRat : ∀ q : LogicRat, fromRat (toRat q) = q := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b, hb⟩
    show fromRat (toRat (mk a b hb)) = mk a b hb
    rw [toRat_mk]
    apply sound
    -- It remains to prove `fromInt ((a/b).num) * b = a * fromInt ((a/b).den)`.
    rw [eq_iff_toInt_eq, toInt_mul, toInt_mul, toInt_fromInt, toInt_fromInt]
    have hb_rat : (toInt b : ℚ) ≠ 0 := by
      intro h
      apply hb
      rw [eq_iff_toInt_eq, toInt_zero]
      exact_mod_cast h
    have hden_rat : (((toInt a : ℚ) / toInt b).den : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt ((toInt a : ℚ) / toInt b).den_pos)
    have hq :
        ((((toInt a : ℚ) / toInt b).num : ℚ) /
          (((toInt a : ℚ) / toInt b).den : ℚ))
          = (toInt a : ℚ) / toInt b := by
      exact_mod_cast ((toInt a : ℚ) / toInt b).num_div_den
    have hcross :
        (((toInt a : ℚ) / toInt b).num : ℚ) * (toInt b : ℚ)
          = (toInt a : ℚ) * (((toInt a : ℚ) / toInt b).den : ℚ) := by
      rwa [div_eq_div_iff hden_rat hb_rat] at hq
    exact_mod_cast hcross

/-- Carrier equivalence between recovered rationals and Mathlib rationals. -/
noncomputable def equivRat : LogicRat ≃ ℚ where
  toFun := toRat
  invFun := fromRat
  left_inv := fromRat_toRat
  right_inv := toRat_fromRat

/-- Transfer principle: equality of recovered rationals is equivalent to
equality after transport to Mathlib's `Rat`. -/
theorem eq_iff_toRat_eq {a b : LogicRat} : a = b ↔ toRat a = toRat b := by
  constructor
  · exact congrArg toRat
  · intro h
    have := congrArg fromRat h
    rw [fromRat_toRat, fromRat_toRat] at this
    exact this

theorem toRat_zero : toRat (0 : LogicRat) = 0 := by
  show toRat (mk 0 1 _) = 0
  rw [toRat_mk, toInt_zero, toInt_one]
  norm_num

theorem toRat_one : toRat (1 : LogicRat) = 1 := by
  show toRat (mk 1 1 _) = 1
  rw [toRat_mk, toInt_one]
  norm_num

theorem toRat_neg (a : LogicRat) : toRat (-a) = -toRat a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b, hb⟩
    show toRat (mk (-a) b hb) = -toRat (mk a b hb)
    rw [toRat_mk, toRat_mk, toInt_neg]
    have hbq : (toInt b : ℚ) ≠ 0 := by
      intro h; apply hb; rw [eq_iff_toInt_eq, toInt_zero]; exact_mod_cast h
    field_simp [hbq]
    norm_num

theorem toRat_add (a b : LogicRat) : toRat (a + b) = toRat a + toRat b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b, hb⟩
      rcases q with ⟨c, d, hd⟩
      show toRat (mk (a * d + c * b) (b * d) _) =
        toRat (mk a b hb) + toRat (mk c d hd)
      simp only [toRat_mk, toInt_add, toInt_mul]
      push_cast
      have hbq : (toInt b : ℚ) ≠ 0 := by
        intro h; apply hb; rw [eq_iff_toInt_eq, toInt_zero]; exact_mod_cast h
      have hdq : (toInt d : ℚ) ≠ 0 := by
        intro h; apply hd; rw [eq_iff_toInt_eq, toInt_zero]; exact_mod_cast h
      field_simp [hbq, hdq]

theorem toRat_mul (a b : LogicRat) : toRat (a * b) = toRat a * toRat b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b, hb⟩
      rcases q with ⟨c, d, hd⟩
      show toRat (mk (a * c) (b * d) _) =
        toRat (mk a b hb) * toRat (mk c d hd)
      simp only [toRat_mk, toInt_mul]
      push_cast
      have hbq : (toInt b : ℚ) ≠ 0 := by
        intro h; apply hb; rw [eq_iff_toInt_eq, toInt_zero]; exact_mod_cast h
      have hdq : (toInt d : ℚ) ≠ 0 := by
        intro h; apply hd; rw [eq_iff_toInt_eq, toInt_zero]; exact_mod_cast h
      field_simp [hbq, hdq]

/-! ## 6. Field identities by transport through `toRat` -/

theorem add_assoc' (a b c : LogicRat) : (a + b) + c = a + (b + c) := by
  rw [eq_iff_toRat_eq, toRat_add, toRat_add, toRat_add, toRat_add]
  ring

theorem add_comm' (a b : LogicRat) : a + b = b + a := by
  rw [eq_iff_toRat_eq, toRat_add, toRat_add]
  ring

theorem zero_add' (a : LogicRat) : (0 : LogicRat) + a = a := by
  rw [eq_iff_toRat_eq, toRat_add, toRat_zero]
  ring

theorem add_zero' (a : LogicRat) : a + (0 : LogicRat) = a := by
  rw [eq_iff_toRat_eq, toRat_add, toRat_zero]
  ring

theorem add_left_neg' (a : LogicRat) : -a + a = 0 := by
  rw [eq_iff_toRat_eq, toRat_add, toRat_neg, toRat_zero]
  ring

theorem mul_assoc' (a b c : LogicRat) : (a * b) * c = a * (b * c) := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_mul, toRat_mul, toRat_mul]
  ring

theorem mul_comm' (a b : LogicRat) : a * b = b * a := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_mul]
  ring

theorem one_mul' (a : LogicRat) : (1 : LogicRat) * a = a := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_one]
  ring

theorem mul_one' (a : LogicRat) : a * (1 : LogicRat) = a := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_one]
  ring

theorem mul_add' (a b c : LogicRat) : a * (b + c) = a * b + a * c := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul]
  ring

theorem add_mul' (a b c : LogicRat) : (a + b) * c = a * c + b * c := by
  rw [eq_iff_toRat_eq, toRat_mul, toRat_add, toRat_add, toRat_mul, toRat_mul]
  ring

end LogicRat

/-! ## Summary

  Foundation.LogicAsFunctionalEquation     (Law of Logic, four conditions on C)
        ↓
  Foundation.ArithmeticFromLogic           (LogicNat ≃ Nat)
        ↓
  Foundation.IntegersFromLogic             (LogicInt ≃ Int, ring axioms)
        ↓
  Foundation.RationalsFromLogic (this)     (LogicRat ≃ Rat carrier)

The field-of-fractions construction recovers the rationals. The
construction does not assume `Rat` exists; it builds the equivalence
classes and operations from `LogicInt` plus the standard quotient
machinery. The carrier-level equivalence is the structural recovery;
the full field axiom catalog (associativity/commutativity/distributivity
of mul, multiplicative inverse for non-zero elements) is a mechanical
extension via the `eq_iff_toRat_eq` transfer principle (mirroring
`eq_iff_toInt_eq` in the integer module).

What this module establishes:
  - The `ratRel` equivalence relation and its setoid (transitivity uses
    `mul_right_cancel` from `LogicInt` proved via the ring isomorphism).
  - `LogicRat` as a Quotient.
  - Zero, one, negation, addition, multiplication.
  - Carrier-level equivalence with `Rat` via `toRat`/`fromRat`
    (`toRat_fromRat` proved; `fromRat_toRat` left as the natural follow-on).

What is left for a follow-up:
  - `fromRat_toRat` direction of the equivalence.
  - Full field axiom catalog (multiplicative inverse, distributivity).
  - Equivalence as a field isomorphism `LogicRat ≃+*+ Rat`.
  - Order on `LogicRat` (descended from `Rat`'s order).
-/

end RationalsFromLogic
end Foundation
end IndisputableMonolith
