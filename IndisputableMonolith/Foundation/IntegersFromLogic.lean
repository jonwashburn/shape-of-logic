/-
  IntegersFromLogic.lean

  Recovery of the integers from `LogicNat`, by Grothendieck completion.

  An integer is a formal difference `a - b` with `a, b : LogicNat`,
  modulo the equivalence `(a, b) ~ (c, d) ↔ a + d = c + b`. This is
  the universal additive group containing `LogicNat` as a sub-monoid.
  In Lean we realize the construction as a quotient of
  `LogicNat × LogicNat`.

  The recovery chain extends:

    Law of Logic (Foundation.LogicAsFunctionalEquation)
      ⊢ J via Translation Theorem and Aczél
      ⊢ LogicNat via orbit structure (Foundation.ArithmeticFromLogic)
      ⊢ LogicInt via Grothendieck completion (this module)
      ⊢ ≃ Int (recovery isomorphism)

  Status: Level 1. Defines the carrier, ring operations (+, -, *, neg),
  proves a small number of key identities (associativity, additive
  identity, additive inverse), and states the equivalence with `Int`
  at the carrier level. A full ring isomorphism (every Mathlib ring
  axiom) is left for a follow-up; the structural recovery is what this
  module establishes.
-/

import Mathlib
import IndisputableMonolith.Foundation.ArithmeticFromLogic

namespace IndisputableMonolith
namespace Foundation
namespace IntegersFromLogic

open ArithmeticFromLogic ArithmeticFromLogic.LogicNat

/-! ## 1. The Grothendieck Equivalence -/

/-- The Grothendieck equivalence relation on pairs of `LogicNat`:
`(a, b) ~ (c, d)` iff `a + d = c + b`. The pair `(a, b)` represents
the formal difference `a - b`. -/
def intRel : (LogicNat × LogicNat) → (LogicNat × LogicNat) → Prop :=
  fun p q => p.1 + q.2 = q.1 + p.2

theorem intRel_refl : ∀ p : LogicNat × LogicNat, intRel p p := by
  intro p
  show p.1 + p.2 = p.1 + p.2
  rfl

theorem intRel_symm : ∀ {p q : LogicNat × LogicNat}, intRel p q → intRel q p := by
  intro p q h
  show q.1 + p.2 = p.1 + q.2
  exact h.symm

theorem intRel_trans : ∀ {p q r : LogicNat × LogicNat},
    intRel p q → intRel q r → intRel p r := by
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ hpq hqr
  show a + f = e + b
  rw [eq_iff_toNat_eq, toNat_add, toNat_add]
  have hpq' : toNat a + toNat d = toNat c + toNat b := by
    have := congrArg toNat (show a + d = c + b from hpq)
    rwa [toNat_add, toNat_add] at this
  have hqr' : toNat c + toNat f = toNat e + toNat d := by
    have := congrArg toNat (show c + f = e + d from hqr)
    rwa [toNat_add, toNat_add] at this
  omega

/-- The setoid structure on `LogicNat × LogicNat` for Grothendieck
completion. -/
instance setoid : Setoid (LogicNat × LogicNat) :=
  ⟨intRel, intRel_refl, intRel_symm, intRel_trans⟩

/-! ## 2. The Type of Logic-Native Integers -/

/-- `LogicInt` is the Grothendieck completion of `LogicNat` under
addition. -/
def LogicInt : Type := Quotient (setoid : Setoid (LogicNat × LogicNat))

namespace LogicInt

/-- Constructor: form an integer from a pair of naturals. -/
def mk (a b : LogicNat) : LogicInt := Quotient.mk' (a, b)

/-- Notation `[a, b]ₗ` for the integer `a − b`. Avoids clash with
list and matrix notations. -/
notation:max "[" a ", " b "]ₗ" => mk a b

theorem sound (a b c d : LogicNat) (h : a + d = c + b) :
    mk a b = mk c d := by
  apply Quotient.sound
  show a + d = c + b
  exact h

/-! ## 3. Embedding LogicNat into LogicInt -/

/-- The natural injection `LogicNat ↪ LogicInt` sending `n` to `[n, 0]`.
This is the inclusion of the additive monoid into its Grothendieck group. -/
def ofLogicNat (n : LogicNat) : LogicInt := mk n LogicNat.zero

@[simp] theorem ofLogicNat_zero : ofLogicNat LogicNat.zero = mk LogicNat.zero LogicNat.zero := rfl

/-! ## 4. Zero, One, Negation, Addition, Multiplication -/

/-- Zero in `LogicInt`. -/
def zero : LogicInt := mk LogicNat.zero LogicNat.zero

/-- One in `LogicInt`. -/
def one : LogicInt := mk (LogicNat.succ LogicNat.zero) LogicNat.zero

instance : Zero LogicInt := ⟨zero⟩
instance : One LogicInt := ⟨one⟩

/-- Negation: `-(a, b) = (b, a)`. -/
def neg : LogicInt → LogicInt :=
  Quotient.lift (fun (p : LogicNat × LogicNat) => mk p.2 p.1) (by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    show mk b a = mk d c
    apply sound
    show b + c = d + a
    rw [eq_iff_toNat_eq, toNat_add, toNat_add]
    have h' : toNat a + toNat d = toNat c + toNat b := by
      have := congrArg toNat (show a + d = c + b from h)
      rwa [toNat_add, toNat_add] at this
    omega)

instance : Neg LogicInt := ⟨neg⟩

/-- Addition: `(a, b) + (c, d) = (a + c, b + d)`. -/
def add : LogicInt → LogicInt → LogicInt :=
  Quotient.lift₂
    (fun (p q : LogicNat × LogicNat) => mk (p.1 + q.1) (p.2 + q.2))
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ hab hcd
      show mk (a + c) (b + d) = mk (a' + c') (b' + d')
      apply sound
      show (a + c) + (b' + d') = (a' + c') + (b + d)
      rw [eq_iff_toNat_eq, toNat_add, toNat_add, toNat_add, toNat_add, toNat_add, toNat_add]
      have hab_nat : toNat a + toNat b' = toNat a' + toNat b := by
        have := congrArg toNat (show a + b' = a' + b from hab)
        rwa [toNat_add, toNat_add] at this
      have hcd_nat : toNat c + toNat d' = toNat c' + toNat d := by
        have := congrArg toNat (show c + d' = c' + d from hcd)
        rwa [toNat_add, toNat_add] at this
      omega)

instance : Add LogicInt := ⟨add⟩

/-- Multiplication: `(a, b) * (c, d) = (ac + bd, ad + bc)`. -/
def mul : LogicInt → LogicInt → LogicInt :=
  Quotient.lift₂
    (fun (p q : LogicNat × LogicNat) =>
       mk (p.1 * q.1 + p.2 * q.2) (p.1 * q.2 + p.2 * q.1))
    (by
      rintro ⟨a, b⟩ ⟨c, d⟩ ⟨a', b'⟩ ⟨c', d'⟩ hab hcd
      show mk (a * c + b * d) (a * d + b * c) = mk (a' * c' + b' * d') (a' * d' + b' * c')
      apply sound
      show (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c)
      rw [eq_iff_toNat_eq]
      simp only [toNat_add, toNat_mul]
      have hab_nat : toNat a + toNat b' = toNat a' + toNat b := by
        have := congrArg toNat (show a + b' = a' + b from hab)
        rwa [toNat_add, toNat_add] at this
      have hcd_nat : toNat c + toNat d' = toNat c' + toNat d := by
        have := congrArg toNat (show c + d' = c' + d from hcd)
        rwa [toNat_add, toNat_add] at this
      -- The Nat goal is a polynomial identity that follows from hab_nat and hcd_nat.
      nlinarith [hab_nat, hcd_nat, sq_nonneg ((toNat a : Int) - toNat a'),
                 Nat.zero_le (toNat a), Nat.zero_le (toNat b),
                 Nat.zero_le (toNat c), Nat.zero_le (toNat d),
                 Nat.zero_le (toNat a'), Nat.zero_le (toNat b'),
                 Nat.zero_le (toNat c'), Nat.zero_le (toNat d')])

instance : Mul LogicInt := ⟨mul⟩

/-! ## 5. Recovery Theorem: LogicInt ≃ Int -/

/-- Map a pair `(a, b) : LogicNat × LogicNat` to `a - b : Int` via the
underlying `Nat` representation. Well-defined on the quotient because
`a + d = c + b` implies `(a : Int) - b = (c : Int) - d`. -/
def toIntCore : LogicNat × LogicNat → Int :=
  fun p => (toNat p.1 : Int) - (toNat p.2 : Int)

theorem toIntCore_respects :
    ∀ p q : LogicNat × LogicNat, p ≈ q → toIntCore p = toIntCore q := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  -- h : a + d = c + b
  show (toNat a : Int) - toNat b = (toNat c : Int) - toNat d
  have hcast := congrArg toNat h
  rw [toNat_add, toNat_add] at hcast
  -- toNat a + toNat d = toNat c + toNat b in Nat.
  -- In Int: (toNat a) + (toNat d) = (toNat c) + (toNat b), so subtract to get the goal.
  have : (toNat a : Int) + toNat d = (toNat c : Int) + toNat b := by exact_mod_cast hcast
  linarith

/-- The recovery map `LogicInt → Int`. -/
def toInt : LogicInt → Int := Quotient.lift toIntCore toIntCore_respects

/-- The inverse `Int → LogicInt`. Maps non-negative `n ≥ 0` to `[n, 0]`
and negative `-n < 0` to `[0, n]`. -/
def fromInt : Int → LogicInt
  | Int.ofNat n   => mk (LogicNat.fromNat n) LogicNat.zero
  | Int.negSucc n => mk LogicNat.zero (LogicNat.fromNat (Nat.succ n))

@[simp] theorem toInt_mk (a b : LogicNat) :
    toInt (mk a b) = (toNat a : Int) - toNat b := rfl

theorem toInt_fromInt : ∀ n : Int, toInt (fromInt n) = n := by
  intro n
  cases n with
  | ofNat n =>
    show toInt (mk (LogicNat.fromNat n) LogicNat.zero) = (Int.ofNat n)
    rw [toInt_mk, toNat_fromNat, toNat_zero]
    simp [Int.ofNat]
  | negSucc n =>
    show toInt (mk LogicNat.zero (LogicNat.fromNat (Nat.succ n))) = Int.negSucc n
    rw [toInt_mk, toNat_zero, toNat_fromNat]
    simp [Int.negSucc_eq]

theorem fromInt_toInt : ∀ z : LogicInt, fromInt (toInt z) = z := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show fromInt (toInt (mk a b)) = mk a b
    rw [toInt_mk]
    -- (toNat a : Int) - toNat b. Case on sign.
    by_cases h : toNat b ≤ toNat a
    · -- Non-negative case
      have hge : (0 : Int) ≤ (toNat a : Int) - toNat b := by
        have : (toNat b : Int) ≤ toNat a := by exact_mod_cast h
        linarith
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hge
      rw [hk]
      show fromInt (Int.ofNat k) = mk a b
      show mk (LogicNat.fromNat k) LogicNat.zero = mk a b
      apply sound
      -- LogicNat.fromNat k + b = a + 0 = a in LogicNat.
      -- We have: (toNat a : Int) - toNat b = k as Int, so toNat a = toNat b + k in Nat.
      have hknat : (k : Int) = (toNat a : Int) - toNat b := hk.symm
      have hknat' : toNat a = toNat b + k := by
        have : (toNat a : Int) = toNat b + k := by linarith
        exact_mod_cast this
      show LogicNat.fromNat k + b = a + LogicNat.zero
      rw [LogicNat.add_zero]
      have hcast := congrArg fromNat hknat'
      rw [LogicNat.fromNat_toNat] at hcast
      -- hcast : a = fromNat (toNat b + k)
      -- We need: fromNat k + b = a
      have : LogicNat.fromNat (toNat b + k) = LogicNat.fromNat (toNat b) + LogicNat.fromNat k := by
        -- fromNat is an additive homomorphism. Prove directly.
        have hh : toNat (LogicNat.fromNat (toNat b) + LogicNat.fromNat k)
                  = toNat b + k := by
          rw [LogicNat.toNat_add, LogicNat.toNat_fromNat, LogicNat.toNat_fromNat]
        have := congrArg LogicNat.fromNat hh
        rw [LogicNat.fromNat_toNat] at this
        exact this.symm
      rw [hcast, this, LogicNat.fromNat_toNat, LogicNat.add_comm]
    · -- Negative case
      push_neg at h
      have hlt : (toNat a : Int) < toNat b := by exact_mod_cast h
      have hltz : (toNat a : Int) - toNat b < 0 := by linarith
      have hsub_pos : 0 < toNat b - toNat a := Nat.sub_pos_of_lt h
      -- (toNat a : Int) - toNat b = -(toNat b - toNat a) and is Int.negSucc of (toNat b - toNat a - 1).
      set m := toNat b - toNat a - 1 with hm_def
      have hsucc : Nat.succ m = toNat b - toNat a := by
        rw [hm_def]
        omega
      have heq : (toNat a : Int) - toNat b = Int.negSucc m := by
        rw [Int.negSucc_eq]
        have h1 : ((Nat.succ m : Int)) = (toNat b - toNat a : Int) := by
          rw [hsucc]
          push_cast
          omega
        push_cast at h1
        linarith
      rw [heq]
      show fromInt (Int.negSucc m) = mk a b
      show mk LogicNat.zero (LogicNat.fromNat (Nat.succ m)) = mk a b
      apply sound
      -- Want: 0 + b = a + fromNat (succ m), i.e. b = a + fromNat (succ m).
      show LogicNat.zero + b = a + LogicNat.fromNat (Nat.succ m)
      rw [LogicNat.zero_add]
      -- toNat b = toNat a + Nat.succ m by hsucc.
      have hbnat : toNat b = toNat a + Nat.succ m := by
        rw [hsucc]; omega
      have hcast := congrArg LogicNat.fromNat hbnat
      rw [LogicNat.fromNat_toNat] at hcast
      have hadd_morph : LogicNat.fromNat (toNat a + Nat.succ m)
                        = LogicNat.fromNat (toNat a) + LogicNat.fromNat (Nat.succ m) := by
        have hh : toNat (LogicNat.fromNat (toNat a) + LogicNat.fromNat (Nat.succ m))
                  = toNat a + Nat.succ m := by
          rw [LogicNat.toNat_add, LogicNat.toNat_fromNat, LogicNat.toNat_fromNat]
        have := congrArg LogicNat.fromNat hh
        rw [LogicNat.fromNat_toNat] at this
        exact this.symm
      rw [hcast, hadd_morph, LogicNat.fromNat_toNat]

/-- **Recovery theorem (carrier)**: `LogicInt` and `Int` are in
bijection via `toInt` and `fromInt`. -/
def equivInt : LogicInt ≃ Int where
  toFun := toInt
  invFun := fromInt
  left_inv := fromInt_toInt
  right_inv := toInt_fromInt

/-! ## 6. Ring-Homomorphism Properties of `toInt`

The maps `toInt` and `fromInt` extend to a ring isomorphism
`LogicInt ≃+* Int`. We prove the homomorphism theorems on the
operations and use them, plus a transfer principle, to derive the
full ring structure on `LogicInt`. -/

theorem toInt_zero : toInt (0 : LogicInt) = 0 := by
  show toInt (mk LogicNat.zero LogicNat.zero) = 0
  rw [toInt_mk]
  simp [toNat_zero]

theorem toInt_one : toInt (1 : LogicInt) = 1 := by
  show toInt (mk (LogicNat.succ LogicNat.zero) LogicNat.zero) = 1
  rw [toInt_mk, toNat_succ, toNat_zero]
  norm_num

theorem toInt_add (a b : LogicInt) : toInt (a + b) = toInt a + toInt b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      show toInt (mk (a + c) (b + d)) = toInt (mk a b) + toInt (mk c d)
      rw [toInt_mk, toInt_mk, toInt_mk]
      rw [toNat_add, toNat_add]
      push_cast
      ring

theorem toInt_neg (a : LogicInt) : toInt (-a) = -toInt a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨a, b⟩
    show toInt (mk b a) = -toInt (mk a b)
    rw [toInt_mk, toInt_mk]
    ring

theorem toInt_mul (a b : LogicInt) : toInt (a * b) = toInt a * toInt b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      show toInt (mk (a * c + b * d) (a * d + b * c)) = toInt (mk a b) * toInt (mk c d)
      rw [toInt_mk, toInt_mk, toInt_mk]
      rw [toNat_add, toNat_add, toNat_mul, toNat_mul, toNat_mul, toNat_mul]
      push_cast
      ring

/-- Transfer principle: an equation in `LogicInt` holds iff it holds
under `toInt`. The workhorse for proving ring identities on
`LogicInt` by reduction to `Int`. -/
theorem eq_iff_toInt_eq {a b : LogicInt} : a = b ↔ toInt a = toInt b := by
  constructor
  · exact congrArg toInt
  · intro h
    have := congrArg fromInt h
    rw [fromInt_toInt, fromInt_toInt] at this
    exact this

/-! ## 7. Ring Axioms on `LogicInt`

By transfer through `toInt`, every ring identity on `LogicInt`
reduces to one on `Int` and is closed by `ring`. -/

theorem add_assoc' (a b c : LogicInt) : (a + b) + c = a + (b + c) := by
  rw [eq_iff_toInt_eq, toInt_add, toInt_add, toInt_add, toInt_add]; ring

theorem add_comm' (a b : LogicInt) : a + b = b + a := by
  rw [eq_iff_toInt_eq, toInt_add, toInt_add]; ring

theorem zero_add' (a : LogicInt) : (0 : LogicInt) + a = a := by
  rw [eq_iff_toInt_eq, toInt_add, toInt_zero]; ring

theorem add_zero' (a : LogicInt) : a + (0 : LogicInt) = a := by
  rw [eq_iff_toInt_eq, toInt_add, toInt_zero]; ring

theorem add_left_neg' (a : LogicInt) : -a + a = 0 := by
  rw [eq_iff_toInt_eq, toInt_add, toInt_neg, toInt_zero]; ring

theorem mul_assoc' (a b c : LogicInt) : (a * b) * c = a * (b * c) := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_mul, toInt_mul, toInt_mul]; ring

theorem mul_comm' (a b : LogicInt) : a * b = b * a := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_mul]; ring

theorem one_mul' (a : LogicInt) : (1 : LogicInt) * a = a := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_one]; ring

theorem mul_one' (a : LogicInt) : a * (1 : LogicInt) = a := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_one]; ring

theorem mul_add' (a b c : LogicInt) : a * (b + c) = a * b + a * c := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_add, toInt_add, toInt_mul, toInt_mul]; ring

theorem add_mul' (a b c : LogicInt) : (a + b) * c = a * c + b * c := by
  rw [eq_iff_toInt_eq, toInt_mul, toInt_add, toInt_add, toInt_mul, toInt_mul]; ring

/-- `LogicInt` has no zero divisors: from `a * b = 0`, either `a = 0`
or `b = 0`. Forced by the ring isomorphism with `Int`. -/
theorem mul_eq_zero {a b : LogicInt} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    have hint : toInt a * toInt b = 0 := by
      rw [← toInt_mul]
      have := congrArg toInt h
      rwa [toInt_zero] at this
    rcases Int.mul_eq_zero.mp hint with ha | hb
    · left
      rw [eq_iff_toInt_eq, toInt_zero]; exact ha
    · right
      rw [eq_iff_toInt_eq, toInt_zero]; exact hb
  · rintro (ha | hb)
    · rw [ha, eq_iff_toInt_eq, toInt_mul, toInt_zero]; ring
    · rw [hb, eq_iff_toInt_eq, toInt_mul, toInt_zero]; ring

/-- Cancellation: if `c ≠ 0` and `a * c = b * c`, then `a = b`. -/
theorem mul_right_cancel {a b c : LogicInt} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hc' : toInt c ≠ 0 := by
    intro habs
    apply hc
    rw [eq_iff_toInt_eq, toInt_zero]; exact habs
  rw [eq_iff_toInt_eq, toInt_mul, toInt_mul] at h
  rw [eq_iff_toInt_eq]
  exact Int.eq_of_mul_eq_mul_right hc' h

end LogicInt

/-! ## Summary

  Foundation.LogicAsFunctionalEquation     (Law of Logic)
        ↓
  Foundation.ArithmeticFromLogic           (LogicNat ≃ Nat)
        ↓
  Foundation.IntegersFromLogic (this)      (LogicInt ≃ Int)

The Grothendieck completion of `LogicNat` recovers the integers. The
construction does not assume `Int` exists; it builds the equivalence
classes and operations from `LogicNat` plus the standard quotient
machinery.

What this module establishes:
  - The Grothendieck equivalence relation and its setoid.
  - `LogicInt` as a Quotient.
  - Zero, one, negation, addition, multiplication.
  - Carrier-level equivalence with `Int`.

What is left for a follow-up:
  - Full ring axiom catalog (associativity, distributivity, etc.) on `LogicInt`.
  - Equivalence as a ring isomorphism `LogicInt ≃+* Int`.
  - Order on `LogicInt` (descended from `Int`'s order).
-/

end IntegersFromLogic
end Foundation
end IndisputableMonolith
