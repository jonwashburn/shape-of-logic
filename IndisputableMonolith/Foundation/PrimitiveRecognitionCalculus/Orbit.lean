/-
  PrimitiveRecognitionCalculus/Orbit.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K2.12, R8, K4.5

  Base-neutral arithmetic begins as the finite orbit of repeated δ. Lean's
  Nat is used here only as a verifier representation, and the equivalence is
  proved explicitly.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Basic

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K2.12. The base-neutral finite orbit of repeated distinction. -/
inductive DistinctionNat where
  | zero
  | succ : DistinctionNat → DistinctionNat
  deriving DecidableEq, Repr

namespace DistinctionNat

/-- R8. Zero is not a successor. -/
theorem zero_ne_succ (n : DistinctionNat) :
    zero ≠ succ n := by
  intro h
  cases h

/-- R8. Successor is injective. -/
theorem succ_injective :
    Function.Injective succ := by
  intro a b h
  cases h
  rfl

/-- R8. Induction over the δ-orbit. -/
theorem induction {P : DistinctionNat → Prop}
    (hzero : P zero)
    (hsucc : ∀ n : DistinctionNat, P n → P (succ n)) :
    ∀ n : DistinctionNat, P n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih => exact hsucc n ih

/-- Verifier representation of the orbit as Lean Nat. -/
def toNat : DistinctionNat → Nat
  | zero => 0
  | succ n => Nat.succ (toNat n)

/-- Build an orbit position from a verifier Nat. -/
def ofNat : Nat → DistinctionNat
  | 0 => zero
  | Nat.succ n => succ (ofNat n)

@[simp] theorem toNat_zero :
    toNat zero = 0 := by
  rfl

@[simp] theorem toNat_succ (n : DistinctionNat) :
    toNat (succ n) = Nat.succ (toNat n) := by
  rfl

@[simp] theorem ofNat_zero :
    ofNat 0 = zero := by
  rfl

@[simp] theorem ofNat_succ (n : Nat) :
    ofNat (Nat.succ n) = succ (ofNat n) := by
  rfl

/-- K4.5. Transport from Lean Nat to the δ-orbit and back is identity. -/
theorem toNat_ofNat (n : Nat) :
    toNat (ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [ofNat, ih]

/-- K4.5. Transport from the δ-orbit to Lean Nat and back is identity. -/
theorem ofNat_toNat (n : DistinctionNat) :
    ofNat (toNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [toNat, ih]

/-- K4.5. The δ-orbit is equivalent to Lean Nat as a verifier display. -/
def equivNat : DistinctionNat ≃ Nat where
  toFun := toNat
  invFun := ofNat
  left_inv := ofNat_toNat
  right_inv := toNat_ofNat

end DistinctionNat

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
