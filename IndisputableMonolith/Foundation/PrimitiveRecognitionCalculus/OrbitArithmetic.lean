/-
  PrimitiveRecognitionCalculus/OrbitArithmetic.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K4.5 (orbit arithmetic), K4.6 (balanced length), K4.7 (cross-multiplication)

  Addition and multiplication on the δ-orbit, with the transport theorems
  to Lean Nat needed for the balanced and cross-multiplication
  characterizations of `PRCInt` and `PRCRat`.

  Strength: δ-only. The construction uses only the inductive structure of
  the orbit and the verifier-level transport already established in
  `Orbit.lean`. No project-local axioms.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Orbit

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DistinctionNat

/-! ## Addition on the δ-orbit -/

/-- K4.5. Addition of orbit positions: concatenation of repetition. -/
def add : DistinctionNat → DistinctionNat → DistinctionNat
  | a, zero => a
  | a, succ b => succ (add a b)

instance : Add DistinctionNat := ⟨add⟩

theorem add_def (a b : DistinctionNat) :
    a + b = add a b := rfl

theorem add_zero_eq (a : DistinctionNat) :
    a + zero = a := rfl

theorem add_succ_eq (a b : DistinctionNat) :
    a + succ b = succ (a + b) := rfl

theorem zero_add_eq (a : DistinctionNat) :
    zero + a = a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      show succ (zero + n) = succ n
      rw [ih]

theorem succ_add_eq (a b : DistinctionNat) :
    succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ n ih =>
      show succ (succ a + n) = succ (succ (a + n))
      rw [ih]

theorem add_comm (a b : DistinctionNat) :
    a + b = b + a := by
  induction a with
  | zero =>
      rw [zero_add_eq, add_zero_eq]
  | succ n ih =>
      rw [succ_add_eq, add_succ_eq, ih]

theorem add_assoc (a b c : DistinctionNat) :
    (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ n ih =>
      show (a + b) + succ n = a + (b + succ n)
      rw [add_succ_eq, add_succ_eq, add_succ_eq, ih]

/-! ## Transport to Lean Nat -/

/-- K4.5. The verifier display of orbit addition matches Lean Nat addition. -/
theorem toNat_add (a b : DistinctionNat) :
    (a + b).toNat = a.toNat + b.toNat := by
  induction b with
  | zero =>
      rw [add_zero_eq, toNat_zero, Nat.add_zero]
  | succ n ih =>
      show (succ (a + n)).toNat = a.toNat + (succ n).toNat
      rw [toNat_succ, toNat_succ, ih]
      omega

/-- The verifier display is injective: equal Nat displays come from equal
orbit positions. -/
theorem toNat_inj {a b : DistinctionNat} (h : a.toNat = b.toNat) :
    a = b := by
  have := congrArg DistinctionNat.ofNat h
  rwa [ofNat_toNat, ofNat_toNat] at this

/-! ## Cancellation -/

/-- K4.5. Left cancellation for orbit addition. -/
theorem add_left_cancel {a b c : DistinctionNat}
    (h : a + b = a + c) : b = c := by
  apply toNat_inj
  have h' : (a + b).toNat = (a + c).toNat := by rw [h]
  rw [toNat_add, toNat_add] at h'
  exact Nat.add_left_cancel h'

/-- K4.5. Right cancellation for orbit addition. -/
theorem add_right_cancel {a b c : DistinctionNat}
    (h : a + c = b + c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

/-! ## Multiplication on the δ-orbit -/

/-- K4.7. Multiplication of orbit positions: nested repetition. -/
def mul : DistinctionNat → DistinctionNat → DistinctionNat
  | _, zero => zero
  | a, succ b => mul a b + a

instance : Mul DistinctionNat := ⟨mul⟩

theorem mul_def (a b : DistinctionNat) :
    a * b = mul a b := rfl

theorem mul_zero_eq (a : DistinctionNat) :
    a * zero = zero := rfl

theorem mul_succ_eq (a b : DistinctionNat) :
    a * succ b = a * b + a := rfl

theorem zero_mul_eq (a : DistinctionNat) :
    zero * a = zero := by
  induction a with
  | zero => rfl
  | succ n ih =>
      show zero * n + zero = zero
      rw [add_zero_eq, ih]

theorem succ_mul_eq (a b : DistinctionNat) :
    succ a * b = a * b + b := by
  induction b with
  | zero =>
      rw [mul_zero_eq, mul_zero_eq, add_zero_eq]
  | succ n ih =>
      show succ a * n + succ a = (a * n + a) + succ n
      rw [ih, add_succ_eq, add_succ_eq]
      congr 1
      rw [add_assoc, add_assoc, add_comm a n]

theorem mul_comm (a b : DistinctionNat) :
    a * b = b * a := by
  induction a with
  | zero =>
      rw [zero_mul_eq, mul_zero_eq]
  | succ n ih =>
      rw [succ_mul_eq, mul_succ_eq, ih]

/-- K4.7. The verifier display of orbit multiplication matches Lean Nat. -/
theorem toNat_mul (a b : DistinctionNat) :
    (a * b).toNat = a.toNat * b.toNat := by
  induction b with
  | zero =>
      show (a * zero).toNat = a.toNat * zero.toNat
      rw [mul_zero_eq, toNat_zero]
      omega
  | succ n ih =>
      show (a * n + a).toNat = a.toNat * (succ n).toNat
      rw [toNat_add, toNat_succ, ih, Nat.mul_succ]

/-- K4.7. Product of nonzero orbit positions is nonzero. -/
theorem mul_ne_zero {a b : DistinctionNat}
    (ha : a ≠ zero) (hb : b ≠ zero) :
    a * b ≠ zero := by
  intro h
  have hnat : (a * b).toNat = zero.toNat := by rw [h]
  rw [toNat_mul, toNat_zero] at hnat
  rcases Nat.mul_eq_zero.mp hnat with hzero | hzero
  · have : a = zero := by
      apply toNat_inj
      rw [toNat_zero]
      exact hzero
    exact ha this
  · have : b = zero := by
      apply toNat_inj
      rw [toNat_zero]
      exact hzero
    exact hb this

end DistinctionNat

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
