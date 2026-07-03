import IndisputableMonolith.Foundation.UniversalForcing

/-!
  OrderRealization.lean

  Order-theoretic realization on `ℤ` with equality cost and unit step.
  This is a lightweight realization: the forced arithmetic is carried by the
  certified internal orbit, while the carrier interpretation is the usual
  embedding of `LogicNat` into `ℤ`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace OrderRealization

open ArithmeticFromLogic

/-- Equality cost on integers. -/
def intCost (a b : ℤ) : Nat :=
  if a = b then 0 else 1

@[simp] theorem intCost_self (a : ℤ) : intCost a a = 0 := by
  simp [intCost]

theorem intCost_symm (a b : ℤ) : intCost a b = intCost b a := by
  by_cases h : a = b
  · subst h; simp [intCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [intCost, h, h']

/-- Interpret `LogicNat` as nonnegative integers. -/
def intOrbitInterpret (n : LogicNat) : ℤ :=
  (LogicNat.toNat n : ℤ)

/-- Ordered integer realization with unit step. -/
def orderRealization : LogicRealization where
  Carrier := ℤ
  Cost := Nat
  zeroCost := inferInstance
  compare := intCost
  zero := 0
  step := fun z => z + 1
  Orbit := LogicNat
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := intOrbitInterpret
  interpret_zero := by simp [intOrbitInterpret]
  interpret_step := by
    intro n
    show ((LogicNat.toNat (LogicNat.succ n) : ℤ) = (LogicNat.toNat n : ℤ) + 1)
    rw [LogicNat.toNat_succ]
    norm_num
  orbit_no_confusion := by
    intro n h
    exact LogicNat.zero_ne_succ n h
  orbit_step_injective := LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := intCost_self
  nonContradiction := intCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨1, ?_⟩
    simp [intCost]

/-- Ordered realization carries the universal forced arithmetic. -/
noncomputable def order_arithmetic_invariant (R : LogicRealization.{0, 0}) :
    (arithmeticOf orderRealization).peano.carrier ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf orderRealization) (arithmeticOf R)

end OrderRealization
end UniversalForcing
end Foundation
end IndisputableMonolith
