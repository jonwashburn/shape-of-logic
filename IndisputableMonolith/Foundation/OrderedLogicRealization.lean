import IndisputableMonolith.Foundation.ModularLogicRealization

/-!
  OrderedLogicRealization.lean

  Ordered faithful realization for Universal Forcing.
-/

namespace IndisputableMonolith
namespace Foundation
namespace OrderedLogicRealization

/-- Equality cost on `Nat`. -/
def natCost (m n : Nat) : Nat :=
  if m = n then 0 else 1

@[simp] theorem natCost_self (n : Nat) : natCost n n = 0 := by
  simp [natCost]

theorem natCost_symm (m n : Nat) : natCost m n = natCost n m := by
  by_cases h : m = n
  · subst h
    simp [natCost]
  · have h' : n ≠ m := by intro hnm; exact h hnm.symm
    simp [natCost, h, h']

/-- The ordered natural-number realization. -/
def natOrderedRealization : LogicRealization where
  Carrier := Nat
  Cost := Nat
  zeroCost := inferInstance
  compare := natCost
  zero := 0
  step := Nat.succ
  Orbit := ArithmeticFromLogic.LogicNat
  orbitZero := ArithmeticFromLogic.LogicNat.zero
  orbitStep := ArithmeticFromLogic.LogicNat.succ
  interpret := ArithmeticFromLogic.LogicNat.toNat
  interpret_zero := ArithmeticFromLogic.LogicNat.toNat_zero
  interpret_step := by
    intro n
    exact ArithmeticFromLogic.LogicNat.toNat_succ n
  orbit_no_confusion := by
    intro n h
    exact ArithmeticFromLogic.LogicNat.zero_ne_succ n h
  orbit_step_injective := ArithmeticFromLogic.LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact ArithmeticFromLogic.LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl ArithmeticFromLogic.LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := natCost_self
  nonContradiction := natCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨1, ?_⟩
    simp [natCost]

/-- Ordered arithmetic is invariant with every realization. -/
noncomputable def ordered_arithmetic_invariant (R : LogicRealization.{0, 0}) :
    (UniversalForcing.arithmeticOf natOrderedRealization).peano.carrier
      ≃ (UniversalForcing.arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (UniversalForcing.arithmeticOf natOrderedRealization)
    (UniversalForcing.arithmeticOf R)

/-- The ordered realization interprets arithmetic faithfully. -/
theorem ordered_faithful :
    LogicRealization.FaithfulArithmeticInterpretation natOrderedRealization where
  injective := by
    intro a b h
    exact (ArithmeticFromLogic.LogicNat.eq_iff_toNat_eq).mpr h
  zero_step_noncollapse := by
    intro n h
    have hnat := congrArg id h
    simp [natOrderedRealization] at hnat
    exact Nat.succ_ne_zero _ hnat.symm

/-- Order on the carrier matches the recovered Peano order. -/
theorem ordered_interpret_le_iff (a b : ArithmeticFromLogic.LogicNat) :
    ArithmeticFromLogic.LogicNat.toNat a ≤ ArithmeticFromLogic.LogicNat.toNat b ↔ a ≤ b := by
  exact (ArithmeticFromLogic.LogicNat.toNat_le a b).symm

end OrderedLogicRealization
end Foundation
end IndisputableMonolith
