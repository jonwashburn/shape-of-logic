import IndisputableMonolith.Foundation.OrderedLogicRealization

/-!
  PhysicsLogicRealization.lean

  Lightweight physics realization hook for Universal Forcing.

  The full physics forcing chain is large and currently imports modules with
  unrelated build fragility. This module gives the stable interface: identity
  ticks as the step action, recognition states as the carrier, and equality
  cost as the minimal realization of physical tick arithmetic.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PhysicsLogicRealization

/-- Minimal recognition-state skeleton indexed by identity ticks. -/
structure PhysicsState where
  tick : ArithmeticFromLogic.LogicNat
  deriving DecidableEq

/-- Equality cost on physics states. -/
def physicsCost (x y : PhysicsState) : Nat :=
  if x = y then 0 else 1

@[simp] theorem physicsCost_self (x : PhysicsState) : physicsCost x x = 0 := by
  simp [physicsCost]

theorem physicsCost_symm (x y : PhysicsState) : physicsCost x y = physicsCost y x := by
  by_cases h : x = y
  · subst h
    simp [physicsCost]
  · have h' : y ≠ x := by intro hyx; exact h hyx.symm
    simp [physicsCost, h, h']

/-- Identity-tick successor. -/
def tickStep (x : PhysicsState) : PhysicsState :=
  ⟨ArithmeticFromLogic.LogicNat.succ x.tick⟩

/-- Interpret the free arithmetic orbit as identity-tick states. -/
def physicsInterpret (n : ArithmeticFromLogic.LogicNat) : PhysicsState :=
  ⟨n⟩

/-- Physics realization skeleton. -/
def physicsRealization : LogicRealization where
  Carrier := PhysicsState
  Cost := Nat
  zeroCost := inferInstance
  compare := physicsCost
  zero := ⟨ArithmeticFromLogic.LogicNat.zero⟩
  step := tickStep
  Orbit := ArithmeticFromLogic.LogicNat
  orbitZero := ArithmeticFromLogic.LogicNat.zero
  orbitStep := ArithmeticFromLogic.LogicNat.succ
  interpret := physicsInterpret
  interpret_zero := rfl
  interpret_step := by intro n; rfl
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
  identity := physicsCost_self
  nonContradiction := physicsCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨⟨ArithmeticFromLogic.LogicNat.succ ArithmeticFromLogic.LogicNat.zero⟩, ?_⟩
    simp [physicsCost]

/-- Physics tick interpretation is faithful. -/
theorem physics_faithful :
    LogicRealization.FaithfulArithmeticInterpretation physicsRealization where
  injective := by
    intro a b h
    cases h
    rfl
  zero_step_noncollapse := by
    intro n h
    have htick := congrArg PhysicsState.tick h
    exact ArithmeticFromLogic.LogicNat.zero_ne_succ n htick

/-- Physics realization has invariant extracted arithmetic. -/
noncomputable def physics_arithmetic_invariant (R : LogicRealization.{0, 0}) :
    (UniversalForcing.arithmeticOf physicsRealization).peano.carrier
      ≃ (UniversalForcing.arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (UniversalForcing.arithmeticOf physicsRealization)
    (UniversalForcing.arithmeticOf R)

end PhysicsLogicRealization
end Foundation
end IndisputableMonolith
