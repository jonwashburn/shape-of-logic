import IndisputableMonolith.Foundation.UniversalForcing

/-!
  DiscreteLogicRealization.lean

  The second Law-of-Logic realization: a discrete Boolean/propositional
  carrier. This is the first non-continuous test case for Universal Forcing.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DiscreteLogicRealization

/-- Boolean comparison cost: zero for equality, one for distinction. -/
def boolCost (p q : Bool) : Nat :=
  if p = q then 0 else 1

@[simp] theorem boolCost_self (p : Bool) : boolCost p p = 0 := by
  simp [boolCost]

theorem boolCost_symm (p q : Bool) : boolCost p q = boolCost q p := by
  by_cases h : p = q
  · subst h
    simp [boolCost]
  · have h' : q ≠ p := by intro hqp; exact h hqp.symm
    simp [boolCost, h, h']

/-- Interpret the free step orbit in the Boolean carrier by parity. -/
def boolOrbitInterpret : ArithmeticFromLogic.LogicNat → Bool
  | ArithmeticFromLogic.LogicNat.identity => false
  | ArithmeticFromLogic.LogicNat.step n => Bool.not (boolOrbitInterpret n)

/-- The discrete propositional Law-of-Logic realization. -/
def boolRealization : LogicRealization where
  Carrier := Bool
  Cost := Nat
  zeroCost := inferInstance
  compare := boolCost
  zero := false
  step := Bool.not
  Orbit := ArithmeticFromLogic.LogicNat
  orbitZero := ArithmeticFromLogic.LogicNat.zero
  orbitStep := ArithmeticFromLogic.LogicNat.succ
  interpret := boolOrbitInterpret
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
  identity := boolCost_self
  nonContradiction := boolCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨true, ?_⟩
    simp [boolCost]

/-- The discrete realization has a non-trivial identity-step shadow. -/
theorem bool_hasIdentityStep : boolRealization.hasIdentityStep :=
  LogicRealization.hasIdentityStep_of_nontrivial boolRealization

/-- Boolean realization has the same forced arithmetic as every realization. -/
noncomputable def bool_arithmetic_invariant (R : LogicRealization.{0, 0}) :
    (UniversalForcing.arithmeticOf boolRealization).peano.carrier
      ≃ (UniversalForcing.arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (UniversalForcing.arithmeticOf boolRealization) (UniversalForcing.arithmeticOf R)

/-- The Boolean realization's forced arithmetic has the Peano surface. -/
theorem bool_peano_surface :
    ArithmeticOf.PeanoSurface (UniversalForcing.arithmeticOf boolRealization) :=
  UniversalForcing.peano_surface boolRealization

end DiscreteLogicRealization
end Foundation
end IndisputableMonolith
