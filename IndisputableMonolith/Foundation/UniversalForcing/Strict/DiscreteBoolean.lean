import IndisputableMonolith.Foundation.UniversalForcing.Strict.PositiveRatio

/-!
  Strict/DiscreteBoolean.lean

  Strict Boolean/propositional realization.  The carrier orbit is periodic,
  but the strict forced arithmetic is the free iteration object derived from
  the native generator, not the finite image inside `Bool`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace DiscreteBoolean

open LogicAsFunctionalEquation

def boolCost (p q : Bool) : Nat :=
  if p = q then 0 else 1

@[simp] theorem boolCost_self (p : Bool) : boolCost p p = 0 := by
  simp [boolCost]

theorem boolCost_symm (p q : Bool) : boolCost p q = boolCost q p := by
  by_cases h : p = q
  · subst h
    simp [boolCost]
  · have h' : q ≠ p := by intro hq; exact h hq.symm
    simp [boolCost, h, h']

def xorBool (p q : Bool) : Bool :=
  xor p q

/-- Strict discrete Boolean realization. -/
def strictBooleanRealization : StrictLogicRealization where
  Carrier := Bool
  Cost := Nat
  zeroCost := inferInstance
  compare := boolCost
  compose := xorBool
  one := false
  generator := true
  identity_law := boolCost_self
  non_contradiction_law := boolCost_symm
  excluded_middle_law := True
  composition_law := True
  invariance_law := True
  nontrivial_law := by
    simp [boolCost]

/-- Strict Boolean forced arithmetic is canonically `LogicNat`. -/
def strictBoolean_arith_equiv_logicNat :
    (StrictLogicRealization.arith strictBooleanRealization).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight strictBooleanRealization).orbitEquivLogicNat

/-- First strict cross-realization invariance theorem:
positive ratios and Boolean propositions force the same arithmetic. -/
noncomputable def strictPositiveRatio_arith_equiv_strictBoolean
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (StrictLogicRealization.arith (PositiveRatio.strictPositiveRatioRealization C h)).peano.carrier
      ≃ (StrictLogicRealization.arith strictBooleanRealization).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (StrictLogicRealization.arith (PositiveRatio.strictPositiveRatioRealization C h))
    (StrictLogicRealization.arith strictBooleanRealization)

end DiscreteBoolean
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
