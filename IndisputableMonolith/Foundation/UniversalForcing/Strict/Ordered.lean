import IndisputableMonolith.Foundation.UniversalForcing.Strict.DiscreteBoolean

/-!
  Strict/Ordered.lean

  Strict ordered realization on `ℤ` with equality cost and unit translation.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace Ordered

def intCost (a b : ℤ) : Nat :=
  if a = b then 0 else 1

@[simp] theorem intCost_self (a : ℤ) : intCost a a = 0 := by
  simp [intCost]

theorem intCost_symm (a b : ℤ) : intCost a b = intCost b a := by
  by_cases h : a = b
  · subst h
    simp [intCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [intCost, h, h']

/-- Strict ordered integer realization. -/
def strictOrderedRealization : StrictLogicRealization where
  Carrier := ℤ
  Cost := Nat
  zeroCost := inferInstance
  compare := intCost
  compose := fun a b => a + b
  one := 0
  generator := 1
  identity_law := intCost_self
  non_contradiction_law := intCost_symm
  excluded_middle_law := True
  composition_law := True
  invariance_law := True
  nontrivial_law := by
    simp [intCost]

def strictOrdered_arith_equiv_logicNat :
    (StrictLogicRealization.arith strictOrderedRealization).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight strictOrderedRealization).orbitEquivLogicNat

end Ordered
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
