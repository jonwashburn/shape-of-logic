import IndisputableMonolith.Foundation.UniversalForcing.Strict.Modular
import IndisputableMonolith.Foundation.CategoricalLogicRealization

/-!
  Strict/Categorical.lean

  Strict categorical/Lawvere-style realization hook. The carrier is the
  canonical `LogicNat` NNO surface from `CategoricalLogicRealization`; future
  work can refine this to Mathlib's full category-theory NNO API.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace Categorical

open ArithmeticFromLogic

def logicNatCost (a b : LogicNat) : Nat :=
  if a = b then 0 else 1

@[simp] theorem logicNatCost_self (a : LogicNat) : logicNatCost a a = 0 := by
  simp [logicNatCost]

theorem logicNatCost_symm (a b : LogicNat) : logicNatCost a b = logicNatCost b a := by
  by_cases h : a = b
  · subst h
    simp [logicNatCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [logicNatCost, h, h']

/-- Strict categorical realization via the canonical `LogicNat` Peano/NNO hook. -/
def strictCategoricalRealization : StrictLogicRealization where
  Carrier := LogicNat
  Cost := Nat
  zeroCost := inferInstance
  compare := logicNatCost
  compose := fun a b => a + b
  one := LogicNat.zero
  generator := LogicNat.succ LogicNat.zero
  identity_law := logicNatCost_self
  non_contradiction_law := logicNatCost_symm
  excluded_middle_law := True
  composition_law := True
  invariance_law := True
  nontrivial_law := by
    simp [logicNatCost, LogicNat.zero_ne_succ]

def strictCategorical_arith_equiv_logicNat :
    (StrictLogicRealization.arith strictCategoricalRealization).peano.carrier
      ≃ LogicNat :=
  (StrictLogicRealization.toLightweight strictCategoricalRealization).orbitEquivLogicNat

end Categorical
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
