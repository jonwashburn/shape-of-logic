import Mathlib
import IndisputableMonolith.Foundation.UniversalForcing.Strict.Ordered

/-!
  Strict/Modular.lean

  Strict modular realization on `ZMod n`. Carrier interpretation is periodic;
  forced arithmetic remains the derived free orbit.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace Modular

def zmodCost {n : ℕ} (a b : ZMod n) : Nat :=
  if a = b then 0 else 1

@[simp] theorem zmodCost_self {n : ℕ} (a : ZMod n) : zmodCost a a = 0 := by
  simp [zmodCost]

theorem zmodCost_symm {n : ℕ} (a b : ZMod n) : zmodCost a b = zmodCost b a := by
  by_cases h : a = b
  · subst h
    simp [zmodCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [zmodCost, h, h']

/-- Strict modular realization for moduli `n > 1`. -/
def strictModularRealization (n : ℕ) [Fact (1 < n)] : StrictLogicRealization where
  Carrier := ZMod n
  Cost := Nat
  zeroCost := inferInstance
  compare := zmodCost
  compose := fun a b => a + b
  one := 0
  generator := 1
  identity_law := zmodCost_self
  non_contradiction_law := zmodCost_symm
  excluded_middle_law := True
  composition_law := True
  invariance_law := True
  nontrivial_law := by
    have hne : (1 : ZMod n) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      rw [ZMod.val_one n, ZMod.val_zero] at hval
      norm_num at hval
    simp [zmodCost, hne]

def strictModular_arith_equiv_logicNat (n : ℕ) [Fact (1 < n)] :
    (StrictLogicRealization.arith (strictModularRealization n)).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight (strictModularRealization n)).orbitEquivLogicNat

end Modular
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
