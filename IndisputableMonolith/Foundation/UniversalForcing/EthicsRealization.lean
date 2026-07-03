import IndisputableMonolith.Foundation.UniversalForcing.NarrativeRealization

/-!
  EthicsRealization.lean

  Lightweight ethical realization: the carrier is the count of morally
  meaningful improvement steps. The domain theory of ethics is not rebuilt
  here; only the identity/step comparison structure needed by Universal
  Forcing is formalized.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace EthicsRealization

open ArithmeticFromLogic
open Invariance.Universal

abbrev MoralImprovementStep := Nat

def ethicsCost (a b : MoralImprovementStep) : Nat :=
  if a = b then 0 else 1

@[simp] theorem ethicsCost_self (a : MoralImprovementStep) : ethicsCost a a = 0 := by
  simp [ethicsCost]

theorem ethicsCost_symm (a b : MoralImprovementStep) : ethicsCost a b = ethicsCost b a := by
  by_cases h : a = b
  · subst h; simp [ethicsCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [ethicsCost, h, h']

def ethicsInterpret (n : LogicNat) : MoralImprovementStep :=
  LogicNat.toNat n

/-- Ethical realization as morally meaningful improvement count. -/
def ethicsRealization : LogicRealization where
  Carrier := MoralImprovementStep
  Cost := Nat
  zeroCost := inferInstance
  compare := ethicsCost
  zero := 0
  step := Nat.succ
  Orbit := LogicNat
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := ethicsInterpret
  interpret_zero := by rfl
  interpret_step := by
    intro n
    show LogicNat.toNat (LogicNat.succ n) = Nat.succ (LogicNat.toNat n)
    rfl
  orbit_no_confusion := by intro n h; exact LogicNat.zero_ne_succ n h
  orbit_step_injective := LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := ethicsCost_self
  nonContradiction := ethicsCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨1, ?_⟩
    simp [ethicsCost]

noncomputable def ethics_arith_equiv_nat :
    (arithmeticOf ethicsRealization).peano.carrier ≃ LogicNat :=
  ethicsRealization.orbitEquivLogicNat

end EthicsRealization
end UniversalForcing
end Foundation
end IndisputableMonolith
