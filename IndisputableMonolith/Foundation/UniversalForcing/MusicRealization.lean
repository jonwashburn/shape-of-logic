import IndisputableMonolith.Foundation.UniversalForcing.Invariance.Universal

/-!
  MusicRealization.lean

  Lightweight musical realization: the carrier records interval steps. The
  semantic reading is pitch-ratio stacking; the forced arithmetic is the
  iteration count of interval composition.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace MusicRealization

open ArithmeticFromLogic
open Invariance.Universal

abbrev MusicalIntervalStep := Nat

def musicCost (a b : MusicalIntervalStep) : Nat :=
  if a = b then 0 else 1

@[simp] theorem musicCost_self (a : MusicalIntervalStep) : musicCost a a = 0 := by
  simp [musicCost]

theorem musicCost_symm (a b : MusicalIntervalStep) : musicCost a b = musicCost b a := by
  by_cases h : a = b
  · subst h; simp [musicCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [musicCost, h, h']

def musicInterpret (n : LogicNat) : MusicalIntervalStep :=
  LogicNat.toNat n

/-- Musical realization as interval-step comparison. -/
def musicRealization : LogicRealization where
  Carrier := MusicalIntervalStep
  Cost := Nat
  zeroCost := inferInstance
  compare := musicCost
  zero := 0
  step := Nat.succ
  Orbit := LogicNat
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := musicInterpret
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
  identity := musicCost_self
  nonContradiction := musicCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨1, ?_⟩
    simp [musicCost]

noncomputable def music_arith_equiv_nat :
    (arithmeticOf musicRealization).peano.carrier ≃ LogicNat :=
  musicRealization.orbitEquivLogicNat

end MusicRealization
end UniversalForcing
end Foundation
end IndisputableMonolith
