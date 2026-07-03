import Mathlib
import IndisputableMonolith.Foundation.UniversalForcing

/-!
  ModularRealization.lean

  Modular/cyclic realization. The carrier is `ZMod n`, with equality cost.
  The semantic orbit in the finite carrier may close; the forced arithmetic is
  the universal iteration object certified by the internal orbit.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace ModularRealization

open ArithmeticFromLogic

/-- Equality cost on a cyclic carrier. -/
def zmodCost {n : ℕ} (a b : ZMod n) : Nat :=
  if a = b then 0 else 1

@[simp] theorem zmodCost_self {n : ℕ} (a : ZMod n) : zmodCost a a = 0 := by
  simp [zmodCost]

theorem zmodCost_symm {n : ℕ} (a b : ZMod n) : zmodCost a b = zmodCost b a := by
  by_cases h : a = b
  · subst h; simp [zmodCost]
  · have h' : b ≠ a := by intro hb; exact h hb.symm
    simp [zmodCost, h, h']

/-- Interpret `LogicNat` in `ZMod n` by the usual coercion of its index. -/
def zmodOrbitInterpret (n : ℕ) (k : LogicNat) : ZMod n :=
  (LogicNat.toNat k : ZMod n)

/-- Modular realization for any nontrivial modulus. -/
def modularRealization (n : ℕ) [Fact (1 < n)] : LogicRealization where
  Carrier := ZMod n
  Cost := Nat
  zeroCost := inferInstance
  compare := zmodCost
  zero := 0
  step := fun z => z + 1
  Orbit := LogicNat
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := zmodOrbitInterpret n
  interpret_zero := by
    show ((0 : ℕ) : ZMod n) = 0
    norm_num
  interpret_step := by
    intro k
    show ((LogicNat.toNat (LogicNat.succ k) : ZMod n) =
      (LogicNat.toNat k : ZMod n) + 1)
    rw [LogicNat.toNat_succ]
    norm_num
  orbit_no_confusion := by
    intro k h
    exact LogicNat.zero_ne_succ k h
  orbit_step_injective := LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs k
    exact LogicNat.induction (motive := P) h0 hs k
  orbitEquivLogicNat := Equiv.refl LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro k; rfl
  identity := zmodCost_self
  nonContradiction := zmodCost_symm
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨(1 : ZMod n), ?_⟩
    have hne : (1 : ZMod n) ≠ 0 := by
      intro h
      have hval := congrArg ZMod.val h
      rw [ZMod.val_one n, ZMod.val_zero] at hval
      norm_num at hval
    simp [zmodCost, hne]

/-- Modular realization carries the universal forced arithmetic. -/
noncomputable def modular_arithmetic_invariant (n : ℕ) [Fact (1 < n)]
    (R : LogicRealization.{0, 0}) :
    (arithmeticOf (modularRealization n)).peano.carrier
      ≃ (arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf (modularRealization n)) (arithmeticOf R)

end ModularRealization
end UniversalForcing
end Foundation
end IndisputableMonolith
