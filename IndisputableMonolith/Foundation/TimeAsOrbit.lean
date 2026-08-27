import Mathlib
import IndisputableMonolith.Foundation.TimeEmergence
import IndisputableMonolith.Foundation.ArithmeticFromLogic
import IndisputableMonolith.Foundation.UniversalForcing.NaturalNumberObject

/-!
# Time as Forced Orbit

This module makes the explicit claim:

> The temporal sequence (`Tick`) is canonically the natural-number object
> forced by recognition.

Concretely, `Tick` is a Lawvere natural-number object under successor
`fun t => ⟨t.index + 1⟩`. By the universal property of natural-number
objects (proved in `UniversalForcing.NaturalNumberObject`), `Tick` is
canonically equivalent to `LogicNat`, the orbit construction of
`ArithmeticFromLogic`. The orbit of recognition and the tick count of
the ledger are the same iteration object up to canonical isomorphism.

This closes the time-as-orbit frontier: time is not added to physics; it
is the canonical iteration object of recognition.

## Honest scope

This module proves time as a *combinatorial* iteration object. It does
not derive metric time, the 8-tick cycle's `D=3` origin (already in
`Foundation.DimensionForcing`), or the arrow of time as Berry-phase
monotonicity (Layer 8 of the cosmological forcing chain, separate work).
What is proved here is the structural identification: recognition steps
generate the natural-number object, and that object is `Tick`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace TimeAsOrbit

open TimeEmergence
open ArithmeticFromLogic
open UniversalForcing

universe u

/-! ## The Tick Successor -/

/-- The canonical successor on `Tick`: advance the index by one. -/
def tickSucc (t : Tick) : Tick := ⟨t.index + 1⟩

@[simp] theorem tickSucc_index (t : Tick) : (tickSucc t).index = t.index + 1 := rfl

/-- The canonical zero tick. -/
def tickZero : Tick := ⟨0⟩

@[simp] theorem tickZero_index : tickZero.index = 0 := rfl

/-! ## Tick is canonically the natural numbers -/

/-- The canonical equivalence between `Tick` and `Nat` via the index. -/
def tickEquivNat : Tick ≃ Nat where
  toFun t := t.index
  invFun n := ⟨n⟩
  left_inv := by intro t; cases t; rfl
  right_inv := by intro n; rfl

@[simp] theorem tickEquivNat_apply (t : Tick) : tickEquivNat t = t.index := rfl
@[simp] theorem tickEquivNat_symm_apply (n : Nat) :
    tickEquivNat.symm n = ⟨n⟩ := rfl

@[simp] theorem tickEquivNat_zero : tickEquivNat tickZero = 0 := rfl

@[simp] theorem tickEquivNat_succ (t : Tick) :
    tickEquivNat (tickSucc t) = (tickEquivNat t) + 1 := rfl

/-- The canonical equivalence `Tick ≃ LogicNat` via `Nat`. -/
def tickEquivLogicNat : Tick ≃ LogicNat :=
  tickEquivNat.trans LogicNat.equivNat.symm

/-! ## Tick is a natural-number object -/

/-- Recursor on `Tick`: iterate `f` from `x` exactly `t.index` times. -/
def tickRecursor {X : Type u} (x : X) (f : X → X) (t : Tick) : X :=
  Nat.rec x (fun _ acc => f acc) t.index

@[simp] theorem tickRecursor_zero {X : Type u} (x : X) (f : X → X) :
    tickRecursor x f tickZero = x := rfl

@[simp] theorem tickRecursor_succ {X : Type u} (x : X) (f : X → X) (t : Tick) :
    tickRecursor x f (tickSucc t) = f (tickRecursor x f t) := rfl

/-- **Tick is a Lawvere natural-number object.** Together with `tickZero`
and `tickSucc`, the `Tick` type satisfies the universal property of the
natural-number object: primitive recursion exists and is unique. -/
def tick_isNNO :
    IsNaturalNumberObject (N := Tick) tickZero tickSucc where
  recursor := fun {X} x f => tickRecursor x f
  recursor_zero := fun {X} x f => tickRecursor_zero x f
  recursor_step := fun {X} x f t => tickRecursor_succ x f t
  recursor_unique := by
    intro X x f h hz hs t
    -- Reduce to induction on t.index.
    suffices hgen : ∀ n : Nat, h ⟨n⟩ = tickRecursor x f ⟨n⟩ by
      have := hgen t.index
      cases t
      exact this
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
        have hstep : h ⟨n + 1⟩ = h (tickSucc ⟨n⟩) := rfl
        rw [hstep, hs ⟨n⟩, ih]
        rfl

/-! ## Time IS the orbit (Lawvere identification) -/

/-- **Time is the orbit.** The `Tick` type is canonically equivalent, as a
natural-number object, to `LogicNat`. The temporal iteration of recognition
and the orbit construction in `ArithmeticFromLogic` deliver the same
iteration object up to unique isomorphism. -/
noncomputable def tick_orbit_eq_logicNat : Tick ≃ LogicNat :=
  IsNaturalNumberObject.equiv tick_isNNO logicNat_isNNO

/-- The Lawvere equivalence sends `tickZero` to `LogicNat.identity`. -/
theorem tick_orbit_eq_logicNat_zero :
    tick_orbit_eq_logicNat tickZero = LogicNat.identity := by
  unfold tick_orbit_eq_logicNat IsNaturalNumberObject.equiv
  exact tick_isNNO.recursor_zero LogicNat.identity LogicNat.step

/-- The Lawvere equivalence intertwines `tickSucc` with `LogicNat.step`. -/
theorem tick_orbit_eq_logicNat_succ (t : Tick) :
    tick_orbit_eq_logicNat (tickSucc t) = LogicNat.step (tick_orbit_eq_logicNat t) := by
  unfold tick_orbit_eq_logicNat IsNaturalNumberObject.equiv
  exact tick_isNNO.recursor_step LogicNat.identity LogicNat.step t

/-! ## Recognition steps iterate the tick successor -/

/-- A `RecognitionStep` advances the tick by one, equivalently applies
`tickSucc` to the input snapshot's tick. This is the bridge from the
ledger dynamics of `TimeEmergence` to the abstract natural-number object
on `Tick`. -/
theorem recognitionStep_iterates_succ (step : RecognitionStep) :
    step.output.tick = tickSucc step.input.tick := by
  have hadv := step.tick_advance
  cases hin : step.input.tick with
  | mk i =>
    cases hout : step.output.tick with
    | mk o =>
      rw [hin, hout] at hadv
      simp [tickSucc]
      exact hadv

/-! ## Headline Certificate -/

/-- **Time-as-Orbit Certificate.**

The temporal sequence is canonically the natural-number object forced by
recognition. -/
structure TimeAsOrbitCert where
  tick_is_NNO : IsNaturalNumberObject (N := Tick) tickZero tickSucc
  tick_equiv_logicNat : Tick ≃ LogicNat
  tick_equiv_logicNat_zero : tick_equiv_logicNat tickZero = LogicNat.identity
  tick_equiv_logicNat_succ :
    ∀ t : Tick, tick_equiv_logicNat (tickSucc t) =
      LogicNat.step (tick_equiv_logicNat t)
  recognition_advances_succ :
    ∀ step : RecognitionStep, step.output.tick = tickSucc step.input.tick

noncomputable def timeAsOrbitCert : TimeAsOrbitCert where
  tick_is_NNO := tick_isNNO
  tick_equiv_logicNat := tick_orbit_eq_logicNat
  tick_equiv_logicNat_zero := tick_orbit_eq_logicNat_zero
  tick_equiv_logicNat_succ := tick_orbit_eq_logicNat_succ
  recognition_advances_succ := recognitionStep_iterates_succ

theorem timeAsOrbitCert_inhabited : Nonempty TimeAsOrbitCert :=
  ⟨timeAsOrbitCert⟩

/-! ## Summary

This module supplies the bridge:

```
RecognitionStep advances Tick by one
       ↓
Tick is a natural-number object
       ↓
Tick ≃ LogicNat (Lawvere universal property)
       ↓
Time is the canonical orbit of recognition
```

The temporal iteration of the ledger and the orbit construction of
`ArithmeticFromLogic` are the same mathematical object up to unique
isomorphism. Time is not background; time is what recognition forces.
-/

end TimeAsOrbit
end Foundation
end IndisputableMonolith
