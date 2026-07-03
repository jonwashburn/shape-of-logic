import IndisputableMonolith.Foundation.UniversalForcing

/-!
  StrictRealization.lean

  Domain-rich Universal Forcing interface.

  The earlier `LogicRealization` interface already proves the lightweight
  Universal Forcing theorem, but it lets a realization carry an internal orbit
  as a field.  `StrictLogicRealization` removes that escape hatch from the
  main theorem path: a strict realization supplies only native comparison,
  composition, identity, invariance, and non-triviality data.  The free orbit
  used by Universal Forcing is then derived uniformly as `LogicNat`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict

open ArithmeticFromLogic

universe u v

/-- A strict Law-of-Logic realization: native law data only, no supplied orbit. -/
structure StrictLogicRealization where
  Carrier : Type u
  Cost : Type v
  zeroCost : Zero Cost
  compare : Carrier → Carrier → Cost
  compose : Carrier → Carrier → Carrier
  one : Carrier
  generator : Carrier
  identity_law : ∀ x : Carrier, compare x x = 0
  non_contradiction_law : ∀ x y : Carrier, compare x y = compare y x
  excluded_middle_law : Prop
  composition_law : Prop
  invariance_law : Prop
  nontrivial_law : compare generator one ≠ 0

attribute [instance] StrictLogicRealization.zeroCost

namespace StrictLogicRealization

/-- The strict free orbit is uniformly the `LogicNat` iteration object. -/
abbrev FreeOrbit (_R : StrictLogicRealization) : Type :=
  LogicNat

/-- Interpret the free orbit of a strict realization in its carrier by
primitive recursion over the native generator and composition operation. -/
def interpret (R : StrictLogicRealization) : FreeOrbit R → R.Carrier
  | LogicNat.identity => R.one
  | LogicNat.step n => R.compose R.generator (interpret R n)

@[simp] theorem interpret_zero (R : StrictLogicRealization) :
    interpret R LogicNat.zero = R.one := rfl

@[simp] theorem interpret_step (R : StrictLogicRealization) (n : FreeOrbit R) :
    interpret R (LogicNat.succ n) = R.compose R.generator (interpret R n) := rfl

/-- Convert a strict realization to the existing lightweight interface.
The orbit fields are all derived from `LogicNat`, not supplied by the caller. -/
def toLightweight (R : StrictLogicRealization) : LogicRealization where
  Carrier := R.Carrier
  Cost := R.Cost
  zeroCost := R.zeroCost
  compare := R.compare
  zero := R.one
  step := fun x => R.compose R.generator x
  Orbit := FreeOrbit R
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := interpret R
  interpret_zero := rfl
  interpret_step := by intro n; rfl
  orbit_no_confusion := by
    intro n h
    exact LogicNat.zero_ne_succ n h
  orbit_step_injective := LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := R.identity_law
  nonContradiction := R.non_contradiction_law
  excludedMiddle := R.excluded_middle_law
  composition := R.composition_law
  actionInvariant := R.invariance_law
  nontrivial := ⟨R.generator, R.nontrivial_law⟩

/-- Strict forced arithmetic is the arithmetic extracted from the derived
lightweight realization. -/
def arith (R : StrictLogicRealization) : ArithmeticOf (toLightweight R) :=
  arithmeticOf (toLightweight R)

/-- Every strict realization has forced arithmetic canonically equivalent to
`LogicNat`. -/
def arith_equiv_logicNat (R : StrictLogicRealization) :
    (arith R).peano.carrier ≃ LogicNat :=
  (toLightweight R).orbitEquivLogicNat

/-- Universal forcing for strict realizations. -/
noncomputable def universal_forcing (R S : StrictLogicRealization) :
    (arith R).peano.carrier ≃ (arith S).peano.carrier :=
  ArithmeticOf.equivOfInitial (arith R) (arith S)

/-- The Peano surface is inherited from the derived free orbit. -/
theorem peano_surface (R : StrictLogicRealization) :
    ArithmeticOf.PeanoSurface (arith R) :=
  UniversalForcing.peano_surface (toLightweight R)

end StrictLogicRealization

end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
