import IndisputableMonolith.Foundation.LogicRealization
import IndisputableMonolith.Foundation.ArithmeticFromLogic

/-!
  ArithmeticOf.lean

  Arithmetic extracted from an abstract Law-of-Logic realization.

  The key point is initiality: once a realization supplies identity/step
  data, the forced arithmetic object is the initial Peano algebra generated
  by that data. Initial objects are unique up to unique isomorphism; this is
  the mechanism behind Universal Forcing.
-/

namespace IndisputableMonolith
namespace Foundation

open ArithmeticFromLogic

universe u

/-- A Peano algebra: a type with a zero element and a step map. -/
structure PeanoObject where
  carrier : Type u
  zero : carrier
  step : carrier → carrier

namespace PeanoObject

/-- Homomorphisms of Peano algebras. -/
structure Hom (A B : PeanoObject) where
  toFun : A.carrier → B.carrier
  map_zero : toFun A.zero = B.zero
  map_step : ∀ x : A.carrier, toFun (A.step x) = B.step (toFun x)

namespace Hom

instance (A B : PeanoObject) : CoeFun (Hom A B) (fun _ => A.carrier → B.carrier) where
  coe f := f.toFun

/-- Identity homomorphism. -/
def id (A : PeanoObject) : Hom A A where
  toFun := fun x => x
  map_zero := rfl
  map_step := fun _ => rfl

/-- Composition of homomorphisms. -/
def comp {A B C : PeanoObject} (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := g.toFun ∘ f.toFun
  map_zero := by rw [Function.comp_apply, f.map_zero, g.map_zero]
  map_step := by
    intro x
    rw [Function.comp_apply, f.map_step, g.map_step, Function.comp_apply]

end Hom

/-- Initiality of a Peano algebra. This is data, so it lives in `Type`. -/
structure IsInitial (A : PeanoObject) where
  lift : ∀ B : PeanoObject, Hom A B
  uniq : ∀ (B : PeanoObject) (f g : Hom A B), f.toFun = g.toFun

end PeanoObject

/-- The arithmetic object forced by a Law-of-Logic realization. -/
structure ArithmeticOf (R : LogicRealization) where
  peano : PeanoObject
  initial : PeanoObject.IsInitial peano

namespace ArithmeticOf

/-- Peano surface of a forced arithmetic object. -/
structure PeanoSurface {R : LogicRealization} (A : ArithmeticOf R) : Prop where
  zero_ne_step : ∀ x : A.peano.carrier, A.peano.zero ≠ A.peano.step x
  step_injective : Function.Injective A.peano.step
  induction :
    ∀ P : A.peano.carrier → Prop,
      P A.peano.zero →
      (∀ n, P n → P (A.peano.step n)) →
      ∀ n, P n

/-! ## LogicNat as the canonical initial Peano object -/

/-- The Peano object carried by `LogicNat`. -/
def logicNatPeano : PeanoObject where
  carrier := LogicNat
  zero := LogicNat.zero
  step := LogicNat.succ

/-- Fold from `LogicNat` into an arbitrary Peano object. -/
def logicNatFold (B : PeanoObject) : LogicNat → B.carrier
  | LogicNat.identity => B.zero
  | LogicNat.step n => B.step (logicNatFold B n)

/-- Lift from `LogicNat` to any Peano object by primitive recursion. -/
def logicNatLift (B : PeanoObject) : PeanoObject.Hom logicNatPeano B where
  toFun := logicNatFold B
  map_zero := rfl
  map_step := by
    intro x
    rfl

private theorem logicNatLift_unique_fun (B : PeanoObject)
    (f : PeanoObject.Hom logicNatPeano B) :
    f.toFun = (logicNatLift B).toFun := by
  funext n
  induction n with
  | identity =>
      exact f.map_zero
  | step n ih =>
      calc
        f.toFun (LogicNat.step n) = B.step (f.toFun n) := f.map_step n
        _ = B.step ((logicNatLift B).toFun n) := by rw [ih]
        _ = (logicNatLift B).toFun (LogicNat.step n) := rfl

/-- `LogicNat` is initial among Peano objects. -/
def logicNat_initial : PeanoObject.IsInitial logicNatPeano where
  lift := logicNatLift
  uniq := by
    intro B f g
    rw [logicNatLift_unique_fun B f, logicNatLift_unique_fun B g]

/-- The Peano object extracted from a realization's own orbit. -/
def realizationPeano (R : LogicRealization) : PeanoObject where
  carrier := R.Orbit
  zero := R.orbitZero
  step := R.orbitStep

/-- Fold from a realization orbit into any Peano object, through the
realization's certified equivalence with `LogicNat`. -/
def realizationFold (R : LogicRealization) (B : PeanoObject) : R.Orbit → B.carrier :=
  fun n => (logicNatLift B).toFun (R.orbitEquivLogicNat n)

/-- Homomorphism from the extracted realization orbit into any Peano object. -/
def realizationLift (R : LogicRealization) (B : PeanoObject) :
    PeanoObject.Hom (realizationPeano R) B where
  toFun := realizationFold R B
  map_zero := by
    unfold realizationFold
    change (logicNatLift B).toFun (R.orbitEquivLogicNat R.orbitZero) = B.zero
    rw [R.orbitEquiv_zero]
    rfl
  map_step := by
    intro x
    unfold realizationFold
    change (logicNatLift B).toFun (R.orbitEquivLogicNat (R.orbitStep x)) =
      B.step ((logicNatLift B).toFun (R.orbitEquivLogicNat x))
    rw [R.orbitEquiv_step]
    rfl

private theorem realizationLift_unique_fun (R : LogicRealization) (B : PeanoObject)
    (f : PeanoObject.Hom (realizationPeano R) B) :
    f.toFun = (realizationLift R B).toFun := by
  funext n
  have hlogic :
      (f.toFun ∘ R.orbitEquivLogicNat.symm) =
        (logicNatLift B).toFun := by
    exact logicNatLift_unique_fun B
      { toFun := f.toFun ∘ R.orbitEquivLogicNat.symm
        map_zero := by
          simp [Function.comp_def]
          have hz := f.map_zero
          have hsymm0 : R.orbitEquivLogicNat.symm LogicNat.zero = R.orbitZero := by
            apply R.orbitEquivLogicNat.injective
            simp [R.orbitEquiv_zero]
          change f.toFun (R.orbitEquivLogicNat.symm LogicNat.zero) = B.zero
          rw [hsymm0]
          exact hz
        map_step := by
          intro k
          simp [Function.comp_def]
          change f.toFun (R.orbitEquivLogicNat.symm (LogicNat.succ k)) =
            B.step (f.toFun (R.orbitEquivLogicNat.symm k))
          have hstep_symm :
              R.orbitEquivLogicNat.symm (LogicNat.succ k) =
                R.orbitStep (R.orbitEquivLogicNat.symm k) := by
            apply R.orbitEquivLogicNat.injective
            rw [R.orbitEquiv_step]
            simp
          rw [hstep_symm]
          simpa [realizationPeano] using f.map_step (R.orbitEquivLogicNat.symm k) }
  have hn : R.orbitEquivLogicNat.symm (R.orbitEquivLogicNat n) = n := by simp
  calc
    f.toFun n = (f.toFun ∘ R.orbitEquivLogicNat.symm) (R.orbitEquivLogicNat n) := by
      simp [Function.comp_def, hn]
    _ = (logicNatLift B).toFun (R.orbitEquivLogicNat n) := by rw [hlogic]
    _ = (realizationLift R B).toFun n := rfl

/-- The extracted realization orbit is initial. -/
def realization_initial (R : LogicRealization) :
    PeanoObject.IsInitial (realizationPeano R) where
  lift := realizationLift R
  uniq := by
    intro B f g
    rw [realizationLift_unique_fun R B f, realizationLift_unique_fun R B g]

/-- Arithmetic extracted from the realization's own identity-step orbit. -/
def extracted (R : LogicRealization) : ArithmeticOf R where
  peano := realizationPeano R
  initial := realization_initial R

/-- Peano surface for the extracted arithmetic of any realization. -/
theorem extracted_peanoSurface (R : LogicRealization) :
    PeanoSurface (extracted R) where
  zero_ne_step := R.orbit_no_confusion
  step_injective := R.orbit_step_injective
  induction := R.orbit_induction

/-- The natural equivalence between two initial Peano objects. -/
noncomputable def equivOfInitial {R S : LogicRealization}
    (A : ArithmeticOf R) (B : ArithmeticOf S) : A.peano.carrier ≃ B.peano.carrier where
  toFun := (A.initial.lift B.peano).toFun
  invFun := (B.initial.lift A.peano).toFun
  left_inv := by
    intro x
    have hcomp :
        (PeanoObject.Hom.comp (B.initial.lift A.peano) (A.initial.lift B.peano)).toFun =
          (PeanoObject.Hom.id A.peano).toFun :=
      A.initial.uniq A.peano
        (PeanoObject.Hom.comp (B.initial.lift A.peano) (A.initial.lift B.peano))
        (PeanoObject.Hom.id A.peano)
    exact congrFun hcomp x
  right_inv := by
    intro y
    have hcomp :
        (PeanoObject.Hom.comp (A.initial.lift B.peano) (B.initial.lift A.peano)).toFun =
          (PeanoObject.Hom.id B.peano).toFun :=
      B.initial.uniq B.peano
        (PeanoObject.Hom.comp (A.initial.lift B.peano) (B.initial.lift A.peano))
        (PeanoObject.Hom.id B.peano)
    exact congrFun hcomp y

/-- Canonical arithmetic object for any realization: the initial Peano object.

This definition is intentionally realization-independent at this stage. The
realization supplies the interpretation; initiality supplies the invariant
arithmetic content. -/
def canonical (R : LogicRealization) : ArithmeticOf R where
  peano := logicNatPeano
  initial := logicNat_initial

/-- The Peano surface for the canonical arithmetic object. -/
theorem canonical_peanoSurface (R : LogicRealization) :
    PeanoSurface (canonical R) where
  zero_ne_step := by
    intro x h
    cases h
  step_injective := by
    intro a b h
    exact LogicNat.succ_injective h
  induction := by
    intro P h0 hstep n
    exact LogicNat.induction (motive := P) h0 hstep n

end ArithmeticOf

end Foundation
end IndisputableMonolith
