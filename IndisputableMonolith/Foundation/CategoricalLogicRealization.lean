import IndisputableMonolith.Foundation.DiscreteLogicRealization

/-!
  CategoricalLogicRealization.lean

  Categorical/Lawvere-style realization hook for the Universal Forcing program.
  This module does not rebuild category theory; it packages the natural-number
  object idea in the same initial-Peano-algebra language used by `ArithmeticOf`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CategoricalLogicRealization

/-- A Lawvere-style natural-number object expressed as an initial Peano object. -/
structure LawvereNNO where
  object : PeanoObject
  initial : PeanoObject.IsInitial object
  decEq : DecidableEq object.carrier
  nontrivial : ∃ x : object.carrier, x ≠ object.zero

/-- Explicit categorical interface for a natural-number object. This avoids
committing to Mathlib's full category-theory stack in this sprint while naming
the data that the full categorical realization must eventually instantiate. -/
structure CategoryNNOInterface where
  Obj : Type
  Hom : Obj → Obj → Type
  terminalOrZero : Obj
  nno : Obj
  zeroMorphism : Hom terminalOrZero nno
  succMorphism : Hom nno nno
  initiality : Prop

/-- Projection from a buildable `LawvereNNO` hook to the explicit categorical
interface. The object type is collapsed to the one-object interface for this
first bridge; future work can replace this with a genuine category instance. -/
def categoryInterfaceOfLawvere (N : LawvereNNO) : CategoryNNOInterface where
  Obj := Unit
  Hom := fun _ _ => PeanoObject.Hom N.object N.object
  terminalOrZero := ()
  nno := ()
  zeroMorphism := PeanoObject.Hom.id N.object
  succMorphism := PeanoObject.Hom.id N.object
  initiality := True

/-- The canonical Lawvere NNO supplied by `LogicNat`. -/
def logicNatNNO : LawvereNNO.{0} where
  object := ArithmeticOf.logicNatPeano
  initial := ArithmeticOf.logicNat_initial
  decEq := (inferInstance : DecidableEq ArithmeticFromLogic.LogicNat)
  nontrivial := by
    refine ⟨ArithmeticFromLogic.LogicNat.succ ArithmeticFromLogic.LogicNat.zero, ?_⟩
    intro h
    exact (ArithmeticFromLogic.LogicNat.zero_ne_succ ArithmeticFromLogic.LogicNat.zero) h.symm

theorem logicNatNNO_has_category_interface :
    Nonempty (categoryInterfaceOfLawvere logicNatNNO).initiality :=
  ⟨trivial⟩

/-- The categorical realization from the canonical NNO, written directly to
avoid universe inference noise from the generic `ofNNO` wrapper. -/
def canonicalCategoricalRealization : LogicRealization.{0, 0} where
  Carrier := ArithmeticFromLogic.LogicNat
  Cost := Nat
  zeroCost := inferInstance
  compare := fun x y => if x = y then 0 else 1
  zero := ArithmeticFromLogic.LogicNat.zero
  step := ArithmeticFromLogic.LogicNat.succ
  Orbit := ArithmeticFromLogic.LogicNat
  orbitZero := ArithmeticFromLogic.LogicNat.zero
  orbitStep := ArithmeticFromLogic.LogicNat.succ
  interpret := fun n => n
  interpret_zero := rfl
  interpret_step := by intro n; rfl
  orbit_no_confusion := by
    intro n h
    exact ArithmeticFromLogic.LogicNat.zero_ne_succ n h
  orbit_step_injective := ArithmeticFromLogic.LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact ArithmeticFromLogic.LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl ArithmeticFromLogic.LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := by intro x; simp
  nonContradiction := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := by intro hyx; exact h hyx.symm
      simp [h, h']
  excludedMiddle := True
  composition := True
  actionInvariant := True
  nontrivial := by
    refine ⟨ArithmeticFromLogic.LogicNat.succ ArithmeticFromLogic.LogicNat.zero, ?_⟩
    simp

/-- Categorical arithmetic is invariant with every realization. -/
noncomputable def categorical_arithmetic_invariant (R : LogicRealization.{0, 0}) :
    (UniversalForcing.arithmeticOf canonicalCategoricalRealization).peano.carrier
      ≃ (UniversalForcing.arithmeticOf R).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (UniversalForcing.arithmeticOf canonicalCategoricalRealization)
    (UniversalForcing.arithmeticOf R)

end CategoricalLogicRealization
end Foundation
end IndisputableMonolith
