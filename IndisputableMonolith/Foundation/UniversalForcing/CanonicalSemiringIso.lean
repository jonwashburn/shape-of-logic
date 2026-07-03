import IndisputableMonolith.Foundation.UniversalForcing.CanonicalIso

/-!
  CanonicalSemiringIso.lean

  Universal Forcing, Part II — the ordered-semiring layer.

  `CanonicalIso.lean` upgraded the universal forcing invariant from a bare
  carrier bijection to a *unique structure-preserving isomorphism of Peano
  algebras* (respecting zero and successor).  This module takes the next step:
  it shows the canonical isomorphism also respects the *arithmetic* the Peano
  structure determines — addition, multiplication, the order, and the
  constants `0` and `1`.

  The construction is faithful to "the operations the initiality fold
  determines".  Every forced carrier folds canonically onto the reference
  initial object `LogicNat` via `R.orbitEquivLogicNat`, and `LogicNat` already
  carries the recovered arithmetic (`ArithmeticFromLogic`: `Add`, `Mul`,
  `LinearOrder`, with the Peano laws as theorems).  We transport `0, 1, +, ×, ≤`
  along that fold, then prove the universal forcing isomorphism commutes with
  all of them.

  The single load-bearing lemma is `fold_iso_compat`: the universal forcing
  isomorphism composed with `S`'s fold to `LogicNat` equals `R`'s fold.  This is
  pure initiality — both are Peano homomorphisms from the (initial) forced
  arithmetic of `R` into `LogicNat`, hence identical.  Everything else follows
  by `Equiv` algebra.

  Scope.  This proves the canonical map is a homomorphism for `+` and `×`, sends
  `0 ↦ 0` and `1 ↦ 1`, and is an order isomorphism for `≤`: the full
  ordered-commutative-semiring isomorphism content at the element level.  It does
  not bundle `LogicNat` (or the carriers) as a Mathlib `OrderedCommSemiring`
  typeclass *instance*; that is a separate, purely `LogicNat`-side enrichment and
  is not needed for the forcing statement.

  Universes.  Realization carriers are pinned to `Type 0` (so the forced Peano
  carriers match `LogicNat : Type 0` and the initiality `uniq` into `logicNatPeano`
  typechecks), with independent cost universes `v, w`.  This is exactly the
  Universal Forcing program's situation.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing

open ArithmeticFromLogic
open ArithmeticOf (logicNatPeano)

universe v w

/-! ## The canonical fold onto the reference initial object -/

/-- The canonical fold of a realization's forced arithmetic onto the reference
`LogicNat`, packaged as a Peano homomorphism. -/
def foldHom (R : LogicRealization.{0, v}) :
    PeanoObject.Hom (forcedArith R).peano logicNatPeano where
  toFun := fun x => R.orbitEquivLogicNat x
  map_zero := R.orbitEquiv_zero
  map_step := R.orbitEquiv_step

@[simp] theorem foldHom_toFun (R : LogicRealization.{0, v})
    (x : (forcedArith R).peano.carrier) :
    (foldHom R).toFun x = R.orbitEquivLogicNat x := rfl

/-- **Fold compatibility (pure initiality).**  The universal forcing isomorphism
`R ⥲ S`, followed by `S`'s fold onto `LogicNat`, equals `R`'s fold onto
`LogicNat`.  Both are Peano homomorphisms out of the initial forced arithmetic of
`R`, so initiality forces them equal. -/
theorem fold_iso_compat (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w})
    (x : (forcedArith R).peano.carrier) :
    S.orbitEquivLogicNat ((universalForcingPeanoEquiv R S).toEquiv x)
      = R.orbitEquivLogicNat x := by
  have h := (forcedArith R).initial.uniq logicNatPeano
    (PeanoObject.Hom.comp (foldHom S) (universalForcingPeanoEquiv R S).toHom)
    (foldHom R)
  exact congrFun h x

/-! ## Transported arithmetic on the forced carrier

The operations are the `LogicNat` operations carried back along the canonical
fold `R.orbitEquivLogicNat`. -/

/-- The forced zero of a realization (transported `0 : LogicNat`). -/
noncomputable def forcedZero (R : LogicRealization.{0, v}) :
    (forcedArith R).peano.carrier :=
  R.orbitEquivLogicNat.symm 0

/-- The forced one of a realization (transported `1 : LogicNat`). -/
noncomputable def forcedOne (R : LogicRealization.{0, v}) :
    (forcedArith R).peano.carrier :=
  R.orbitEquivLogicNat.symm 1

/-- Forced addition (transported `+` on `LogicNat`). -/
noncomputable def forcedAdd (R : LogicRealization.{0, v})
    (a b : (forcedArith R).peano.carrier) : (forcedArith R).peano.carrier :=
  R.orbitEquivLogicNat.symm (R.orbitEquivLogicNat a + R.orbitEquivLogicNat b)

/-- Forced multiplication (transported `×` on `LogicNat`). -/
noncomputable def forcedMul (R : LogicRealization.{0, v})
    (a b : (forcedArith R).peano.carrier) : (forcedArith R).peano.carrier :=
  R.orbitEquivLogicNat.symm (R.orbitEquivLogicNat a * R.orbitEquivLogicNat b)

/-- Forced order (transported `≤` on `LogicNat`). -/
def forcedLe (R : LogicRealization.{0, v})
    (a b : (forcedArith R).peano.carrier) : Prop :=
  R.orbitEquivLogicNat a ≤ R.orbitEquivLogicNat b

/-! ## The universal forcing isomorphism is an ordered-semiring isomorphism -/

/-- The canonical isomorphism sends the forced zero to the forced zero. -/
theorem iso_map_forcedZero (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w}) :
    (universalForcingPeanoEquiv R S).toEquiv (forcedZero R) = forcedZero S := by
  apply S.orbitEquivLogicNat.injective
  simp only [forcedZero, fold_iso_compat, Equiv.apply_symm_apply]

/-- The canonical isomorphism sends the forced one to the forced one. -/
theorem iso_map_forcedOne (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w}) :
    (universalForcingPeanoEquiv R S).toEquiv (forcedOne R) = forcedOne S := by
  apply S.orbitEquivLogicNat.injective
  simp only [forcedOne, fold_iso_compat, Equiv.apply_symm_apply]

/-- **Additivity.**  The canonical isomorphism is a homomorphism for forced
addition. -/
theorem iso_map_forcedAdd (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w})
    (a b : (forcedArith R).peano.carrier) :
    (universalForcingPeanoEquiv R S).toEquiv (forcedAdd R a b)
      = forcedAdd S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b) := by
  apply S.orbitEquivLogicNat.injective
  simp only [forcedAdd, fold_iso_compat, Equiv.apply_symm_apply]

/-- **Multiplicativity.**  The canonical isomorphism is a homomorphism for forced
multiplication. -/
theorem iso_map_forcedMul (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w})
    (a b : (forcedArith R).peano.carrier) :
    (universalForcingPeanoEquiv R S).toEquiv (forcedMul R a b)
      = forcedMul S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b) := by
  apply S.orbitEquivLogicNat.injective
  simp only [forcedMul, fold_iso_compat, Equiv.apply_symm_apply]

/-- **Order isomorphism.**  The canonical isomorphism preserves and reflects the
forced order. -/
theorem iso_map_forcedLe (R : LogicRealization.{0, v}) (S : LogicRealization.{0, w})
    (a b : (forcedArith R).peano.carrier) :
    forcedLe R a b
      ↔ forcedLe S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b) := by
  simp only [forcedLe, fold_iso_compat]

/-! ## Certificate -/

/-- **Universal Forcing ordered-semiring isomorphism certificate.**

For any two Law-of-Logic realizations, the canonical isomorphism between their
forced arithmetics preserves `0`, `1`, addition, multiplication, and the order.
Together with `UniversalForcingIsoCert` (zero/successor preservation and
uniqueness) this says the forced arithmetics are isomorphic as ordered
commutative semirings, canonically, across all realizations. -/
structure ForcedOrderedSemiringIsoCert where
  preserves_zero : ∀ (R S : LogicRealization.{0, 0}),
    (universalForcingPeanoEquiv R S).toEquiv (forcedZero R) = forcedZero S
  preserves_one : ∀ (R S : LogicRealization.{0, 0}),
    (universalForcingPeanoEquiv R S).toEquiv (forcedOne R) = forcedOne S
  preserves_add : ∀ (R S : LogicRealization.{0, 0}) (a b : (forcedArith R).peano.carrier),
    (universalForcingPeanoEquiv R S).toEquiv (forcedAdd R a b)
      = forcedAdd S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b)
  preserves_mul : ∀ (R S : LogicRealization.{0, 0}) (a b : (forcedArith R).peano.carrier),
    (universalForcingPeanoEquiv R S).toEquiv (forcedMul R a b)
      = forcedMul S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b)
  preserves_le : ∀ (R S : LogicRealization.{0, 0}) (a b : (forcedArith R).peano.carrier),
    forcedLe R a b
      ↔ forcedLe S ((universalForcingPeanoEquiv R S).toEquiv a)
          ((universalForcingPeanoEquiv R S).toEquiv b)

/-- The ordered-semiring isomorphism certificate is inhabited. -/
noncomputable def forcedOrderedSemiringIsoCert : ForcedOrderedSemiringIsoCert where
  preserves_zero := fun R S => iso_map_forcedZero R S
  preserves_one := fun R S => iso_map_forcedOne R S
  preserves_add := fun R S => iso_map_forcedAdd R S
  preserves_mul := fun R S => iso_map_forcedMul R S
  preserves_le := fun R S => iso_map_forcedLe R S

end UniversalForcing
end Foundation
end IndisputableMonolith
