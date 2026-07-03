import IndisputableMonolith.Foundation.UniversalForcing

/-!
  CanonicalIso.lean

  Universal Forcing, Part II (arithmetic-extraction layer).

  The existing Universal Forcing spine (`UniversalForcing.universal_forcing`,
  `ArithmeticOf.equivOfInitial`) produces a *bare carrier bijection*
  `(arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier` between the
  forced arithmetics of any two Law-of-Logic realizations.  A bijection between
  two number systems is weaker than an isomorphism of number systems: it does
  not, on its face, respect zero or successor.

  This module closes that gap at the Peano-algebra layer:

  1. `equivOfInitial_map_zero` / `equivOfInitial_map_step`: the universal
     forcing bijection *does* send zero to zero and commute with the step map,
     so it is a homomorphism of Peano algebras, not merely a set bijection.
  2. `PeanoEquiv`: a bundled structure-preserving isomorphism of Peano objects.
  3. `peanoEquiv_unique`: any two structure-preserving isomorphisms between the
     same pair of forced arithmetics have the *same* underlying function.  This
     is the "canonical" in "canonically equivalent": the isomorphism is not
     merely some isomorphism, it is the unique one.
  4. `universalForcingIsoCert`: the package, quantified over all realizations.

  Everything is stated at the `{0, 0}` realization universe used throughout the
  rest of the Universal Forcing program (positive-ratio, discrete-Boolean,
  modular, categorical, etc. realizations are all `LogicRealization.{0, 0}`), so
  the Peano carriers all live in `Type 0` and the file is universe-monomorphic.

  Honest scope.  This upgrades the invariant from `≃` to *unique Peano-algebra
  isomorphism*.  Preservation of the *ring* operations `+`, `×` and the order
  `≤` is the next step and is not proved here, because `PeanoObject` in
  `ArithmeticOf.lean` carries only `zero` and `step`.  The richer
  ordered-semiring iso is the remaining work toward the full Part II crown.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing

open ArithmeticFromLogic

universe u v w

/-! ## Universe-pinned forced arithmetic

`ArithmeticOf` carries five universe parameters: two for the realization carrier
and cost, one for the forced Peano carrier, and two for the `IsInitial` lift and
uniqueness target universes.  The bare `arithmeticOf R` leaves the last two free,
so each textual occurrence spawns fresh unpinned universe metavariables.  This
abbreviation pins every `ArithmeticOf` universe to the single realization
universe `u`, which is exactly the situation in the Universal Forcing program
(orbits live in `Type u`).  Using it throughout keeps the file
universe-monomorphic in spirit while staying polymorphic in `u, v`. -/

/-- The forced arithmetic of a realization, with all `ArithmeticOf` universes
pinned to the realization's own carrier universe. -/
abbrev forcedArith (R : LogicRealization.{u, v}) :
    ArithmeticOf.{u, v, u, u, u} R :=
  arithmeticOf R

/-! ## Bundled structure-preserving isomorphism of Peano objects -/

/-- A structure-preserving isomorphism of Peano objects: an equivalence of
carriers that respects zero and step. -/
structure PeanoEquiv (A B : PeanoObject.{u}) where
  toEquiv : A.carrier ≃ B.carrier
  map_zero : toEquiv A.zero = B.zero
  map_step : ∀ x, toEquiv (A.step x) = B.step (toEquiv x)

namespace PeanoEquiv

/-- The underlying Peano homomorphism of a structure-preserving isomorphism. -/
def toHom {A B : PeanoObject.{u}} (e : PeanoEquiv A B) : PeanoObject.Hom A B where
  toFun := e.toEquiv
  map_zero := e.map_zero
  map_step := e.map_step

end PeanoEquiv

/-! ## The universal forcing bijection is a Peano homomorphism

`R` and `S` share the carrier universe `u` (their cost universes `v, w` are
independent), so both forced Peano carriers live in `Type u` and the
canonicality argument's `uniq` call typechecks.  All `ArithmeticOf` universes
are pinned through `forcedArith`. -/

/-- The universal forcing bijection sends the forced zero to the forced zero. -/
theorem equivOfInitial_map_zero (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w}) :
    (ArithmeticOf.equivOfInitial (forcedArith R) (forcedArith S))
        (forcedArith R).peano.zero
      = (forcedArith S).peano.zero :=
  ((forcedArith R).initial.lift (forcedArith S).peano).map_zero

/-- The universal forcing bijection commutes with the forced step map. -/
theorem equivOfInitial_map_step (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w})
    (x : (forcedArith R).peano.carrier) :
    (ArithmeticOf.equivOfInitial (forcedArith R) (forcedArith S))
        ((forcedArith R).peano.step x)
      = (forcedArith S).peano.step
          ((ArithmeticOf.equivOfInitial (forcedArith R) (forcedArith S)) x) :=
  ((forcedArith R).initial.lift (forcedArith S).peano).map_step x

/-- The canonical structure-preserving isomorphism between the forced
arithmetics of two realizations. This packages the universal forcing bijection
together with proofs that it respects zero and step. -/
noncomputable def universalForcingPeanoEquiv
    (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w}) :
    PeanoEquiv (forcedArith R).peano (forcedArith S).peano where
  toEquiv := ArithmeticOf.equivOfInitial (forcedArith R) (forcedArith S)
  map_zero := equivOfInitial_map_zero R S
  map_step := equivOfInitial_map_step R S

@[simp] theorem universalForcingPeanoEquiv_toEquiv
    (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w}) :
    (universalForcingPeanoEquiv R S).toEquiv
      = ArithmeticOf.equivOfInitial (forcedArith R) (forcedArith S) :=
  rfl

/-! ## Canonicality: the structure-preserving isomorphism is unique -/

/-- **Canonicality.**  Any two structure-preserving isomorphisms between the
forced arithmetics of two realizations have the same underlying function.  The
isomorphism furnished by Universal Forcing is therefore the unique one. -/
theorem peanoEquiv_unique (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w})
    (e₁ e₂ : PeanoEquiv (forcedArith R).peano (forcedArith S).peano) :
    (e₁.toEquiv : (forcedArith R).peano.carrier → (forcedArith S).peano.carrier)
      = (e₂.toEquiv : (forcedArith R).peano.carrier → (forcedArith S).peano.carrier) :=
  (forcedArith R).initial.uniq (forcedArith S).peano e₁.toHom e₂.toHom

/-- Any Peano homomorphism into the target forced arithmetic equals the
universal forcing map: there is exactly one Peano homomorphism, and it is an
isomorphism. -/
theorem hom_eq_universalForcing (R : LogicRealization.{u, v}) (S : LogicRealization.{u, w})
    (f : PeanoObject.Hom (forcedArith R).peano (forcedArith S).peano) :
    f.toFun = (universalForcingPeanoEquiv R S).toEquiv :=
  (forcedArith R).initial.uniq (forcedArith S).peano f
    ((forcedArith R).initial.lift (forcedArith S).peano)

/-! ## Certificate, quantified over all realizations -/

/-- **Universal Forcing isomorphism certificate.**

For any two Law-of-Logic realizations, there is a canonical structure-preserving
isomorphism between their forced arithmetics, and that isomorphism is unique. -/
structure UniversalForcingIsoCert where
  /-- The canonical Peano-algebra isomorphism between any two forced arithmetics. -/
  iso : ∀ R S : LogicRealization.{0, 0},
    PeanoEquiv (forcedArith R).peano (forcedArith S).peano
  /-- That isomorphism is unique as a structure-preserving map. -/
  unique : ∀ (R S : LogicRealization.{0, 0})
      (e₁ e₂ : PeanoEquiv (forcedArith R).peano (forcedArith S).peano),
      (e₁.toEquiv : (forcedArith R).peano.carrier → (forcedArith S).peano.carrier)
        = e₂.toEquiv

/-- The certificate is inhabited by the canonical iso and its uniqueness. -/
noncomputable def universalForcingIsoCert : UniversalForcingIsoCert where
  iso := fun R S => universalForcingPeanoEquiv R S
  unique := fun R S => peanoEquiv_unique R S

end UniversalForcing
end Foundation
end IndisputableMonolith
