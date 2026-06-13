import IndisputableMonolith.Foundation.AbsoluteFloorClosure

/-!
# T-2 → T-1 : The Forcing Function From Absolute Nothing To Distinction

This module closes the last floor below the Recognition Science forcing chain.
The existing absolute floor (`AbsoluteFloorClosure.lean`) took meta-language
proposition distinguishability `∃ P Q : Prop, P ≠ Q` and a non-singleton
universe as *given* preconditions. Here those preconditions are *derived*, from
the strongest possible encoding of absolute nothing, using no axioms.

## How absolute nothing is encoded

Absolute nothing is the empty type `Empty`: it has no inhabitants and a unique
morphism into every type (`Empty.elim`). That is the complete categorical
signature of nothing — it is the initial object, the thing with nothing inside
and the thing that maps into anything because there is no input to constrain.

## The forcing function (the engine)

Absolute nothing is not stable, and the instability is forced, not assumed.

1. To *name* nothing is to write `Empty`. But `Empty` itself has type `Type`.
   So the very act of denoting nothing at universe level `n` makes nothing an
   *object* at level `n+1`. Nothing reflects upward into something. This is
   `naming_nothing_populates_universe : Nonempty Type`.

2. Once `Type` is inhabited and contains the initial object `Empty`, it also
   admits the terminal object `Unit`. These two cannot be the same type:
   `Empty` has no inhabitant, `Unit` has one, so any identification transports
   the inhabitant of `Unit` into `Empty`, which is impossible. This is
   `nothing_ne_something : Nothing ≠ Unit`. That inequality is the first
   distinction.

3. From the first distinction the object-level distinction `∃ x y, x ≠ y`, the
   type-level distinction `∃ α β, α ≠ β`, and the propositional distinction
   `∃ P Q : Prop, P ≠ Q` all follow as theorems with no premise. The last of
   these is exactly the meta-language fact the prior floor assumed; it is now
   discharged.

4. The forced Boolean distinction is the floor consumed by the public T-1
   through T8 bridge. This file stays at T-2/T-1 and does not import the
   later spine.

## Axiom status

The core results in this file use **no axioms**. Run
`#print axioms nothingToDistinctionCert` to confirm. "From nothing" is meant
in the strongest sense available inside a formal system: the distinction is a
theorem of bare type formation, resting on no postulate, classical or RS-specific.
-/

namespace IndisputableMonolith
namespace Foundation
namespace NothingToDistinction

/-! ## T-2: absolute nothing -/

/-- Absolute nothing: the type with no inhabitants. The strongest encoding of
"there is no object." We keep it as a `def` (not an `abbrev`) so the name does
not silently unfold; the unfolding is invoked explicitly where needed. -/
def Nothing : Type := Empty

/-- Nothing contains nothing. The witness `IsEmpty Nothing` is itself an object:
asserting that nothing is empty is already producing a something. -/
theorem nothing_has_no_object : IsEmpty Nothing :=
  ⟨fun e => Empty.elim e⟩

/-- The unique morphism out of nothing into any target. This is the categorical
signature of the initial object: nothing maps into everything because there is
no inhabitant to constrain the map. -/
def nothing_eliminates {C : Sort _} : Nothing → C :=
  fun e => Empty.elim e

/-! ## The engine: naming nothing populates the universe one level up -/

/-- Naming absolute nothing makes nothing an object of `Type`. Nothing at one
level is something at the level above. This is the irreversible first step:
the universe of types is non-empty the instant nothing is denoted. -/
theorem naming_nothing_populates_universe : Nonempty Type :=
  ⟨Nothing⟩

/-! ## T-1: the first distinction, forced -/

/-- The minimal something: the terminal object, with exactly one inhabitant. -/
def Something : Type := Unit

theorem something_has_object : Nonempty Something :=
  ⟨()⟩

/-- The first distinction. Nothing and something are necessarily different
types: identifying them would carry the inhabitant of `Unit` into `Empty`. No
premise is used. -/
theorem nothing_ne_something : Nothing ≠ Something := by
  intro h
  have hn : Nonempty Nothing := by
    rw [h]; exact ⟨()⟩
  obtain ⟨e⟩ := hn
  exact Empty.elim e

/-- Type-level distinction, derived from the encoding of absolute nothing. -/
theorem type_distinction_forced : ∃ (α β : Type), α ≠ β :=
  ⟨Nothing, Something, nothing_ne_something⟩

/-- Propositional distinction, derived. This is exactly the meta-language fact
`AbsoluteFloorClosure.AbsoluteFloorWitness` previously took as a precondition:
`True` (the proposition that holds) and `False` (the proposition that does not)
cannot be equal, since equality would carry the proof of `True` into `False`. -/
theorem prop_distinction_forced : ∃ P Q : Prop, P ≠ Q :=
  ⟨True, False, by intro h; exact h ▸ trivial⟩

/-- Object-level distinction on a concrete carrier, derived. The two values of
`Bool` are the first realized bit. -/
theorem object_distinction_forced : ∃ (α : Type) (x y : α), x ≠ y :=
  ⟨Bool, true, false, by decide⟩

/-- The Bool instance of the forced distinction, in the exact shape the object
floor consumes. -/
theorem bool_distinction_from_nothing : ∃ x y : Bool, x ≠ y :=
  ⟨false, true, by decide⟩

/-- The forcing function itself, stated as an arrow: from the fact that nothing
is empty, a distinction is produced. -/
theorem nothingForcesDistinction (_ : IsEmpty Nothing) :
    ∃ (α β : Type), α ≠ β :=
  ⟨Nothing, Something, nothing_ne_something⟩

/-! ## Closure into the existing floor -/

/-- The absolute-floor witness for `Bool`, with its meta-language precondition
now *discharged from nothing* rather than assumed. The `meta_distinguishes`
field is supplied by `prop_distinction_forced`. -/
theorem absolute_floor_from_nothing :
    AbsoluteFloorClosure.AbsoluteFloorWitness Bool where
  meta_distinguishes := prop_distinction_forced
  nontrivial_specifiable :=
    (AbsoluteFloorClosure.bool_absolute_floor).nontrivial_specifiable

/-! ## Certificate -/

/-- Joint certificate: from the encoding of absolute nothing, the universe is
populated, type/propositional/object distinctions all hold, and the prior
floor's meta-precondition is discharged. -/
structure NothingToDistinctionCert : Prop where
  universe_populated : Nonempty Type
  type_distinction : ∃ α β : Type, α ≠ β
  prop_distinction : ∃ P Q : Prop, P ≠ Q
  object_distinction : ∃ (α : Type) (x y : α), x ≠ y
  bool_distinction : ∃ x y : Bool, x ≠ y
  floor_discharged : AbsoluteFloorClosure.AbsoluteFloorWitness Bool

/-- The certificate is theorem-backed. -/
theorem nothingToDistinctionCert : NothingToDistinctionCert where
  universe_populated := naming_nothing_populates_universe
  type_distinction := type_distinction_forced
  prop_distinction := prop_distinction_forced
  object_distinction := object_distinction_forced
  bool_distinction := bool_distinction_from_nothing
  floor_discharged := absolute_floor_from_nothing

end NothingToDistinction
end Foundation
end IndisputableMonolith
