import Mathlib

/-!
# Maximal Forcing: Primitive and Claim Language

This module starts the Maximal Forcing Closure program.

The target is:

* from distinction / Law of Logic, derive every invariant that is invariant
  across all admissible realizations;
* prove every remaining degree of freedom is either forced by a deeper
  admissibility condition or independent by countermodel.

This file only defines the primitive and claim language. It intentionally does
not assert the crown theorem.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- The primitive starting point for maximal forcing. The two constructors are
kept distinct so later modules can prove their equivalence rather than silently
identify them. -/
inductive Primitive where
  /-- Object-level distinction: `exists x y : K, x != y`. -/
  | distinction
  /-- Law-of-Logic realization, after the floor is non-vacuous. -/
  | lawOfLogic
  deriving DecidableEq, Repr

/-- A claim about realizations. The `label` is audit-facing metadata; the theorem
content is the predicate `holds`. -/
structure RealityClaim (R : Type u) where
  label : String
  holds : R -> Prop

/-- A claim is forced on an admissible class when it holds in every admissible
realization. -/
def Forced {R : Type u} (Admissible : Set R) (C : RealityClaim R) : Prop :=
  ∀ R0 : R, R0 ∈ Admissible -> C.holds R0

/-- A claim is independent over an admissible class when two admissible
realizations disagree on it. -/
def Independent {R : Type u} (Admissible : Set R) (C : RealityClaim R) : Prop :=
  ∃ R0 R1 : R,
    R0 ∈ Admissible ∧ R1 ∈ Admissible ∧ C.holds R0 ∧ ¬ C.holds R1

/-- A named selection principle for claims not yet forced on the current
admissible class. -/
structure SelectionPrinciple {R : Type u} (Admissible : Set R)
    (C : RealityClaim R) where
  label : String
  applies : Prop

/-- A claim is selected when it is not forced on the current admissible class but
does have a named selection principle. This is not final closure; it is an
honest tag that must later be strengthened to `Forced` or `Independent`. -/
def Selected {R : Type u} (Admissible : Set R) (C : RealityClaim R) : Prop :=
  ¬ Forced Admissible C ∧ Nonempty (SelectionPrinciple Admissible C)

end MaximalForcing
end Foundation
end IndisputableMonolith
