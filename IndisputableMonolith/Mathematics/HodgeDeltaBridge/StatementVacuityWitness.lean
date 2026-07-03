import IndisputableMonolith.Mathematics.HodgeClassicalStatement

/-!
# δ-Hodge Bridge: statement-vacuity witness (RED-FLAG GUARD)

**This module proves that the project's classical Hodge statement is VACUOUS.**
It is a guard, not a result. Read the warning before citing anything here.

`HodgeClassicalStatement.RationalHodgeConjectureStatement` is
```
∀ X p, ∃ cl : CanonicalCycleClassMap X p,
  ∀ α (_ : α.cohomologyClass = cl.targetCohomology),
    ∃ Z, Nonempty (CycleClassEquals cl Z α).
```
The prover supplies `cl`, and `cl` supplies its own `targetCohomology`
(an *arbitrary* ℚ-module) and its own `cycleClass` (an *arbitrary* additive
map). Nothing ties `targetCohomology` to the actual `H^{2p}(X,ℚ)` of `X`, and
nothing ties `cycleClass` to the actual geometric cycle class. So the prover can
pick the zero module `PUnit` as the target and discharge the whole statement.
`rational_hodge_statement_is_vacuous` below is that discharge.

Consequences:

* Every conditional theorem in the project of the form
  `(… targets …) → RationalHodgeConjectureStatement` is vacuous: its conclusion
  is provable outright, independent of the hypotheses. Discharging those
  targets proves nothing about Hodge.
* The strengthened `HodgeDeltaBridge.FullTargetRationalHodgeStatement` supplies
  the cohomology externally, which blocks *this* exact zero-module trick. But it
  still lets the prover pick `cycleClass` as an arbitrary additive map out of the
  hollow `AlgebraicCycle` type (whose `support`/`irreducibleComponent` are
  arbitrary `Type u`, and whose `component_irreducible` is a self-certified
  `Prop` set to `True`). A surjective additive `cycleClass` therefore exists, so
  the full-target statement is also not referee-grade. (That direction is argued
  here, not yet Lean-proven; the base-statement vacuity below is Lean-proven.)

A genuine referee-grade statement must (a) fix `targetCohomology` to the real
`H^{2p}(X,ℚ)` from Mathlib, (b) fix `cycleClass` to the canonical geometric
cycle class map, and (c) make `AlgebraicCycle` carry real algebraic subvariety
content. None of those hold today.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge
namespace VacuityWitness

open HodgeClassicalStatement

universe u

/-- The zero cohomology object: carrier `PUnit`, every operation trivial. Not a
real cohomology group; just enough to satisfy the unconstrained interface. -/
def trivialCohomology (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) :
    RationalCohomologyClass.{u} X where
  degree := 2 * p
  carrier := PUnit.{u+1}
  zero := ⟨⟩
  add := fun _ _ => ⟨⟩
  neg := fun _ => ⟨⟩
  smul := fun _ _ => ⟨⟩
  add_assoc := by intros; exact Subsingleton.elim _ _
  add_comm := by intros; exact Subsingleton.elim _ _
  add_zero := by intros; exact Subsingleton.elim _ _
  add_neg := by intros; exact Subsingleton.elim _ _
  smul_one := by intros; exact Subsingleton.elim _ _
  smul_zero := by intros; exact Subsingleton.elim _ _
  smul_add := by intros; exact Subsingleton.elim _ _
  mul_smul := by intros; exact Subsingleton.elim _ _
  add_smul := by intros; exact Subsingleton.elim _ _
  zero_smul := by intros; exact Subsingleton.elim _ _
  rationalLattice := PUnit.{u+1}
  rationalCoordinates := fun _ => ⟨⟩

/-- The prover-chosen cycle class map into the zero module. -/
def trivialCycleClassMap (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) :
    CanonicalCycleClassMap.{u} X p where
  targetCohomology := trivialCohomology X p
  degree_eq := rfl
  cycleClass := fun _ => ⟨⟩
  map_zero := by intros; rfl
  map_add := by intros; rfl
  map_smul := by intros; rfl

/-- A throwaway inhabitant of the hollow `AlgebraicCycle` type. -/
def trivialCycle (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) :
    AlgebraicCycle.{u, u} X p where
  support := PUnit.{u+1}
  irreducibleComponent := PUnit.{u+1}
  fintype_components := inferInstance
  componentMap := fun _ => ⟨⟩
  coefficient := fun _ => 0
  embedding_in_carrier := fun _ => Classical.choice X.carrier_nonempty
  codimension := fun _ => p
  codimension_eq := fun _ => rfl
  component_irreducible := fun _ => True
  component_irreducible_holds := fun _ => trivial

/-- **The project's classical Hodge statement is vacuous.** It is discharged by
a zero-module target with no relation to the actual cohomology of `X`. This is a
red-flag guard: it means the statement must be strengthened before any proof of
it counts as a proof of the Hodge conjecture. -/
theorem rational_hodge_statement_is_vacuous : RationalHodgeConjectureStatement.{u} := by
  intro X p
  haveI : Subsingleton (trivialCycleClassMap X p).targetCohomology.carrier :=
    (inferInstance : Subsingleton PUnit.{u+1})
  refine ⟨trivialCycleClassMap X p, ?_⟩
  intro α hcompat
  refine ⟨trivialCycle X p, ⟨?_⟩⟩
  exact {
    cohomologyCompatible := hcompat
    classEquality := Subsingleton.elim _ _
  }

end VacuityWitness
end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith
