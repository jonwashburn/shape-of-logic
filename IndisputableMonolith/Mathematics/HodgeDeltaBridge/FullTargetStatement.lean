import IndisputableMonolith.Mathematics.HodgeDeltaBridge.EquationSelector

/-!
# δ-Hodge Bridge: full-target Hodge statement

The original classical statement interface quantified over `α` only after a
cycle-class map had chosen its `targetCohomology`, then required
`α.cohomologyClass = cl.targetCohomology`.  That is useful but too weak as a
referee-grade target: a bad proof can choose a tiny target and make most classes
non-compatible.

This file introduces an explicit full-target interface.  A
`FullRationalHodgeTarget X p` is the rational Hodge target for `(X,p)` together
with the class family that is supposed to be represented.  The final statement
quantifies over that target and over all its classes.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge

open HodgeClassicalStatement

universe u

/-- Full rational Hodge target for `(X,p)`: one ambient cohomology object and
the family of rational Hodge classes inside it.  This prevents the cycle-class
map from making the theorem vacuous by choosing a too-small target after the
classes are known. -/
structure FullRationalHodgeTarget
    (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ) where
  cohomology : RationalCohomologyClass X
  degree_eq : cohomology.degree = 2 * p
  hodgeClass : Type u
  classVector : hodgeClass → cohomology.carrier
  isHodge : IsRationalHodgeClass X p cohomology

/-- Convert a class in a full Hodge target into the existing bundled
`RationalHodgeClass` interface. -/
def FullRationalHodgeTarget.toRationalHodgeClass
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p)
    (α : H.hodgeClass) :
    RationalHodgeClass.{u, u} X p where
  cohomologyClass := H.cohomology
  classVector := H.classVector α
  isHodge := H.isHodge

/-- A cycle-class map is full-target-compatible when its target is the fixed
full Hodge cohomology object. -/
structure FullTargetCycleClassMap
    {X : SmoothProjectiveComplexVariety.{u}}
    {p : ℕ}
    (H : FullRationalHodgeTarget X p) where
  cl : CanonicalCycleClassMap.{u} X p
  target_eq : cl.targetCohomology = H.cohomology

/-- Full-target rational Hodge conjecture: for every full Hodge target, choose a
fixed cycle-class map into that target and represent every class in the target by
an algebraic cycle. -/
def FullTargetRationalHodgeStatement : Prop :=
  ∀ (X : SmoothProjectiveComplexVariety.{u})
    (p : ℕ)
    (H : FullRationalHodgeTarget X p),
    ∃ F : FullTargetCycleClassMap H,
      ∀ α : H.hodgeClass,
        ∃ Z : AlgebraicCycle.{u, u} X p,
          Nonempty (CycleClassEquals F.cl Z (H.toRationalHodgeClass α))

/-- Name for the final strengthened target. -/
def hodge_conjecture_unconditional_full_target : Prop :=
  FullTargetRationalHodgeStatement.{u}

end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith

