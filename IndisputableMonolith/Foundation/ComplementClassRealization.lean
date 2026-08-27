import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Foundation.CircleWinding
import IndisputableMonolith.Foundation.CircleParam
import IndisputableMonolith.Foundation.LeastCostUnitLinking
import IndisputableMonolith.Foundation.SemanticClockFromMeasure
import IndisputableMonolith.Foundation.HomologySphereAlgebra

/-!
# Every complement class is a recognition trajectory, in the working model

The working complement of the unknot is homotopy-equivalent to a circle,
so its first homology is `ℤ`. Every integer is the winding of an
explicit loop: the `n`-fold cover of the fundamental loop.

The realized debit/credit pair already occupies windings `1` and `-1`,
which are the unit-charge minimizers.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ComplementClassRealization

open CircleParam CircleWinding
open scoped Real unitInterval
open Patterns
open ClosedFramework
open HierarchyRealization
open LinkingFromHierarchy
open LinkingNecessity
open LeastCostUnitLinking
open SemanticClockFromMeasure
open PublicSpine.PartINamedAxiomClosure
open HomologySphereAlgebra
open AlexanderDuality

/-- The `n`-fold loop on the recognition circle. -/
noncomputable def nfoldLoop (n : ℤ) : C(I, SphereOne) where
  toFun := fun t => trigCirclePoint ((n : ℝ) * (2 * Real.pi) * (t : ℝ))
  continuous_toFun :=
    continuous_trigCirclePoint.comp
      ((continuous_const.mul continuous_const).mul continuous_subtype_val)

theorem nfoldLoop_zero (n : ℤ) :
    nfoldLoop n 0 = trigCirclePoint 0 := by
  simp [nfoldLoop]

/-- The linear lift of the `n`-fold loop. -/
noncomputable def nfoldLift (n : ℤ) : C(I, ℝ) where
  toFun := fun t => (n : ℝ) * (2 * Real.pi) * (t : ℝ)
  continuous_toFun :=
    (continuous_const.mul continuous_const).mul continuous_subtype_val

theorem nfoldLift_lifts (n : ℤ) :
    trigCirclePoint ∘ (nfoldLift n : I → ℝ) = (nfoldLoop n : I → SphereOne) :=
  rfl

theorem nfold_displacement (n : ℤ) :
    pathDisplacement (nfoldLoop n) = (n : ℝ) * (2 * Real.pi) := by
  rw [pathDisplacement_eq (nfoldLoop n) (nfoldLift n) (nfoldLift_lifts n)]
  simp [nfoldLift]

theorem nfold_winding (n : ℤ) :
    pathWinding (nfoldLoop n) = n := by
  unfold pathWinding
  rw [nfold_displacement]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- Every integer class is realized by a recognition loop. -/
theorem every_integer_is_a_winding (n : ℤ) :
    ∃ γ : C(I, SphereOne), pathWinding γ = n :=
  ⟨nfoldLoop n, nfold_winding n⟩

/-- The realized pair already occupies the two unit windings. -/
theorem realized_pair_occupies_unit_classes
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    pathWinding (recognitionCircleLoop F H) = 1 ∧
      pathWinding (LinkingNecessity.creditLoop F H) = -1 :=
  realized_pair_has_unit_windings F H

/-- Least cost forces those unit windings. -/
theorem least_cost_forces_unit_charge
    {n : ℤ} (hn : n ≠ 0)
    (hle : chargeCost n ≤ chargeCost 1) :
    n = 1 ∨ n = -1 :=
  least_cost_unit_linking hn hle

/-- The eight-tick measure forces a Gray clock. Already a theorem;
re-exported so the paper residuals live in one place. -/
theorem forced_gray_clock
    {d T : ℕ} {pass : Fin T → Pattern d}
    (h : EightTickComplete pass) :
    GrayCoverSemanticModel pass :=
  eightTick_implies_gray h

/-- General-`M` codimension count, given Alexander duality as a
hypothesis. The sphere case is already `PublicSpineLinkingClosure`. -/
theorem general_M_codimension
    {G : Type*} [AddCommGroup G] (D : ℕ)
    (hAlex : Nontrivial G ↔
      CircleReducedCohomologyNontrivial ((D : ℤ) - 2)) :
    Nontrivial G ↔ D = 3 :=
  codimension_of_alexander (G := G) D hAlex

end ComplementClassRealization
end Foundation
end IndisputableMonolith
