import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.AnalyticCounterexample
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.RealityStructure

/-!
# Counted-once comparison

This module formalises the phrase "each constituent comparison is counted
once."  Algebraically, for two component costs `u` and `v`, this means the
combiner is affine in each variable separately:

`a + b*u + c*v + d*u*v`.

Identity and symmetry then force the RCL-family form.
The resource-syntax and no-hidden-state bridges in sibling modules show how
this algebra arises from using each comparison resource once, with no hidden
route memory.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-- The RCL family predicate for a one-variable derived cost. -/
def RCLFamily (F : ℝ → ℝ) : Prop :=
  ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
    HasMultiplicativeConsistency F P ∧
    (∀ u v, P u v = 2 * u + 2 * v + c * u * v)

/-- A combiner is counted-once when it is affine in each input separately. -/
def CountedOnceCombiner (P : ℝ → ℝ → ℝ) : Prop :=
  ∃ a b c d : ℝ, ∀ u v, P u v = a + b * u + c * v + d * u * v

/-- A combiner is symmetric when exchanging its arguments does not change it. -/
def SymmetricCombiner (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ u v, P u v = P v u

/-- Counted-once composition for a comparison operator. -/
def CountedOnceComposition (C : ComparisonOperator) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    CountedOnceCombiner P ∧
    SymmetricCombiner P ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      derivedCost C (x * y) + derivedCost C (x / y) =
        P (derivedCost C x) (derivedCost C y))

/-- Counted-once composition is a special case of finite pairwise polynomial
closure. -/
theorem counted_once_to_finite_pairwise_polynomial
    (C : ComparisonOperator)
    (hCount : CountedOnceComposition C) :
    FinitePairwisePolynomialClosure C := by
  rcases hCount with ⟨P, ⟨a, b, c, d, hP⟩, hSym, hCons⟩
  refine ⟨P, ?_, hSym, hCons⟩
  refine ⟨a, b, c, d, 0, 0, ?_⟩
  intro u v
  rw [hP]
  ring

/-- Counted-once operative comparison forces the RCL family. -/
theorem counted_once_combiner_forces_rcl
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (hCount : CountedOnceComposition C) :
    RCLFamily (derivedCost C) := by
  rcases hCount with ⟨P, ⟨a, b, c, d, hP⟩, hSym, hCons⟩
  rcases rcl_direct_theorem C hOp P a b c d hP hSym hCons with
    ⟨c0, hRCL⟩
  exact ⟨P, c0, hCons, hRCL⟩

/-- Continuous non-counted composition is not enough to force the RCL family:
the quartic-log combiner has a square-root interaction term. -/
theorem double_counting_not_allowed :
    ¬ ∃ c : ℝ, ∀ a b : ℝ, 0 < a → 0 < b →
      quarticCombiner a b = 2 * a + 2 * b + c * a * b :=
  quarticCombiner_not_rcl_family

/-- Analytic reparameterisation is not counted-once: it changes the polynomial
degree of the combiner. -/
theorem analytic_reparameterization_not_counted_once :
    ¬ ∃ c : ℝ, ∀ s : ℝ, reparamDiagonal s = degreeTwoDiagonal c s :=
  reparam_diagonal_not_degree_two

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
