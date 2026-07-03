import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Cost.JcostLogic

/-!
  LogicAsFunctionalEquationLogic.lean

  Law-of-Logic comparison operators on recovered reals.

  This is the recovered-real mirror of
  `Foundation.LogicAsFunctionalEquation`.  The analytic regularity fields
  (continuity and the polynomial-combiner theorem surface) are transported
  through `LogicReal.toReal`; the local structural fields (identity,
  symmetry, scale invariance, non-triviality) are stated directly over
  `LogicReal`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquationLogic

open RealsFromLogic RealsFromLogic.LogicReal
open LogicAsFunctionalEquation
open Cost.JcostLogic

noncomputable section

/-! ## Recovered-real comparison operators -/

/-- A comparison operator over recovered reals. -/
abbrev ComparisonOperatorL := LogicReal → LogicReal → LogicReal

/-- Derived one-argument cost over recovered reals. -/
@[simp] def derivedCostL (C : ComparisonOperatorL) : LogicReal → LogicReal :=
  fun r => C r (fromReal 1)

/-- Transport a recovered-real comparison operator to the existing real
comparison-operator surface. -/
def transportComparison (C : ComparisonOperatorL) :
    LogicAsFunctionalEquation.ComparisonOperator :=
  fun x y => toReal (C (fromReal x) (fromReal y))

/-- Identity over recovered reals. -/
def IdentityL (C : ComparisonOperatorL) : Prop :=
  ∀ x : LogicReal, (0 : LogicReal) < x → C x x = fromReal 0

/-- Non-contradiction / reciprocal symmetry over recovered reals. -/
def NonContradictionL (C : ComparisonOperatorL) : Prop :=
  ∀ x y : LogicReal, (0 : LogicReal) < x → (0 : LogicReal) < y → C x y = C y x

/-- Scale invariance over recovered reals. -/
def ScaleInvariantL (C : ComparisonOperatorL) : Prop :=
  ∀ x y lam : LogicReal, (0 : LogicReal) < x → (0 : LogicReal) < y → (0 : LogicReal) < lam →
    C (lam * x) (lam * y) = C x y

/-- Non-triviality over recovered reals. -/
def NonTrivialL (C : ComparisonOperatorL) : Prop :=
  ∃ x : LogicReal, (0 : LogicReal) < x ∧ derivedCostL C x ≠ fromReal 0

/-- Recovered-real Law of Logic. The structural fields are native to
`LogicReal`; the analytic/polynomial regularity surface is explicitly
transported to the already-verified real theorem. -/
structure SatisfiesLawsOfLogicL (C : ComparisonOperatorL) : Prop where
  identity : IdentityL C
  non_contradiction : NonContradictionL C
  scale_invariant : ScaleInvariantL C
  non_trivial : NonTrivialL C
  transported_real_laws :
    LogicAsFunctionalEquation.SatisfiesLawsOfLogic (transportComparison C)

/-! ## Structural transport lemmas -/

theorem identityL_to_real (C : ComparisonOperatorL) (h : IdentityL C) :
    LogicAsFunctionalEquation.Identity (transportComparison C) := by
  intro x hx
  unfold transportComparison
  have hxL : (0 : LogicReal) < fromReal x := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]
    exact hx
  have hL := congrArg toReal (h (fromReal x) hxL)
  simpa [toReal_fromReal] using hL

theorem nonContradictionL_to_real (C : ComparisonOperatorL) (h : NonContradictionL C) :
    LogicAsFunctionalEquation.NonContradiction (transportComparison C) := by
  intro x y hx hy
  unfold transportComparison
  have hxL : (0 : LogicReal) < fromReal x := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hx
  have hyL : (0 : LogicReal) < fromReal y := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hy
  exact congrArg toReal (h (fromReal x) (fromReal y) hxL hyL)

theorem scaleInvariantL_to_real (C : ComparisonOperatorL) (h : ScaleInvariantL C) :
    LogicAsFunctionalEquation.ScaleInvariant (transportComparison C) := by
  intro x y lam hx hy hlam
  unfold transportComparison
  have hxL : (0 : LogicReal) < fromReal x := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hx
  have hyL : (0 : LogicReal) < fromReal y := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hy
  have hlamL : (0 : LogicReal) < fromReal lam := by
    rw [lt_iff_toReal_lt, toReal_zero, toReal_fromReal]; exact hlam
  have hmulx : fromReal lam * fromReal x = fromReal (lam * x) := by
    rw [eq_iff_toReal_eq]; simp [toReal_fromReal]
  have hmuly : fromReal lam * fromReal y = fromReal (lam * y) := by
    rw [eq_iff_toReal_eq]; simp [toReal_fromReal]
  have hL := h (fromReal x) (fromReal y) (fromReal lam) hxL hyL hlamL
  rw [hmulx, hmuly] at hL
  exact congrArg toReal hL

theorem nonTrivialL_to_real (C : ComparisonOperatorL) (h : NonTrivialL C) :
    LogicAsFunctionalEquation.NonTrivial (transportComparison C) := by
  rcases h with ⟨x, hx, hxne⟩
  refine ⟨toReal x, ?_, ?_⟩
  · simpa [lt_iff_toReal_lt] using hx
  · intro hzero
    apply hxne
    rw [eq_iff_toReal_eq]
    have hzero' : toReal (C (fromReal (toReal x)) (fromReal 1)) = 0 := by
      simpa [transportComparison, LogicAsFunctionalEquation.derivedCost, toReal_fromReal]
        using hzero
    rw [fromReal_toReal] at hzero'
    simpa [derivedCostL, toReal_fromReal] using hzero'

/-- The recovered-real Law of Logic transports to the existing real theorem
surface. -/
theorem lawsL_to_real {C : ComparisonOperatorL} (h : SatisfiesLawsOfLogicL C) :
    LogicAsFunctionalEquation.SatisfiesLawsOfLogic (transportComparison C) :=
  h.transported_real_laws

/-- RCL is forced for recovered-real logic, by transport through the existing
real theorem. -/
theorem RCL_is_unique_functional_form_of_logicL
    (C : ComparisonOperatorL) (h : SatisfiesLawsOfLogicL C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      DAlembert.Inevitability.HasMultiplicativeConsistency
        (LogicAsFunctionalEquation.derivedCost (transportComparison C)) P ∧
      (∀ u v, P u v = 2*u + 2*v + c*u*v) :=
  LogicAsFunctionalEquation.RCL_is_unique_functional_form_of_logic
    (transportComparison C) (lawsL_to_real h)

end

end LogicAsFunctionalEquationLogic
end Foundation
end IndisputableMonolith
