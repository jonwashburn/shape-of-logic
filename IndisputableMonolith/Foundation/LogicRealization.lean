import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.ArithmeticFromLogic

/-!
  LogicRealization.lean

  Setting-independent interface for the Universal Forcing program.

  The point of this file is not to finish Universal Forcing in one stroke.
  It creates the common object into which different Law-of-Logic settings
  (continuous positive ratios, discrete propositions, categorical settings)
  can be mapped.
-/

namespace IndisputableMonolith
namespace Foundation

open LogicAsFunctionalEquation
open ArithmeticFromLogic

universe u v

/-- A Law-of-Logic realization: a carrier with comparison cost, identity
element, step/generator action, and the structural laws needed by the
Universal Forcing program.

The fields are intentionally lean: each realization supplies its own topology,
order, category, or discrete structure through the propositions carried here.
The invariant target is not the ambient carrier; it is the arithmetic object
extracted from the identity/step data. -/
structure LogicRealization where
  Carrier : Type u
  Cost : Type v
  zeroCost : Zero Cost
  compare : Carrier → Carrier → Cost
  zero : Carrier
  step : Carrier → Carrier
  Orbit : Type u
  orbitZero : Orbit
  orbitStep : Orbit → Orbit
  interpret : Orbit → Carrier
  interpret_zero : interpret orbitZero = zero
  interpret_step : ∀ n : Orbit, interpret (orbitStep n) = step (interpret n)
  orbit_no_confusion : ∀ n : Orbit, orbitZero ≠ orbitStep n
  orbit_step_injective : Function.Injective orbitStep
  orbit_induction :
    ∀ P : Orbit → Prop,
      P orbitZero →
      (∀ n, P n → P (orbitStep n)) →
      ∀ n, P n
  orbitEquivLogicNat : Orbit ≃ LogicNat
  orbitEquiv_zero : orbitEquivLogicNat orbitZero = LogicNat.zero
  orbitEquiv_step : ∀ n : Orbit,
    orbitEquivLogicNat (orbitStep n) = LogicNat.succ (orbitEquivLogicNat n)
  identity : ∀ x : Carrier, compare x x = 0
  nonContradiction : ∀ x y : Carrier, compare x y = compare y x
  excludedMiddle : Prop
  composition : Prop
  actionInvariant : Prop
  nontrivial : ∃ x : Carrier, compare x zero ≠ 0

attribute [instance] LogicRealization.zeroCost

namespace LogicRealization

/-- The identity-step shadow of a realization. This is the data from which
`ArithmeticOf` extracts arithmetic. -/
def hasIdentityStep (R : LogicRealization) : Prop :=
  ∃ x : R.Carrier, R.compare x R.zero ≠ 0

theorem hasIdentityStep_of_nontrivial (R : LogicRealization) :
    R.hasIdentityStep :=
  R.nontrivial

/-- A realization whose internal forced arithmetic embeds faithfully into its
ambient carrier. Periodic realizations, such as modular carriers, need not
satisfy this; their internal orbit is still free while the carrier
interpretation is periodic. -/
structure FaithfulArithmeticInterpretation (R : LogicRealization) : Prop where
  injective : Function.Injective R.interpret
  zero_step_noncollapse : ∀ n : R.Orbit, R.interpret R.orbitZero ≠ R.interpret (R.orbitStep n)

/-- Fold over `LogicNat` into the positive-ratio carrier for the selected
non-trivial generator. -/
noncomputable def positiveRatioOrbitInterpret
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    LogicNat → {x : ℝ // 0 < x}
  | LogicNat.identity => ⟨1, one_pos⟩
  | LogicNat.step n =>
      let γ : ℝ := Classical.choose h.non_trivial
      let x := positiveRatioOrbitInterpret C h n
      ⟨γ * x.1, mul_pos (Classical.choose_spec h.non_trivial).1 x.2⟩

@[simp] theorem positiveRatioOrbitInterpret_val
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) (n : LogicNat) :
    (positiveRatioOrbitInterpret C h n).1 =
      ArithmeticFromLogic.embed (ArithmeticFromLogic.generatorOfLawsOfLogic h) n := by
  induction n with
  | identity =>
      rfl
  | step n ih =>
      simp [positiveRatioOrbitInterpret, ArithmeticFromLogic.embed, ih,
        ArithmeticFromLogic.generatorOfLawsOfLogic]

/-- Continuous positive-ratio Law-of-Logic realizations embed into the
setting-independent interface. -/
noncomputable def ofPositiveRatioComparison
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    LogicRealization where
  Carrier := {x : ℝ // 0 < x}
  Cost := ℝ
  zeroCost := inferInstance
  compare := fun x y => C x.1 y.1
  zero := ⟨1, one_pos⟩
  step := fun x =>
    let γ : ℝ := Classical.choose h.non_trivial
    ⟨γ * x.1, mul_pos (Classical.choose_spec h.non_trivial).1 x.2⟩
  Orbit := LogicNat
  orbitZero := LogicNat.zero
  orbitStep := LogicNat.succ
  interpret := positiveRatioOrbitInterpret C h
  interpret_zero := rfl
  interpret_step := by
    intro n
    rfl
  orbit_no_confusion := by
    intro n hzero
    exact LogicNat.zero_ne_succ n hzero
  orbit_step_injective := LogicNat.succ_injective
  orbit_induction := by
    intro P h0 hs n
    exact LogicNat.induction (motive := P) h0 hs n
  orbitEquivLogicNat := Equiv.refl LogicNat
  orbitEquiv_zero := rfl
  orbitEquiv_step := by intro n; rfl
  identity := by
    intro x
    exact h.identity x.1 x.2
  nonContradiction := by
    intro x y
    exact h.non_contradiction x.1 y.1 x.2 y.2
  excludedMiddle := ExcludedMiddle C
  composition := RouteIndependence C
  actionInvariant := ScaleInvariant C
  nontrivial := by
    rcases h.non_trivial with ⟨x, hx, hcost⟩
    exact ⟨⟨x, hx⟩, hcost⟩

/-- The continuous positive-ratio realization satisfies the abstract
identity-step predicate. -/
theorem positiveRatio_hasIdentityStep
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (ofPositiveRatioComparison C h).hasIdentityStep :=
  hasIdentityStep_of_nontrivial _

/-- The continuous positive-ratio orbit interpretation is injective. -/
theorem positiveRatio_interpret_injective
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    Function.Injective (positiveRatioOrbitInterpret C h) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  rw [positiveRatioOrbitInterpret_val, positiveRatioOrbitInterpret_val] at hval
  exact ArithmeticFromLogic.embed_injective
    (ArithmeticFromLogic.generatorOfLawsOfLogic h) hval

/-- The continuous positive-ratio realization interprets its forced arithmetic
faithfully into the positive real carrier. -/
theorem positiveRatio_faithful
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    FaithfulArithmeticInterpretation (ofPositiveRatioComparison C h) where
  injective := by
    intro a b hab
    exact positiveRatio_interpret_injective C h hab
  zero_step_noncollapse := by
    intro n hcollapse
    exact LogicNat.zero_ne_succ n (positiveRatio_interpret_injective C h hcollapse)

end LogicRealization

end Foundation
end IndisputableMonolith
