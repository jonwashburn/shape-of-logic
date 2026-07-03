import IndisputableMonolith.Foundation.UniversalForcing.StrictRealization

/-!
  Strict/PositiveRatio.lean

  Strict continuous positive-ratio realization, built directly from
  `SatisfiesLawsOfLogic` in `LogicAsFunctionalEquation`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace PositiveRatio

open LogicAsFunctionalEquation

/-- Strict positive-ratio realization from the existing Law-of-Logic package. -/
noncomputable def strictPositiveRatioRealization
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    StrictLogicRealization where
  Carrier := {x : ℝ // 0 < x}
  Cost := ℝ
  zeroCost := inferInstance
  compare := fun x y => C x.1 y.1
  compose := fun x y => ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  one := ⟨1, one_pos⟩
  generator :=
    let γ : ℝ := Classical.choose h.non_trivial
    ⟨γ, (Classical.choose_spec h.non_trivial).1⟩
  identity_law := by
    intro x
    exact h.identity x.1 x.2
  non_contradiction_law := by
    intro x y
    exact h.non_contradiction x.1 y.1 x.2 y.2
  excluded_middle_law := ExcludedMiddle C
  composition_law := RouteIndependence C
  invariance_law := ScaleInvariant C
  nontrivial_law := by
    exact (Classical.choose_spec h.non_trivial).2

/-- Strict positive-ratio forced arithmetic is canonically `LogicNat`. -/
noncomputable def positiveRatio_arith_equiv_logicNat
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (StrictLogicRealization.arith (strictPositiveRatioRealization C h)).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight (strictPositiveRatioRealization C h)).orbitEquivLogicNat

/-- The strict-derived lightweight realization has the same forced arithmetic
as the existing positive-ratio lightweight wrapper. -/
noncomputable def positiveRatio_strict_equiv_existing
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (StrictLogicRealization.arith (strictPositiveRatioRealization C h)).peano.carrier
      ≃ (UniversalForcing.arithmeticOf (LogicRealization.ofPositiveRatioComparison C h)).peano.carrier :=
  ArithmeticOf.equivOfInitial
    (StrictLogicRealization.arith (strictPositiveRatioRealization C h))
    (UniversalForcing.arithmeticOf (LogicRealization.ofPositiveRatioComparison C h))

end PositiveRatio
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith
