import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.AbsoluteFloorClosure

/-!
  NonTrivialityFromDistinguishability.lean

  Move 1: promote `NonTrivial` from a posit to a corollary.

  In `Foundation.LogicAsFunctionalEquation`, `SatisfiesLawsOfLogic`
  carries a `non_trivial` field stating that the derived cost function
  is not identically zero on the positive ratios. The reason it was
  posited at all is that the constant-zero comparison operator
  vacuously satisfies the four Aristotelian conditions; without an
  extra commitment we cannot rule it out.

  This module replaces `non_trivial` with the more natural Aristotelian
  content: **distinguishability**, the claim that comparison is not
  vacuous, i.e. there exists at least one pair of distinct positive
  quantities whose comparison cost is non-zero.

  We then prove the equivalence: under Identity + Non-Contradiction +
  Scale Invariance, distinguishability is equivalent to the original
  `NonTrivial` predicate. So distinguishability is the canonical
  Aristotelian content; `NonTrivial` is an algebraic reformulation of
  the same fact.

  This makes the framework slightly more fundamental: the residual
  posit in `SatisfiesLawsOfLogic` is now stated in genuinely
  Aristotelian language, with no reference to the derived-cost
  definition.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open Real

/-- **Distinguishability**: comparison is operative, i.e. there exists
at least one pair of positive quantities whose comparison is not
vacuous. This is the operative Aristotelian content of comparison. -/
def Distinguishability (C : ComparisonOperator) : Prop :=
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ C x y ≠ 0

/-- **Equivalence (forward)**: distinguishability implies the algebraic
non-triviality predicate, given Scale Invariance. -/
theorem nonTrivial_of_distinguishability
    (C : ComparisonOperator)
    (hSI : ScaleInvariant C)
    (hDist : Distinguishability C) :
    NonTrivial C := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hDist
  -- Use scale invariance with λ = y⁻¹ to get C(x/y, 1) = C(x, y) ≠ 0.
  have hyinv : (0 : ℝ) < y⁻¹ := inv_pos.mpr hy
  have hxoverypos : (0 : ℝ) < x / y := div_pos hx hy
  have hkey : C (y⁻¹ * x) (y⁻¹ * y) = C x y := hSI x y y⁻¹ hx hy hyinv
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hy
  have hyinv_y : y⁻¹ * y = 1 := inv_mul_cancel₀ hyne
  have hyinv_x : y⁻¹ * x = x / y := by
    field_simp
  rw [hyinv_y, hyinv_x] at hkey
  refine ⟨x / y, hxoverypos, ?_⟩
  show derivedCost C (x / y) ≠ 0
  unfold derivedCost
  rw [hkey]
  exact hxy

/-- **Equivalence (backward)**: the algebraic non-triviality predicate
implies distinguishability. -/
theorem distinguishability_of_nonTrivial
    (C : ComparisonOperator)
    (hNT : NonTrivial C) :
    Distinguishability C := by
  obtain ⟨x, hx, hxne⟩ := hNT
  refine ⟨x, 1, hx, one_pos, ?_⟩
  show C x 1 ≠ 0
  exact hxne

/-- **Equivalence theorem**: under scale invariance, distinguishability
and non-triviality are the same condition. -/
theorem nonTrivial_iff_distinguishability
    (C : ComparisonOperator) (hSI : ScaleInvariant C) :
    NonTrivial C ↔ Distinguishability C :=
  ⟨distinguishability_of_nonTrivial C, nonTrivial_of_distinguishability C hSI⟩

/-! ## A canonical form of `SatisfiesLawsOfLogic` using distinguishability -/

/-- The canonical Aristotelian form of the Law of Logic, with
distinguishability replacing the algebraic non-triviality predicate. -/
structure SatisfiesLawsOfLogicCanonical (C : ComparisonOperator) : Prop where
  identity            : Identity C
  non_contradiction   : NonContradiction C
  excluded_middle     : ExcludedMiddle C
  scale_invariant     : ScaleInvariant C
  route_independence  : RouteIndependence C
  distinguishability  : Distinguishability C

/-- The canonical form is equivalent to the existing form. -/
theorem canonical_iff_existing (C : ComparisonOperator) :
    SatisfiesLawsOfLogicCanonical C ↔ SatisfiesLawsOfLogic C := by
  constructor
  · intro h
    refine
      { identity := h.identity
      , non_contradiction := h.non_contradiction
      , excluded_middle := h.excluded_middle
      , scale_invariant := h.scale_invariant
      , route_independence := h.route_independence
      , non_trivial := nonTrivial_of_distinguishability C h.scale_invariant h.distinguishability }
  · intro h
    refine
      { identity := h.identity
      , non_contradiction := h.non_contradiction
      , excluded_middle := h.excluded_middle
      , scale_invariant := h.scale_invariant
      , route_independence := h.route_independence
      , distinguishability := distinguishability_of_nonTrivial C h.non_trivial }

/-! ## Absolute-floor supplied canonical form

The structure above still stores `distinguishability` directly for
backward compatibility. The absolute-floor route below supplies that
field from a non-trivial specifiability witness on the positive-ratio
carrier, together with the statement that the comparison operator detects
the resulting carrier-level distinction.
-/

/-- Positive-ratio carrier used by the continuous Law-of-Logic realization. -/
abbrev PositiveRatio := {x : ℝ // 0 < x}

/-- Law-of-Logic data with distinguishability supplied by the absolute-floor
closure: a non-trivial specification of the positive-ratio carrier plus a
comparison operator that detects distinct specified carrier points. -/
structure SatisfiesLawsOfLogicAbsoluteFloor (C : ComparisonOperator) : Prop where
  identity            : Identity C
  non_contradiction   : NonContradiction C
  excluded_middle     : ExcludedMiddle C
  scale_invariant     : ScaleInvariant C
  route_independence  : RouteIndependence C
  floor               : AbsoluteFloorClosure.AbsoluteFloorWitness PositiveRatio
  detects_floor       : ∀ x y : PositiveRatio, x ≠ y → C x.1 y.1 ≠ 0

/-- Absolute-floor Law-of-Logic data supplies ordinary distinguishability. -/
theorem distinguishability_of_absoluteFloor
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogicAbsoluteFloor C) :
    Distinguishability C := by
  obtain ⟨x, y, hxy⟩ :=
    AbsoluteFloorClosure.bare_distinguishability_of_absolute_floor h.floor
  exact ⟨x.1, y.1, x.2, y.2, h.detects_floor x y hxy⟩

/-- The absolute-floor form induces the canonical Law-of-Logic form. -/
theorem canonical_of_absoluteFloor
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogicAbsoluteFloor C) :
    SatisfiesLawsOfLogicCanonical C where
  identity := h.identity
  non_contradiction := h.non_contradiction
  excluded_middle := h.excluded_middle
  scale_invariant := h.scale_invariant
  route_independence := h.route_independence
  distinguishability := distinguishability_of_absoluteFloor C h

/-- The absolute-floor form induces the existing algebraic form used by
downstream modules. -/
theorem existing_of_absoluteFloor
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogicAbsoluteFloor C) :
    SatisfiesLawsOfLogic C :=
  (canonical_iff_existing C).mp (canonical_of_absoluteFloor C h)

/-! ## The constant-zero exclusion

The constant-zero comparison operator `C ≡ 0` satisfies Identity,
Non-Contradiction, Excluded Middle, Scale Invariance, and a vacuous
form of Route Independence. The reason it does not satisfy the Law of
Logic is precisely that it fails distinguishability — comparison
collapses, so reality on this operator has no operative content.

This is the structural reason why distinguishability is a genuine
Aristotelian content rather than an external assumption: an operator
satisfying every other condition but failing distinguishability is
the constant-zero operator, which is the formal expression of "no
comparison is operative." -/

/-- The constant-zero comparison operator. -/
def constZero : ComparisonOperator := fun _ _ => 0

/-- Constant zero satisfies identity. -/
theorem constZero_identity : Identity constZero := by
  intro x _; rfl

/-- Constant zero satisfies non-contradiction. -/
theorem constZero_nonContradiction : NonContradiction constZero := by
  intro x y _ _; rfl

/-- Constant zero is continuous on the positive quadrant. -/
theorem constZero_continuous : ExcludedMiddle constZero := by
  unfold ExcludedMiddle
  exact continuousOn_const

/-- Constant zero is scale-invariant. -/
theorem constZero_scaleInvariant : ScaleInvariant constZero := by
  intro _ _ _ _ _ _; rfl

/-- Constant zero fails distinguishability. -/
theorem constZero_not_distinguishable : ¬ Distinguishability constZero := by
  intro ⟨_, _, _, _, h⟩
  exact h rfl

/-- Constant zero fails non-triviality. -/
theorem constZero_not_nonTrivial : ¬ NonTrivial constZero := by
  intro ⟨_, _, h⟩
  exact h rfl

/-! ## Summary

Move 1 closure: distinguishability is an Aristotelian content, the
algebraic `NonTrivial` predicate is one of its consequences under
scale invariance, and the only operator that satisfies all the other
laws but fails distinguishability is the constant-zero operator. The
residual posit in `SatisfiesLawsOfLogic` is therefore reducible to a
genuinely Aristotelian commitment, and the framework can be stated
canonically using `SatisfiesLawsOfLogicCanonical`. -/

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith
