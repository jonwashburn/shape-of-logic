import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.DistinctionToJCost

/-!
# Cutset row 1: ratio dependence is cross-floor unit freedom

Row 1 of the kernel ledger is the composition law; its product coefficient is
a gauge. Its open sub-sentence is *ratio dependence*: the cost of comparing two
readings depends on them only through their ratio. This module prices that
sub-sentence in the harness.

## Blade

**Cross-floor unit freedom.** Rescaling both readings by one factor (moving
both to the floor above, or changing the unit) leaves the comparison unchanged.
This is the tree's `ScaleInvariant`, and it is the same identification as row
4a read on the comparison: every floor is the same recognizer, so the
comparison cannot see the unit.

## Result

* `scaleInvariant_iff_ratioDependent`: unit freedom **is** ratio dependence,
  extensionally, on positive readings. Shape: **merge**. This is bookkeeping,
  not derivation: it says which floor word the sub-sentence is, and that no
  continuity or homogeneity input is needed for the equivalence.
* The difference cost `x - y` and the Hamming-style cost `|x - y|` fail unit
  freedom (`4 - 2 ≠ 2 - 1`); the canonical `J` comparison passes it.
* Composition to the RCL form then goes through the banked
  `positiveRatio_law_forces_RCL`, which needs the full Law-of-Logic package
  (including continuity and route independence: the continuum purchase). The
  coefficient stays a gauge.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row1Ratio

open LogicAsFunctionalEquation DistinctionToJCost

noncomputable section

/-- **Ratio dependence.** The comparison is a function of the ratio. -/
def RatioDependent (C : ComparisonOperator) : Prop :=
  ∃ f : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → C x y = f (x / y)

/-- **Unit freedom is ratio dependence.** A merge: the blade and the sentence
are the same predicate on positive readings. -/
theorem scaleInvariant_iff_ratioDependent (C : ComparisonOperator) :
    ScaleInvariant C ↔ RatioDependent C := by
  constructor
  · intro h
    refine ⟨fun r => C r 1, fun x y hx hy => ?_⟩
    have hy0 : y ≠ 0 := hy.ne'
    have hxy : y * (x / y) = x := by field_simp
    have := h (x / y) 1 y (div_pos hx hy) one_pos hy
    rw [hxy, mul_one] at this
    exact this
  · rintro ⟨f, hf⟩ x y lam hx hy hl
    rw [hf _ _ (mul_pos hl hx) (mul_pos hl hy), hf x y hx hy, mul_div_mul_left _ _ hl.ne']

/-- The difference comparison. -/
def differenceComparison : ComparisonOperator := fun x y => x - y

/-- The Hamming-style comparison: the size of the difference. -/
def hammingComparison : ComparisonOperator := fun x y => |x - y|

theorem difference_not_scaleInvariant : ¬ ScaleInvariant differenceComparison := by
  intro h
  have := h 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num [differenceComparison] at this

theorem hamming_not_scaleInvariant : ¬ ScaleInvariant hammingComparison := by
  intro h
  have := h 2 1 2 (by norm_num) (by norm_num) (by norm_num)
  norm_num [hammingComparison] at this

theorem hamming_not_ratioDependent : ¬ RatioDependent hammingComparison :=
  fun h => hamming_not_scaleInvariant ((scaleInvariant_iff_ratioDependent _).mpr h)

theorem hamming_identity : Identity hammingComparison := fun x _ => by
  simp [hammingComparison]

theorem hamming_nonContradiction : NonContradiction hammingComparison := fun x y _ _ => by
  simp [hammingComparison, abs_sub_comm]

theorem jcost_scaleInvariant : ScaleInvariant jcostComparison :=
  jcostComparison_satisfies_laws.scale_invariant

theorem jcost_ratioDependent : RatioDependent jcostComparison :=
  (scaleInvariant_iff_ratioDependent _).mp jcost_scaleInvariant

/-- **Row 1 sub-sentence in the harness.** Floor: T1 on the comparison
(identity and reciprocal symmetry). Sentence: ratio dependence. Blade: unit
freedom. Real: the `J` comparison. Violator: the Hamming-style comparison. -/
def row : CutsetRow ComparisonOperator where
  Floor := fun C => Identity C ∧ NonContradiction C
  Sentence := RatioDependent
  Blade := ScaleInvariant
  provenance := .definition
    "cross-floor unit freedom: rescaling both readings by the floor's unit leaves the comparison unchanged"
  real := jcostComparison
  real_floor := ⟨jcostComparison_satisfies_laws.identity,
    jcostComparison_satisfies_laws.non_contradiction⟩
  blade_real := jcost_scaleInvariant
  violator := hammingComparison
  violator_floor := ⟨hamming_identity, hamming_nonContradiction⟩
  violator_violates := hamming_not_ratioDependent
  blade_kills_violator := hamming_not_scaleInvariant
  exclusion := fun C _ hs hb => hs ((scaleInvariant_iff_ratioDependent C).mp hb)

/-- Composition, conditional on the full Law-of-Logic package. -/
theorem rcl_of_laws (C : ComparisonOperator) (hC : SatisfiesLawsOfLogic C) :
    RatioDependent C ∧
      ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
        DAlembert.Inevitability.HasMultiplicativeConsistency (derivedCost C) P ∧
        (∀ u v, P u v = 2*u + 2*v + c*u*v) :=
  ⟨(scaleInvariant_iff_ratioDependent C).mp hC.scale_invariant,
    positiveRatio_law_forces_RCL C hC⟩

structure Cert : Prop where
  merge : ∀ C : ComparisonOperator, ScaleInvariant C ↔ RatioDependent C
  difference_fails : ¬ ScaleInvariant differenceComparison
  hamming_fails : ¬ ScaleInvariant hammingComparison
  j_passes : ScaleInvariant jcostComparison
  row_forces : ∀ C, row.Floor C → row.Blade C → row.Sentence C
  row_class_nonempty : ∃ C, row.Floor C ∧ ¬ row.Sentence C
  composition : ∀ C : ComparisonOperator, SatisfiesLawsOfLogic C →
    RatioDependent C ∧
      ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
        DAlembert.Inevitability.HasMultiplicativeConsistency (derivedCost C) P ∧
        (∀ u v, P u v = 2*u + 2*v + c*u*v)

theorem cert : Cert where
  merge := scaleInvariant_iff_ratioDependent
  difference_fails := difference_not_scaleInvariant
  hamming_fails := hamming_not_scaleInvariant
  j_passes := jcost_scaleInvariant
  row_forces := row.forces
  row_class_nonempty := row.class_nonempty
  composition := rcl_of_laws

end

end Row1Ratio
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
