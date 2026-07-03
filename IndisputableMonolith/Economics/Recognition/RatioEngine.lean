import IndisputableMonolith.Verification.CPT.Exports
import IndisputableMonolith.Economics.Recognition.Observable

/-!
# Ratio Engine for Recognition Economics

Lean-side wrapper for the practical `econ_jcost` package:

* project economic ratio data to log-neutrality;
* expose the Jevons/geometric-mean level in log coordinates;
* wrap the repository's proved CPT `P -> B -> A` factorization theorem.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

open scoped BigOperators

noncomputable section

/-- Log data for a positive economic ratio panel after logs have been taken. -/
abbrev LogPanel (ι : Type*) := ι → ℝ

/-- Mean log-ratio. Its exponential is the Jevons/geometric-mean level. -/
def logMean {ι : Type*} [Fintype ι] (y : LogPanel ι) : ℝ :=
  (∑ i : ι, y i) / (Fintype.card ι : ℝ)

/-- Jevons level in log coordinates. -/
def jevonsLevel {ι : Type*} [Fintype ι] (y : LogPanel ι) : ℝ :=
  Real.exp (logMean y)

/-- Projection to the neutral log hyperplane. -/
def projectedLog {ι : Type*} [Fintype ι] (y : LogPanel ι) : LogPanel ι :=
  fun i => y i - logMean y

/-- The projection step removes the common level: projected logs sum to zero. -/
theorem projectedLog_sum_zero {ι : Type*} [Fintype ι] [Nonempty ι] (y : LogPanel ι) :
    (∑ i : ι, projectedLog y i) = 0 := by
  unfold projectedLog logMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard_nat : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hcard_nat
  have huniv : ((Finset.univ : Finset ι).card : ℝ) = (Fintype.card ι : ℝ) := by
    simp
  field_simp [hcard]
  rw [huniv]
  ring

/-- J-energy of a projected log panel. -/
def projectedJEnergy {ι : Type*} [Fintype ι] (y : LogPanel ι) : ℝ :=
  ∑ i : ι, (Real.cosh (projectedLog y i) - 1)

theorem projectedJEnergy_nonneg {ι : Type*} [Fintype ι] (y : LogPanel ι) :
    0 ≤ projectedJEnergy y := by
  unfold projectedJEnergy
  apply Finset.sum_nonneg
  intro i _hi
  have hcosh : 1 ≤ Real.cosh (projectedLog y i) := by
    rcases eq_or_ne (projectedLog y i) 0 with h0 | h0
    · rw [h0, Real.cosh_zero]
    · exact le_of_lt (Real.one_lt_cosh.mpr h0)
  linarith

/-- Economic CPT projection stage. -/
abbrev EconProjectionStage (X Y : Type) :=
  IndisputableMonolith.Verification.CPT.Pipeline.ProjectionStage X Y

/-- Economic CPT coercivity stage. -/
abbrev EconCoercivityStage (Y Z : Type) :=
  IndisputableMonolith.Verification.CPT.Pipeline.CoercivityStage Y Z

/-- Economic CPT aggregation stage. -/
abbrev EconAggregationStage (Z : Type) :=
  IndisputableMonolith.Verification.CPT.Pipeline.AggregationStage Z

/-- Economic ratio pipeline. -/
def econPhiStar {X Y Z : Type}
    (P : EconProjectionStage X Y)
    (B : EconCoercivityStage Y Z)
    (A : EconAggregationStage Z) :
    IndisputableMonolith.Verification.CPT.Procedure X :=
  IndisputableMonolith.Verification.CPT.Pipeline.PhiStar P B A

/-- Lean wrapper for the proved CPT P->B->A factorization. -/
theorem econ_ratio_pipeline_factorization {X Y Z : Type}
    (P : EconProjectionStage X Y)
    (B : EconCoercivityStage Y Z)
    (A : EconAggregationStage Z) :
    econPhiStar P B A = A.run ∘ B.run ∘ P.run :=
  IndisputableMonolith.Verification.CPT.Exports.CPT_PIPELINE_factorization P B A

/-- Zero-decision soundness, inherited from CPT. -/
theorem econ_ratio_pipeline_sound {X Y Z : Type}
    (P : EconProjectionStage X Y)
    (B : EconCoercivityStage Y Z)
    (A : EconAggregationStage Z)
    (membership : X → Prop)
    (hzero : ∀ x,
      econPhiStar P B A x = IndisputableMonolith.Verification.CPT.DecisionTag.zero →
        membership x) :
    ∀ x,
      econPhiStar P B A x = IndisputableMonolith.Verification.CPT.DecisionTag.zero →
        membership x :=
  IndisputableMonolith.Verification.CPT.Exports.CPT_PIPELINE_sound P B A membership hzero

/-- Nonzero-decision soundness, inherited from CPT. -/
theorem econ_ratio_pipeline_nonzero_sound {X Y Z : Type}
    (P : EconProjectionStage X Y)
    (B : EconCoercivityStage Y Z)
    (A : EconAggregationStage Z)
    (excluded : X → Prop)
    (hnonzero : ∀ x,
      econPhiStar P B A x = IndisputableMonolith.Verification.CPT.DecisionTag.nonzero →
        excluded x) :
    ∀ x,
      econPhiStar P B A x = IndisputableMonolith.Verification.CPT.DecisionTag.nonzero →
        excluded x :=
  IndisputableMonolith.Verification.CPT.Exports.CPT_PIPELINE_nonzero_sound P B A excluded hnonzero

end

end Recognition
end Economics
end IndisputableMonolith
