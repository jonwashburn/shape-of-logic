import IndisputableMonolith.Gravity.Pillar3Successor.RapidityOverlapKernel

/-!
# Metric-attachment selection wall

The standalone rapidity-overlap kernel proves that a metric-dependent exact-J
completion can have a nonzero finite derivative.  This file asks the separate
selection question: do the currently available generic constraints choose
that completion?

They do not.  Exact recovery at the inverse Minkowski metric, silence at zero
amplitude, axis symmetry, and differentiability along every matrix line allow
both the metric-blind leaf and the rapidity-overlap leaf.  The former has zero
metric derivative; the latter has a nonzero derivative on the same named unit
variation.  Consequently those premises do not select a unique metric leaf.

This is the typed residual left by the formulation wall.  It does not weaken
the positive finite-kernel theorems, and it does not promote either completion
to a Recognition-derived physical or continuum action.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace Pillar3Successor
namespace MetricAttachmentSelectionWall

open RapidityOverlapKernel

/-- Candidate local inverse-metric completion of one exact-J channel. -/
abbrev MetricLeaf :=
  Matrix4 → Fin 3 → ℝ → ℝ

/--
Generic constraints inherited by both the old blind lift and the new
rapidity-overlap lift.  No overlap ansatz or target derivative is included.
-/
def FlatExactJLeafPremises (F : MetricLeaf) : Prop :=
  (∀ (axis : Fin 3) (amplitude : ℝ),
      F minkowskiInverse axis amplitude = exactJLeaf amplitude) ∧
  (∀ (h : Matrix4) (axis : Fin 3),
      F h axis 0 = 0) ∧
  (∀ (h : Matrix4) (left right : Fin 3) (amplitude : ℝ),
      F h left amplitude = F h right amplitude) ∧
  (∀ (h H : Matrix4) (axis : Fin 3) (amplitude : ℝ),
      DifferentiableAt ℝ
        (fun t => F (matrixLine h H t) axis amplitude)
        0)

theorem metricBlindLeaf_satisfies_currentPremises :
    FlatExactJLeafPremises metricBlindLeaf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro axis amplitude
    rfl
  · intro h axis
    simp [metricBlindLeaf, exactJLeaf]
  · intro h left right amplitude
    rfl
  · intro h H axis amplitude
    exact
      (metricBlindLeaf_line_derivative_zero
        h H axis amplitude).differentiableAt

theorem rapidityMetricLeaf_axis_independent
    (h : Matrix4) (left right : Fin 3) (amplitude : ℝ) :
    rapidityMetricLeaf h left amplitude =
      rapidityMetricLeaf h right amplitude := by
  rw [rapidityMetricLeaf_eq, rapidityMetricLeaf_eq]

theorem rapidityMetricLeaf_satisfies_currentPremises :
    FlatExactJLeafPremises rapidityMetricLeaf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact rapidityMetricLeaf_minkowski
  · exact rapidityMetricLeaf_zero
  · exact rapidityMetricLeaf_axis_independent
  · intro h H axis amplitude
    exact
      (rapidityMetricLeaf_line_hasDerivAt
        h H axis amplitude).differentiableAt

theorem metricBlindLeaf_ne_rapidityMetricLeaf :
    (metricBlindLeaf : MetricLeaf) ≠ rapidityMetricLeaf := by
  intro heq
  have hvalue :=
    congrFun
      (congrFun
        (congrFun heq halfTimeInverse)
        (0 : Fin 3))
      1
  rw [rapidityMetricLeaf_eq] at hvalue
  simp [metricBlindLeaf, halfTimeInverse] at hvalue
  have hpos : 0 < exactJLeaf 1 := by
    unfold exactJLeaf
    linarith [Real.one_lt_cosh.mpr (by norm_num : (1 : ℝ) ≠ 0)]
  linarith

/--
The named current premises do not select a unique local metric completion.
-/
theorem currentPremises_do_not_select_uniqueMetricLeaf :
    ¬ ∃! F : MetricLeaf, FlatExactJLeafPremises F := by
  intro hunique
  rcases hunique with ⟨selected, hselected, unique⟩
  have hblind :
      (metricBlindLeaf : MetricLeaf) = selected :=
    unique metricBlindLeaf metricBlindLeaf_satisfies_currentPremises
  have hrapidity :
      (rapidityMetricLeaf : MetricLeaf) = selected :=
    unique rapidityMetricLeaf rapidityMetricLeaf_satisfies_currentPremises
  exact metricBlindLeaf_ne_rapidityMetricLeaf
    (hblind.trans hrapidity.symm)

theorem rapidityMetricLeaf_unit_derivative_ne_zero :
    deriv
      (fun t =>
        rapidityMetricLeaf
          (matrixLine minkowskiInverse timeTimeVariation t)
          (0 : Fin 3) 1)
      0 ≠ 0 := by
  rw [(rapidityMetricLeaf_line_hasDerivAt
    minkowskiInverse timeTimeVariation (0 : Fin 3) 1).deriv]
  simp [timeTimeVariation]
  have hpos : 0 < exactJLeaf 1 := by
    unfold exactJLeaf
    linarith [Real.one_lt_cosh.mpr (by norm_num : (1 : ℝ) ≠ 0)]
  exact hpos.ne'

/--
The same named premises support a zero-response completion and a nonzero-response
completion on the same inverse-Minkowski line and unit amplitude.
-/
theorem currentPremises_support_zero_and_nonzero_response :
    HasDerivAt
      (fun t =>
        metricBlindLeaf
          (matrixLine minkowskiInverse timeTimeVariation t)
          (0 : Fin 3) 1)
      0 0 ∧
    deriv
      (fun t =>
        rapidityMetricLeaf
          (matrixLine minkowskiInverse timeTimeVariation t)
          (0 : Fin 3) 1)
      0 ≠ 0 := by
  exact
    ⟨metricBlindLeaf_line_derivative_zero
      minkowskiInverse timeTimeVariation (0 : Fin 3) 1,
      rapidityMetricLeaf_unit_derivative_ne_zero⟩

end MetricAttachmentSelectionWall
end Pillar3Successor
end Gravity
end IndisputableMonolith
