import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationIndependence
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# CurrentRSBundle — Day-0 rescale surface for Part I gate campaign

Plan: `plans/PartI_Full_Closure_Campaign_Plan_20260723.html` Day 0.

Defines the exact non-calibration cost bundle PublicSpine uses for the gauge
family, plus a positive rescale action on gauge models whose laws are stated
**without** mentioning `IsCalibrated` / unit curvature in the action itself.

`rescale_changes_calibration` may *measure* calibration as an effect theorem
after the fact; calibration is not a field of `CurrentRSBundle` or of
`rescale`.

If this surface cannot be stated without smuggling the target, Test A is
NO DECISION — that case does not arise here: the surface is the already-banked
`costLambda` family under `FullNonCalibrationCostLaws`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace CurrentRSBundle

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration

/-- Bare cost laws currently imported by PublicSpine residual work:
reciprocity, normalization, RCL composition, continuity on `Ioi 0`.
No calibration conjunct. -/
structure CurrentRSBundle where
  F : ℝ → ℝ
  reciprocal : IsReciprocalCost F
  normalized : IsNormalized F
  composition : SatisfiesCompositionLaw F
  continuous : ContinuousOn F (Set.Ioi 0)

/-- Gauge models: the positive one-parameter family realizing the bundle. -/
structure GaugeModel where
  c : ℝ
  positive : 0 < c

/-- Continuum cost of a gauge model. -/
noncomputable def GaugeModel.cost (M : GaugeModel) : ℝ → ℝ :=
  fun x => costLambda M.c x

/-- Every gauge model yields a `CurrentRSBundle`. -/
noncomputable def GaugeModel.toBundle (M : GaugeModel) : CurrentRSBundle where
  F := M.cost
  reciprocal := costLambda_isReciprocalCost M.c
  normalized := costLambda_isNormalized M.c
  composition := costLambda_satisfiesCompositionLaw M.c
  continuous := costLambda_continuousOn M.c

/-- **Rescale action (target-free).** Multiplies the gauge coordinate by a
positive factor. Does not mention `IsCalibrated`. -/
noncomputable def rescale (lam : ℝ) (hlam : 0 < lam) (M : GaugeModel) : GaugeModel where
  c := lam * M.c
  positive := mul_pos hlam M.positive

theorem rescale_c (lam : ℝ) (hlam : 0 < lam) (M : GaugeModel) :
    (rescale lam hlam M).c = lam * M.c :=
  rfl

/-- Rescale preserves the non-calibration bundle laws (via `toBundle`). -/
theorem rescale_preserves_currentRS (lam : ℝ) (hlam : 0 < lam) (M : GaugeModel) :
    IsReciprocalCost (rescale lam hlam M).cost ∧
    IsNormalized (rescale lam hlam M).cost ∧
    SatisfiesCompositionLaw (rescale lam hlam M).cost ∧
    ContinuousOn (rescale lam hlam M).cost (Set.Ioi 0) := by
  exact ⟨(rescale lam hlam M).toBundle.reciprocal,
    (rescale lam hlam M).toBundle.normalized,
    (rescale lam hlam M).toBundle.composition,
    (rescale lam hlam M).toBundle.continuous⟩

theorem rescale_toBundle (lam : ℝ) (hlam : 0 < lam) (M : GaugeModel) :
    (rescale lam hlam M).toBundle =
      { F := (rescale lam hlam M).cost
        reciprocal := costLambda_isReciprocalCost (lam * M.c)
        normalized := costLambda_isNormalized (lam * M.c)
        composition := costLambda_satisfiesCompositionLaw (lam * M.c)
        continuous := costLambda_continuousOn (lam * M.c) } :=
  rfl

/-- Effect theorem (not a field of `rescale`): non-unit rescale of the
calibrated unit leaves the calibrated locus. -/
theorem rescale_changes_calibration
    (lam : ℝ) (hlam : 0 < lam) (hlamne : lam ≠ 1) :
    IsCalibrated (GaugeModel.cost ⟨1, one_pos⟩) ∧
      ¬ IsCalibrated (GaugeModel.cost (rescale lam hlam ⟨1, one_pos⟩)) := by
  have hcal : IsCalibrated (fun x => costLambda (1 : ℝ) x) :=
    (costLambda_isCalibrated_iff one_pos).mpr rfl
  have hpos : 0 < lam * (1 : ℝ) := mul_pos hlam one_pos
  have hnot : ¬ IsCalibrated (fun x => costLambda (lam * 1) x) := by
    intro h
    have : lam * (1 : ℝ) = 1 := (costLambda_isCalibrated_iff hpos).mp h
    have : lam = 1 := by simpa using this
    exact hlamne this
  exact ⟨hcal, by simpa [GaugeModel.cost, rescale] using hnot⟩

/-- Unit rescale is the identity on gauge coordinates. -/
theorem rescale_one (M : GaugeModel) :
    (rescale 1 one_pos M).c = M.c := by
  simp [rescale]

/-- Day-0 cert: surface is inhabited and rescale is well-defined without
calibration fields. -/
structure CurrentRSBundleCert : Prop where
  gauge_to_bundle :
    ∀ M : GaugeModel,
      IsReciprocalCost M.cost ∧
      IsNormalized M.cost ∧
      SatisfiesCompositionLaw M.cost ∧
      ContinuousOn M.cost (Set.Ioi 0)
  rescale_welldefined :
    ∀ (lam : ℝ) (hlam : 0 < lam) (M : GaugeModel),
      (rescale lam hlam M).c = lam * M.c
  unit_id : ∀ M : GaugeModel, (rescale 1 one_pos M).c = M.c
  calib_effect :
    ∀ (lam : ℝ) (hlam : 0 < lam), lam ≠ 1 →
      IsCalibrated (GaugeModel.cost ⟨1, one_pos⟩) ∧
        ¬ IsCalibrated (GaugeModel.cost (rescale lam hlam ⟨1, one_pos⟩))

theorem currentRSBundleCert_holds : CurrentRSBundleCert where
  gauge_to_bundle := fun M =>
    ⟨M.toBundle.reciprocal, M.toBundle.normalized,
      M.toBundle.composition, M.toBundle.continuous⟩
  rescale_welldefined := fun lam hlam M => rescale_c lam hlam M
  unit_id := rescale_one
  calib_effect := fun lam hlam hne => rescale_changes_calibration lam hlam hne

end CurrentRSBundle
end PublicSpine
end Foundation
end IndisputableMonolith
