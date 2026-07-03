import Mathlib
import IndisputableMonolith.Verification.CurvatureSpaceCert

namespace IndisputableMonolith.Verification.MetricCurvature

structure MetricCurvatureCert where
  deriving Repr

/-- Verification of Metric & Curvature Grounding. -/
@[simp] def MetricCurvatureCert.verified (_c : MetricCurvatureCert) : Prop :=
  IndisputableMonolith.Verification.CurvatureSpace.CurvatureSpaceCert.verified {}

@[simp] theorem MetricCurvatureCert.verified_any (c : MetricCurvatureCert) :
    MetricCurvatureCert.verified c := by
  simpa [MetricCurvatureCert.verified] using
    (IndisputableMonolith.Verification.CurvatureSpace.CurvatureSpaceCert.verified_any {})

end MetricCurvature
end IndisputableMonolith.Verification
