import Mathlib
import IndisputableMonolith.StandardModel.WeinbergAngle
import IndisputableMonolith.StandardModel.Q3Representations

/-!
# Phase 2 — P2-θW: electroweak `sin²θ_W` (Weinberg angle) scorecard

**Predicted (RS) core:** `sin²θ_W = (3-φ)/6` (alias `sin2ThetaW_RS` in
`Q3Representations`).

**Observed (PDG-style reference):** `sin²θ_W ≈ 0.2229` in `WeinbergAngle.sin2ThetaW_observed`.

**Falsifier (one sentence):** If a future on-shell or MS `sin²θ_W` reference moves by more
than 0.01 from `(3-φ)/6` *without* a change in the certified φ/α input bounds, the
identity-level match is false.

**Status:** The tight match `|bestPrediction - 0.2229| < 0.01` is a proved **PARTIAL** bridge
(leading formula vs one reference number); rung-normalization and scheme dependence is the
residual, named below.

**Lean: 0 sorry, 0 new axiom**
-/

namespace IndisputableMonolith.Physics.WeinbergAngleScoreCard

open IndisputableMonolith
open IndisputableMonolith.StandardModel
open IndisputableMonolith.StandardModel.Q3Representations

noncomputable section

def row_sin2_thetaW_codata : ℝ := WeinbergAngle.sin2ThetaW_observed

theorem row_sin2_thetaW_codata_bracket :
    (0.22 : ℝ) < row_sin2_thetaW_codata ∧ row_sin2_thetaW_codata < (0.23 : ℝ) := by
  simpa [row_sin2_thetaW_codata] using WeinbergAngle.sin2_theta_bounds

theorem row_sin2_thetaW_RS_bracket :
    0.228 < sin2ThetaW_RS ∧ sin2ThetaW_RS < 0.232 := sin2ThetaW_RS_approx

theorem row_best_prediction_match :
    |WeinbergAngle.bestPrediction - row_sin2_thetaW_codata| < 0.01 :=
  WeinbergAngle.best_prediction_close_to_observed

structure WeinbergAngleScoreCardCert where
  codata_in_ref_band :
    (0.22 : ℝ) < row_sin2_thetaW_codata ∧ row_sin2_thetaW_codata < (0.23 : ℝ)
  rs_bracket : 0.228 < sin2ThetaW_RS ∧ sin2ThetaW_RS < 0.232
  one_cent_match : |WeinbergAngle.bestPrediction - row_sin2_thetaW_codata| < 0.01

theorem weinbergAngleScoreCardCert_holds : Nonempty WeinbergAngleScoreCardCert :=
  ⟨{ codata_in_ref_band := row_sin2_thetaW_codata_bracket
     rs_bracket := row_sin2_thetaW_RS_bracket
     one_cent_match := row_best_prediction_match }⟩

end

end IndisputableMonolith.Physics.WeinbergAngleScoreCard
