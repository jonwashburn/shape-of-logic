import Mathlib
import IndisputableMonolith.StandardModel.HiggsRungAssignment

/-!
# Phase 2 — P2-HIGGS: Higgs mass `m_H` scorecard (EW + Q₃ correction chain)

**Predicted (RS):** `mH_rs_level3 = v * sqrt(sin²θ_W * 17/16)` with
`v = 246` GeV (canonical EWSB display) and `sin²θ_W = (3-φ)/6`.

**Observed:** PDG `m_H ≈ 125.2` GeV.

**Falsifier (one sentence):** If a future `m_H` world average moves outside
`(120, 130)` GeV while the RS `sin²θ_W` and `v` inputs remain in their proved bands,
the interval prediction is false.

**Status:** `PARTIAL_THEOREM` — the `(120,130)` window and 5% proximity to 125.2 GeV are proved;
`v = 246` GeV remains a display anchor (same residual family as the Fermi-constant row).

**Lean: 0 sorry, 0 new axiom**
-/

namespace IndisputableMonolith.Physics.HiggsMassScoreCard

open IndisputableMonolith
open IndisputableMonolith.StandardModel
open IndisputableMonolith.StandardModel.HiggsRungAssignment

noncomputable section

noncomputable def row_mH_codata : ℝ := mH_obs

theorem row_mH_codata_pos : 0 < row_mH_codata := by
  unfold row_mH_codata mH_obs
  norm_num

theorem row_mH_pred_interval :
    120 < mH_rs_level3 ∧ mH_rs_level3 < 130 := mH_prediction_in_interval

theorem row_mH_within_five_percent :
    |mH_rs_level3 - row_mH_codata| / row_mH_codata < 0.05 := by
  simpa [row_mH_codata] using mH_within_5_percent_of_observed

structure HiggsMassScoreCardCert where
  mass_interval : 120 < mH_rs_level3 ∧ mH_rs_level3 < 130
  five_percent : |mH_rs_level3 - mH_obs| / mH_obs < 0.05

theorem higgsMassScoreCardCert_holds : Nonempty HiggsMassScoreCardCert :=
  ⟨{ mass_interval := row_mH_pred_interval
     five_percent := mH_within_5_percent_of_observed }⟩

end

end IndisputableMonolith.Physics.HiggsMassScoreCard
