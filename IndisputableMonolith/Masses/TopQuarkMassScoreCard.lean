import Mathlib
import IndisputableMonolith.Masses.Verification
import IndisputableMonolith.Masses.QuarkScoreCard

/-!
# Phase 2 — P2-t: top quark structural mass (φ-ladder, order-of-magnitude row)

**Predicted (RS):** `top_quark_pred = φ^51 / 2,000,000` MeV (`Verification`).

**Measurement anchor:** PDG 2024 center `m_t ≈ 172.69` GeV $=$ `172690` MeV (reference only; no
tight match is claimed in `Verification`).

**Falsifier (one sentence):** A PDG or RS φ-update that forces `top_quark_pred` outside
`$(10^4,10^6)$` MeV with the current structural definition falsifies the
order-magnitude scorecard (same inequality as `top_quark_pred_order`).

**Status:** `PARTIAL_THEOREM` on positivity, exact `t/c = φ^6`, and the wide MeV
interval; no sub-percent absolute mass match to `172690` MeV (same residual family as
`QuarkScoreCard` / `QuarkAbsoluteBridgeScoreCard`).

**Lean: 0 sorry, 0 new axiom**
-/

namespace IndisputableMonolith.Masses.TopQuarkMassScoreCard

open IndisputableMonolith
open IndisputableMonolith.Masses.Verification
open IndisputableMonolith.Masses.QuarkScoreCard
open IndisputableMonolith.Constants

noncomputable section

def row_pdg_top_MeV : ℝ := 172690

theorem row_pdg_top_positive : 0 < row_pdg_top_MeV := by unfold row_pdg_top_MeV; norm_num

theorem row_top_pos : 0 < top_quark_pred := quark_preds_pos.2.2

theorem row_top_charm : top_quark_pred / charm_quark_pred = phi ^ (6 : ℕ) := top_charm_ratio

theorem row_top_order_MeV :
    (10000 : ℝ) < top_quark_pred ∧ top_quark_pred < 1000000 := top_quark_pred_order

theorem row_top_in_band_scorecard : (10000 : ℝ) < top_quark_pred ∧ top_quark_pred < 1000000 :=
  row_top_quark_in_band

structure TopQuarkMassScoreCardCert where
  positive : 0 < top_quark_pred
  top_charm : top_quark_pred / charm_quark_pred = phi ^ (6 : ℕ)
  order_MeV : (10000 : ℝ) < top_quark_pred ∧ top_quark_pred < 1000000
  pdg_ref_pos : 0 < row_pdg_top_MeV

theorem topQuarkMassScoreCardCert_holds : Nonempty TopQuarkMassScoreCardCert :=
  ⟨{ positive := row_top_pos
     top_charm := row_top_charm
     order_MeV := row_top_order_MeV
     pdg_ref_pos := row_pdg_top_positive }⟩

end

end IndisputableMonolith.Masses.TopQuarkMassScoreCard
