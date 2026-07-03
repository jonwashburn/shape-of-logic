import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.QuarkScoreCard
import IndisputableMonolith.Masses.DisplayBridgeAlgebra

/-!
# Quark Absolute Bridge Score Card

Phase 0 rows **P0-Q01..P0-Q06** in
`planning/PHYSICAL_DERIVATION_PLAN.md`.

## Statement

This module deepens the existing `QuarkScoreCard`: the equal-`Z`
anchor bridge and the structural `rs_mass_MeV` formula agree exactly on
the **within-family ratios** for `u/c/t`. This is theorem-grade.

The absolute MeV bridge is still a **PARTIAL_THEOREM** / residual, not a
closed mass claim. The current definitions have two different anchors:

* `Verification.rs_mass_MeV` is a sector yardstick in displayed MeV,
  including the `10^6` reporting divisor.
* `RSBridge.massAtAnchor` is a native anchor expression with the
  gap-corrected exponent `r - 8 + gap (ZOf f)` and no SI display divisor.

## Measurement target

PDG 2024 quark masses:
`m_u = 2.16 MeV`, `m_c = 1.27 GeV`, `m_t = 172.69 GeV`, with the
down-sector rows still awaiting the same absolute bridge.

Falsifier: if the future SI/display bridge cannot map the native anchor
formula and the MeV sector formula into the same calibrated quantity, the
absolute quark-mass rows stay open.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Masses.QuarkAbsoluteBridgeScoreCard

open Constants
open Verification
open QuarkScoreCard
open IndisputableMonolith.RSBridge

noncomputable section

/-! ## Re-exported row aliases -/

/-- P0-Q bridge row: the structural charm/up ratio as a real-power φ law. -/
theorem row_structural_charm_up_ratio_rpow :
    charm_quark_pred / up_quark_pred = phi ^ (11 : ℝ) := by
  simpa [Real.rpow_natCast] using row_charm_up_ratio

/-- P0-Q bridge row: the structural top/charm ratio as a real-power φ law. -/
theorem row_structural_top_charm_ratio_rpow :
    top_quark_pred / charm_quark_pred = phi ^ (6 : ℝ) := by
  simpa [Real.rpow_natCast] using row_top_charm_ratio

/-! ## Anchor-side ratios -/

theorem row_anchor_charm_up_ratio_exp :
    massAtAnchor .c / massAtAnchor .u =
      Real.exp ((11 : ℝ) * Real.log phi) := by
  have hZ : ZOf .c = ZOf .u := by decide
  have h := anchor_ratio .c .u hZ
  have hr : ((rung .c : ℝ) - rung .u) = (11 : ℝ) := by
    simp [rung]
    norm_num
  simpa [hr] using h

theorem row_anchor_top_charm_ratio_exp :
    massAtAnchor .t / massAtAnchor .c =
      Real.exp ((6 : ℝ) * Real.log phi) := by
  have hZ : ZOf .t = ZOf .c := by decide
  have h := anchor_ratio .t .c hZ
  have hr : ((rung .t : ℝ) - rung .c) = (6 : ℝ) := by
    simp [rung]
    norm_num
  simpa [hr] using h

theorem row_anchor_charm_up_ratio_rpow :
    massAtAnchor .c / massAtAnchor .u = phi ^ (11 : ℝ) := by
  rw [row_anchor_charm_up_ratio_exp]
  rw [Real.rpow_def_of_pos phi_pos]
  ring_nf

theorem row_anchor_top_charm_ratio_rpow :
    massAtAnchor .t / massAtAnchor .c = phi ^ (6 : ℝ) := by
  rw [row_anchor_top_charm_ratio_exp]
  rw [Real.rpow_def_of_pos phi_pos]
  ring_nf

theorem row_anchor_strange_down_ratio_exp :
    massAtAnchor .s / massAtAnchor .d =
      Real.exp ((11 : ℝ) * Real.log phi) := by
  have hZ : ZOf .s = ZOf .d := by decide
  have h := anchor_ratio .s .d hZ
  have hr : ((rung .s : ℝ) - rung .d) = (11 : ℝ) := by
    simp [rung]
    norm_num
  simpa [hr] using h

theorem row_anchor_bottom_strange_ratio_exp :
    massAtAnchor .b / massAtAnchor .s =
      Real.exp ((6 : ℝ) * Real.log phi) := by
  have hZ : ZOf .b = ZOf .s := by decide
  have h := anchor_ratio .b .s hZ
  have hr : ((rung .b : ℝ) - rung .s) = (6 : ℝ) := by
    simp [rung]
    norm_num
  simpa [hr] using h

theorem row_anchor_strange_down_ratio_rpow :
    massAtAnchor .s / massAtAnchor .d = phi ^ (11 : ℝ) := by
  rw [row_anchor_strange_down_ratio_exp]
  rw [Real.rpow_def_of_pos phi_pos]
  ring_nf

theorem row_anchor_bottom_strange_ratio_rpow :
    massAtAnchor .b / massAtAnchor .s = phi ^ (6 : ℝ) := by
  rw [row_anchor_bottom_strange_ratio_exp]
  rw [Real.rpow_def_of_pos phi_pos]
  ring_nf

/-! ## Structural/anchor ratio agreement -/

theorem row_charm_up_structural_anchor_agree :
    charm_quark_pred / up_quark_pred =
      massAtAnchor .c / massAtAnchor .u := by
  rw [row_structural_charm_up_ratio_rpow, row_anchor_charm_up_ratio_rpow]

theorem row_top_charm_structural_anchor_agree :
    top_quark_pred / charm_quark_pred =
      massAtAnchor .t / massAtAnchor .c := by
  rw [row_structural_top_charm_ratio_rpow, row_anchor_top_charm_ratio_rpow]

/-! ## Absolute residual remains named and explicit -/

/-- The absolute mass bridge is still the named residual from `QuarkScoreCard`. -/
def row_absolute_quark_bridge_residual : Prop :=
  QuarkAbsoluteMassResidual

theorem row_absolute_quark_bridge_residual_is_named :
    row_absolute_quark_bridge_residual = QuarkAbsoluteMassResidual := rfl

structure QuarkAbsoluteBridgeScoreCardCert where
  display_algebra :
    DisplayBridgeAlgebra.DisplayBridgeAlgebraCert
  charm_up_ratio_agrees :
    charm_quark_pred / up_quark_pred =
      massAtAnchor .c / massAtAnchor .u
  top_charm_ratio_agrees :
    top_quark_pred / charm_quark_pred =
      massAtAnchor .t / massAtAnchor .c
  strange_down_anchor_ratio :
    massAtAnchor .s / massAtAnchor .d = phi ^ (11 : ℝ)
  bottom_strange_anchor_ratio :
    massAtAnchor .b / massAtAnchor .s = phi ^ (6 : ℝ)
  residual_named :
    row_absolute_quark_bridge_residual = QuarkAbsoluteMassResidual

theorem quarkAbsoluteBridgeScoreCardCert_holds :
    Nonempty QuarkAbsoluteBridgeScoreCardCert :=
  ⟨{ display_algebra := DisplayBridgeAlgebra.displayBridgeAlgebraCert_holds
     charm_up_ratio_agrees := row_charm_up_structural_anchor_agree
     top_charm_ratio_agrees := row_top_charm_structural_anchor_agree
     strange_down_anchor_ratio := row_anchor_strange_down_ratio_rpow
     bottom_strange_anchor_ratio := row_anchor_bottom_strange_ratio_rpow
     residual_named := row_absolute_quark_bridge_residual_is_named }⟩

end

end IndisputableMonolith.Masses.QuarkAbsoluteBridgeScoreCard
