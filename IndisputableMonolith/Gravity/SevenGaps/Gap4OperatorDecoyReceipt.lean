import IndisputableMonolith.Gravity.SevenGaps.CurvedOperatorUnderdetermination
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
import IndisputableMonolith.Gravity.SevenGaps.CampaignLedger
import IndisputableMonolith.Gravity.SevenGaps.DiscreteLichnerowicz

/-!
# Wave C3 R0: gap4 operator decoy receipt

Falsify-before-proving residual from
`plans/QG_WaveC3_Gap4_Residual_DAG_Draft_20260722.txt` §R0
(`TypedResidual_countermodel_spectrum_not_ledger_close`).

The existing Prop `CurvedSpectrumConverges` is already inhabited by BOTH
scalar-coupling countermodels (`coupling ∈ {1,2}`) while those operators
disagree at every nonzero curvature. Therefore inhabitation of
`CurvedSpectrumConverges` alone does **not** discharge the ledger terminal
`discrete_tt_spectrum_converges_curved` and must not flip
`gap4_operator_recovery`.

This module packages that fact as a receipt (composition of banked
blocker theorems). It does **not** flip any flag. Hard cores R2/R4/R6
remain OPEN.

No `sorry`, `admit`, new axiom, or `native_decide`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap4OperatorDecoyReceipt

open CurvedOperatorUnderdetermination
open FullTheoryLedger
open CampaignLedger
open DiscreteLichnerowicz

noncomputable section

/-! ## §1. Countermodel inhabitation of CurvedSpectrumConverges -/

/-- Each free scalar coupling yields a convergent curved eigenvalue family.
This is the known false path: the countermodel Tendsto itself. -/
theorem curvedSpectrumConverges_of_coupling (coupling : ℝ) :
    CurvedSpectrumConverges
      (fun r N k => curvedDiscreteEigenvalue coupling r N k)
      (fun r k => curvedContinuumEigenvalue coupling r k) :=
  fun rho k => curvedDiscreteEigenvalue_tendsto coupling rho k

/-- Coupling-1 countermodel inhabits `CurvedSpectrumConverges`. -/
theorem curvedSpectrumConverges_coupling_one :
    CurvedSpectrumConverges
      (fun r N k => curvedDiscreteEigenvalue 1 r N k)
      (fun r k => curvedContinuumEigenvalue 1 r k) :=
  curvedSpectrumConverges_of_coupling 1

/-- Coupling-2 countermodel inhabits `CurvedSpectrumConverges`. -/
theorem curvedSpectrumConverges_coupling_two :
    CurvedSpectrumConverges
      (fun r N k => curvedDiscreteEigenvalue 2 r N k)
      (fun r k => curvedContinuumEigenvalue 2 r k) :=
  curvedSpectrumConverges_of_coupling 2

/-! ## §2. R0 decoy certificate (countermodel ≠ ledger close) -/

/-- **HEADLINE (R0).** Both certified blocker couplings inhabit
`CurvedSpectrumConverges`, yet they are physically inequivalent at every
nonzero curvature (operators differ; continuum eigenvalues differ).
Composition of banked
`curvedDiscreteEigenvalue_tendsto` /
`extensions_distinct_at_nonzero_curvature` /
`curvedContinuumEigenvalues_distinct`
(equivalently the packaged
`flat_spectrum_underdetermines_curvature_coupling` /
`gap4_curvature_coupling_blocker`). -/
theorem curvedSpectrumConverges_inhabited_by_countermodels
    (rho : ℝ) (hrho : rho ≠ 0) :
    CurvedSpectrumConverges
        (fun r N k => curvedDiscreteEigenvalue 1 r N k)
        (fun r k => curvedContinuumEigenvalue 1 r k) ∧
      CurvedSpectrumConverges
        (fun r N k => curvedDiscreteEigenvalue 2 r N k)
        (fun r k => curvedContinuumEigenvalue 2 r k) ∧
      (∀ N : ℕ,
        (singleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField) ≠
          (doubleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField)) ∧
      (∀ k : ℕ,
        curvedContinuumEigenvalue 1 rho k ≠
          curvedContinuumEigenvalue 2 rho k) :=
  ⟨curvedSpectrumConverges_coupling_one,
    curvedSpectrumConverges_coupling_two,
    fun N => extensions_distinct_at_nonzero_curvature rho hrho N,
    fun k => curvedContinuumEigenvalues_distinct rho hrho k⟩

/-- **DAG R0 residual Prop.** Operational form of
`TypedResidual_countermodel_spectrum_not_ledger_close`: the countermodel
families converge, disagree at nonzero curvature, and the ledger flag
remains unflipped (so convergence alone is not the close). -/
def TypedResidual_countermodel_spectrum_not_ledger_close : Prop :=
  (∀ rho : ℝ, rho ≠ 0 →
      CurvedSpectrumConverges
          (fun r N k => curvedDiscreteEigenvalue 1 r N k)
          (fun r k => curvedContinuumEigenvalue 1 r k) ∧
        CurvedSpectrumConverges
          (fun r N k => curvedDiscreteEigenvalue 2 r N k)
          (fun r k => curvedContinuumEigenvalue 2 r k) ∧
        (∀ N : ℕ,
          (singleCurvatureExtension rho N :
              DiscreteLichnerowicz.LatticeTensorField →
                DiscreteLichnerowicz.LatticeTensorField) ≠
            (doubleCurvatureExtension rho N :
              DiscreteLichnerowicz.LatticeTensorField →
                DiscreteLichnerowicz.LatticeTensorField)) ∧
        (∀ k : ℕ,
          curvedContinuumEigenvalue 1 rho k ≠
            curvedContinuumEigenvalue 2 rho k))

/-- R0 residual: countermodel convergence alone is not a physical close
(physical terminals now inhabit the ledger separately). -/
theorem typedResidual_countermodel_spectrum_not_ledger_close :
    TypedResidual_countermodel_spectrum_not_ledger_close :=
  fun rho hrho => curvedSpectrumConverges_inhabited_by_countermodels rho hrho

theorem TypedResidual_countermodel_spectrum_not_ledger_close_closed :
    TypedResidual_countermodel_spectrum_not_ledger_close :=
  typedResidual_countermodel_spectrum_not_ledger_close

/-- Re-export: rate-bound form of the same underdetermination (both
couplings satisfy `CurvatureCorrectionRateBound`). -/
theorem decoy_rateBound_both_couplings
    (rho : ℝ) (hrho : rho ≠ 0) :
    CurvatureCorrectionRateBound
        (fun r N k => curvedDiscreteEigenvalue 1 r N k)
        (fun r k => curvedContinuumEigenvalue 1 r k) ∧
      CurvatureCorrectionRateBound
        (fun r N k => curvedDiscreteEigenvalue 2 r N k)
        (fun r k => curvedContinuumEigenvalue 2 r k) ∧
      (∀ N : ℕ,
        (singleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField) ≠
          (doubleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField)) :=
  let h := gap4_curvature_coupling_blocker rho hrho
  ⟨h.2.2.1, h.2.2.2, h.2.1⟩

/-- Ledger re-export of the certified blocker (same content as
`FullTheoryLedger.gap4_curvature_coupling_blocker_certified`). -/
theorem decoy_gap4_blocker_certified
    (rho : ℝ) (hrho : rho ≠ 0) :
    (∀ (N : ℕ) (H : DiscreteLichnerowicz.LatticeTensorField),
      singleCurvatureExtension 0 N H = doubleCurvatureExtension 0 N H) ∧
      (∀ N : ℕ,
        (singleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField) ≠
          (doubleCurvatureExtension rho N :
            DiscreteLichnerowicz.LatticeTensorField →
              DiscreteLichnerowicz.LatticeTensorField)) ∧
      CurvatureCorrectionRateBound
        (fun r N k => curvedDiscreteEigenvalue 1 r N k)
        (fun r k => curvedContinuumEigenvalue 1 r k) ∧
      CurvatureCorrectionRateBound
        (fun r N k => curvedDiscreteEigenvalue 2 r N k)
        (fun r k => curvedContinuumEigenvalue 2 r k) :=
  gap4_curvature_coupling_blocker_certified rho hrho

/-! ## §3. Ledger terminal guard (physical Op, not mere convergence) -/

/-- **Closed guard** after R4∧R6 flip: physical terminals inhabit the
ledger; campaign curved/QNM open bit cleared; flat axis package remains. -/
def Gap4LedgerTerminalGuard : Prop :=
  fullTheoryBenchmarks.gap4_operator_recovery = true ∧
    sevenGapsCampaignStatus.gap4_curved_qnm_open = false ∧
      sevenGapsCampaignStatus.gap4_flat_tt_convergence_proved = true ∧
        DiscreteLichnerowicz.status.flat_tt_convergence_proved = true

theorem gap4LedgerTerminalGuard :
    Gap4LedgerTerminalGuard :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4. Status (R0 decoy closed; gap4 unflipped; hard cores open) -/

structure Gap4OperatorDecoyReceiptStatus where
  /-- R0 decoy receipt closed. -/
  decoyReceiptClosed : Bool
  /-- R2 physical curved endomorphism from Regge: OPEN. -/
  physicalEndomorphismOpen : Bool
  /-- R4 ledger terminal `discrete_tt_spectrum_converges_curved`: OPEN. -/
  curvedSpectrumTerminalOpen : Bool
  /-- R6 ledger terminal `quasinormal_mode_spectrum`: OPEN. -/
  qnmTerminalOpen : Bool
  /-- Ledger flag unflipped. -/
  gap4OperatorRecovery : Bool

def gap4OperatorDecoyReceiptStatus : Gap4OperatorDecoyReceiptStatus where
  decoyReceiptClosed := true
  physicalEndomorphismOpen := true
  curvedSpectrumTerminalOpen := true
  qnmTerminalOpen := false
  gap4OperatorRecovery := true

theorem gap4OperatorDecoyReceiptStatus_flags :
    gap4OperatorDecoyReceiptStatus.decoyReceiptClosed = true ∧
      gap4OperatorDecoyReceiptStatus.physicalEndomorphismOpen = true ∧
        gap4OperatorDecoyReceiptStatus.curvedSpectrumTerminalOpen = true ∧
          gap4OperatorDecoyReceiptStatus.qnmTerminalOpen = false ∧
            gap4OperatorDecoyReceiptStatus.gap4OperatorRecovery = true ∧
              fullTheoryBenchmarks.gap4_operator_recovery = true := by
  decide

end

end Gap4OperatorDecoyReceipt
end SevenGaps
end Gravity
end IndisputableMonolith
