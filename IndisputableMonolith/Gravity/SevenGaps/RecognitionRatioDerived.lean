import IndisputableMonolith.Gravity.Analysis.RecognitionMeshDualEntryCoupling4D
import IndisputableMonolith.Gravity.SevenGaps.RecognitionRatioSubstrateBlocker

/-!
# Wave B residual R5: ledger-named `recognition_ratio_derived`

QG full-completion session, Wave B. Packages the R4 inhabited coupling
`meshDualEntryCoupling` with the blocker's conditional derivation and the
stationarity minimizer receipt under the exact ledger Prop name named by
`FullTheoryLedger.FullTheoryBenchmarks.gap1_bridge_derived`.

## Honesty / scope

* Does **not** flip `gap1_bridge_derived` (R6 needs R0a + R0b + this Prop).
* Carrier remains the reshaped `H = ℝ` from R1–R4, not an encoded
  Freudenthal triangulation (`encodedFreudenthalLiftOpen` upstream).
* The enrichment existential is discharged by the mesh dual-entry family
  `meshDualEntry` (R3/R4), not by a bare `RecognitionLedger`.
* No field of the premise smuggles `xRatio`; the log appears only in the
  derived conclusions inherited from the blocker.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps

open Analysis.RecognitionMeshDualEntryCoupling4D
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## §1. Ledger-named closing Prop (derivation half) -/

/-- **Ledger-named Prop (derivation half of `gap1_bridge_derived`).**

There exists a dual-entry enrichment and an assembled
`DeficitSourceConstitutiveCoupling` equal to the mesh dual-entry coupling,
such that (i) the blocker's conditional recognition-ratio inequality holds
at every carrier point, and (ii) the log-ratio equals the total strain of
the unique sourced J-stationarity minimizer (so `xRatio` is the
exponential of that minimizer strain, not a posited field). -/
def recognition_ratio_derived : Prop :=
  ∃ (E : ℝ → DualEntryStrainState (Fin 1))
    (C : DeficitSourceConstitutiveCoupling ℝ),
    (∀ h, E h = meshDualEntry h) ∧
      C = meshDualEntryCoupling ∧
        (∀ σ,
          |Real.log ((ratioBridgeFromDeficitSourceCoupling C).xRatio σ)
              - C.kappa σ * C.geometricDeficit σ|
            ≤ (C.channels : ℝ) / 6 * C.meshScale ^ 3) ∧
          (∀ σ,
            Real.log ((ratioBridgeFromDeficitSourceCoupling C).xRatio σ)
              = ∑ i, sourcedMinimizer C.channels (C.sourceStrength σ) i) ∧
            (∀ σ,
              (ratioBridgeFromDeficitSourceCoupling C).xRatio σ
                = Real.exp
                    (∑ i, sourcedMinimizer C.channels
                      (C.sourceStrength σ) i))

/-- **THEOREM (R5 closed).** The ledger-named Prop is inhabited by the
mesh dual-entry coupling: conditional inequality from
`recognition_ratio_derived_of_deficit_source_coupling`, minimizer
identification from `deficitSourceCoupling_logRatio_eq_minimizer_strain`. -/
theorem recognition_ratio_derived_holds : recognition_ratio_derived := by
  refine ⟨meshDualEntry, meshDualEntryCoupling, fun _ => rfl, rfl, ?_, ?_, ?_⟩
  · intro σ
    exact recognition_ratio_derived_of_deficit_source_coupling
      meshDualEntryCoupling σ
  · intro σ
    exact deficitSourceCoupling_logRatio_eq_minimizer_strain
      meshDualEntryCoupling σ
  · intro σ
    have hlog :=
      deficitSourceCoupling_logRatio_eq_minimizer_strain meshDualEntryCoupling σ
    have hpos :
        0 < (ratioBridgeFromDeficitSourceCoupling
          meshDualEntryCoupling).xRatio σ :=
      (ratioBridgeFromDeficitSourceCoupling meshDualEntryCoupling).xRatio_pos σ
    calc (ratioBridgeFromDeficitSourceCoupling meshDualEntryCoupling).xRatio σ
        = Real.exp
            (Real.log
              ((ratioBridgeFromDeficitSourceCoupling
                meshDualEntryCoupling).xRatio σ)) :=
          (Real.exp_log hpos).symm
      _ = Real.exp
            (∑ i, sourcedMinimizer meshDualEntryCoupling.channels
              (meshDualEntryCoupling.sourceStrength σ) i) := by
          rw [hlog]

/-- Alias matching the DAG residual name. -/
def TypedResidual_recognition_ratio_derived : Prop :=
  recognition_ratio_derived

theorem typedResidual_recognition_ratio_derived_closed :
    TypedResidual_recognition_ratio_derived :=
  recognition_ratio_derived_holds

theorem TypedResidual_recognition_ratio_derived_closed :
    TypedResidual_recognition_ratio_derived :=
  typedResidual_recognition_ratio_derived_closed

/-! ## §2. Status (no FullTheoryLedger / CampaignLedger flag touch) -/

structure RecognitionRatioDerivedStatus where
  r5Closed : Bool
  gap1BridgeDerived : Bool

def recognitionRatioDerivedStatus : RecognitionRatioDerivedStatus where
  r5Closed := true
  gap1BridgeDerived := false

theorem recognitionRatioDerivedStatus_flags :
    recognitionRatioDerivedStatus.r5Closed = true ∧
      recognitionRatioDerivedStatus.gap1BridgeDerived = false := by
  decide

end

end SevenGaps
end Gravity
end IndisputableMonolith
