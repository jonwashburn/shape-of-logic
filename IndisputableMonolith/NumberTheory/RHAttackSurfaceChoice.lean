import IndisputableMonolith.NumberTheory.BridgeStrengthAudit

/-!
  RHAttackSurfaceChoice.lean

  Track G of the RH unconditional-closure plan.

  After the bridge-strength audit, the cleanest primary attack surface is the
  critical-strip zero-free bridge:

    `CriticalStripZeroFreeBridge`

  It feeds directly into the recovered-arithmetic RH chain and does not require
  the over-strong Vector-C `ZeroCompositionWitness` fields that currently
  contradict `WitnessedDefectSensor.in_strip` for arbitrary matching phase
  data.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace RHAttackSurfaceChoice

open BridgeStrengthAudit
open StripZeroFreeRegion
open RHRecognitionRecast

noncomputable section

/-- Candidate attack surfaces after Track A. -/
inductive AttackSurface
  | boundaryTransport
  | zeroInducedProxy
  | criticalStrip
  | honestPhaseCost
deriving DecidableEq, Repr

/-- The selected primary surface for the next serious attack. -/
def chosenAttackSurface : AttackSurface :=
  AttackSurface.criticalStrip

/-- The chosen surface closes the recovered witnessed RH thesis when supplied. -/
theorem chosenAttackSurface_closes_logicRH
    (bridge : CriticalStripZeroFreeBridge) :
    LogicRHWitnessedThesis :=
  logicRHWitnessedThesis_of_criticalStripZeroFreeBridge bridge

/-- Selection certificate. -/
structure AttackSurfaceSelection where
  chosen : AttackSurface
  closes_logicRH :
    chosen = AttackSurface.criticalStrip →
      CriticalStripZeroFreeBridge → LogicRHWitnessedThesis
  reason_vectorC_not_primary :
    ∀ sensor : WitnessedDefectSensor,
      ZeroCompositionWitness sensor.rho → False

def attackSurfaceSelection : AttackSurfaceSelection where
  chosen := chosenAttackSurface
  closes_logicRH := by
    intro hchosen bridge
    exact chosenAttackSurface_closes_logicRH bridge
  reason_vectorC_not_primary :=
    not_zeroCompositionWitness_of_witnessedSensor

end

end RHAttackSurfaceChoice
end NumberTheory
end IndisputableMonolith
