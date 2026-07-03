import IndisputableMonolith.NumberTheory.RHRecognitionRecast
import IndisputableMonolith.NumberTheory.BoundaryTransport
import IndisputableMonolith.NumberTheory.ProxyPhysicalizationBridge
import IndisputableMonolith.NumberTheory.HonestPhaseAdmissibility
import IndisputableMonolith.NumberTheory.CompositionDivergence

/-!
  BridgeStrengthAudit.lean

  Track A of the RH unconditional-closure plan.

  The purpose of this module is not to claim a new route to RH. It records the
  exact logical strength of the currently named bridge objects. Some bridges
  are already proved equivalent to the RH core. Others only imply the witnessed
  RH core, and their planned reverse directions are too strong under the
  current definitions: they require a `ZeroCompositionWitness` for a point whose
  `WitnessedDefectSensor.in_strip` field explicitly places it off the critical
  line.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace BridgeStrengthAudit

open AnalyticTrace
open VectorCFromHonestPhase
open GenuineZetaPhaseFromRCL
open CanonicalZeroComposition
open StripZeroFreeRegion
open RHRecognitionRecast

noncomputable section

/-! ## 1. The witnessed RH core used by the analytic bridges -/

/-- The witnessed RH core used by the analytic bridge family. -/
def WitnessedRHCore : Prop :=
  ∀ sensor : WitnessedDefectSensor, sensor.charge = 0

/-- The contradiction form is equivalent to the charge-zero form. -/
theorem witnessedRHCore_iff_no_nonzero_witness :
    WitnessedRHCore ↔
      (∀ sensor : WitnessedDefectSensor, sensor.charge ≠ 0 → False) := by
  constructor
  · intro h sensor hne
    exact hne (h sensor)
  · intro h sensor
    by_contra hne
    exact h sensor hne

/-! ## 2. Already exact RH-equivalent bridge surfaces -/

/-- Boundary transport is exactly the abstract no-nonzero-charge RH core. -/
theorem boundaryTransport_exact :
    BoundaryTransportCert ↔
      (∀ sensor : DefectSensor, sensor.charge ≠ 0 → False) :=
  boundaryTransportCert_iff_rh_core

/-- Zero-induced proxy physicalization is exactly Mathlib's RH. -/
theorem zeroInducedProxyPhysicalization_exact :
    ZeroInducedProxyPhysicalizationBridge ↔ RiemannHypothesis :=
  zeroInducedBridge_iff_rh

/-- Honest phase cost is exactly the witnessed RH core. -/
theorem honestPhaseCostBridge_exact :
    HonestPhaseCostBridge ↔ WitnessedRHCore := by
  simpa [WitnessedRHCore] using HonestPhaseCostBridge_iff_rh

/-- Witnessed admissibility is exactly the witnessed RH core. -/
theorem witnessedAdmissibilityBridge_exact :
    WitnessedHonestPhaseAdmissibilityBridge ↔ WitnessedRHCore := by
  simpa [WitnessedRHCore] using witnessedHonestPhaseAdmissibilityBridge_iff_rh

/-- The witness-only nonzero Vector-C bridge is exactly the witnessed RH core. -/
theorem nonzeroWitnessBridge_exact :
    Nonempty NonzeroZeroCompositionWitnessBridge ↔ WitnessedRHCore := by
  constructor
  · intro hbridge sensor
    have hno : ¬ ∃ sensor : WitnessedDefectSensor, sensor.charge ≠ 0 :=
      nonempty_nonzeroWitnessBridge_iff_no_nonzero_charge.mp hbridge
    by_contra hne
    exact hno ⟨sensor, hne⟩
  · intro hcore
    exact nonempty_nonzeroWitnessBridge_iff_no_nonzero_charge.mpr (by
      rintro ⟨sensor, hne⟩
      exact hne (hcore sensor))

/-- The newly isolated critical-strip bridge closes the witnessed recovered
RH thesis. This is one-way because the module currently records only the
right-half strip bridge, not a full equivalence with Mathlib's RH. -/
theorem criticalStripBridge_closes_logicRH :
    CriticalStripZeroFreeBridge → LogicRHWitnessedThesis :=
  logicRHWitnessedThesis_of_criticalStripZeroFreeBridge

/-! ## 3. Exact equivalences that can be added now -/

/-- A zero-free criterion is exactly the witnessed RH core.

The reverse direction is vacuous only in the specific fields that require
nonzero witnessed sensors; the `charge_zero_of_honest_phase` field is supplied
directly by the witnessed RH core. -/
theorem zeroFreeCriterion_iff_witnessedRHCore :
    ZeroFreeCriterion ↔ WitnessedRHCore := by
  constructor
  · intro zfc sensor
    by_contra hne
    exact rh_from_zero_free_criterion zfc sensor hne
  · intro h
    exact {
      logDeriv_bounded_on_strip := fun _ hσ => carrierDerivBound_pos hσ
      carrier_nonvanishing_on_strip := fun _ hσ => carrier_nonvanishing hσ
      honest_phase_family := by
        intro sensor hne
        exact False.elim (hne (h sensor))
      charge_zero_of_honest_phase := by
        intro sensor _hzfd
        exact h sensor
    }

/-- The composition-closure hypothesis is exactly the statement that every
complex point is on the critical line. This is stronger than Mathlib's RH
because it does not restrict to zeros of `riemannZeta`. -/
theorem compositionClosureHypothesis_iff_all_points_on_line :
    Nonempty CompositionClosureHypothesis ↔
      (∀ ρ : ℂ, ¬ OnCriticalLine ρ → False) := by
  constructor
  · intro hcch
    rcases hcch with ⟨cch⟩
    exact rh_from_composition_closure cch
  · intro h
    exact ⟨{
      bound := 0
      reflected := by
        intro ρ hρ n
        exact False.elim (h ρ hρ)
    }⟩

/-! ## 4. One-way bridges and their obstruction -/

/-- A witnessed sensor in the current API is strictly to the right of the
critical line, so it cannot carry a zero-composition witness. -/
theorem not_zeroCompositionWitness_of_witnessedSensor
    (sensor : WitnessedDefectSensor) :
    ZeroCompositionWitness sensor.rho → False := by
  intro w
  have hline : OnCriticalLine sensor.rho :=
    zeroCompositionWitness_forces_on_critical_line w
  have hstrip : 1 / 2 < sensor.rho.re := sensor.in_strip.1
  have hre : sensor.rho.re = 1 / 2 := hline
  linarith

/-- Consequently, a Vector-C bridge plus matching honest phase data for a
witnessed sensor is impossible. This is why a reverse implication from the
witnessed RH core to `VectorCChargeZeroBridge` is not available under the
current broad definition of the bridge. -/
theorem vectorCBridge_forbids_matching_phase_data
    (bridge : VectorCChargeZeroBridge)
    (sensor : WitnessedDefectSensor)
    (hzfd : ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = sensor.toDefectSensor) :
    False :=
  not_zeroCompositionWitness_of_witnessedSensor sensor
    (bridge.witness_of_honest_phase sensor hzfd)

/-- The phase-composition bridge implies the witnessed RH core. -/
theorem phaseCompositionBridge_implies_witnessedRHCore
    (bridge : ZetaPhaseCompositionBridge) :
    WitnessedRHCore := by
  exact (witnessedRHCore_iff_no_nonzero_witness.mpr
    (witnessed_rh_from_phaseCompositionBridge bridge))

/-- The genuine phase bridge implies the witnessed RH core. -/
theorem genuinePhaseCompositionBridge_implies_witnessedRHCore
    (bridge : GenuinePhaseCompositionBridge) :
    WitnessedRHCore := by
  exact (witnessedRHCore_iff_no_nonzero_witness.mpr
    (witnessed_rh_from_genuinePhaseCompositionBridge bridge))

/-- The canonical-minimum bridge implies the witnessed RH core. -/
theorem canonicalMinimumBridge_implies_witnessedRHCore
    (bridge : GenuinePhaseCanonicalMinimumBridge) :
    WitnessedRHCore := by
  exact (witnessedRHCore_iff_no_nonzero_witness.mpr
    (witnessed_rh_from_canonicalMinimumBridge bridge))

/-- A direct honest-phase charge-zero bridge implies the witnessed RH core.
The reverse direction is not available for arbitrary `ZetaPhaseFamilyData`,
which need not be tied to a witnessed sensor. -/
theorem honestPhaseChargeZeroBridge_implies_witnessedRHCore
    (bridge : HonestPhaseChargeZeroBridge) :
    WitnessedRHCore := by
  exact (witnessedRHCore_iff_no_nonzero_witness.mpr
    (direct_rh_from_honestPhaseChargeZeroBridge bridge))

/-! ## 5. Machine-readable summary bundle -/

/-- RH-equivalent bridge family currently proved as exact iff statements. -/
structure RHEquivalentBridgeFamily where
  boundaryTransport :
    BoundaryTransportCert ↔
      (∀ sensor : DefectSensor, sensor.charge ≠ 0 → False)
  zeroInducedProxy :
    ZeroInducedProxyPhysicalizationBridge ↔ RiemannHypothesis
  honestPhaseCost :
    HonestPhaseCostBridge ↔ WitnessedRHCore
  witnessedAdmissibility :
    WitnessedHonestPhaseAdmissibilityBridge ↔ WitnessedRHCore
  nonzeroWitnessBridge :
    Nonempty NonzeroZeroCompositionWitnessBridge ↔ WitnessedRHCore
  zeroFreeCriterion :
    ZeroFreeCriterion ↔ WitnessedRHCore

def rhEquivalentBridgeFamily : RHEquivalentBridgeFamily where
  boundaryTransport := boundaryTransport_exact
  zeroInducedProxy := zeroInducedProxyPhysicalization_exact
  honestPhaseCost := honestPhaseCostBridge_exact
  witnessedAdmissibility := witnessedAdmissibilityBridge_exact
  nonzeroWitnessBridge := nonzeroWitnessBridge_exact
  zeroFreeCriterion := zeroFreeCriterion_iff_witnessedRHCore

/-- One-way bridge family: these imply witnessed RH, but current definitions do
not support the planned reverse direction as an iff theorem. -/
structure RHOneWayBridgeFamily where
  vectorC :
    VectorCChargeZeroBridge → WitnessedRHCore
  phaseComposition :
    ZetaPhaseCompositionBridge → WitnessedRHCore
  genuinePhaseComposition :
    GenuinePhaseCompositionBridge → WitnessedRHCore
  canonicalMinimum :
    GenuinePhaseCanonicalMinimumBridge → WitnessedRHCore
  criticalStrip :
    CriticalStripZeroFreeBridge → LogicRHWitnessedThesis
  compositionClosure :
    Nonempty CompositionClosureHypothesis ↔
      (∀ ρ : ℂ, ¬ OnCriticalLine ρ → False)

def rhOneWayBridgeFamily : RHOneWayBridgeFamily where
  vectorC := fun bridge =>
    witnessedRHCore_iff_no_nonzero_witness.mpr
      (direct_rh_from_vectorC_bridge bridge)
  phaseComposition := phaseCompositionBridge_implies_witnessedRHCore
  genuinePhaseComposition := genuinePhaseCompositionBridge_implies_witnessedRHCore
  canonicalMinimum := canonicalMinimumBridge_implies_witnessedRHCore
  criticalStrip := criticalStripBridge_closes_logicRH
  compositionClosure := compositionClosureHypothesis_iff_all_points_on_line

/-- Track A status theorem: all currently justified equivalence and one-way
surfaces are packaged in this module. -/
theorem bridgeStrengthAudit_complete :
    Nonempty RHEquivalentBridgeFamily ∧ Nonempty RHOneWayBridgeFamily :=
  ⟨⟨rhEquivalentBridgeFamily⟩, ⟨rhOneWayBridgeFamily⟩⟩

end

end BridgeStrengthAudit
end NumberTheory
end IndisputableMonolith
