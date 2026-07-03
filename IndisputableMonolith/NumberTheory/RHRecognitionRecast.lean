import IndisputableMonolith.NumberTheory.CanonicalZeroComposition
import IndisputableMonolith.NumberTheory.ZetaLedgerBridge
import IndisputableMonolith.NumberTheory.StripZeroFreeRegion
import IndisputableMonolith.NumberTheory.ZetaFromTheta
import IndisputableMonolith.Foundation.IntegersFromLogic

/-!
  RHRecognitionRecast.lean

  Express the RH edge entirely through the recovered arithmetic substrate.

  Methodology:

  1. The recovered integers `LogicInt` from `Foundation.IntegersFromLogic`
     are used as the carrier of zeta-zero charge data.
  2. The previous canonical-minimum bridge is restated in recovered-integer
     terms, then connected to the existing `PhysicallyExists` ontological
     dichotomy (`charge_zero_iff_physicallyExists`).
  3. The remaining open content is named cleanly: every witnessed defect
     sensor is physically realized in the recovered RS ledger.

  This module does not prove RH. It puts the RS recognition substrate
  on the actual edge and shows that the existing analytic chain becomes a
  recovered-arithmetic chain with the same irreducible bite.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace RHRecognitionRecast

open Foundation.IntegersFromLogic
open Foundation.IntegersFromLogic.LogicInt
open IndisputableMonolith.Unification.UnifiedRH
open CanonicalZeroComposition
open GenuineZetaPhaseFromRCL

noncomputable section

/-! ## 1. Recovered-integer charge -/

/-- The recovered-integer charge of a witnessed defect sensor. -/
def logicCharge (sensor : WitnessedDefectSensor) : LogicInt :=
  fromInt sensor.charge

/-- The recovered charge vanishes iff the classical charge vanishes. -/
theorem logicCharge_zero_iff_classical (sensor : WitnessedDefectSensor) :
    logicCharge sensor = (0 : LogicInt) ↔ sensor.charge = 0 := by
  unfold logicCharge
  constructor
  · intro h
    have := congrArg toInt h
    rw [toInt_fromInt, toInt_zero] at this
    exact this
  · intro h
    rw [eq_iff_toInt_eq, toInt_fromInt, toInt_zero, h]

/-- The recovered charge of a defect sensor (without witness). -/
def logicChargeOfSensor (sensor : DefectSensor) : LogicInt :=
  fromInt sensor.charge

theorem logicChargeOfSensor_zero_iff_classical (sensor : DefectSensor) :
    logicChargeOfSensor sensor = (0 : LogicInt) ↔ sensor.charge = 0 := by
  unfold logicChargeOfSensor
  constructor
  · intro h
    have := congrArg toInt h
    rw [toInt_fromInt, toInt_zero] at this
    exact this
  · intro h
    rw [eq_iff_toInt_eq, toInt_fromInt, toInt_zero, h]

/-! ## 2. Ontological dichotomy in recovered arithmetic -/

/-- Recovered-arithmetic form of the ontological dichotomy: the recovered
charge of a defect sensor vanishes iff the sensor is physically realized in
the RS ledger. -/
theorem logicCharge_zero_iff_physicallyExists (sensor : DefectSensor) :
    logicChargeOfSensor sensor = (0 : LogicInt) ↔ PhysicallyExists sensor := by
  rw [logicChargeOfSensor_zero_iff_classical]
  exact charge_zero_iff_physicallyExists sensor

/-- Witnessed-sensor form of the recovered dichotomy. -/
theorem witnessed_logicCharge_zero_iff_physicallyExists
    (sensor : WitnessedDefectSensor) :
    logicCharge sensor = (0 : LogicInt) ↔
      PhysicallyExists sensor.toDefectSensor := by
  rw [logicCharge_zero_iff_classical,
      ← WitnessedDefectSensor.toDefectSensor_charge sensor]
  exact charge_zero_iff_physicallyExists _

/-! ## 3. Canonical minimum implies recovered charge zero -/

/-- A canonical minimum certificate forces the witnessed sensor's
recovered-integer charge to vanish. -/
theorem logicCharge_zero_of_canonicalMinimumCert
    {sensor : WitnessedDefectSensor} {gzfd : GenuineZetaPhaseFamilyData}
    (cert : GenuinePhaseCanonicalMinimumCert sensor gzfd) :
    logicCharge sensor = (0 : LogicInt) := by
  have hline : OnCriticalLine sensor.rho :=
    (canonical_value_one_iff_zeroDeviation sensor.rho).mp cert.canonical_minimum
  have hcontr : False := by
    have hstrip : 1 / 2 < sensor.rho.re := sensor.in_strip.1
    have hre : sensor.rho.re = 1 / 2 := hline
    linarith
  exact False.elim hcontr

/-! ## 4. Recovered-arithmetic RH thesis -/

/-- Witnessed-sensor recovered RH thesis: every witnessed defect sensor has
recovered-integer charge zero.

Equivalently (by the dichotomy): every witnessed defect sensor is physically
realized in the RS ledger.

This is the recovered-arithmetic restatement of the witnessed RH core. -/
def LogicRHWitnessedThesis : Prop :=
  ∀ sensor : WitnessedDefectSensor, logicCharge sensor = (0 : LogicInt)

/-- Sensor-level recovered RH thesis. -/
def LogicRHSensorThesis : Prop :=
  ∀ sensor : DefectSensor, logicChargeOfSensor sensor = (0 : LogicInt)

/-- The recovered witnessed thesis is logically equivalent to the witnessed RH
core. -/
theorem logicRHWitnessedThesis_iff_witnessed_rh :
    LogicRHWitnessedThesis ↔
      (∀ sensor : WitnessedDefectSensor, sensor.charge = 0) := by
  unfold LogicRHWitnessedThesis
  refine forall_congr' (fun sensor => ?_)
  exact logicCharge_zero_iff_classical sensor

/-- The sensor-level recovered thesis is the recovered restatement of the
ontological dichotomy: every defect sensor is physically realized. -/
theorem logicRHSensorThesis_iff_all_physical :
    LogicRHSensorThesis ↔
      (∀ sensor : DefectSensor, PhysicallyExists sensor) := by
  unfold LogicRHSensorThesis
  refine forall_congr' (fun sensor => ?_)
  exact logicCharge_zero_iff_physicallyExists sensor

/-- The recovered sensor thesis implies the witnessed core. -/
theorem witnessed_rh_from_logicRHSensorThesis
    (h : LogicRHSensorThesis) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hne
  have hphys :=
    (logicRHSensorThesis_iff_all_physical.mp h) sensor.toDefectSensor
  have hzero :
      sensor.toDefectSensor.charge = 0 :=
    (charge_zero_iff_physicallyExists sensor.toDefectSensor).mpr hphys
  rw [WitnessedDefectSensor.toDefectSensor_charge] at hzero
  exact hne hzero

/-- A canonical-minimum bridge implies the recovered witnessed RH thesis. -/
theorem logicRHWitnessedThesis_of_canonicalMinimumBridge
    (bridge : GenuinePhaseCanonicalMinimumBridge) :
    LogicRHWitnessedThesis := by
  intro sensor
  by_cases hne : sensor.charge = 0
  · exact (logicCharge_zero_iff_classical sensor).mpr hne
  · obtain ⟨zfd, hzs, hzf⟩ :=
      honest_argument_principle_phase_family sensor hne
    have cert := bridge.minimum_of_genuine_phase sensor zfd hzs hzf
    exact logicCharge_zero_of_canonicalMinimumCert cert

/-! ## 5. Final attack-surface summary -/

/-- The full RH chain expressed in recovered-arithmetic recognition terms. -/
structure RHRecognitionAttackSurface where
  arithmetic : VectorCFromHonestPhase.RecoveredArithmeticSubstrate
  canonical_law : ZeroCompositionLaw
  canonical_law_is_cosh : ∀ t : ℝ, canonical_law.H t = Real.cosh t
  ontological_dichotomy :
    ∀ sensor : DefectSensor,
      logicChargeOfSensor sensor = (0 : LogicInt) ↔ PhysicallyExists sensor
  open_logic_thesis : LogicRHWitnessedThesis → Prop

/-- The recognition attack surface is constructed from already-derived
content; only the recovered RH thesis remains as the named open input. -/
noncomputable def rhRecognitionAttackSurface : RHRecognitionAttackSurface where
  arithmetic := VectorCFromHonestPhase.recoveredArithmeticSubstrate
  canonical_law := canonicalZeroCompositionLaw
  canonical_law_is_cosh := canonicalZeroCompositionLaw_forces_cosh
  ontological_dichotomy := logicCharge_zero_iff_physicallyExists
  open_logic_thesis := fun _ => True

/-- The recovered RH thesis (witnessed form) closes the witnessed RH core. -/
theorem witnessed_rh_from_logicRHWitnessedThesis
    (h : LogicRHWitnessedThesis) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hne
  exact hne (logicRHWitnessedThesis_iff_witnessed_rh.mp h sensor)

/-! ## 6. Phase 6 + Phase 7 closure of the recovered chain

The strong analytic inputs of the RH chain are now:

* a `CompletedZetaFunctionalEquationCert` (Phase 6, unconditionally inhabited
  from Mathlib);
* a `CriticalStripZeroFreeBridge` (Phase 7, the named open input that is no
  stronger than Mathlib's `RiemannHypothesis`).

We show that with the strip bridge, the recovered witnessed RH thesis closes
without any further analytic work. This is the honest end of the chain: every
remaining gap is concentrated in the strip bridge. -/

open StripZeroFreeRegion

/-- A witnessed defect sensor's hypothetical zero `ρ` lies strictly inside the
critical strip, in particular `ρ ≠ 1`. -/
private lemma witnessed_rho_ne_one (sensor : WitnessedDefectSensor) :
    sensor.rho ≠ 1 := by
  intro h
  have hre : sensor.rho.re = 1 := by simp [h]
  have hlt : sensor.rho.re < 1 := sensor.in_strip.2
  linarith

/-- If the open right half-strip is zero-free, every witnessed defect sensor
has charge zero.

This packages the meromorphic-order calculation: at any `ρ` with
`1/2 < Re ρ < 1`, `ζ` is analytic and (by hypothesis) nonzero, so
`meromorphicOrderAt zetaReciprocal ρ = 0`, which forces the sensor charge to
be zero. -/
theorem logicCharge_zero_of_criticalStripZeroFree
    (w : CriticalStripZeroFree) (sensor : WitnessedDefectSensor) :
    logicCharge sensor = (0 : LogicInt) := by
  have hne1 : sensor.rho ≠ 1 := witnessed_rho_ne_one sensor
  have hzeta_ne : riemannZeta sensor.rho ≠ 0 :=
    w.zero_free sensor.rho sensor.in_strip.1 sensor.in_strip.2
  have hAnalytic : AnalyticAt ℂ riemannZeta sensor.rho :=
    analyticAt_riemannZeta hne1
  have hzeta_ord :
      analyticOrderAt riemannZeta sensor.rho = 0 :=
    hAnalytic.analyticOrderAt_eq_zero.mpr hzeta_ne
  have hzeta_mero_ord :
      meromorphicOrderAt riemannZeta sensor.rho = 0 := by
    have := hAnalytic.meromorphicOrderAt_eq
    rw [hzeta_ord] at this
    simpa using this
  have hrec_ord :
      meromorphicOrderAt zetaReciprocal sensor.rho = 0 := by
    rw [meromorphicOrderAt_zetaReciprocal, hzeta_mero_ord]; simp
  have hwit := sensor.order_witness
  rw [hrec_ord] at hwit
  have hcharge_neg : (-sensor.charge : ℤ) = 0 := by
    have : ((-sensor.charge : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := hwit.symm
    exact_mod_cast this
  have hcharge : sensor.charge = 0 := by linarith
  exact (logicCharge_zero_iff_classical sensor).mpr hcharge

/-- The critical-strip bridge closes the recovered RH thesis. -/
theorem logicRHWitnessedThesis_of_criticalStripZeroFreeBridge
    (bridge : CriticalStripZeroFreeBridge) :
    LogicRHWitnessedThesis := by
  intro sensor
  rcases bridge with ⟨w⟩
  exact logicCharge_zero_of_criticalStripZeroFree w sensor

/-- The RS-Native Zeta Phase 8 certificate.

A bundle of:
* the unconditional Phase 6 cert (FE for completed zeta) from Mathlib,
* a closure theorem reducing the recovered RH thesis to the named Phase 7
  critical-strip bridge,
* the witnessed-RH consequence, also gated on the same bridge. -/
structure RSNativeZetaPhase8Cert where
  fe_cert : ZetaFromTheta.CompletedZetaFunctionalEquationCert
  closure :
    CriticalStripZeroFreeBridge → LogicRHWitnessedThesis
  closure_implies_witnessed_rh :
    CriticalStripZeroFreeBridge →
      ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False

def rsNativeZetaPhase8Cert : RSNativeZetaPhase8Cert where
  fe_cert := ZetaFromTheta.completedZetaFunctionalEquationCert
  closure := logicRHWitnessedThesis_of_criticalStripZeroFreeBridge
  closure_implies_witnessed_rh := by
    intro bridge sensor hne
    exact witnessed_rh_from_logicRHWitnessedThesis
      (logicRHWitnessedThesis_of_criticalStripZeroFreeBridge bridge) sensor hne

/-- Phase 8 honest summary, as a single theorem.

`(Phase 6 cert ∧ Phase 7 bridge) → recovered RH thesis closes`.

Phase 6 is unconditionally inhabited, so the entire bite is concentrated in
the Phase 7 bridge, which is no stronger than Mathlib's `RiemannHypothesis`. -/
theorem rsNativeZeta_phase8_closure
    (_fe : ZetaFromTheta.CompletedZetaFunctionalEquationCert)
    (bridge : CriticalStripZeroFreeBridge) :
    LogicRHWitnessedThesis :=
  logicRHWitnessedThesis_of_criticalStripZeroFreeBridge bridge

/-- Mathlib's RH closes the recovered chain. This is not new mathematics; it
exhibits the recovered chain as a strict consequence of `RiemannHypothesis`. -/
theorem logicRHWitnessedThesis_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    LogicRHWitnessedThesis :=
  logicRHWitnessedThesis_of_criticalStripZeroFreeBridge
    (criticalStripZeroFreeBridge_of_riemannHypothesis hRH)

end

end RHRecognitionRecast
end NumberTheory
end IndisputableMonolith
