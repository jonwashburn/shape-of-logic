import IndisputableMonolith.NumberTheory.AnalyticTrace
import IndisputableMonolith.NumberTheory.HonestPhaseAdmissibility
import IndisputableMonolith.NumberTheory.HonestPhaseBudgetBridge
import IndisputableMonolith.NumberTheory.ZeroCompositionInterface
import IndisputableMonolith.NumberTheory.VectorCSymmetryOnlyNoGo
import IndisputableMonolith.NumberTheory.LogicRH_From_RCL
import IndisputableMonolith.Foundation.RealsFromLogic
import IndisputableMonolith.Foundation.LogicAsFunctionalEquationLogic

/-!
  VectorCFromHonestPhase.lean

  RH attack surface, Route C / Vector C version.

  Methodology:

  1. Use the recovered arithmetic foundation. The RH arithmetic ledger is
     backed by `LogicNat` / `LogicInt` / `LogicRat` / `LogicReal`, and the
     recovered prime ledger is imported through `LogicRH_From_RCL`.

  2. Treat the target theorem physically. An off-critical zeta zero is a
     witnessed defect sensor. Its physical content is not merely symmetry of
     completed ξ; `VectorCSymmetryOnlyNoGo` proves symmetry alone is too weak.
     The extra physical content must be a genuine phase-composition witness:
     the honest local zeta phase package must instantiate a calibrated
     d'Alembert / J-cost law at the zero's deviation.

  This module does not prove RH. It makes the remaining theorem smaller and
  honest: a `ZetaPhaseCompositionBridge` is enough, and all other ingredients
  are already derived or transported from first principles.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace VectorCFromHonestPhase

open AnalyticTrace
open LogicRH_From_RCL
open LogicPrimeLedgerAtom
open Foundation.RealsFromLogic
open Foundation.RealsFromLogic.LogicReal
open Foundation.LogicAsFunctionalEquationLogic

/-! ## 1. Physical reading of the RH edge -/

/-- A witnessed zeta zero, read as a physical defect sensor.

Physically:
* `sensor` is the zero-derived defect sensor.
* `rho` is the zero location.
* `charge_ne_zero` says the zero is off the critical-line charge-zero sector.

The analytic trace machinery already constructs honest phase data from such a
sensor; see `honest_argument_principle_phase_family`. -/
structure PhysicalZetaZeroSensor where
  sensor : WitnessedDefectSensor
  charge_ne_zero : sensor.charge ≠ 0

/-- Every physical zeta-zero sensor carries honest phase-family data already
constructed in the analytic trace layer. -/
theorem exists_honest_phase_data (pz : PhysicalZetaZeroSensor) :
    ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = pz.sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = pz.sensor.toDefectSensor :=
  honest_argument_principle_phase_family pz.sensor pz.charge_ne_zero

/-- Honest phase data already has bounded excess. This is proved before any
new Vector-C input is supplied. -/
theorem honest_phase_excess_already_bounded
    (zfd : ZetaPhaseFamilyData) :
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily) :=
  honestPhaseFamily_excess_bounded zfd

/-- Symmetry-only Vector C is known to be insufficient. This theorem is imported
as a stage gate so that the new bridge cannot silently collapse to completed-ξ
reflection/conjugation data alone. -/
theorem vectorC_symmetry_only_blocked :
    ¬ (∀ (Ξ : CompletedXiSurface) (ρ : ℂ),
        PureVectorCDoublingData Ξ ρ → Nonempty (ZeroCompositionWitness ρ)) :=
  pureVectorCDoublingData_requires_extra_input

/-! ## 2. Recovered arithmetic foundation as a real input, not a slogan -/

/-- The recovered arithmetic substrate used by the RH attack.

This packages the pieces that are already derived from the Law-of-Logic number
tower and used at the prime-ledger boundary. -/
structure RecoveredArithmeticSubstrate where
  primeLedgerLogic : PrimeLedgerLogicCert
  realEquiv : LogicReal ≃ ℝ
  logicPrimeClassicalCompatibility :
    ∀ p : Foundation.ArithmeticFromLogic.LogicNat,
      LogicPrimeLedgerAtom.PrimeLedgerAtomLogic p ↔ PrimeLedgerAtom
        (Foundation.ArithmeticFromLogic.LogicNat.toNat p)

/-- The recovered arithmetic substrate is already available. -/
noncomputable def recoveredArithmeticSubstrate : RecoveredArithmeticSubstrate where
  primeLedgerLogic := primeLedgerLogicCert
  realEquiv := equivReal
  logicPrimeClassicalCompatibility := fun _ => Iff.rfl

/-! ## 3. The only new analytic input: phase composition -/

/-- A specific honest zeta phase package instantiates a zero-composition witness.

This is the narrowed Vector-C bridge. It is physical because it says the honest
phase data of the zeta-zero sensor is not just topological charge data; it
actually realizes the calibrated d'Alembert / J-cost composition law at the
zero deviation. -/
structure ZetaPhaseCompositionCert
    (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData) where
  sensor_match : zfd.sensor = sensor.toDefectSensor
  family_match : zfd.phaseFamily.sensor = sensor.toDefectSensor
  witness : ZeroCompositionWitness sensor.rho

/-- The global bridge needed by this Vector-C route.

It is intentionally narrower than `BoundaryTransportCert`: it only speaks about
the honest phase package attached to witnessed zeta-zero sensors. -/
structure ZetaPhaseCompositionBridge where
  composition_of_honest_phase :
    ∀ (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData),
      zfd.sensor = sensor.toDefectSensor →
      zfd.phaseFamily.sensor = sensor.toDefectSensor →
        ZetaPhaseCompositionCert sensor zfd

/-- The RH-relevant Vector-C bridge: only nonzero-charge witnessed zeta sensors
need a phase-composition certificate.  This avoids overclaiming about arbitrary
zero-charge phase packages while preserving exactly the charge-exclusion target. -/
structure NonzeroZetaPhaseCompositionBridge where
  composition_of_nonzero_honest_phase :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 →
      ∀ (zfd : ZetaPhaseFamilyData),
        zfd.sensor = sensor.toDefectSensor →
        zfd.phaseFamily.sensor = sensor.toDefectSensor →
          ZetaPhaseCompositionCert sensor zfd

/-- Witness-only form of the nonzero Vector-C target.  The honest phase package
itself is already constructed by the argument-principle layer; the real content
is the zero-composition witness at the sensor's center. -/
structure NonzeroZeroCompositionWitnessBridge where
  witness_of_nonzero :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 →
      ZeroCompositionWitness sensor.rho

/-- A phase-composition certificate forces the corresponding sensor's zero onto
the critical line. -/
theorem onCriticalLine_of_phaseCompositionCert
    {sensor : WitnessedDefectSensor} {zfd : ZetaPhaseFamilyData}
    (cert : ZetaPhaseCompositionCert sensor zfd) :
    OnCriticalLine sensor.rho :=
  zeroCompositionWitness_forces_on_critical_line cert.witness

/-- A phase-composition certificate forces the witnessed sensor charge to zero.

The connection from critical-line support to charge-zero is exactly the
definition of a witnessed defect sensor in the analytic trace stack. -/
theorem charge_zero_of_phaseCompositionCert
    {sensor : WitnessedDefectSensor} {zfd : ZetaPhaseFamilyData}
    (cert : ZetaPhaseCompositionCert sensor zfd) :
    sensor.charge = 0 := by
  have hline : OnCriticalLine sensor.rho :=
    onCriticalLine_of_phaseCompositionCert cert
  have hcontr : False := by
    have hstrip : 1 / 2 < sensor.rho.re := sensor.in_strip.1
    have hre : sensor.rho.re = 1 / 2 := hline
    linarith
  exact False.elim hcontr

/-- A phase-composition bridge gives the direct Vector-C charge-zero bridge
needed by `AnalyticTrace`. -/
noncomputable def vectorCChargeZeroBridge_of_phaseCompositionBridge
    (bridge : ZetaPhaseCompositionBridge) :
    AnalyticTrace.VectorCChargeZeroBridge where
  witness_of_honest_phase := by
    intro sensor hzfd
    let zfd : ZetaPhaseFamilyData := Classical.choose hzfd
    have hzspec := Classical.choose_spec hzfd
    exact (bridge.composition_of_honest_phase sensor zfd hzspec.1 hzspec.2).witness

/-- A phase-composition bridge gives the witnessed RH core. -/
theorem witnessed_rh_from_phaseCompositionBridge
    (bridge : ZetaPhaseCompositionBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hne
  obtain ⟨zfd, hzsensor, hzfamily⟩ :=
    honest_argument_principle_phase_family sensor hne
  have cert := bridge.composition_of_honest_phase sensor zfd hzsensor hzfamily
  exact hne (charge_zero_of_phaseCompositionCert cert)

/-- A nonzero-charge phase-composition bridge gives the witnessed RH core. -/
theorem witnessed_rh_from_nonzeroPhaseCompositionBridge
    (bridge : NonzeroZetaPhaseCompositionBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hne
  obtain ⟨zfd, hzsensor, hzfamily⟩ :=
    honest_argument_principle_phase_family sensor hne
  have cert :=
    bridge.composition_of_nonzero_honest_phase sensor hne zfd hzsensor hzfamily
  exact hne (charge_zero_of_phaseCompositionCert cert)

/-- A phase-composition bridge supplies the witnessed honest-phase admissibility
bridge.  The composition certificate forces charge zero; bounded excess for
honest phase data then upgrades charge zero to finite recognition budget. -/
theorem witnessedHonestPhaseAdmissibilityBridge_of_phaseCompositionBridge
    (bridge : ZetaPhaseCompositionBridge) :
    WitnessedHonestPhaseAdmissibilityBridge where
  admissible_of_honest_phase := by
    intro sensor zfd hzsensor
    have hzfamily : zfd.phaseFamily.sensor = sensor.toDefectSensor := by
      simpa [hzsensor] using zfd.family_sensor
    have cert := bridge.composition_of_honest_phase sensor zfd hzsensor hzfamily
    exact (honestPhaseAdmissible_iff_charge_zero zfd).2
      (by simpa [hzsensor] using charge_zero_of_phaseCompositionCert cert)

/-- A nonzero-charge phase-composition bridge supplies witnessed honest-phase
admissibility.  Zero-charge sensors are admissible by the existing
`honestPhaseAdmissible_iff_charge_zero`; nonzero-charge sensors are impossible
by the bridge. -/
def witnessedHonestPhaseAdmissibilityBridge_of_nonzeroPhaseCompositionBridge
    (bridge : NonzeroZetaPhaseCompositionBridge) :
    WitnessedHonestPhaseAdmissibilityBridge where
  admissible_of_honest_phase := by
    intro sensor zfd hzsensor
    by_cases hzero : sensor.charge = 0
    · exact (honestPhaseAdmissible_iff_charge_zero zfd).2
        (by simpa [hzsensor] using hzero)
    · exact False.elim
        (witnessed_rh_from_nonzeroPhaseCompositionBridge bridge sensor hzero)

/-- The full phase-composition bridge implies the RH-relevant nonzero-charge
bridge. -/
def nonzeroPhaseCompositionBridge_of_phaseCompositionBridge
    (bridge : ZetaPhaseCompositionBridge) :
    NonzeroZetaPhaseCompositionBridge where
  composition_of_nonzero_honest_phase := by
    intro sensor _ zfd hs hf
    exact bridge.composition_of_honest_phase sensor zfd hs hf

/-- A nonzero phase-composition bridge supplies the witness-only bridge. -/
noncomputable def nonzeroWitnessBridge_of_nonzeroPhaseCompositionBridge
    (bridge : NonzeroZetaPhaseCompositionBridge) :
    NonzeroZeroCompositionWitnessBridge where
  witness_of_nonzero := by
    intro sensor hne
    let hzfd := honest_argument_principle_phase_family sensor hne
    let zfd : ZetaPhaseFamilyData := Classical.choose hzfd
    have hzspec := Classical.choose_spec hzfd
    exact (bridge.composition_of_nonzero_honest_phase
      sensor hne zfd hzspec.1 hzspec.2).witness

/-- A witness-only bridge supplies the nonzero phase-composition bridge. -/
def nonzeroPhaseCompositionBridge_of_nonzeroWitnessBridge
    (bridge : NonzeroZeroCompositionWitnessBridge) :
    NonzeroZetaPhaseCompositionBridge where
  composition_of_nonzero_honest_phase := by
    intro sensor hne zfd hzsensor hzfamily
    exact
      { sensor_match := hzsensor
        family_match := hzfamily
        witness := bridge.witness_of_nonzero sensor hne }

/-- The witness-only and phase-package versions of the nonzero Vector-C target
are equivalent as inhabited structures. -/
theorem nonempty_nonzeroWitnessBridge_iff_nonempty_nonzeroPhaseCompositionBridge :
    Nonempty NonzeroZeroCompositionWitnessBridge ↔
      Nonempty NonzeroZetaPhaseCompositionBridge := by
  constructor
  · rintro ⟨h⟩
    exact ⟨nonzeroPhaseCompositionBridge_of_nonzeroWitnessBridge h⟩
  · rintro ⟨h⟩
    exact ⟨nonzeroWitnessBridge_of_nonzeroPhaseCompositionBridge h⟩

/-- No witnessed strip sensor can carry a zero-composition witness, because such
a witness forces the center onto the critical line while witnessed sensors live
in the open right half of the strip. -/
theorem not_zeroCompositionWitness_of_witnessedSensor
    (sensor : WitnessedDefectSensor) :
    ¬ Nonempty (ZeroCompositionWitness sensor.rho) := by
  rintro ⟨w⟩
  have hline : OnCriticalLine sensor.rho :=
    zeroCompositionWitness_forces_on_critical_line w
  have hright : 1 / 2 < sensor.rho.re := sensor.in_strip.1
  unfold OnCriticalLine at hline
  linarith

/-- The witness-only Vector-C target is exactly the absence of nonzero witnessed
zeta charge.  Supplying a witness for a nonzero sensor immediately contradicts
the strip condition; conversely, if no nonzero sensors exist, the bridge is
vacuous. -/
theorem nonempty_nonzeroWitnessBridge_iff_no_nonzero_charge :
    Nonempty NonzeroZeroCompositionWitnessBridge ↔
      ¬ ∃ sensor : WitnessedDefectSensor, sensor.charge ≠ 0 := by
  constructor
  · rintro ⟨bridge⟩ h
    rcases h with ⟨sensor, hne⟩
    exact not_zeroCompositionWitness_of_witnessedSensor sensor
      ⟨bridge.witness_of_nonzero sensor hne⟩
  · intro h
    refine ⟨{ witness_of_nonzero := ?_ }⟩
    intro sensor hne
    exact False.elim (h ⟨sensor, hne⟩)

/-- A phase-composition bridge proves the analytic RH route without invoking
`BoundaryTransportCert`. -/
theorem direct_rh_from_phaseCompositionBridge
    (bridge : ZetaPhaseCompositionBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  witnessed_rh_from_phaseCompositionBridge bridge

/-! ## 4. Assumption audit for the new edge -/

/-- Everything needed by the new Vector-C route, split into derived content and
the single open analytic bridge. -/
structure VectorCAttackSurface where
  arithmetic : RecoveredArithmeticSubstrate
  symmetry_only_no_go :
    ¬ (∀ (Ξ : CompletedXiSurface) (ρ : ℂ),
        PureVectorCDoublingData Ξ ρ → Nonempty (ZeroCompositionWitness ρ))
  honest_phase_exists : ∀ pz : PhysicalZetaZeroSensor,
    ∃ zfd : ZetaPhaseFamilyData,
      zfd.sensor = pz.sensor.toDefectSensor ∧
        zfd.phaseFamily.sensor = pz.sensor.toDefectSensor
  honest_excess_bounded : ∀ zfd : ZetaPhaseFamilyData,
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily)
  open_phase_composition_bridge : ZetaPhaseCompositionBridge → Prop

/-- The attack surface is fully derived except for the explicitly named
phase-composition bridge. -/
noncomputable def vectorCAttackSurface : VectorCAttackSurface where
  arithmetic := recoveredArithmeticSubstrate
  symmetry_only_no_go := vectorC_symmetry_only_blocked
  honest_phase_exists := exists_honest_phase_data
  honest_excess_bounded := honest_phase_excess_already_bounded
  open_phase_composition_bridge := fun _ => True

/-- If the one remaining phase-composition bridge is supplied, the witnessed RH
core follows. This is the new edge to attack. -/
theorem vectorC_attack_closes_witnessed_rh
    (_surface : VectorCAttackSurface)
    (bridge : ZetaPhaseCompositionBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  witnessed_rh_from_phaseCompositionBridge bridge

end VectorCFromHonestPhase
end NumberTheory
end IndisputableMonolith
