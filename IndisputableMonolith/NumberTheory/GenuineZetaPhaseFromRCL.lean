import IndisputableMonolith.NumberTheory.HonestPhaseBudgetBridge
import IndisputableMonolith.NumberTheory.VectorCFromHonestPhase

/-!
  GenuineZetaPhaseFromRCL.lean

  Upgrade the RH Route C phase package from pole-only phase data to genuine
  regular-factor phase data.

  Current state before this module:
  * `ZetaPhaseFamilyData` carries `zetaDerivedPhaseFamily`, whose regular
    perturbation is identically zero.
  * `MeromorphicCircleOrder.lean` already defines
    `genuineZetaDerivedPhaseFamily` and proves a genuine perturbation witness
    for it from `QuantitativeLocalFactorization`.

  This module joins those two facts. It does not prove RH. It proves that the
  same honest local factorization data used in Route C also gives a genuine
  regular-factor phase family with bounded annular excess. That removes the
  "pole-only scaffold" concern from the Vector-C attack surface.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace GenuineZetaPhaseFromRCL

/-! ## 1. Genuine phase-family data -/

/-- The genuine regular-factor version of a zeta phase-family package.

This uses the same sensor and quantitative local factorization as
`ZetaPhaseFamilyData`, but replaces the pole-only `zetaDerivedPhaseFamily` by
`genuineZetaDerivedPhaseFamily`, which includes the Lipschitz-controlled
regular-factor phase. -/
structure GenuineZetaPhaseFamilyData where
  sensor : DefectSensor
  witness : QuantitativeLocalFactorization
  witness_realPart : witness.center.re = sensor.realPart
  witness_order : witness.order = -sensor.charge
  phaseFamily : DefectPhaseFamily
  family_sensor : phaseFamily.sensor = sensor
  family_genuine : phaseFamily = genuineZetaDerivedPhaseFamily sensor witness witness_order

/-- Any current honest zeta phase package has a genuine regular-factor
companion using the same local factorization witness. -/
noncomputable def genuineOfHonestPhase
    (zfd : ZetaPhaseFamilyData) : GenuineZetaPhaseFamilyData where
  sensor := zfd.sensor
  witness := zfd.witness
  witness_realPart := zfd.witness_realPart
  witness_order := zfd.witness_order
  phaseFamily := genuineZetaDerivedPhaseFamily zfd.sensor zfd.witness zfd.witness_order
  family_sensor := by
    rfl
  family_genuine := rfl

/-! ## 2. Derived perturbation witness and bounded excess -/

/-- The genuine phase package carries the already-proved regular-factor
perturbation witness. -/
noncomputable def GenuineZetaPhaseFamilyData.perturbationWitness
    (gzfd : GenuineZetaPhaseFamilyData) :
    DefectPhasePerturbationWitness gzfd.phaseFamily := by
  simpa [gzfd.family_genuine] using
    genuineZetaDerivedPhasePerturbationWitness
      gzfd.sensor gzfd.witness gzfd.witness_order

/-- Genuine regular-factor phase data has bounded annular excess. -/
theorem genuinePhaseFamily_excess_bounded
    (gzfd : GenuineZetaPhaseFamilyData) :
    RealizedDefectAnnularExcessBounded (gzfd.phaseFamily.toSampledFamily) := by
  exact phaseFamily_excess_bounded_of_perturbationWitness
    gzfd.phaseFamily gzfd.perturbationWitness

/-- Therefore every current honest zeta phase package has a genuine companion
with bounded annular excess. -/
theorem genuine_companion_excess_bounded
    (zfd : ZetaPhaseFamilyData) :
    RealizedDefectAnnularExcessBounded
      ((genuineOfHonestPhase zfd).phaseFamily.toSampledFamily) :=
  genuinePhaseFamily_excess_bounded (genuineOfHonestPhase zfd)

/-! ## 3. How this feeds the Vector-C edge -/

/-- A phase-composition certificate may now be requested for the genuine
regular-factor companion, rather than for the pole-only package. -/
structure GenuinePhaseCompositionCert
    (sensor : WitnessedDefectSensor) (gzfd : GenuineZetaPhaseFamilyData) where
  sensor_match : gzfd.sensor = sensor.toDefectSensor
  family_match : gzfd.phaseFamily.sensor = sensor.toDefectSensor
  witness : ZeroCompositionWitness sensor.rho

/-- The corresponding genuine-phase bridge. This is the sharper open analytic
bridge after removing the pole-only scaffold. -/
structure GenuinePhaseCompositionBridge where
  composition_of_genuine_phase :
    ∀ (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData),
      zfd.sensor = sensor.toDefectSensor →
      zfd.phaseFamily.sensor = sensor.toDefectSensor →
        GenuinePhaseCompositionCert sensor (genuineOfHonestPhase zfd)

/-- A genuine-phase bridge implies the previous phase-composition bridge. -/
noncomputable def phaseCompositionBridge_of_genuine
    (bridge : GenuinePhaseCompositionBridge) :
    VectorCFromHonestPhase.ZetaPhaseCompositionBridge where
  composition_of_honest_phase := by
    intro sensor zfd hzsensor hzfamily
    have gcert := bridge.composition_of_genuine_phase sensor zfd hzsensor hzfamily
    exact {
      sensor_match := hzsensor
      family_match := hzfamily
      witness := gcert.witness
    }

/-- Consequently a genuine-phase composition bridge proves the witnessed RH
core through the already-built Vector-C route. -/
theorem witnessed_rh_from_genuinePhaseCompositionBridge
    (bridge : GenuinePhaseCompositionBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  VectorCFromHonestPhase.witnessed_rh_from_phaseCompositionBridge
    (phaseCompositionBridge_of_genuine bridge)

/-- The new sharpened edge: all already-derived ingredients are genuine
regular-factor phase data with bounded excess; only the genuine phase
composition bridge remains. -/
structure GenuineVectorCAttackSurface where
  base : VectorCFromHonestPhase.VectorCAttackSurface
  genuine_excess_bounded :
    ∀ zfd : ZetaPhaseFamilyData,
      RealizedDefectAnnularExcessBounded
        ((genuineOfHonestPhase zfd).phaseFamily.toSampledFamily)
  open_genuine_phase_composition : GenuinePhaseCompositionBridge → Prop

noncomputable def genuineVectorCAttackSurface : GenuineVectorCAttackSurface where
  base := VectorCFromHonestPhase.vectorCAttackSurface
  genuine_excess_bounded := genuine_companion_excess_bounded
  open_genuine_phase_composition := fun _ => True

end GenuineZetaPhaseFromRCL
end NumberTheory
end IndisputableMonolith
