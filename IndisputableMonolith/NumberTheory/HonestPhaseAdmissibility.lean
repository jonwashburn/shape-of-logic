import IndisputableMonolith.NumberTheory.AnalyticTrace

/-!
# Honest Phase Admissibility

Route C narrows the analytic RH target to honest zeta-derived phase data.  This
module defines the admissibility predicate for that data and proves that it is
equivalent to the charge-zero conclusion needed by `AnalyticTrace.ZeroFreeCriterion`.
-/

namespace IndisputableMonolith
namespace NumberTheory

open AnalyticTrace

/-- Honest phase data is admissible when its realized sampled family has finite
recognition budget, i.e. bounded total annular J-cost. -/
structure HonestPhaseAdmissible (zfd : ZetaPhaseFamilyData) : Prop where
  finiteRecognitionBudget :
    RealizedDefectAnnularCostBounded (zfd.phaseFamily.toSampledFamily)

/-- Admissible honest phase data has zero charge. -/
theorem charge_zero_of_honestPhaseAdmissible
    (zfd : ZetaPhaseFamilyData) (hadm : HonestPhaseAdmissible zfd) :
    zfd.sensor.charge = 0 :=
  honestPhaseFamily_charge_zero_of_costBounded zfd hadm.finiteRecognitionBudget

/-- Honest phase admissibility is equivalent to zero charge.  The reverse
direction uses the already-proved bounded-excess theorem for honest phase data. -/
theorem honestPhaseAdmissible_iff_charge_zero (zfd : ZetaPhaseFamilyData) :
    HonestPhaseAdmissible zfd ↔ zfd.sensor.charge = 0 := by
  constructor
  · intro hadm
    exact charge_zero_of_honestPhaseAdmissible zfd hadm
  · intro hzero
    exact ⟨(honestPhaseFamily_cost_bounded_iff_charge_zero zfd).mpr hzero⟩

/-- A global admissibility bridge for all honest zeta phase data. -/
structure HonestPhaseAdmissibilityBridge where
  admissible : ∀ zfd : ZetaPhaseFamilyData, HonestPhaseAdmissible zfd

/-- A global admissibility bridge gives the direct charge-zero bridge used in
`AnalyticTrace`. -/
def chargeZeroBridge_of_admissibilityBridge
    (hb : HonestPhaseAdmissibilityBridge) :
    HonestPhaseChargeZeroBridge where
  charge_zero_of_honest_phase := fun zfd =>
    charge_zero_of_honestPhaseAdmissible zfd (hb.admissible zfd)

/-- Conversely, a direct charge-zero bridge gives admissibility, since zero
charge plus bounded excess gives bounded total cost. -/
def admissibilityBridge_of_chargeZeroBridge
    (hb : HonestPhaseChargeZeroBridge) :
    HonestPhaseAdmissibilityBridge where
  admissible := fun zfd =>
    (honestPhaseAdmissible_iff_charge_zero zfd).2
      (hb.charge_zero_of_honest_phase zfd)

/-- The admissibility bridge and the charge-zero bridge are equivalent. -/
theorem honestPhaseAdmissibilityBridge_iff_chargeZeroBridge :
    HonestPhaseAdmissibilityBridge ↔ HonestPhaseChargeZeroBridge :=
  ⟨chargeZeroBridge_of_admissibilityBridge,
   admissibilityBridge_of_chargeZeroBridge⟩

/-- A global honest-phase admissibility bridge gives a `ZeroFreeCriterion`. -/
noncomputable def zeroFreeCriterion_of_honestPhaseAdmissibility
    (hb : HonestPhaseAdmissibilityBridge) :
    ZeroFreeCriterion :=
  zeroFreeCriterion_of_honestPhaseChargeZeroBridge
    (chargeZeroBridge_of_admissibilityBridge hb)

/-- A global honest-phase admissibility bridge proves the analytic RH core. -/
theorem direct_rh_from_honestPhaseAdmissibility
    (hb : HonestPhaseAdmissibilityBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  rh_from_zero_free_criterion
    (zeroFreeCriterion_of_honestPhaseAdmissibility hb)

/-! ## Carrier admissibility insertion point -/

/-- Carrier-side admissibility specialized to actual witnessed zeta sensors.
This is the narrow Route C bridge: whenever a witnessed zero produces honest
phase-family data, the Euler carrier admits that phase data with finite
recognition budget. -/
structure WitnessedHonestPhaseAdmissibilityBridge where
  admissible_of_honest_phase :
    ∀ (sensor : WitnessedDefectSensor) (zfd : ZetaPhaseFamilyData),
      zfd.sensor = sensor.toDefectSensor → HonestPhaseAdmissible zfd

/-- A witnessed admissibility bridge proves the witnessed RH core. -/
theorem witnessed_rh_from_honestPhaseAdmissibility
    (hb : WitnessedHonestPhaseAdmissibilityBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False := by
  intro sensor hm
  obtain ⟨zfd, hzsensor, _hzfamily⟩ :=
    honest_argument_principle_phase_family sensor hm
  have hadm : HonestPhaseAdmissible zfd :=
    hb.admissible_of_honest_phase sensor zfd hzsensor
  have hz : zfd.sensor.charge = 0 :=
    charge_zero_of_honestPhaseAdmissible zfd hadm
  have hs : sensor.toDefectSensor.charge = 0 := by
    simpa [hzsensor] using hz
  exact hm (by simpa using hs)

/-- Conversely, the witnessed RH core makes the admissibility bridge true,
because each honest phase package then has zero charge, hence bounded total
cost by the already-proved excess bound. -/
def witnessedHonestPhaseAdmissibilityBridge_of_rh
    (hrh : ∀ sensor : WitnessedDefectSensor, sensor.charge = 0) :
    WitnessedHonestPhaseAdmissibilityBridge where
  admissible_of_honest_phase := by
    intro sensor zfd hzsensor
    have hcharge_sensor : sensor.charge = 0 := hrh sensor
    have hcharge_zfd : zfd.sensor.charge = 0 := by
      simpa [hzsensor] using hcharge_sensor
    exact (honestPhaseAdmissible_iff_charge_zero zfd).2 hcharge_zfd

/-- The witnessed admissibility bridge is equivalent to the witnessed RH core.
This is the honest audit: deriving carrier admissibility for all witnessed
honest phase data is not a routine estimate; it is RH in Route C form. -/
theorem witnessedHonestPhaseAdmissibilityBridge_iff_rh :
    WitnessedHonestPhaseAdmissibilityBridge ↔
      (∀ sensor : WitnessedDefectSensor, sensor.charge = 0) := by
  constructor
  · intro hb sensor
    by_contra hm
    exact witnessed_rh_from_honestPhaseAdmissibility hb sensor hm
  · exact witnessedHonestPhaseAdmissibilityBridge_of_rh

/-- A witnessed admissibility bridge also provides a direct charge-zero bridge
for the actual phase data associated with witnessed sensors. -/
theorem direct_rh_from_witnessedAdmissibilityBridge
    (hb : WitnessedHonestPhaseAdmissibilityBridge) :
    ∀ (sensor : WitnessedDefectSensor), sensor.charge ≠ 0 → False :=
  witnessed_rh_from_honestPhaseAdmissibility hb

/-! ## Capacity-gate audit -/

/-- Honest phase admissibility cannot hold at nonzero charge.  This is the
capacity gate exposed by the annular topological floor: finite recognition
budget forces charge zero. -/
theorem not_honestPhaseAdmissible_of_charge_ne_zero
    (zfd : ZetaPhaseFamilyData) (hcharge : zfd.sensor.charge ≠ 0) :
    ¬ HonestPhaseAdmissible zfd := by
  intro hadm
  exact hcharge (charge_zero_of_honestPhaseAdmissible zfd hadm)

/-- Excess control is already available for honest zeta phase data, but at
nonzero charge it still does not give admissibility.  The obstruction is the
topological floor, not the regular perturbation. -/
theorem honestPhase_excess_bounded_and_not_admissible_of_charge_ne_zero
    (zfd : ZetaPhaseFamilyData) (hcharge : zfd.sensor.charge ≠ 0) :
    RealizedDefectAnnularExcessBounded (zfd.phaseFamily.toSampledFamily) ∧
      ¬ HonestPhaseAdmissible zfd :=
  ⟨honestPhaseFamily_excess_bounded zfd,
    not_honestPhaseAdmissible_of_charge_ne_zero zfd hcharge⟩

/-- A nonzero witnessed charge refutes the witnessed admissibility bridge. -/
theorem not_witnessedHonestPhaseAdmissibilityBridge_of_exists_nonzero_charge
    (h : ∃ sensor : WitnessedDefectSensor, sensor.charge ≠ 0) :
    ¬ WitnessedHonestPhaseAdmissibilityBridge := by
  rintro hb
  rcases h with ⟨sensor, hcharge⟩
  exact witnessed_rh_from_honestPhaseAdmissibility hb sensor hcharge

/-- The witnessed admissibility bridge is exactly the absence of nonzero
witnessed charge. -/
theorem witnessedHonestPhaseAdmissibilityBridge_iff_no_nonzero_charge :
    WitnessedHonestPhaseAdmissibilityBridge ↔
      ¬ ∃ sensor : WitnessedDefectSensor, sensor.charge ≠ 0 := by
  constructor
  · intro hb h
    exact not_witnessedHonestPhaseAdmissibilityBridge_of_exists_nonzero_charge h hb
  · intro h
    exact witnessedHonestPhaseAdmissibilityBridge_of_rh (fun sensor => by
      by_contra hcharge
      exact h ⟨sensor, hcharge⟩)

end NumberTheory
end IndisputableMonolith
