import IndisputableMonolith.Gravity.RecordFluxStress

/-!
# Posted-record heat to null stress flux

This module isolates the exact algebraic bridge between the posted heat of a
fixed recognition cut and the null contraction of its event-stress matrix.

If every active channel covector has the same pairing `q` with one probe `k`,
then the stress contraction is exactly `q²` times the posted record heat.
An explicit calibration law then gives the local boost-heat equation.

Honesty tags:

* THEOREM: the sum, contraction, calibration, and decoy algebra below.
* MODEL: the channel covectors, probe, uniform-pairing attachment, and physical
  heat calibration.
* OPEN: deriving those MODEL inputs from recognition geometry.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace RecordFluxBoostHeat

open ClausiusEinsteinBridge
open RecordFluxStress
open Holography.LocalRecognitionHorizonCut

/--
Uniform attachment of the cut channels to one probe.  The common pairing is
an explicit geometric MODEL input; it is not inferred from the cut record.
-/
def UniformProbeAttachment
    {a s : ℕ}
    (p : ExteriorCutChannel a s → Fin 4 → ℝ)
    (k : Fin 4 → ℝ)
    (q : ℝ) : Prop :=
  ∀ ch, (∑ μ, p ch μ * k μ) = q

/--
The real-valued posted heat is the sum of the real channel weights.
-/
theorem exteriorStepHeat_cast_eq_sum_channelDelta
    {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) :
    (exteriorStepHeat c c' : ℝ) =
      ∑ ch : ExteriorCutChannel a s, channelDelta c c' ch := by
  have h := exteriorStepHeat_eq_sum_channelDeltaZ c c'
  unfold channelDelta
  exact_mod_cast h

/--
Uniform probe pairing converts the fixed event-stress contraction into the
posted cut heat times the common squared pairing.
-/
theorem quadContr_cutEventStress_eq_sq_mul_heat
    {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H)
    (p : ExteriorCutChannel a s → Fin 4 → ℝ)
    (k : Fin 4 → ℝ)
    (q : ℝ)
    (hattach : UniformProbeAttachment p k q) :
    quadContr (cutEventStress c c' p) k =
      q ^ 2 * (exteriorStepHeat c c' : ℝ) := by
  rw [quadContr_cutEventStress]
  unfold UniformProbeAttachment at hattach
  simp_rw [hattach]
  rw [← Finset.sum_mul]
  rw [← exteriorStepHeat_cast_eq_sum_channelDelta c c']
  ring

/--
Named MODEL normalization assumption required to convert bit-valued posted
heat into the local boost-energy normalization.  It supplies the whole
physical heat-scale conversion and is not derived from the record data.
-/
def PostedBoostHeatNormalizationAssumption
    (surfaceGravity boostMoment heatScale q : ℝ) : Prop :=
  heatScale = -surfaceGravity * boostMoment * q ^ 2

/--
With uniform channel attachment and the explicit calibration, calibrated
posted heat equals minus surface gravity times boost moment times null stress
flux.  The theorem derives the equality from two separately named inputs.
-/
theorem matchesPostedBoostHeat_of_attachment
    {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H)
    (p : ExteriorCutChannel a s → Fin 4 → ℝ)
    (k : Fin 4 → ℝ)
    (q surfaceGravity boostMoment heatScale : ℝ)
    (hattach : UniformProbeAttachment p k q)
    (hcal : PostedBoostHeatNormalizationAssumption
      surfaceGravity boostMoment heatScale q) :
    heatScale * (exteriorStepHeat c c' : ℝ) =
      -surfaceGravity * boostMoment *
        quadContr (cutEventStress c c' p) k := by
  rw [quadContr_cutEventStress_eq_sq_mul_heat c c' p k q hattach]
  unfold PostedBoostHeatNormalizationAssumption at hcal
  rw [hcal]
  ring

/--
Load-bearing decoy: zero channel covectors produce zero stress flux, so they
cannot represent a nonzero calibrated posted heat.
-/
theorem zero_covectors_fail_nonzero_posted_heat
    {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H)
    (k : Fin 4 → ℝ)
    (surfaceGravity boostMoment heatScale : ℝ)
    (hheat : heatScale * (exteriorStepHeat c c' : ℝ) ≠ 0) :
    ¬ heatScale * (exteriorStepHeat c c' : ℝ) =
      -surfaceGravity * boostMoment *
        quadContr
          (cutEventStress c c' (fun _ _ => (0 : ℝ))) k := by
  intro h
  rw [cutEventStress_zero_of_covector_zero] at h
  have hz :
      quadContr (0 : Matrix (Fin 4) (Fin 4) ℝ) k = 0 := by
    simp [quadContr]
  rw [hz, mul_zero] at h
  exact hheat h

/-- Certificate for the conditional posted-heat transport. -/
structure RecordFluxBoostHeatCert : Prop where
  heat_is_channel_sum :
    ∀ {a s b r : ℕ} {kappa : ℝ}
      {H : LocalHorizonContext a s b r kappa}
      (c c' : LocalCut H),
      (exteriorStepHeat c c' : ℝ) =
        ∑ ch : ExteriorCutChannel a s, channelDelta c c' ch
  uniform_attachment_transports :
    ∀ {a s b r : ℕ} {kappa : ℝ}
      {H : LocalHorizonContext a s b r kappa}
      (c c' : LocalCut H)
      (p : ExteriorCutChannel a s → Fin 4 → ℝ)
      (k : Fin 4 → ℝ)
      (q surfaceGravity boostMoment heatScale : ℝ),
      UniformProbeAttachment p k q →
      PostedBoostHeatNormalizationAssumption
        surfaceGravity boostMoment heatScale q →
      heatScale * (exteriorStepHeat c c' : ℝ) =
        -surfaceGravity * boostMoment *
          quadContr (cutEventStress c c' p) k

theorem recordFluxBoostHeatCert : RecordFluxBoostHeatCert where
  heat_is_channel_sum := exteriorStepHeat_cast_eq_sum_channelDelta
  uniform_attachment_transports :=
    matchesPostedBoostHeat_of_attachment

end RecordFluxBoostHeat
end Gravity
end IndisputableMonolith
