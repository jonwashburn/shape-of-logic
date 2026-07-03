import Mathlib
import IndisputableMonolith.Physics.CasimirEffectCertV2

/-!
# Phi-Ladder Corrections to Casimir Pressure

This module defines the RS correction layer

`P_RS(a) = P_Casimir(a) * (1 + δφ)`

and proves the algebraic sanity facts.  Actual material response functions are
kept as hypotheses until a Lifshitz/dispersive boundary module exists.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirPhiCorrections

open CasimirPlateModes

noncomputable section

/-- Material boundary families for the correction model. -/
inductive MaterialBoundary where
  | idealConductor
  | finiteConductor
  | dielectric
  | graphene
  | superconductor
  | metamaterial
  | fluidSeparated
  | hydrationLayer
  deriving DecidableEq, Repr

/-- Geometry families for correction bookkeeping. -/
inductive CasimirGeometry where
  | parallelPlates
  | spherePlate
  | cylinderPlate
  | corrugated
  | sphereSphere
  | layeredCavity
  deriving DecidableEq, Repr

/-- Parameters on which an RS φ-ladder correction may depend. -/
structure PhiCorrectionInputs where
  separation : PlateSeparation
  material : MaterialBoundary
  geometry : CasimirGeometry
  coatingThickness : ℝ
  plasmaWavelength : ℝ
  phononBandCenter : ℝ
  coherenceLength : ℝ
  hydrationThickness : ℝ

/-- A model for the φ-ladder correction factor. -/
structure PhiCorrectionModel where
  deltaPhi : PhiCorrectionInputs → ℝ

/-- Corrected RS pressure. -/
noncomputable def correctedPressure
    (M : PhiCorrectionModel) (x : PhiCorrectionInputs) : ℝ :=
  idealPressure x.separation * (1 + M.deltaPhi x)

/-- Zero correction recovers the standard ideal Casimir pressure. -/
theorem correctedPressure_eq_ideal_of_delta_zero
    (M : PhiCorrectionModel) (x : PhiCorrectionInputs)
    (hδ : M.deltaPhi x = 0) :
    correctedPressure M x = idealPressure x.separation := by
  unfold correctedPressure
  rw [hδ]
  ring

/-- Positive `δφ` increases attractive magnitude: pressure becomes more
negative than the ideal attractive pressure. -/
theorem correctedPressure_more_attractive_of_delta_pos
    (M : PhiCorrectionModel) (x : PhiCorrectionInputs)
    (hδ : 0 < M.deltaPhi x) :
    correctedPressure M x < idealPressure x.separation := by
  unfold correctedPressure
  have hp : idealPressure x.separation < 0 :=
    idealPressure_negative x.separation
  have hmul : idealPressure x.separation * M.deltaPhi x < 0 :=
    mul_neg_of_neg_of_pos hp hδ
  linarith

/-- If `-1 < δφ`, the corrected pressure remains attractive. -/
theorem correctedPressure_negative_of_delta_gt_neg_one
    (M : PhiCorrectionModel) (x : PhiCorrectionInputs)
    (hδ : -1 < M.deltaPhi x) :
    correctedPressure M x < 0 := by
  unfold correctedPressure
  have hp : idealPressure x.separation < 0 :=
    idealPressure_negative x.separation
  have hfactor : 0 < 1 + M.deltaPhi x := by linarith
  exact mul_neg_of_neg_of_pos hp hfactor

/-- If `δφ < -1`, the correction reverses the sign and produces repulsive
pressure in this algebraic model. -/
theorem correctedPressure_repulsive_of_delta_lt_neg_one
    (M : PhiCorrectionModel) (x : PhiCorrectionInputs)
    (hδ : M.deltaPhi x < -1) :
    0 < correctedPressure M x := by
  unfold correctedPressure
  have hp : idealPressure x.separation < 0 :=
    idealPressure_negative x.separation
  have hfactor : 1 + M.deltaPhi x < 0 := by linarith
  exact mul_pos_of_neg_of_neg hp hfactor

/-- Material-response hypotheses that must be supplied before claiming an
actual device-level correction. -/
structure MaterialPhiHypothesis where
  model : PhiCorrectionModel
  material : MaterialBoundary
  geometry : CasimirGeometry
  resonance_claim : Prop
  falsifier : Prop

/-- Per-material ceiling hypothesis: material physics prevents the correction
from crossing the repulsive `δφ < -1` threshold. -/
structure MaterialCeilingHypothesis where
  model : PhiCorrectionModel
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  delta_phi_above_minus_one :
    ∀ x : PhiCorrectionInputs, -1 + epsilon ≤ model.deltaPhi x

/-- Under a material ceiling, the corrected pressure remains attractive. -/
theorem correctedPressure_negative_under_material_ceiling
    (H : MaterialCeilingHypothesis) (x : PhiCorrectionInputs) :
    correctedPressure H.model x < 0 := by
  apply correctedPressure_negative_of_delta_gt_neg_one
  have hceil := H.delta_phi_above_minus_one x
  linarith [H.epsilon_pos, hceil]

/-- Certificate for the theorem-level algebra of φ-corrected pressure. -/
structure PhiCorrectionCert where
  recovery :
    ∀ (M : PhiCorrectionModel) (x : PhiCorrectionInputs),
      M.deltaPhi x = 0 →
        correctedPressure M x = idealPressure x.separation
  enhanced_attraction :
    ∀ (M : PhiCorrectionModel) (x : PhiCorrectionInputs),
      0 < M.deltaPhi x →
        correctedPressure M x < idealPressure x.separation
  remains_attractive :
    ∀ (M : PhiCorrectionModel) (x : PhiCorrectionInputs),
      -1 < M.deltaPhi x →
        correctedPressure M x < 0
  sign_reversal :
    ∀ (M : PhiCorrectionModel) (x : PhiCorrectionInputs),
      M.deltaPhi x < -1 →
        0 < correctedPressure M x
  ceiling_constrained_attraction :
    ∀ (H : MaterialCeilingHypothesis) (x : PhiCorrectionInputs),
      correctedPressure H.model x < 0

/-- The φ-correction algebra certificate. -/
def phiCorrectionCert : PhiCorrectionCert where
  recovery := correctedPressure_eq_ideal_of_delta_zero
  enhanced_attraction := correctedPressure_more_attractive_of_delta_pos
  remains_attractive := correctedPressure_negative_of_delta_gt_neg_one
  sign_reversal := correctedPressure_repulsive_of_delta_lt_neg_one
  ceiling_constrained_attraction := correctedPressure_negative_under_material_ceiling

end

end CasimirPhiCorrections
end QFT
end IndisputableMonolith
