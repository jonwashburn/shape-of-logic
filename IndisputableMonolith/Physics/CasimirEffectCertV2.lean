import Mathlib
import IndisputableMonolith.Physics.CasimirEffectFromRS
import IndisputableMonolith.QFT.CasimirPlateModes
import IndisputableMonolith.QFT.CasimirRecognitionBoundary

/-!
# Casimir Effect Certificate V2

This is the master certificate for the formal Casimir lane.  It upgrades the
older numerology/J-cost certificates by bundling:

* the ideal parallel-plate pressure law,
* the RS boundary-mode cost interpretation,
* the RS-native `ℏ = φ^(-5)` substitution,
* the existing `720 = 8 * 90` structural provenance,
* explicit falsifier hooks for pressure and sign tests.
-/

namespace IndisputableMonolith
namespace Physics
namespace CasimirEffectCertV2

open QFT.CasimirPlateModes
open QFT.CasimirRecognitionBoundary

noncomputable section

/-- Claim hygiene tags for this module's components. -/
inductive ClaimStatus where
  | theorem
  | model
  | hypothesis
  | openProblem
  deriving DecidableEq, Repr

/-- Falsifier hook for the ideal pressure law: a measurement falsifies the ideal
model when it lies outside a declared tolerance around the predicted pressure. -/
structure PressureLawFalsifier where
  measuredPressure : ℝ
  predictedPressure : ℝ
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  falsifies : Prop := |measuredPressure - predictedPressure| > tolerance

/-- Falsifier hook for the attraction claim: a positive pressure at positive
separation contradicts the ideal attractive parallel-plate model. -/
structure SignFalsifier where
  separation : PlateSeparation
  measuredPressure : ℝ
  falsifies : Prop := 0 < measuredPressure

/-- Geometry status used by the certificate.  Only ideal parallel plates are
theorem-level in this first formalization pass. -/
def geometryStatus (cfg : CasimirEffectFromRS.CasimirConfig) : ClaimStatus :=
  match cfg with
  | CasimirEffectFromRS.CasimirConfig.parallelPlates => ClaimStatus.theorem
  | CasimirEffectFromRS.CasimirConfig.spherePlate => ClaimStatus.model
  | CasimirEffectFromRS.CasimirConfig.cylinderPlate => ClaimStatus.model
  | CasimirEffectFromRS.CasimirConfig.corrugated => ClaimStatus.model
  | CasimirEffectFromRS.CasimirConfig.sphereSphere => ClaimStatus.model

/-- The legacy five-configuration taxonomy is retained. -/
theorem geometry_count_retained :
    Fintype.card CasimirEffectFromRS.CasimirConfig = 5 :=
  CasimirEffectFromRS.casimirConfigCount

/-- The legacy structural `720 = 8 * 90` provenance is retained, but it is not
used as the analytic derivation of the pressure coefficient. -/
theorem factor_720_as_8tick_times_fermion_dof :
    (720 : ℕ) = 8 * 90 :=
  CasimirEffectFromRS.casimir_factor_8tick

/-- The parallel-plate geometry is theorem-level in the V2 certificate. -/
theorem parallel_plate_status :
    geometryStatus CasimirEffectFromRS.CasimirConfig.parallelPlates =
      ClaimStatus.theorem := rfl

/-- Corrugated geometries are model-level once the roughness algebra is
formalized; material response remains a separate hypothesis. -/
theorem corrugated_status :
    geometryStatus CasimirEffectFromRS.CasimirConfig.corrugated =
      ClaimStatus.model := rfl

/-- Master Casimir certificate. -/
structure CasimirV2Cert where
  ideal_plate : IdealPlateCert
  recognition_boundary : RecognitionBoundaryCert
  geometry_count : Fintype.card CasimirEffectFromRS.CasimirConfig = 5
  factor_8tick : (720 : ℕ) = 8 * 90
  parallel_plate_theorem :
    geometryStatus CasimirEffectFromRS.CasimirConfig.parallelPlates =
      ClaimStatus.theorem
  corrugated_model :
    geometryStatus CasimirEffectFromRS.CasimirConfig.corrugated =
      ClaimStatus.model

/-- The V2 certificate instance. -/
def cert : CasimirV2Cert where
  ideal_plate := idealPlateCert
  recognition_boundary := recognitionBoundaryCert
  geometry_count := geometry_count_retained
  factor_8tick := factor_720_as_8tick_times_fermion_dof
  parallel_plate_theorem := parallel_plate_status
  corrugated_model := corrugated_status

/-- The V2 certificate is inhabited without new axioms. -/
theorem cert_inhabited : Nonempty CasimirV2Cert := ⟨cert⟩

/-- Projection: the V2 certificate recovers the attractive ideal pressure law. -/
theorem cert_recovers_attraction (a : PlateSeparation) :
    idealPressure a < 0 :=
  cert.ideal_plate.attractive a

/-- Projection: the V2 certificate recovers the RS boundary cost nonnegativity. -/
theorem cert_recovers_boundary_cost_nonneg (I : BoundaryModeInventory) :
    0 ≤ renormalizedBoundaryCost I :=
  cert.recognition_boundary.cost_nonnegative I

/-- Projection: the V2 certificate recovers the `ℏ = φ^(-5)` pressure form. -/
theorem cert_recovers_phi_hbar_pressure (a : PlateSeparation) :
    idealPressure a =
      -Real.pi ^ 2 * (Constants.phi ^ (-(5 : ℝ))) * Constants.c /
        (240 * a.value ^ 4) :=
  cert.ideal_plate.hbar_phi_form a

end

end CasimirEffectCertV2
end Physics
end IndisputableMonolith
