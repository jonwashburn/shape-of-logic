import IndisputableMonolith.NumberTheory.PrimeLedgerAtom
import IndisputableMonolith.NumberTheory.EulerLedgerPartition
import IndisputableMonolith.NumberTheory.CompletedZetaLedger
import IndisputableMonolith.NumberTheory.ArgumentPrincipleSensor
import IndisputableMonolith.NumberTheory.EulerCarrierRealizability
import IndisputableMonolith.NumberTheory.BoundaryTransport
import IndisputableMonolith.NumberTheory.ZetaLedgerBridge

/-!
# RS Physical Thesis Decomposition

Replaces the opaque `RSPhysicalThesis` dependency with a structured bundle of
the exact ingredients needed for the RH proof.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Unification.UnifiedRH

/-- Decomposed data behind the old `RSPhysicalThesis`. -/
structure RSPhysicalThesisData where
  primeLedger : PrimeLedgerCert
  eulerPartition : EulerLedgerPartitionCert
  completedLedger : CompletedZetaLedgerCert
  zeroDefect : ArgumentPrincipleSensorCert
  realizableLedger : EulerRealizableLedgerCert
  boundaryTransport : BoundaryTransportCert
  t1Boundary : T1BoundaryExclusionCert

/-- The current proved/explicit data bundle, except for the remaining physical
boundary transport bridge. -/
noncomputable def rsPhysicalThesisData_of_boundaryTransport
    (boundary : BoundaryTransportCert) : RSPhysicalThesisData where
  primeLedger := primeLedgerCert
  eulerPartition := eulerLedgerPartitionCert
  completedLedger := completedZetaLedgerCert
  zeroDefect := argumentPrincipleSensorCert
  realizableLedger := eulerRealizableLedgerCert
  boundaryTransport := boundary
  t1Boundary := t1BoundaryExclusionCert

/-- Boundary transport rules out every right-half strip zero. -/
theorem no_strip_zeros_of_decomposed_data (data : RSPhysicalThesisData) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → False := by
  intro ρ _hzero hlo hhi
  let sensor : DefectSensor := zetaDefectSensor ρ.re ⟨hlo, hhi⟩ 1
  have hm : sensor.charge ≠ 0 := by
    dsimp [sensor]
    exact zetaDefectSensor_charge_ne_zero ρ.re ⟨hlo, hhi⟩
  have hdiv : CostDivergent sensor :=
    nonzero_charge_cost_divergent sensor hm
  exact no_cost_divergent_sensor_of_boundary_transport data.boundaryTransport sensor hdiv

/-- If no strip zero exists, the old `RSPhysicalThesis` holds vacuously. -/
theorem rsPhysicalThesis_of_no_strip_zeros
    (hno : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → False) :
    RSPhysicalThesis := by
  intro ρ hzero hlo hhi
  exact False.elim (hno ρ hzero hlo hhi)

/-- Decomposed data implies the old `RSPhysicalThesis` interface. -/
theorem rsPhysicalThesis_of_data (data : RSPhysicalThesisData) :
    RSPhysicalThesis :=
  rsPhysicalThesis_of_no_strip_zeros (no_strip_zeros_of_decomposed_data data)

end NumberTheory
end IndisputableMonolith
