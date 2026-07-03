import IndisputableMonolith.NumberTheory.EulerCarrierRealizability
import IndisputableMonolith.NumberTheory.T1BoundaryExclusion

/-!
# Boundary Transport

The remaining physical bridge in the RH-from-RCL route.

`UnifiedRH.lean` already proves that nonzero-charge realized defect families
have a concrete collapse scalar approaching zero.  The still-open RS physical
content is whether that concrete collapse transports to the T1-bounded Euler
realizability scalar.  This file exposes that bridge as a named certificate.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Unification.UnifiedRH

/-- Boundary transport certificate.  This is the main remaining RS physical
bridge: realized defect collapse must transport to the actual Euler ledger
boundary. -/
structure BoundaryTransportCert where
  bridge : EulerBoundaryBridgeAssumption

/-- A boundary transport certificate is exactly the old Euler boundary bridge. -/
theorem boundaryTransportCert_iff_EBBA :
    BoundaryTransportCert ↔ EulerBoundaryBridgeAssumption := by
  constructor
  · intro h
    exact h.bridge
  · intro h
    exact ⟨h⟩

/-- Boundary transport is logically equivalent to the no-nonzero-charge
sensor statement already identified in `UnifiedRH.lean` as the RH core. -/
theorem boundaryTransportCert_iff_rh_core :
    BoundaryTransportCert ↔
      (∀ sensor : DefectSensor, sensor.charge ≠ 0 → False) := by
  rw [boundaryTransportCert_iff_EBBA]
  exact EBBA_iff_rh

/-- A boundary transport certificate gives the old divergence-witness interface. -/
theorem divergence_witnesses_boundary_of_cert
    (cert : BoundaryTransportCert) (sensor : DefectSensor) :
    letI : PhysicallyRealizableLedger sensor := euler_physically_realizable sensor
    DivergenceWitnessesBoundary sensor := by
  exact euler_boundary_bridge cert.bridge sensor

/-- With boundary transport, a nonzero cost-divergent Euler sensor is impossible. -/
theorem no_cost_divergent_sensor_of_boundary_transport
    (cert : BoundaryTransportCert) (sensor : DefectSensor) :
    ¬ CostDivergent sensor := by
  letI : PhysicallyRealizableLedger sensor := euler_physically_realizable sensor
  letI : DivergenceWitnessesBoundary sensor := euler_boundary_bridge cert.bridge sensor
  exact ontological_exclusion_of_realizable sensor (euler_trace_admissible sensor)

end NumberTheory
end IndisputableMonolith
