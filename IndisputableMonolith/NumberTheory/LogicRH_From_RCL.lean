import IndisputableMonolith.NumberTheory.RH_From_RCL
import IndisputableMonolith.NumberTheory.LogicPrimeLedgerAtom

/-!
  LogicRH_From_RCL.lean

  Recovered-prime-ledger wrapper for the RH-from-RCL decomposition.

  The analytic zeta/xi/winding infrastructure remains Mathlib-backed and
  unchanged.  This module only replaces the arithmetic ledger hook with a
  certificate that includes the recovered-prime ledger, then transports back
  to the existing `PrimeLedgerCert` required by the RH assembly.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicRH_From_RCL

open LogicPrimeLedgerAtom

/-- RH decomposition data with an explicit recovered-prime-ledger component.

The classical field is retained because the analytic zeta stack still speaks
Mathlib's `ℕ`/`ℂ`; the `primeLedgerLogic` field records that the arithmetic
ledger has been recovered from `LogicNat` and is compatible with the classical
ledger by transport. -/
structure RSPhysicalThesisDataLogic where
  primeLedgerLogic : PrimeLedgerLogicCert
  primeLedgerClassical : PrimeLedgerCert
  eulerPartition : EulerLedgerPartitionCert
  completedLedger : CompletedZetaLedgerCert
  zeroDefect : ArgumentPrincipleSensorCert
  realizableLedger : EulerRealizableLedgerCert
  boundaryTransport : BoundaryTransportCert
  t1Boundary : T1BoundaryExclusionCert

/-- Forget the recovered-prime wrapper to the current decomposed data bundle. -/
def toClassicalData (data : RSPhysicalThesisDataLogic) : RSPhysicalThesisData where
  primeLedger := data.primeLedgerClassical
  eulerPartition := data.eulerPartition
  completedLedger := data.completedLedger
  zeroDefect := data.zeroDefect
  realizableLedger := data.realizableLedger
  boundaryTransport := data.boundaryTransport
  t1Boundary := data.t1Boundary

/-- Build logic-aware RH decomposition data from the current boundary transport
certificate. The only remaining obstruction is still `BoundaryTransportCert`;
the recovered-prime ledger is no longer an extra assumption. -/
noncomputable def logicData_of_boundaryTransport
    (boundary : BoundaryTransportCert) : RSPhysicalThesisDataLogic where
  primeLedgerLogic := primeLedgerLogicCert
  primeLedgerClassical := primeLedgerCert
  eulerPartition := eulerLedgerPartitionCert
  completedLedger := completedZetaLedgerCert
  zeroDefect := argumentPrincipleSensorCert
  realizableLedger := eulerRealizableLedgerCert
  boundaryTransport := boundary
  t1Boundary := t1BoundaryExclusionCert

/-- Logic-aware data implies the old `RSPhysicalThesis` interface. -/
theorem rsPhysicalThesis_of_logic_data (data : RSPhysicalThesisDataLogic) :
    RSPhysicalThesis :=
  rsPhysicalThesis_of_data (toClassicalData data)

/-- RH from RCL with a recovered-prime-ledger wrapper. Analytic boundary
transport remains exactly the previous obstruction. -/
theorem riemann_hypothesis_from_rcl_logicPrime
    (boundary : BoundaryTransportCert) :
    RiemannHypothesis :=
  rh_full (rsPhysicalThesis_of_logic_data (logicData_of_boundaryTransport boundary))

/-- Completion boundary is unchanged: the recovered prime ledger changes the
arithmetic input surface, not the analytic RH core. -/
theorem rh_from_rcl_logicPrime_completion_boundary :
    (BoundaryTransportCert → RiemannHypothesis) ∧
    (BoundaryTransportCert ↔
      (∀ sensor : DefectSensor, sensor.charge ≠ 0 → False)) := by
  exact ⟨riemann_hypothesis_from_rcl_logicPrime, boundaryTransportCert_iff_rh_core⟩

end LogicRH_From_RCL
end NumberTheory
end IndisputableMonolith
