import IndisputableMonolith.Unification.UnifiedRH

/-!
# Euler Carrier Realizability

The Euler carrier is already realized in `UnifiedRH.lean` as a
T1-bounded ledger.  This module extracts that result into the file layout used
by the RH-from-RCL derivation plan.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Unification.UnifiedRH

/-- Euler trace admissibility is available for every defect sensor. -/
theorem euler_trace_admissible_concrete (sensor : DefectSensor) :
    EulerTraceAdmissible sensor :=
  euler_trace_admissible sensor

/-- The Euler ledger is physically realizable in the T1-bounded sense. -/
noncomputable def euler_ledger_realizable (sensor : DefectSensor) :
    PhysicallyRealizableLedger sensor :=
  euler_physically_realizable sensor

/-- Certificate for Euler carrier realizability. -/
structure EulerRealizableLedgerCert where
  admissible : ∀ sensor : DefectSensor, EulerTraceAdmissible sensor
  realizable : ∀ sensor : DefectSensor, PhysicallyRealizableLedger sensor

/-- The proved Euler realizability certificate. -/
noncomputable def eulerRealizableLedgerCert : EulerRealizableLedgerCert where
  admissible := euler_trace_admissible_concrete
  realizable := euler_ledger_realizable

end NumberTheory
end IndisputableMonolith
