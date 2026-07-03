import IndisputableMonolith.NumberTheory.ConcreteEulerLedger
import IndisputableMonolith.Unification.UnifiedRH

/-!
# Directed Euler Ledger Interface

This module packages the finite concrete Euler ledgers from
`ConcreteEulerLedger.lean` into a directed system over finite prime supports,
and then connects that system to the existing ontology-side interfaces from
`UnifiedRH.lean`.

## What is proved here

For every `DefectSensor`, we construct:

* a directed family of concrete finite arithmetic ledgers indexed by
  `Finset Nat.Primes`,
* coherence under support enlargement (every prime already present in a smaller
  support remains present in any larger support),
* the already-proved admissible Euler trace,
* the already-proved T1-bounded realizability proxy.

## What is *not* yet proved here

This still does not discharge `RSPhysicalThesis`. The remaining gap is the
global physical-identification step that would transport the concrete directed
Euler ledger into the `PhysicallyExists` predicate, which is defined using the
`eulerLedgerScalarState` rather than the bounded proxy `eulerScalarProxy`.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Foundation
open IndisputableMonolith.Unification.UnifiedRH

/-- Finite prime supports indexing concrete Euler-ledger stages. -/
abbrev PrimeSupport := Finset Nat.Primes

/-- Finite prime supports form a directed set under inclusion, with upper bound
given by union. -/
theorem primeSupport_directed (S T : PrimeSupport) :
    ∃ U : PrimeSupport, S ⊆ U ∧ T ⊆ U := by
  exact ⟨S ∪ T, Finset.subset_union_left, Finset.subset_union_right⟩

/-- Prime-event membership persists under support enlargement. -/
theorem primeEulerEvent_mem_sensorEulerLedger_of_subset
    (sensor : DefectSensor) {S T : PrimeSupport}
    (hST : S ⊆ T) {p : Nat.Primes} (hp : p ∈ S) :
    primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈
      (sensorEulerLedger sensor T).events := by
  exact primeEulerEvent_mem_sensorEulerLedger sensor (hST hp)

/-- Reciprocal prime-event membership also persists under support enlargement. -/
theorem reciprocal_primeEulerEvent_mem_sensorEulerLedger_of_subset
    (sensor : DefectSensor) {S T : PrimeSupport}
    (hST : S ⊆ T) {p : Nat.Primes} (hp : p ∈ S) :
    LedgerForcing.reciprocal
        (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈
      (sensorEulerLedger sensor T).events := by
  exact reciprocal_primeEulerEvent_mem_sensorEulerLedger sensor (hST hp)

/-- A directed system of concrete Euler ledgers attached to a single sensor. -/
structure DirectedEulerLedgerSystem (sensor : DefectSensor) where
  /-- The finite-stage ledger at a given prime support. -/
  stage : PrimeSupport → LedgerForcing.Ledger
  /-- Every finite stage is balanced. -/
  stage_balanced : ∀ support, LedgerForcing.balanced (stage support)
  /-- Hence every finite stage has zero net flow. -/
  stage_net_flow_zero :
    ∀ support agent, LedgerForcing.net_flow (stage support) agent = 0
  /-- Every prime in the support contributes both the Euler event and its
  reciprocal. -/
  stage_prime_pair :
    ∀ {support : PrimeSupport} {p : Nat.Primes}, p ∈ support →
      primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈
          (stage support).events ∧
        LedgerForcing.reciprocal
          (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈
            (stage support).events
  /-- Coherence under support enlargement: any prime already present in a
  smaller support remains present in every larger support. -/
  stage_prime_pair_mono :
    ∀ {S T : PrimeSupport} {p : Nat.Primes}, S ⊆ T → p ∈ S →
      primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈
          (stage T).events ∧
        LedgerForcing.reciprocal
          (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈
            (stage T).events
  /-- Directedness of the support index set. -/
  directed_support :
    ∀ S T : PrimeSupport, ∃ U : PrimeSupport, S ⊆ U ∧ T ⊆ U
  /-- Explicit stage cost formula. -/
  stage_cost_formula :
    ∀ support : PrimeSupport,
      LedgerForcing.ledger_cost (stage support) =
        2 * (support.toList.map
          (fun p : Nat.Primes => LedgerForcing.J ((p : ℝ) ^ (-sensor.realPart)))).sum

/-- The canonical directed concrete Euler-ledger system attached to a sensor. -/
noncomputable def concreteDirectedEulerLedgerSystem (sensor : DefectSensor) :
    DirectedEulerLedgerSystem sensor where
  stage := sensorEulerLedger sensor
  stage_balanced := sensorEulerLedger_balanced sensor
  stage_net_flow_zero := sensorEulerLedger_net_flow_zero sensor
  stage_prime_pair := by
    intro support p hp
    exact ⟨primeEulerEvent_mem_sensorEulerLedger sensor hp,
      reciprocal_primeEulerEvent_mem_sensorEulerLedger sensor hp⟩
  stage_prime_pair_mono := by
    intro S T p hST hp
    exact ⟨primeEulerEvent_mem_sensorEulerLedger_of_subset sensor hST hp,
      reciprocal_primeEulerEvent_mem_sensorEulerLedger_of_subset sensor hST hp⟩
  directed_support := primeSupport_directed
  stage_cost_formula := sensorEulerLedger_cost_formula sensor

/-- A convenient union-stage corollary: the union support contains the prime
data from both constituent supports. -/
theorem concreteDirectedEulerLedgerSystem_union_contains
    (sensor : DefectSensor) {S T : PrimeSupport} {p : Nat.Primes}
    (hp : p ∈ S ∨ p ∈ T) :
    let sys := concreteDirectedEulerLedgerSystem sensor
    primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈
        (sys.stage (S ∪ T)).events ∧
      LedgerForcing.reciprocal
        (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈
          (sys.stage (S ∪ T)).events := by
  let sys := concreteDirectedEulerLedgerSystem sensor
  rcases hp with hp | hp
  · exact sys.stage_prime_pair_mono Finset.subset_union_left hp
  · exact sys.stage_prime_pair_mono Finset.subset_union_right hp

/-- The finite-to-directed arithmetic package, connected to the ontology-side
admissibility and realizability interfaces. -/
structure EulerLedgerOntologyInterface (sensor : DefectSensor) where
  /-- Concrete finite stages over prime supports. -/
  directedLedger : DirectedEulerLedgerSystem sensor
  /-- Analytic admissibility of the associated Euler trace. -/
  admissibleTrace : EulerTraceAdmissible sensor
  /-- T1-bounded realizability proxy coming from the Euler carrier. -/
  realizableProxy : PhysicallyRealizableLedger sensor

/-- Every sensor has the combined directed-ledger / admissibility /
realizability package. -/
noncomputable def concreteEulerLedgerOntologyInterface (sensor : DefectSensor) :
    EulerLedgerOntologyInterface sensor where
  directedLedger := concreteDirectedEulerLedgerSystem sensor
  admissibleTrace := euler_trace_admissible sensor
  realizableProxy := euler_physically_realizable sensor

/-- The ontology package carries a compatible regular Euler carrier. -/
theorem EulerLedgerOntologyInterface.has_regular_carrier
    {sensor : DefectSensor} (pkg : EulerLedgerOntologyInterface sensor) :
    ∃ carrier : RegularCarrier,
      carrier.radius = sensor.realPart - 1 / 2 ∧ 0 < carrier.radius :=
  pkg.admissibleTrace.carrier_compatible

/-- The realizability proxy in the ontology package is positive at every depth. -/
theorem EulerLedgerOntologyInterface.scalarState_pos
    {sensor : DefectSensor} (pkg : EulerLedgerOntologyInterface sensor) (N : ℕ) :
    letI : PhysicallyRealizableLedger sensor := pkg.realizableProxy
    0 < PhysicallyRealizableLedger.scalarState (sensor := sensor) N := by
  letI : PhysicallyRealizableLedger sensor := pkg.realizableProxy
  simpa using PhysicallyRealizableLedger.scalarStatePos (sensor := sensor) N

/-- The realizability proxy in the ontology package has uniformly bounded T1
defect. -/
theorem EulerLedgerOntologyInterface.scalarDefectBounded
    {sensor : DefectSensor} (pkg : EulerLedgerOntologyInterface sensor) :
    letI : PhysicallyRealizableLedger sensor := pkg.realizableProxy
    ∃ K : ℝ, ∀ N : ℕ,
      IndisputableMonolith.Foundation.LawOfExistence.defect
        (PhysicallyRealizableLedger.scalarState (sensor := sensor) N) ≤ K := by
  letI : PhysicallyRealizableLedger sensor := pkg.realizableProxy
  simpa using PhysicallyRealizableLedger.scalarDefectBounded (sensor := sensor)

/-- Concrete theorem form: every sensor has a directed arithmetic Euler ledger,
an admissible Euler trace, and a T1-bounded realizability proxy. This is the
current strongest proved bridge from arithmetic Euler data into the ontology
layer. -/
theorem concreteEulerLedgerOntologyInterface_exists (sensor : DefectSensor) :
    ∃ pkg : EulerLedgerOntologyInterface sensor,
      (∀ support : PrimeSupport,
        LedgerForcing.balanced (pkg.directedLedger.stage support)) ∧
      (∀ support : PrimeSupport, ∀ agent : ℕ,
        LedgerForcing.net_flow (pkg.directedLedger.stage support) agent = 0) ∧
      (∃ carrier : RegularCarrier,
        carrier.radius = sensor.realPart - 1 / 2 ∧ 0 < carrier.radius) ∧
      (letI : PhysicallyRealizableLedger sensor := pkg.realizableProxy
       ∃ K : ℝ, ∀ N : ℕ,
        IndisputableMonolith.Foundation.LawOfExistence.defect
          (PhysicallyRealizableLedger.scalarState (sensor := sensor) N) ≤ K) := by
  refine ⟨concreteEulerLedgerOntologyInterface sensor, ?_, ?_, ?_, ?_⟩
  · intro support
    exact (concreteEulerLedgerOntologyInterface sensor).directedLedger.stage_balanced support
  · intro support agent
    exact (concreteEulerLedgerOntologyInterface sensor).directedLedger.stage_net_flow_zero support agent
  · exact (concreteEulerLedgerOntologyInterface sensor).has_regular_carrier
  · exact (concreteEulerLedgerOntologyInterface sensor).scalarDefectBounded

end NumberTheory
end IndisputableMonolith
