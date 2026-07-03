import Mathlib
import IndisputableMonolith.Foundation.LedgerForcing
import IndisputableMonolith.Foundation.RecognitionForcing
import IndisputableMonolith.NumberTheory.EulerInstantiation

/-!
# Concrete Euler Ledger

This module formalizes the first arithmetic-to-ledger identification step.

For any positive real exponent `σ` and any finite prime support, we build an
actual `LedgerForcing.Ledger` whose recognition-event ratios are the Euler
terms `p^{-σ}` together with their reciprocals. For a `DefectSensor`, taking
`σ = sensor.realPart` produces a finite, balanced arithmetic ledger indexed by
the same strip coordinate that appears in the sensor machinery.

This does **not** yet prove `RSPhysicalThesis`. What it does provide is the
first fully concrete bridge object:

* a real arithmetic ledger built from prime Euler data,
* double-entry balance by construction,
* zero net flow by the generic ledger conservation theorem,
* positive nontrivial recognition cost for each prime event,
* an explicit total ledger-cost formula in terms of `J (p^{-σ})`.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Foundation

/-! ## Prime Euler events -/

/-- The strip real part of a defect sensor is positive. -/
theorem sensor_realPart_pos (sensor : DefectSensor) : 0 < sensor.realPart := by
  linarith [sensor.in_strip.1]

/-- The basic arithmetic recognition event contributed by a prime Euler factor.

Its ratio is the positive real quantity `p^{-σ}`. -/
noncomputable def primeEulerEvent (σ : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    LedgerForcing.RecognitionEvent where
  source := 0
  target := p
  ratio := (p : ℝ) ^ (-σ)
  ratio_pos := eigenvalue_pos hσ p

@[simp] theorem primeEulerEvent_ratio (σ : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    (primeEulerEvent σ hσ p).ratio = (p : ℝ) ^ (-σ) := rfl

@[simp] theorem primeEulerEvent_target (σ : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    (primeEulerEvent σ hσ p).target = p := rfl

/-- The prime Euler event is genuinely nontrivial: its ratio is strictly below `1`. -/
theorem primeEulerEvent_ratio_lt_one {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (primeEulerEvent σ hσ p).ratio < 1 := by
  simpa [primeEulerEvent] using eigenvalue_lt_one hσ p

/-- Hence the prime Euler event does not have ratio `1`. -/
theorem primeEulerEvent_ratio_ne_one {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (primeEulerEvent σ hσ p).ratio ≠ 1 := by
  exact (primeEulerEvent_ratio_lt_one hσ p).ne

/-- The reciprocal Euler event has ratio `p^σ`. -/
theorem reciprocal_primeEulerEvent_ratio {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (LedgerForcing.reciprocal (primeEulerEvent σ hσ p)).ratio = (p : ℝ) ^ σ := by
  simp [LedgerForcing.reciprocal, primeEulerEvent, Real.rpow_neg, inv_inv]

/-- The cost of the prime Euler event is exactly `J(p^{-σ})`. -/
@[simp] theorem primeEulerEvent_cost_eq_J (σ : ℝ) (hσ : 0 < σ) (p : Nat.Primes) :
    LedgerForcing.event_cost (primeEulerEvent σ hσ p) =
      LedgerForcing.J ((p : ℝ) ^ (-σ)) := by
  rfl

/-- Each prime Euler event has strictly positive recognition cost. -/
theorem primeEulerEvent_cost_pos {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    0 < LedgerForcing.event_cost (primeEulerEvent σ hσ p) := by
  have hrecognition :
      0 < RecognitionForcing.recognition_cost (primeEulerEvent σ hσ p) := by
    exact RecognitionForcing.nontrivial_recognition_positive_cost
      (primeEulerEvent σ hσ p) (primeEulerEvent_ratio_ne_one hσ p)
  simpa [RecognitionForcing.recognition_cost, LedgerForcing.event_cost] using hrecognition

/-! ## Finite Euler ledgers -/

/-- Build a concrete finite Euler ledger from a finite list of primes.

Each prime contributes one event with ratio `p^{-σ}` and one reciprocal event,
so balance is preserved at every step. -/
noncomputable def finiteEulerLedger (σ : ℝ) (hσ : 0 < σ) :
    List Nat.Primes → LedgerForcing.Ledger
  | [] => LedgerForcing.empty_ledger
  | p :: ps => LedgerForcing.add_event (finiteEulerLedger σ hσ ps) (primeEulerEvent σ hσ p)

/-- Every finite Euler ledger is balanced. -/
theorem finiteEulerLedger_balanced (σ : ℝ) (hσ : 0 < σ) (support : List Nat.Primes) :
    LedgerForcing.balanced (finiteEulerLedger σ hσ support) :=
  LedgerForcing.ledger_balanced _

/-- Every finite Euler ledger has zero net flow at every agent. -/
theorem finiteEulerLedger_net_flow_zero (σ : ℝ) (hσ : 0 < σ)
    (support : List Nat.Primes) (agent : ℕ) :
    LedgerForcing.net_flow (finiteEulerLedger σ hσ support) agent = 0 := by
  exact LedgerForcing.conservation_from_balance _ (finiteEulerLedger_balanced σ hσ support) agent

/-- If a prime belongs to the support list, its Euler event appears in the ledger. -/
theorem primeEulerEvent_mem_finiteEulerLedger {σ : ℝ} {hσ : 0 < σ} :
    ∀ {support : List Nat.Primes} {p : Nat.Primes},
      p ∈ support →
      primeEulerEvent σ hσ p ∈ (finiteEulerLedger σ hσ support).events
  | [], _, hp => by cases hp
  | q :: qs, p, hp => by
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst p
        simp [finiteEulerLedger, LedgerForcing.add_event]
      · simp [finiteEulerLedger, LedgerForcing.add_event,
          primeEulerEvent_mem_finiteEulerLedger (support := qs) hp]

/-- If a prime belongs to the support list, its reciprocal Euler event also appears. -/
theorem reciprocal_primeEulerEvent_mem_finiteEulerLedger {σ : ℝ} {hσ : 0 < σ} :
    ∀ {support : List Nat.Primes} {p : Nat.Primes},
      p ∈ support →
      LedgerForcing.reciprocal (primeEulerEvent σ hσ p) ∈
        (finiteEulerLedger σ hσ support).events
  | [], _, hp => by cases hp
  | q :: qs, p, hp => by
      simp only [List.mem_cons] at hp
      rcases hp with hp | hp
      · subst p
        simp [finiteEulerLedger, LedgerForcing.add_event]
      · simp [finiteEulerLedger, LedgerForcing.add_event,
          reciprocal_primeEulerEvent_mem_finiteEulerLedger (support := qs) hp]

/-- Adding one paired event contributes exactly twice its single-event cost. -/
private theorem ledger_cost_foldl_with_offset
    (events : List LedgerForcing.RecognitionEvent) (acc : ℝ) :
    events.foldl (fun acc e => acc + LedgerForcing.event_cost e) acc =
      acc + events.foldl (fun acc e => acc + LedgerForcing.event_cost e) 0 := by
  induction events generalizing acc with
  | nil =>
      simp
  | cons e es ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + LedgerForcing.event_cost e),
        ih (0 + LedgerForcing.event_cost e)]
      ring

/-- Adding one paired event contributes exactly twice its single-event cost. -/
private theorem add_event_cost_formula (L : LedgerForcing.Ledger)
    (e : LedgerForcing.RecognitionEvent) :
    LedgerForcing.ledger_cost (LedgerForcing.add_event L e) =
      2 * LedgerForcing.event_cost e + LedgerForcing.ledger_cost L := by
  unfold LedgerForcing.ledger_cost LedgerForcing.add_event
  simp only [List.foldl_cons]
  rw [LedgerForcing.reciprocity]
  rw [ledger_cost_foldl_with_offset]
  ring

/-- Explicit total-cost formula for a finite Euler ledger in terms of the
single-event costs. -/
theorem finiteEulerLedger_cost_formula (σ : ℝ) (hσ : 0 < σ) :
    ∀ support : List Nat.Primes,
      LedgerForcing.ledger_cost (finiteEulerLedger σ hσ support) =
        2 * (support.map (fun p => LedgerForcing.event_cost (primeEulerEvent σ hσ p))).sum
  | [] => by
      simp [finiteEulerLedger, LedgerForcing.empty_ledger_cost]
  | p :: ps => by
      rw [finiteEulerLedger, add_event_cost_formula,
        finiteEulerLedger_cost_formula σ hσ ps]
      simp
      ring

/-- The same total-cost formula, rewritten directly in terms of `J (p^{-σ})`. -/
theorem finiteEulerLedger_cost_formula_J (σ : ℝ) (hσ : 0 < σ) (support : List Nat.Primes) :
    LedgerForcing.ledger_cost (finiteEulerLedger σ hσ support) =
      2 * (support.map (fun p : Nat.Primes => LedgerForcing.J ((p : ℝ) ^ (-σ)))).sum := by
  simpa [primeEulerEvent_cost_eq_J] using finiteEulerLedger_cost_formula σ hσ support

/-! ## Sensor-indexed concrete Euler ledgers -/

/-- The concrete finite Euler ledger attached to a defect sensor. -/
noncomputable def sensorEulerLedger (sensor : DefectSensor) (support : Finset Nat.Primes) :
    LedgerForcing.Ledger :=
  finiteEulerLedger sensor.realPart (sensor_realPart_pos sensor) support.toList

/-- The sensor-indexed concrete Euler ledger is balanced. -/
theorem sensorEulerLedger_balanced (sensor : DefectSensor) (support : Finset Nat.Primes) :
    LedgerForcing.balanced (sensorEulerLedger sensor support) := by
  unfold sensorEulerLedger
  exact finiteEulerLedger_balanced sensor.realPart (sensor_realPart_pos sensor) support.toList

/-- The sensor-indexed concrete Euler ledger has zero net flow. -/
theorem sensorEulerLedger_net_flow_zero (sensor : DefectSensor)
    (support : Finset Nat.Primes) (agent : ℕ) :
    LedgerForcing.net_flow (sensorEulerLedger sensor support) agent = 0 := by
  unfold sensorEulerLedger
  exact finiteEulerLedger_net_flow_zero sensor.realPart (sensor_realPart_pos sensor) support.toList agent

/-- Every supported prime contributes its Euler event to the sensor-indexed ledger. -/
theorem primeEulerEvent_mem_sensorEulerLedger
    (sensor : DefectSensor) {support : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p ∈ support) :
    primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈
      (sensorEulerLedger sensor support).events := by
  unfold sensorEulerLedger
  exact primeEulerEvent_mem_finiteEulerLedger
    (support := support.toList) (p := p) (by simpa using hp)

/-- Every supported prime also contributes the reciprocal Euler event. -/
theorem reciprocal_primeEulerEvent_mem_sensorEulerLedger
    (sensor : DefectSensor) {support : Finset Nat.Primes} {p : Nat.Primes}
    (hp : p ∈ support) :
    LedgerForcing.reciprocal (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈
      (sensorEulerLedger sensor support).events := by
  unfold sensorEulerLedger
  exact reciprocal_primeEulerEvent_mem_finiteEulerLedger
    (support := support.toList) (p := p) (by simpa using hp)

/-- Explicit total J-cost formula for the sensor-indexed concrete Euler ledger. -/
theorem sensorEulerLedger_cost_formula (sensor : DefectSensor)
    (support : Finset Nat.Primes) :
    LedgerForcing.ledger_cost (sensorEulerLedger sensor support) =
      2 * (support.toList.map
        (fun p : Nat.Primes => LedgerForcing.J ((p : ℝ) ^ (-sensor.realPart)))).sum := by
  unfold sensorEulerLedger
  simpa using finiteEulerLedger_cost_formula_J
    sensor.realPart (sensor_realPart_pos sensor) support.toList

/-- First concrete arithmetic identification theorem.

Finite Euler-product data at the real part of a `DefectSensor` determines an
actual double-entry ledger with:

* balance,
* zero net flow,
* explicit prime-event membership,
* explicit total J-cost.

This is the first fully concrete bridge object from arithmetic Euler data into
the ledger language used by the RS sensor framework. -/
theorem sensorEulerLedger_identification (sensor : DefectSensor)
    (support : Finset Nat.Primes) :
    let L := sensorEulerLedger sensor support
    LedgerForcing.balanced L ∧
    (∀ agent : ℕ, LedgerForcing.net_flow L agent = 0) ∧
    (∀ p : Nat.Primes, p ∈ support →
      primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p ∈ L.events ∧
      LedgerForcing.reciprocal
        (primeEulerEvent sensor.realPart (sensor_realPart_pos sensor) p) ∈ L.events) ∧
    LedgerForcing.ledger_cost L =
      2 * (support.toList.map
        (fun p : Nat.Primes => LedgerForcing.J ((p : ℝ) ^ (-sensor.realPart)))).sum := by
  refine ⟨sensorEulerLedger_balanced sensor support, ?_, ?_,
    sensorEulerLedger_cost_formula sensor support⟩
  · intro agent
    exact sensorEulerLedger_net_flow_zero sensor support agent
  · intro p hp
    exact ⟨primeEulerEvent_mem_sensorEulerLedger sensor hp,
      reciprocal_primeEulerEvent_mem_sensorEulerLedger sensor hp⟩

end NumberTheory
end IndisputableMonolith
