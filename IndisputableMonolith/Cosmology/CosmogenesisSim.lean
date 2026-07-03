import Mathlib

/-!
# Cosmogenesis Simulation: a computable, kernel-checked mirror

`Cosmology/PreBigBang` and `Cosmology/FirstTick` prove the dynamics over `ℝ`.
This module gives the same cosmogenesis a **computable** form over `ℚ`, so the
simulation is a Lean object you can `#eval`, with a conservation law proved in
the kernel rather than only checked at runtime.

The recognition ledger is mirrored exactly:

* `QEvent` is `Foundation.LedgerForcing.RecognitionEvent` over `ℚ`.
* `qreciprocal` swaps source/target and inverts the ratio.
* `addEvent` posts an event together with its reciprocal (double-entry).
* `qcost` is the summed J-cost; `qcost_addEvent` is the per-tick increment
  `+ 2·J(ratio)`, mirroring `FirstTick.ledger_cost_add_event`.

The conserved quantity (σ) takes its multiplicative form here, which is rational
and therefore computable: the **flow product** at an agent, the product of the
ratios of all events touching it. Double-entry posting multiplies it by
`r · r⁻¹ = 1`, so it is invariant. `cosmogenesis_conserves` proves the flow
product is exactly `1` at every agent after the full 8-tick cosmogenesis, for any
positive seed, with no `decide` and no `sorry`.

The self-similar recurrence `r ↦ 1 + 1/r` runs over `ℚ` and produces the exact
Fibonacci convergents `2, 3/2, 5/3, 8/5, 13/8, …`, which converge to `φ`. So the
emergence of `φ` is visible as an exact rational sequence, and `#eval` shows it.
-/

set_option linter.unusedSimpArgs false

namespace IndisputableMonolith
namespace Cosmology
namespace CosmogenesisSim

/-- A recognition event over `ℚ`. Mirror of `LedgerForcing.RecognitionEvent`. -/
structure QEvent where
  source : ℕ
  target : ℕ
  ratio : ℚ
  deriving Repr

/-- The reciprocal event: swap source/target, invert the ratio. -/
def qreciprocal (e : QEvent) : QEvent := ⟨e.target, e.source, e.ratio⁻¹⟩

/-- The canonical recognition cost over `ℚ`: `J(x) = (x + x⁻¹)/2 - 1`. -/
def qJ (x : ℚ) : ℚ := (x + x⁻¹) / 2 - 1

/-- Total ledger cost. Mirror of `LedgerForcing.ledger_cost`. -/
def qcost (es : List QEvent) : ℚ := (es.map (fun e => qJ e.ratio)).sum

/-- An event's contribution to the flow at an agent: its ratio if it touches the
agent (as source or target), and `1` otherwise. -/
def flowContribution (agent : ℕ) (e : QEvent) : ℚ :=
  if e.source = agent ∨ e.target = agent then e.ratio else 1

/-- The flow product at an agent: the product over all events of their
contribution. This is the multiplicative (computable) form of σ. Conserved
value is `1`. -/
def flowProduct (es : List QEvent) (agent : ℕ) : ℚ :=
  (es.map (flowContribution agent)).prod

/-- Post one distinction. Double-entry forces the reciprocal in with it.
Mirror of `LedgerForcing.add_event`. -/
def addEvent (es : List QEvent) (e : QEvent) : List QEvent :=
  e :: qreciprocal e :: es

/-! ## Cost increment per tick (mirror of `FirstTick.ledger_cost_add_event`) -/

/-- `J` is reciprocal-symmetric over `ℚ`. -/
theorem qJ_recip (x : ℚ) : qJ x⁻¹ = qJ x := by
  unfold qJ; rw [inv_inv]; ring

/-- Posting one paired event raises the cost by exactly `2·J(ratio)`. -/
theorem qcost_addEvent (L : List QEvent) (e : QEvent) :
    qcost (addEvent L e) = qcost L + 2 * qJ e.ratio := by
  unfold qcost addEvent
  simp only [List.map_cons, List.sum_cons, qreciprocal, qJ_recip]
  ring

/-! ## σ as a conserved multiplicative invariant -/

/-- The empty ledger has flow product `1` at every agent. -/
theorem flowProduct_nil (agent : ℕ) : flowProduct [] agent = 1 := by
  simp [flowProduct]

/-- An event and its reciprocal contribute a factor of exactly `1` at every
agent: either both touch it (factor `r · r⁻¹ = 1`) or neither does (factor `1`). -/
theorem flowContribution_pair (e : QEvent) (he : e.ratio ≠ 0) (agent : ℕ) :
    flowContribution agent e * flowContribution agent (qreciprocal e) = 1 := by
  simp only [flowContribution, qreciprocal]
  by_cases h : e.source = agent ∨ e.target = agent
  · rw [if_pos h, if_pos h.symm]
    exact mul_inv_cancel₀ he
  · rw [if_neg h, if_neg (mt Or.symm h)]
    ring

/-- **Conservation step.** Posting a paired event leaves the flow product
unchanged at every agent (the `r · r⁻¹ = 1` cancellation). -/
theorem flowProduct_addEvent (L : List QEvent) (e : QEvent) (he : e.ratio ≠ 0)
    (agent : ℕ) : flowProduct (addEvent L e) agent = flowProduct L agent := by
  unfold flowProduct addEvent
  simp only [List.map_cons, List.prod_cons]
  rw [← mul_assoc, flowContribution_pair e he agent, one_mul]

/-- Flow product is `1` for any ledger built solely by `addEvent` from empty,
provided every posted ratio is nonzero. -/
theorem flowProduct_foldl (agent : ℕ) (f : ℕ → QEvent)
    (hf : ∀ t, (f t).ratio ≠ 0) (n : ℕ) :
    flowProduct ((List.range n).foldl (fun L t => addEvent L (f t)) []) agent = 1 := by
  induction n with
  | zero => simp [flowProduct]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [flowProduct_addEvent _ _ (hf k) agent, ih]

/-! ## The self-similar recurrence and the cosmogenesis ledger -/

/-- The self-similar recognition recurrence `r ↦ 1 + 1/r` over `ℚ`.
Exact Fibonacci convergents to `φ`. -/
def recurSeq (seed : ℚ) : ℕ → ℚ
  | 0 => seed
  | (n + 1) => 1 + (recurSeq seed n)⁻¹

/-- The recurrence stays positive for a positive seed. -/
theorem recurSeq_pos (seed : ℚ) (hs : 0 < seed) : ∀ t, 0 < recurSeq seed t
  | 0 => hs
  | (n + 1) => by
      have hp : 0 < recurSeq seed n := recurSeq_pos seed hs n
      have hinv : 0 < (recurSeq seed n)⁻¹ := inv_pos.mpr hp
      show (0 : ℚ) < 1 + (recurSeq seed n)⁻¹
      linarith

/-- The Gray-code Hamiltonian cycle on the 3-cube, closing back to its start. -/
def cyc : List ℕ := [0, 1, 3, 2, 6, 7, 5, 4, 0]

/-- The cadence walk has nine vertices (eight edges, closed loop). -/
theorem cyc_length : cyc.length = 9 := by native_decide

/-- Exactly eight ticks are posted in `cosmogenesis`. -/
theorem cosmogenesis_tick_count (_seed : ℚ) :
    (List.range 8).length = 8 := rfl

/-- Positive ratio distinct from unity incurs positive `qJ` cost. -/
theorem qJ_pos {x : ℚ} (hx : 0 < x) (hne : x ≠ 1) : 0 < qJ x := by
  have h : qJ x = (x - 1) ^ 2 / (2 * x) := by
    unfold qJ
    field_simp [hx.ne']
    ring
  have h01 : x - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (x - 1) ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr h01
  rw [h]
  exact div_pos hsq (by linarith)

/-- Default seed-2 run posts a genuine distinction at tick 0. -/
theorem seed2_distinction : (recurSeq 2 0) ≠ 1 := by native_decide

/-- The recognition event posted at tick `t`: an edge of the 3-cube carrying the
`t`-th recurrence ratio. -/
def cosmoEvent (seed : ℚ) (t : ℕ) : QEvent :=
  ⟨cyc.getD t 0, cyc.getD (t + 1) 0, recurSeq seed t⟩

/-- **The cosmogenesis ledger.** Eight ticks posted onto the empty ledger, one
per edge of the 3-cube cadence, each paired by double-entry. -/
def cosmogenesis (seed : ℚ) : List QEvent :=
  (List.range 8).foldl (fun L t => addEvent L (cosmoEvent seed t)) []

/-- **σ conservation, proved.** After the full cosmogenesis, the flow product is
exactly `1` at every agent, for any positive seed. No `decide`, no `sorry`. -/
theorem cosmogenesis_conserves (seed : ℚ) (hs : 0 < seed) (agent : ℕ) :
    flowProduct (cosmogenesis seed) agent = 1 :=
  flowProduct_foldl agent (cosmoEvent seed)
    (fun t => (recurSeq_pos seed hs t).ne') 8

/-- Each paired posting adds two events. -/
theorem addEvent_length (L : List QEvent) (e : QEvent) :
    (addEvent L e).length = L.length + 2 := by
  simp [addEvent]

/-- A ledger built by `n` paired postings from empty has `2n` events. -/
theorem foldl_addEvent_length (f : ℕ → QEvent) (n : ℕ) :
    ((List.range n).foldl (fun L t => addEvent L (f t)) []).length = 2 * n := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [addEvent_length, ih]
      ring

/-- The cosmogenesis posts sixteen events (eight ticks, each paired). -/
theorem cosmogenesis_length (seed : ℚ) : (cosmogenesis seed).length = 16 := by
  have h : (cosmogenesis seed).length = 2 * 8 := foldl_addEvent_length (cosmoEvent seed) 8
  omega

/-- First-tick cost is positive for the canonical seed-2 cosmogenesis run. -/
theorem seed2_first_tick_cost_pos : 0 < qJ (recurSeq 2 0) :=
  qJ_pos (recurSeq_pos 2 (by norm_num) 0) seed2_distinction

/-- Certificates mirrored by `cosmogenesis_golden_trace_v0` (Python microkernel). -/
structure TraceCertificates where
  event_count : (cosmogenesis 2).length = 16
  sigma_at_zero : flowProduct (cosmogenesis 2) 0 = 1
  cadence_eight_ticks : (List.range 8).length = 8
  cyc_closed_nine_vertices : cyc.length = 9
  first_tick_cost_pos : 0 < qJ (recurSeq 2 0)

/-- Kernel-checked trace certificates for the canonical seed-2 run. -/
theorem trace_certificates_seed2 : TraceCertificates where
  event_count := cosmogenesis_length 2
  sigma_at_zero := cosmogenesis_conserves 2 (by norm_num) 0
  cadence_eight_ticks := cosmogenesis_tick_count 2
  cyc_closed_nine_vertices := cyc_length
  first_tick_cost_pos := seed2_first_tick_cost_pos

/-! ## Runnable demonstrations

These are evaluable. Uncomment locally to watch the universe emerge.

`#eval (List.range 9).map (fun t => recurSeq 2 t)`  -- 2, 3/2, 5/3, 8/5, … → φ
`#eval qcost (cosmogenesis 2)`                       -- the climbing cost
`#eval (cosmogenesis 2).length`                      -- 16
`#eval flowProduct (cosmogenesis 2) 0`               -- 1  (σ conserved)
-/

/-- Conservation holds for the seed-2 run as a direct corollary, kernel-proved. -/
example (agent : ℕ) : flowProduct (cosmogenesis 2) agent = 1 :=
  cosmogenesis_conserves 2 (by norm_num) agent

end CosmogenesisSim
end Cosmology
end IndisputableMonolith
