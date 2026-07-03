import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.LedgerForcing
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability

/-!
# Recognition Economics Core

This module starts the implementation of Recognition Economics as an
economics-facing layer over already-proved Recognition Science primitives.

The core commitment is deliberately small:

* economic objects are finite distinguishable holdings;
* exchange costs are J-costs of positive ratios;
* an economic ledger is a recognition ledger;
* σ-feasibility is zero net log-flow for every agent.

No new economic theorem is smuggled in here. The conservation theorem below is
exactly `Foundation.LedgerForcing.conservation_from_balance` repackaged for the
economic namespace.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

open IndisputableMonolith.Cost

noncomputable section

/-- A finite economic distinction. At this layer the only native structure is
being distinguishable from other finite alternatives. -/
abbrev Distinction := ℕ

/-- An economic agent carries finite distinguishable holdings and a recognition
budget. Later modules add preferences, observables, contracts, and display
bridges on top of this substrate. -/
structure EconAgent where
  endowment : Finset Distinction
  jbudget : ℝ

/-- An economic ledger is the already-proved recognition ledger read as a ledger
of economic terms-of-trade events. -/
structure EconLedger where
  ledger : IndisputableMonolith.Foundation.LedgerForcing.Ledger

/-- Net recognition skew of an economic ledger at an agent. -/
def netFlow (L : EconLedger) (agent : ℕ) : ℝ :=
  IndisputableMonolith.Foundation.LedgerForcing.net_flow L.ledger agent

/-- σ-feasibility: every agent has zero net log-flow. -/
def sigmaFeasible (L : EconLedger) : Prop :=
  ∀ agent : ℕ, netFlow L agent = 0

/-- J-cost of a price or terms-of-trade ratio. -/
def exchangeCost (price equilibriumPrice : ℝ) : ℝ :=
  Jcost (price / equilibriumPrice)

/-- The empty economic ledger. -/
def emptyLedger : EconLedger where
  ledger := IndisputableMonolith.Foundation.LedgerForcing.empty_ledger

/-- Every economic ledger conserves σ because `LF.Ledger` includes the
double-entry balance proof by construction. -/
theorem econ_ledger_conserves (L : EconLedger) : sigmaFeasible L := by
  intro agent
  exact
    IndisputableMonolith.Foundation.LedgerForcing.conservation_from_balance
      L.ledger
      (IndisputableMonolith.Foundation.LedgerForcing.ledger_balanced L.ledger)
      agent

theorem emptyLedger_sigmaFeasible : sigmaFeasible emptyLedger :=
  econ_ledger_conserves emptyLedger

/-- At equilibrium, exchange cost is zero. -/
theorem exchangeCost_at_equilibrium {p : ℝ} (hp : p ≠ 0) :
    exchangeCost p p = 0 := by
  unfold exchangeCost
  rw [div_self hp]
  exact Jcost_unit0

/-- Positive ratios have nonnegative exchange cost. -/
theorem exchangeCost_nonneg {p e : ℝ} (hp : 0 < p) (he : 0 < e) :
    0 ≤ exchangeCost p e := by
  unfold exchangeCost
  exact Jcost_nonneg (div_pos hp he)

/-- The cost of overpricing by a ratio equals the cost of underpricing by the
reciprocal ratio. -/
theorem exchangeCost_symmetric {p e : ℝ} (hp : 0 < p) (he : 0 < e) :
    exchangeCost p e = exchangeCost e p := by
  unfold exchangeCost
  have hsym := Jcost_symm (div_pos hp he)
  have hrec : (p / e)⁻¹ = e / p := by
    field_simp [hp.ne', he.ne']
  simpa [hrec] using hsym

/-- Finite distinction probability, re-exported in the economics namespace. -/
abbrev Event (N : ℕ) :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability.Event N

/-- Finite rational expectation, re-exported for economic payoff observables. -/
abbrev deltaExpectation {N : ℕ} (X : Fin (N + 1) → ℚ) : ℚ :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability.expectation X

end

end Recognition
end Economics
end IndisputableMonolith
