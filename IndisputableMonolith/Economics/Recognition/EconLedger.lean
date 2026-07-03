import IndisputableMonolith.Economics.Recognition.Core

/-!
# Economic Ledger Helpers

Paired economic trades are recognition events added together with their
reciprocal entries. Conservation is inherited from the double-entry ledger
forcing theorem.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

noncomputable section

/-- Economic trade event, using the foundation-level recognition event. -/
abbrev TradeEvent :=
  IndisputableMonolith.Foundation.LedgerForcing.RecognitionEvent

/-- Cost of a trade event. -/
def tradeCost (e : TradeEvent) : ℝ :=
  IndisputableMonolith.Foundation.LedgerForcing.event_cost e

/-- Add a trade together with its reciprocal entry. -/
def addPairedTrade (L : EconLedger) (e : TradeEvent) : EconLedger where
  ledger := IndisputableMonolith.Foundation.LedgerForcing.add_event L.ledger e

theorem tradeCost_reciprocal (e : TradeEvent) :
    tradeCost e =
      tradeCost (IndisputableMonolith.Foundation.LedgerForcing.reciprocal e) :=
  IndisputableMonolith.Foundation.LedgerForcing.reciprocity e

theorem addPairedTrade_sigmaFeasible (L : EconLedger) (e : TradeEvent) :
    sigmaFeasible (addPairedTrade L e) :=
  econ_ledger_conserves (addPairedTrade L e)

theorem addPairedTrade_balanced (L : EconLedger) (e : TradeEvent) :
    IndisputableMonolith.Foundation.LedgerForcing.balanced (addPairedTrade L e).ledger :=
  IndisputableMonolith.Foundation.LedgerForcing.add_event_balanced L.ledger e

/-- The economic ledger forcing principle, imported from the foundation layer. -/
theorem economic_ledger_forcing_principle :
    (∀ x : ℝ, x ≠ 0 →
      IndisputableMonolith.Foundation.LedgerForcing.J x =
        IndisputableMonolith.Foundation.LedgerForcing.J (x⁻¹)) ∧
    (∀ e : TradeEvent,
      tradeCost e =
        tradeCost (IndisputableMonolith.Foundation.LedgerForcing.reciprocal e)) ∧
    (∀ e : TradeEvent,
      Real.log e.ratio +
        Real.log (IndisputableMonolith.Foundation.LedgerForcing.reciprocal e).ratio = 0) ∧
    (∃ L : EconLedger,
      sigmaFeasible L ∧
        IndisputableMonolith.Foundation.LedgerForcing.ledger_cost L.ledger = 0) := by
  rcases IndisputableMonolith.Foundation.LedgerForcing.ledger_forcing_principle with
    ⟨hJ, hrecip, hlog, L, _hbal, hcost⟩
  refine ⟨hJ, ?_, hlog, ⟨⟨L⟩, econ_ledger_conserves ⟨L⟩, hcost⟩⟩
  intro e
  exact hrecip e

end

end Recognition
end Economics
end IndisputableMonolith
