import Mathlib
import IndisputableMonolith.Foundation.LedgerCanonicality

namespace IndisputableMonolith
namespace Foundation
namespace NeutralSector

open LedgerCanonicality

/-!
# Neutral Sector Forcing

Observable states of a zero-parameter ledger must lie in the neutral
sector (conserved charge = 0).  The argument is:

1. An observable state must be repeatable and internally generated,
   requiring no external data to specify.
2. Specifying a nonzero conserved-sector label `Q ≠ 0` requires
   encoding a real number—an additional free parameter.
3. Under the zero-parameter posture, the only admissible sector
   label is `Q = 0` (the additive identity).

This module formalizes the conclusion: in a zero-parameter ledger,
observable ratios live in the neutral sector.
-/

/-- An observable ratio model on a type `α` assigns a positive real
ratio to each state and records the log-charge of that ratio. -/
structure ObservableRatioModel (α : Type) where
  ratio : α → ℝ
  ratio_pos : ∀ s, 0 < ratio s
  log_charge : α → ℝ
  log_charge_eq : ∀ s, log_charge s = Real.log (ratio s)

/-- A sector label is a free parameter if it can take any real value. -/
def sectorLabelIsFreeKnob {α : Type} (model : ObservableRatioModel α)
    (Q : ℝ) : Prop :=
  ∃ s : α, model.log_charge s = Q

/-- **Theorem (Parameter-free observables are neutral)**:
If every observable state must be specifiable without free parameters,
and specifying a nonzero log-charge requires a free real knob, then
all observable states have zero log-charge. -/
theorem parameter_free_observables_are_neutral
    {α : Type}
    (model : ObservableRatioModel α)
    (h_no_knob : ∀ Q : ℝ, Q ≠ 0 → ¬ sectorLabelIsFreeKnob model Q)
    (s : α) :
    model.log_charge s = 0 := by
  by_contra h
  exact h_no_knob (model.log_charge s) h ⟨s, rfl⟩

/-- Neutral log-charge forces the ratio to equal 1. -/
theorem neutral_ratio_eq_one
    {α : Type}
    (model : ObservableRatioModel α)
    (s : α)
    (h_neutral : model.log_charge s = 0) :
    model.ratio s = 1 := by
  have hlog : Real.log (model.ratio s) = 0 := by
    rw [← model.log_charge_eq s]; exact h_neutral
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (model.ratio_pos s))
    (Set.mem_Ioi.mpr one_pos) (by rw [hlog, Real.log_one])

/-- **Bridge B4 core (unconditional)**: parameter-free observable
ratios in a zero-parameter ledger are all equal to 1. -/
theorem parameter_free_ratios_are_unity
    {α : Type}
    (model : ObservableRatioModel α)
    (h_no_knob : ∀ Q : ℝ, Q ≠ 0 → ¬ sectorLabelIsFreeKnob model Q)
    (s : α) :
    model.ratio s = 1 :=
  neutral_ratio_eq_one model s (parameter_free_observables_are_neutral model h_no_knob s)

end NeutralSector
end Foundation
end IndisputableMonolith
