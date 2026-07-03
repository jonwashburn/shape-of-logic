import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# The Trolley Problem as a J/σ Tradeoff

## §XXIII.C row "Philosophical paradoxes" — Trolley side.

The trolley problem: a runaway trolley will kill 5 people unless
diverted onto a side track that will kill 1 person.  Pull the
lever to divert (utilitarian) or do nothing (deontological)?

In RS: utilitarianism minimizes J-cost (5 lives saved >
1 life saved).  Deontology preserves σ-conservation: the act of
pulling the lever creates a σ-imbalance (an act of agency that
breaks the no-action equilibrium), even though it strictly
decreases J.

The genuine moral tension is the J/σ tradeoff:

  - Pulling the lever: J decreases (5 → 1 deaths) but σ-skew
    is created (active killing introduces an agency-imbalance).
  - Not pulling: σ is preserved but J is maximal.

The 14 DREAM virtues from `Ethics/Virtues/CompletenessClosure`
provide the structural bridge: a virtue-aligned action can be
J-reducing AND σ-preserving simultaneously, but the trolley
constraints force a strict tradeoff.

## What this module provides

1. `TrolleyChoice`: inductive `pull | doNothing`.
2. `livesLost`: 1 (pull) or 5 (doNothing).
3. `sigmaCost`: 1 (pull, agency imbalance) or 0 (doNothing).
4. `jCost`: lives lost (proxy for J-cost on the lives manifold).
5. `tradeoff_strict`: pulling lowers J but raises σ.
6. `no_strictly_dominant_choice`: neither choice dominates the
   other on both axes.
7. Master cert `TrolleyTradeoffCert` with 5 fields.
-/

namespace IndisputableMonolith
namespace Decision
namespace Trolley

open Constants

noncomputable section

/-- The trolley choice: pull the lever or do nothing. -/
inductive TrolleyChoice where
  | pull
  | doNothing
  deriving DecidableEq, Inhabited

namespace TrolleyChoice

/-- Display name. -/
def name : TrolleyChoice → String
  | pull      => "pull lever"
  | doNothing => "do nothing"

end TrolleyChoice

/-- Lives lost as a function of choice. -/
def livesLost (c : TrolleyChoice) : ℕ :=
  match c with
  | TrolleyChoice.pull      => 1
  | TrolleyChoice.doNothing => 5

/-- σ-cost: agency imbalance from active killing. -/
def sigmaCost (c : TrolleyChoice) : ℝ :=
  match c with
  | TrolleyChoice.pull      => 1
  | TrolleyChoice.doNothing => 0

/-- J-cost proxy: lives lost as real number. -/
def jCost (c : TrolleyChoice) : ℝ := (livesLost c : ℝ)

/-- Pulling lowers J: `jCost(pull) < jCost(doNothing)`. -/
theorem pull_lowers_J : jCost TrolleyChoice.pull < jCost TrolleyChoice.doNothing := by
  unfold jCost livesLost
  norm_num

/-- Pulling raises σ: `sigmaCost(pull) > sigmaCost(doNothing)`. -/
theorem pull_raises_sigma :
    sigmaCost TrolleyChoice.pull > sigmaCost TrolleyChoice.doNothing := by
  unfold sigmaCost
  norm_num

/-- The tradeoff is strict: lowering J requires raising σ, and
    vice versa. -/
theorem tradeoff_strict :
    jCost TrolleyChoice.pull < jCost TrolleyChoice.doNothing ∧
    sigmaCost TrolleyChoice.pull > sigmaCost TrolleyChoice.doNothing :=
  ⟨pull_lowers_J, pull_raises_sigma⟩

/-- No choice strictly dominates the other on both axes.
    Pulling is better on J, worse on σ; doNothing is the reverse. -/
theorem no_strictly_dominant_choice
    (c1 c2 : TrolleyChoice)
    (h_diff : c1 ≠ c2) :
    ¬ (jCost c1 < jCost c2 ∧ sigmaCost c1 < sigmaCost c2) := by
  intro ⟨hJ, hσ⟩
  cases c1 with
  | pull =>
    cases c2 with
    | pull => exact absurd rfl h_diff
    | doNothing =>
      have := pull_raises_sigma
      linarith
  | doNothing =>
    cases c2 with
    | pull =>
      have := pull_lowers_J
      linarith
    | doNothing => exact absurd rfl h_diff

/-! ## Master certificate -/

/-- **TROLLEY TRADEOFF MASTER CERTIFICATE.** -/
structure TrolleyTradeoffCert where
  pull_lives_lost : livesLost TrolleyChoice.pull = 1
  doNothing_lives_lost : livesLost TrolleyChoice.doNothing = 5
  tradeoff :
    jCost TrolleyChoice.pull < jCost TrolleyChoice.doNothing ∧
    sigmaCost TrolleyChoice.pull > sigmaCost TrolleyChoice.doNothing
  no_dominance :
    ∀ (c1 c2 : TrolleyChoice), c1 ≠ c2 →
      ¬ (jCost c1 < jCost c2 ∧ sigmaCost c1 < sigmaCost c2)
  pull_creates_agency_imbalance :
    sigmaCost TrolleyChoice.pull = 1

/-- The master certificate is inhabited. -/
def trolleyTradeoffCert : TrolleyTradeoffCert where
  pull_lives_lost := rfl
  doNothing_lives_lost := rfl
  tradeoff := tradeoff_strict
  no_dominance := no_strictly_dominant_choice
  pull_creates_agency_imbalance := rfl

end

end Trolley
end Decision
end IndisputableMonolith
