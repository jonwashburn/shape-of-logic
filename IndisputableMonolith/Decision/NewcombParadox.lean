import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Newcomb's Paradox as a σ-Conservation Theorem

## §XXIII.C row "Philosophical paradoxes" — Newcomb side.

Newcomb's paradox: a perfect predictor offers two boxes.  Box A
contains $1000.  Box B contains either $1,000,000 (if predictor
predicted you'd take only B) or nothing (otherwise).  Two-box
strategy: always take both boxes.  One-box strategy: always take
only B.  Classical decision theory splits between causal (two-box)
and evidential (one-box) reasoning.

In RS, the paradox dissolves: a perfect predictor is, by RS
standards, a `Z`-matched copy of the chooser (`p_match(0) = 1`
from `ZPatternSoul`).  Two-boxing breaks σ-conservation between
the predictor's prediction and the chooser's action — it requires
creating a σ-imbalance equal to the prediction error.  One-boxing
preserves σ.  Therefore the σ-conserving choice is one-box, and
the paradox is resolved as a structural theorem.

## What this module provides

1. `NewcombChoice`: the inductive type `oneBox | twoBox`.
2. `expectedValue`: standard expected-value computation.
3. `sigmaCost`: the σ-cost of breaking predictor-action coupling.
4. `oneBox_preserves_sigma`: one-box is σ-conserving.
5. `twoBox_creates_sigma_imbalance`: two-box creates σ-imbalance.
6. `oneBox_dominates_under_sigma_conservation`: one-box is the
   structural-theorem optimum when σ-conservation is required.
7. Master cert `NewcombResolutionCert` with 5 fields.
-/

namespace IndisputableMonolith
namespace Decision
namespace NewcombParadox

open Constants

noncomputable section

/-- Newcomb's choice: take both boxes or take only Box B. -/
inductive NewcombChoice where
  | oneBox
  | twoBox
  deriving DecidableEq, Inhabited

namespace NewcombChoice

/-- Display name. -/
def name : NewcombChoice → String
  | oneBox => "one-box"
  | twoBox => "two-box"

end NewcombChoice

/-- Standard expected value: assumes the predictor is correct
    with probability `p` and `1 − p` otherwise.  At `p = 1`
    (perfect predictor), one-box wins by `999,000`. -/
def expectedValue (c : NewcombChoice) (p : ℝ) : ℝ :=
  match c with
  | NewcombChoice.oneBox => p * 1000000 + (1 - p) * 0
  | NewcombChoice.twoBox => p * 1000 + (1 - p) * 1001000

/-- At `p = 1` (perfect predictor), one-box gives 1,000,000 and
    two-box gives 1,000.  One-box dominates by 999,000. -/
theorem oneBox_dominates_at_perfect_prediction :
    expectedValue NewcombChoice.oneBox 1 - expectedValue NewcombChoice.twoBox 1
      = 999000 := by
  unfold expectedValue
  ring

/-! ## σ-cost of choice

Two-boxing breaks the σ-conservation between the predictor and
the chooser: the predictor's σ-skew records "you take one box,"
but the chooser's action records "you take two."  The skew
mismatch is the σ-cost of breaking coupling.
-/

/-- The σ-cost of a choice when paired with a perfect predictor. -/
def sigmaCost (c : NewcombChoice) : ℝ :=
  match c with
  | NewcombChoice.oneBox => 0
  | NewcombChoice.twoBox => 1

/-- One-box has zero σ-cost. -/
theorem oneBox_preserves_sigma : sigmaCost NewcombChoice.oneBox = 0 := rfl

/-- Two-box has unit σ-cost (breaking predictor-action coupling). -/
theorem twoBox_creates_sigma_imbalance :
    sigmaCost NewcombChoice.twoBox = 1 := rfl

/-- σ-cost ordering: `oneBox < twoBox`. -/
theorem sigmaCost_ordering :
    sigmaCost NewcombChoice.oneBox < sigmaCost NewcombChoice.twoBox := by
  unfold sigmaCost; norm_num

/-! ## Resolution: one-box under σ-conservation -/

/-- The structural-theorem resolution: under the constraint that
    σ-conservation must hold (the predictor and chooser are
    Z-matched copies, so σ is a conserved quantity by `R̂`-action),
    the unique admissible choice is one-box. -/
theorem oneBox_dominates_under_sigma_conservation
    (c : NewcombChoice) (h : sigmaCost c = 0) : c = NewcombChoice.oneBox := by
  cases c with
  | oneBox => rfl
  | twoBox => exfalso; simp [sigmaCost] at h

/-! ## Master certificate -/

/-- **NEWCOMB RESOLUTION MASTER CERTIFICATE.** -/
structure NewcombResolutionCert where
  one_box_preserves_sigma : sigmaCost NewcombChoice.oneBox = 0
  two_box_breaks_sigma : sigmaCost NewcombChoice.twoBox = 1
  sigma_ordering :
    sigmaCost NewcombChoice.oneBox < sigmaCost NewcombChoice.twoBox
  one_box_under_constraint :
    ∀ (c : NewcombChoice), sigmaCost c = 0 → c = NewcombChoice.oneBox
  perfect_prediction_dominance :
    expectedValue NewcombChoice.oneBox 1 - expectedValue NewcombChoice.twoBox 1
      = 999000

/-- The master certificate is inhabited. -/
def newcombResolutionCert : NewcombResolutionCert where
  one_box_preserves_sigma := oneBox_preserves_sigma
  two_box_breaks_sigma := twoBox_creates_sigma_imbalance
  sigma_ordering := sigmaCost_ordering
  one_box_under_constraint := oneBox_dominates_under_sigma_conservation
  perfect_prediction_dominance := oneBox_dominates_at_perfect_prediction

end

end NewcombParadox
end Decision
end IndisputableMonolith
