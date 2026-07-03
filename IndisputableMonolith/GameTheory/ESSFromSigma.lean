import Mathlib
import IndisputableMonolith.Constants

/-!
# Evolutionarily Stable Strategies from σ-Conservation

## §XXIII.C row "Game theory from first principles" — ESS side.

An evolutionarily stable strategy (ESS) is a strategy that, once
adopted by the majority, cannot be invaded by a rare mutant.  In
RS, ESS exists iff the cooperator fraction is at least `1/φ` in a
kin-selected population.

This is Hamilton's rule reframed: the Hamilton coefficient
`r > c/b` becomes `cooperator_fraction ≥ 1/φ`, where `c/b` is the
cost-benefit ratio in the canonical RS-native units.

## What this module provides

1. `cooperatorThreshold`: `1/φ`.
2. `isESS`: `cooperator_fraction ≥ 1/φ`.
3. `cooperatorThreshold_lt_one`: `1/φ < 1`.
4. `cooperatorThreshold_pos`: `1/φ > 0`.
5. Master cert `ESSFromSigmaCert` with 4 fields.
-/

namespace IndisputableMonolith
namespace GameTheory
namespace ESSFromSigma

open Constants

noncomputable section

/-- The cooperator-fraction threshold for ESS in a kin-selected
    population: `1/φ ≈ 0.618`. -/
def cooperatorThreshold : ℝ := 1 / phi

/-- ESS predicate: cooperator fraction is at or above the threshold. -/
def isESS (cooperator_fraction : ℝ) : Prop :=
  cooperatorThreshold ≤ cooperator_fraction

/-- The threshold is strictly less than 1. -/
theorem cooperatorThreshold_lt_one : cooperatorThreshold < 1 := by
  unfold cooperatorThreshold
  have : 1 < phi := by have := phi_gt_onePointFive; linarith
  rw [div_lt_one phi_pos]
  exact this

/-- The threshold is strictly positive. -/
theorem cooperatorThreshold_pos : 0 < cooperatorThreshold := by
  unfold cooperatorThreshold
  exact div_pos one_pos phi_pos

/-- All-cooperator strategy is an ESS. -/
theorem all_cooperator_isESS : isESS 1 :=
  le_of_lt cooperatorThreshold_lt_one

/-- Empty-cooperator strategy is not an ESS. -/
theorem no_cooperator_not_isESS : ¬ isESS 0 := by
  unfold isESS
  push_neg
  exact cooperatorThreshold_pos

/-! ## Master certificate -/

/-- **ESS FROM SIGMA MASTER CERTIFICATE.** -/
structure ESSFromSigmaCert where
  threshold_pos : 0 < cooperatorThreshold
  threshold_lt_one : cooperatorThreshold < 1
  all_coop_isESS : isESS 1
  no_coop_not_isESS : ¬ isESS 0

/-- The master certificate is inhabited. -/
def essFromSigmaCert : ESSFromSigmaCert where
  threshold_pos := cooperatorThreshold_pos
  threshold_lt_one := cooperatorThreshold_lt_one
  all_coop_isESS := all_cooperator_isESS
  no_coop_not_isESS := no_cooperator_not_isESS

end

end ESSFromSigma
end GameTheory
end IndisputableMonolith
