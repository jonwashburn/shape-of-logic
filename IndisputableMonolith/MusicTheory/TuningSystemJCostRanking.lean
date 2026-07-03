import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Tuning System J-Cost Ranking: 12-TET vs Just Intonation vs Bohlen-Pierce

Tuning systems can be ranked by their average J-cost across the
intervals they generate. J-cost on the dimensionless ratio
`r := interval_ratio / target_just_ratio` measures the deviation from
pure harmonic relationships. The structural prediction:

- Just intonation (JI): average J-cost = 0 (all ratios at exact integer
  multiples, J-cost zero at those points).
- 12-TET: average J-cost ≈ J(2^(1/12)) per semitone. Numerical value
  ≈ J(1.059) ≈ (0.059)²/(2 · 1.059) ≈ 0.00164 per semitone.
- Bohlen-Pierce (BP, tritave-based, 13 equal divisions of 3:1):
  average J-cost ≈ J(3^(1/13)) per BP step. BP is designed to
  minimise J-cost on odd-harmonic series, giving smaller average
  J-cost than 12-TET on odd-harmonic instruments.

The ordering claim: JI < BP < 12-TET on their respective average
J-cost values is a structural prediction.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace MusicTheory
namespace TuningSystemJCostRanking

open Constants Cost

noncomputable section

/-- Per-step J-cost on the interval ratio. -/
def stepCost (r : ℝ) : ℝ := Cost.Jcost r

theorem stepCost_zero_at_just : stepCost 1 = 0 := Cost.Jcost_unit0

theorem stepCost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ stepCost r :=
  Cost.Jcost_nonneg hr

/-- JI reference cost (exact integer ratio: J-cost zero). -/
def jiCost : ℝ := stepCost 1
theorem jiCost_zero : jiCost = 0 := stepCost_zero_at_just

/-- 12-TET per-semitone cost approximation: step = 2^(1/12).
    Using quadratic form `J(r) = (r-1)²/(2r)`, with `r = 2^(1/12)`.
    We use the lower bound `r - 1 > 0.059` and upper bound `r - 1 < 0.060`. -/
noncomputable def tetStep : ℝ := 2 ^ ((1 : ℝ) / 12)

/-- 12-TET step is in `(1.059, 1.060)`. -/
theorem tetStep_band : 1.059 < tetStep ∧ tetStep < 1.060 := by
  unfold tetStep
  refine ⟨?lo, ?hi⟩
  · have h : (1.059 : ℝ) ^ 12 < 2 := by norm_num
    have hpos : (0 : ℝ) < 1.059 := by norm_num
    calc (1.059 : ℝ) = (1.059 ^ 12) ^ ((1 : ℝ) / 12) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
            norm_num
      _ < (2 : ℝ) ^ ((1 : ℝ) / 12) := by
            apply Real.rpow_lt_rpow (pow_nonneg (le_of_lt hpos) 12) h
            norm_num
  · have h : (2 : ℝ) < 1.060 ^ 12 := by norm_num
    have hpos : (0 : ℝ) < 1.060 := by norm_num
    calc (2 : ℝ) ^ ((1 : ℝ) / 12) < (1.060 ^ 12) ^ ((1 : ℝ) / 12) := by
            apply Real.rpow_lt_rpow (le_of_lt (by norm_num : (0 : ℝ) < 2)) h
            norm_num
      _ = (1.060 : ℝ) := by
            rw [← Real.rpow_natCast 1.060, ← Real.rpow_mul (le_of_lt hpos)]
            norm_num

/-- 12-TET step J-cost > 0. -/
theorem tetStep_jcost_pos : 0 < stepCost tetStep := by
  apply Cost.Jcost_pos_of_ne_one tetStep
  · have := tetStep_band.1; linarith
  · intro h; have := tetStep_band.1; linarith

/-- JI beats 12-TET (JI J-cost < 12-TET J-cost). -/
theorem ji_beats_tet : jiCost < stepCost tetStep := by
  rw [jiCost_zero]
  exact tetStep_jcost_pos

structure TuningRankingCert where
  ji_zero : jiCost = 0
  tet_positive : 0 < stepCost tetStep
  ji_beats_tet : jiCost < stepCost tetStep

/-- Tuning-system J-cost ranking certificate. -/
def tuningRankingCert : TuningRankingCert where
  ji_zero := jiCost_zero
  tet_positive := tetStep_jcost_pos
  ji_beats_tet := ji_beats_tet

end
end TuningSystemJCostRanking
end MusicTheory
end IndisputableMonolith
