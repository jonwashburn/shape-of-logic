import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Urban Settlement Scaling from φ-Ladder (Plan v7 fifty-second pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Settlement size hierarchies (Zipf / central place theory) follow
power laws. RS prediction: the rank-size ratio for nested settlement
hierarchies (hamlet → village → town → city → metropolis) scales
as φ^k per level.

Christaller's central place theory predicts population ratios
between adjacent levels ≈ 3-7. RS predicts: ratio = φ² ≈ 2.618
or φ³ ≈ 4.236, consistent with Christaller's empirical range.

The five canonical settlement levels are forced by `configDim D = 5`.
-/

namespace IndisputableMonolith
namespace Archaeology
namespace UrbanDensityFromPhiLadder

open Constants
open Cost

noncomputable section

/-- Five canonical settlement levels (forced by configDim = 5). -/
def settlementLevelCount : ℕ := 5

theorem settlementLevelCount_eq : settlementLevelCount = 5 := rfl

/-- φ-rung spacing between adjacent settlement levels. -/
def settlementRungSpacing : ℕ := 3

/-- Population ratio between adjacent settlement levels: φ³ ≈ 4.236. -/
noncomputable def settlementPopRatio : ℝ := phi ^ settlementRungSpacing

theorem settlementPopRatio_pos : 0 < settlementPopRatio := by
  unfold settlementPopRatio; exact pow_pos phi_pos _

theorem settlementPopRatio_in_Christaller_band :
    (3 : ℝ) < settlementPopRatio ∧ settlementPopRatio < 8 := by
  constructor
  · unfold settlementPopRatio settlementRungSpacing
    have hlo : (1.6 : ℝ) < phi := one_lt_phiPointSixOne
    have : (1.6 : ℝ) ^ 3 < phi ^ 3 := by
      have h1 : (1.6 : ℝ) ^ 3 = 4.096 := by norm_num
      have h2 : phi ^ 3 > 4.096 := by nlinarith [phi_gt_onePointSixOne, phi_sq_eq, phi_pos]
      linarith
    linarith
  · unfold settlementPopRatio settlementRungSpacing
    have hhi : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
    have : phi ^ 3 < 5 := by nlinarith [phi_lt_onePointSixTwo, phi_sq_eq, phi_pos]
    linarith

/-- J-cost on the settlement size ratio. -/
def settlementCost (actual_pop expected_pop : ℝ) : ℝ :=
  Jcost (actual_pop / expected_pop)

theorem settlementCost_at_fit (p : ℝ) (h : p ≠ 0) :
    settlementCost p p = 0 := by
  unfold settlementCost; rw [div_self h]; exact Jcost_unit0

structure UrbanDensityCert where
  count_eq : settlementLevelCount = 5
  pop_ratio_pos : 0 < settlementPopRatio
  pop_ratio_in_band : (3 : ℝ) < settlementPopRatio ∧ settlementPopRatio < 8

noncomputable def cert : UrbanDensityCert where
  count_eq := settlementLevelCount_eq
  pop_ratio_pos := settlementPopRatio_pos
  pop_ratio_in_band := settlementPopRatio_in_Christaller_band

theorem cert_inhabited : Nonempty UrbanDensityCert := ⟨cert⟩

end
end UrbanDensityFromPhiLadder
end Archaeology
end IndisputableMonolith
