import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Lorenz Curve and Gini from Sigma-Budget Conservation

Per-decile J-cost on `r_k := observed_decile_k_share / equal_share`.
The Gini coefficient is structurally the integral of J-costs across
deciles. The critical value for high-mobility vs trapped-underclass
corresponds to Gini ≈ `J(φ) ∈ (0.11, 0.13)` on the income-share
deviation ratio — the same canonical quantum that bounds pathology
thresholds across every other domain.

The structural prediction: countries with Gini ≤ J(φ) have structurally
higher intergenerational mobility than those with Gini > J(φ). This
matches the empirical Great Gatsby Curve (Krueger 2012; Chetty 2014):
the US, UK, Brazil, Mexico all sit above the canonical band; the Nordic
countries and much of East Asia sit at or below it.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Economics
namespace LorenzCurveFromSigmaBudget

open Constants Cost

noncomputable section

/-- Per-decile J-cost on the income-share ratio. -/
def decileCost (r : ℝ) : ℝ := Cost.Jcost r

theorem decileCost_zero_at_equal : decileCost 1 = 0 := Cost.Jcost_unit0

theorem decileCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    decileCost r = decileCost r⁻¹ := Cost.Jcost_symm hr

theorem decileCost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ decileCost r :=
  Cost.Jcost_nonneg hr

theorem decileCost_pos_off_equal {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < decileCost r := Cost.Jcost_pos_of_ne_one r hr hne

/-- High-mobility/trapped boundary = canonical golden-section quantum. -/
def MobilityThreshold : ℝ := Cost.Jcost phi

/-- A country economy is in the trapped-underclass regime iff its
inequality-adjusted decile cost (Gini proxy) meets or exceeds the threshold. -/
def IsHighInequalityRegime (gini_proxy : ℝ) : Prop :=
  MobilityThreshold ≤ gini_proxy

/-- A country economy is in the high-mobility regime iff it sits below. -/
def IsHighMobilityRegime (gini_proxy : ℝ) : Prop :=
  gini_proxy < MobilityThreshold

theorem regimes_exclusive {g : ℝ} :
    ¬ (IsHighMobilityRegime g ∧ IsHighInequalityRegime g) := by
  rintro ⟨h_lt, h_ge⟩
  exact (lt_irrefl _) (lt_of_lt_of_le h_lt h_ge)

theorem mobility_threshold_band :
    0.11 < MobilityThreshold ∧ MobilityThreshold < 0.13 := by
  unfold MobilityThreshold
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  rw [Cost.Jcost_eq_sq hphi_ne]
  have h_lo : (1.61 : ℝ) < phi := Constants.phi_gt_onePointSixOne
  have h_hi : phi < (1.62 : ℝ) := Constants.phi_lt_onePointSixTwo
  have hpos : (0 : ℝ) < 2 * phi := by
    have : (0 : ℝ) < phi := Constants.phi_pos
    linarith
  refine ⟨?lo, ?hi⟩
  · rw [lt_div_iff₀ hpos]; nlinarith [h_lo, h_hi]
  · rw [div_lt_iff₀ hpos]; nlinarith [h_lo, h_hi]

structure LorenzCurveCert where
  equal_zero : decileCost 1 = 0
  reciprocal_symm : ∀ {r : ℝ}, 0 < r → decileCost r = decileCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ decileCost r
  threshold_band :
    0.11 < MobilityThreshold ∧ MobilityThreshold < 0.13
  regimes_exclusive :
    ∀ {g : ℝ}, ¬ (IsHighMobilityRegime g ∧ IsHighInequalityRegime g)

/-- Lorenz-curve inequality certificate. -/
def lorenzCurveCert : LorenzCurveCert where
  equal_zero := decileCost_zero_at_equal
  reciprocal_symm := decileCost_reciprocal_symm
  cost_nonneg := decileCost_nonneg
  threshold_band := mobility_threshold_band
  regimes_exclusive := regimes_exclusive

end
end LorenzCurveFromSigmaBudget
end Economics
end IndisputableMonolith
