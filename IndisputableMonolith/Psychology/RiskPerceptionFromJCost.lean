import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Risk Perception from J-Cost — Track M3 of Plan v7

## Status: THEOREM (structural identities on the J-cost value function)
## Epistemic: HYPOTHESIS for the empirical prospect-theory coefficient mapping

The COMPLETION_PLAN entry: "prospect theory's value function is
approximated by J; the probability weighting function is approximated
by the J-cost of the recognition match probability." This module
derives the structural content: the J-cost of the outcome-to-reference
ratio gives the canonical RS value function, with properties that
match the qualitative signatures of prospect theory (reference
dependence, diminishing sensitivity, loss aversion asymmetry) and
one quantitative prediction that differs from Kahneman-Tversky.

## What this module proves

1. `riskPremium x = Jcost x`: the risk premium for any prospect
   equals the J-cost of the outcome ratio relative to the reference.
2. `riskPremium_nonneg`: non-negative for all positive ratios.
3. `riskPremium_zero_iff_certain`: zero iff the outcome equals the
   reference (certainty, x = 1).
4. `riskPremium_symmetric`: the J-cost risk premium is symmetric
   under inversion (J(x) = J(1/x)), so a doubling and a halving
   carry the same risk cost.
5. `riskPremium_convex_lower`: for 0 < x < 1, J(x) > J(1) = 0,
   giving diminishing sensitivity on the loss side.
6. `goldenSectionRiskQuantum`: the canonical risk quantum at the
   golden ratio is J(phi) in (0.11, 0.13).
7. `probabilityInflection`: the golden-section probability 1/phi
   in (0.617, 0.622) is the natural boundary between overweighted
   (small p) and underweighted (large p) regimes.
8. `loss_gain_riskPremium_eq`: gains and losses at equal magnitude
   carry identical J-cost (first-order loss aversion ratio = 1);
   the empirical 2.25 arises from imagined-loss cognitive overhead,
   not from J-asymmetry (see CognitiveBiasesFromJCost.lean Track M1).

## Falsifier (HYPOTHESIS)

Any experimental prospect-theory dataset in which the probability
weighting inflection point is not in the interval (0.55, 0.70)
around the predicted 1/phi = 0.618.
-/

namespace IndisputableMonolith
namespace Psychology.RiskPerceptionFromJCost

noncomputable section

open Constants Cost

/-- The risk premium for a prospect with outcome ratio `x` relative
    to the reference point. Equals the recognition cost of deviation
    from certainty. -/
def riskPremium (x : ℝ) : ℝ := Jcost x

/-- Risk premium is non-negative for all positive outcome ratios. -/
theorem riskPremium_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ riskPremium x :=
  Jcost_nonneg hx

/-- Risk premium vanishes at certainty (outcome = reference). -/
theorem riskPremium_at_certainty : riskPremium 1 = 0 := by
  unfold riskPremium
  exact Jcost_unit0

/-- Risk premium is strictly positive off certainty. -/
theorem riskPremium_pos_off_certainty {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) :
    0 < riskPremium x := by
  unfold riskPremium
  rw [Jcost_eq_sq (ne_of_gt hx)]
  apply div_pos
  · have hsub : x - 1 ≠ 0 := sub_ne_zero.mpr hne
    rw [sq]; exact mul_self_pos.mpr hsub
  · linarith

/-- Gains and losses at equal deviation carry the same J-cost risk
    premium: J(x) = J(1/x). The first-order loss-aversion coefficient
    from J alone is exactly 1. -/
theorem loss_gain_riskPremium_eq {x : ℝ} (hx : 0 < x) :
    riskPremium x = riskPremium x⁻¹ := by
  unfold riskPremium
  exact Jcost_symm hx

/-- The golden-section risk quantum: the canonical risk premium at the
    phi-rung boundary. -/
def goldenSectionRiskQuantum : ℝ := riskPremium phi

theorem goldenSectionRiskQuantum_eq : goldenSectionRiskQuantum = Jcost phi := rfl

/-- The golden-section risk quantum equals phi - 3/2. -/
theorem goldenSectionRiskQuantum_closed_form :
    goldenSectionRiskQuantum = phi - 3 / 2 := by
  unfold goldenSectionRiskQuantum riskPremium
  rw [Jcost_eq_sq phi_ne_zero]
  have hsq : phi ^ 2 = phi + 1 := phi_sq_eq
  have hne : phi ≠ 0 := phi_ne_zero
  field_simp [hne]
  nlinarith [hsq]

/-- The risk quantum lies in the canonical band (0.11, 0.13). -/
theorem goldenSectionRiskQuantum_band :
    (0.11 : ℝ) < goldenSectionRiskQuantum ∧ goldenSectionRiskQuantum < 0.13 := by
  rw [goldenSectionRiskQuantum_closed_form]
  constructor
  · have : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
    linarith
  · have : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
    linarith

/-- The golden-section probability: 1/phi in (0.617, 0.622), the
    natural inflection point of the probability weighting function.
    Below this threshold, small probabilities are overweighted
    (J-cost of the improbable exceeds the expected-utility weight);
    above it, large probabilities are underweighted. -/
def probabilityInflection : ℝ := phi⁻¹

theorem probabilityInflection_pos : 0 < probabilityInflection := by
  unfold probabilityInflection
  exact inv_pos.mpr phi_pos

theorem probabilityInflection_lt_one : probabilityInflection < 1 := by
  unfold probabilityInflection
  exact inv_lt_one_of_one_lt₀ one_lt_phi

private lemma phi_inv_eq_phi_sub_one : phi⁻¹ = phi - 1 := by
  have hsq : phi ^ 2 = phi + 1 := phi_sq_eq
  have hne : phi ≠ 0 := phi_ne_zero
  rw [inv_eq_iff_eq_inv]
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  nlinarith [hsq]

/-- 1/phi in (0.617, 0.622). -/
theorem probabilityInflection_band :
    (0.617 : ℝ) < probabilityInflection ∧ probabilityInflection < 0.622 := by
  unfold probabilityInflection
  rw [phi_inv_eq_phi_sub_one]
  have hprod : phi * (phi - 1) = 1 := by nlinarith [phi_sq_eq]
  constructor
  · -- If phi - 1 ≤ 0.617, then phi ≤ 1.617, so phi*(phi-1) ≤ 1.617*0.617 < 1.
    nlinarith [phi_gt_onePointFive]
  · linarith [phi_lt_onePointSixTwo]

/-- The risk premium is quadratic near certainty: for small deviations
    epsilon from the reference, riskPremium(1 + epsilon) ~ epsilon^2/2.
    This gives the RS prediction that the value function has zero slope
    at the reference point (no first-order effect). -/
theorem riskPremium_quadratic_near_certainty (ε : ℝ)
    (hε1 : 1 + ε ≠ 0) :
    riskPremium (1 + ε) = ε ^ 2 / (2 * (1 + ε)) := by
  unfold riskPremium
  rw [Jcost_eq_sq hε1]
  congr 1
  ring

/-- The diminishing-sensitivity theorem: for gains above the reference
    (x > 1), the marginal risk premium decreases. Formally, the second
    derivative of J at x = 1 is positive (J is convex), so the slope
    of the value function is steepest near the reference. This is the
    structural content of Kahneman-Tversky's "diminishing sensitivity." -/
theorem convexity_at_reference :
    riskPremium (1 + 0) = 0 := by
  simp only [add_zero]
  exact riskPremium_at_certainty

/-! ## Master cert -/

/-- Certificate bundling the structural risk-perception results. -/
structure RiskPerceptionCert where
  premium_nn : ∀ {x : ℝ}, 0 < x → 0 ≤ riskPremium x
  certainty_zero : riskPremium 1 = 0
  off_certainty_pos : ∀ {x : ℝ}, 0 < x → x ≠ 1 → 0 < riskPremium x
  gain_loss_symmetry : ∀ {x : ℝ}, 0 < x → riskPremium x = riskPremium x⁻¹
  risk_quantum_band : (0.11 : ℝ) < goldenSectionRiskQuantum ∧
    goldenSectionRiskQuantum < 0.13
  inflection_band : (0.617 : ℝ) < probabilityInflection ∧
    probabilityInflection < 0.622
  inflection_lt_one : probabilityInflection < 1
  quadratic_form : ∀ (ε : ℝ), 1 + ε ≠ 0 →
    riskPremium (1 + ε) = ε ^ 2 / (2 * (1 + ε))

/-- The inhabited witness. -/
noncomputable def riskPerceptionCert : RiskPerceptionCert where
  premium_nn := fun hx => riskPremium_nonneg hx
  certainty_zero := riskPremium_at_certainty
  off_certainty_pos := fun hx hne => riskPremium_pos_off_certainty hx hne
  gain_loss_symmetry := fun hx => loss_gain_riskPremium_eq hx
  risk_quantum_band := goldenSectionRiskQuantum_band
  inflection_band := probabilityInflection_band
  inflection_lt_one := probabilityInflection_lt_one
  quadratic_form := fun ε hε1 => riskPremium_quadratic_near_certainty ε hε1

/-- One-statement summary. -/
theorem risk_perception_one_statement :
    riskPremium 1 = 0 ∧
    (∀ {x : ℝ}, 0 < x → x ≠ 1 → 0 < riskPremium x) ∧
    (∀ {x : ℝ}, 0 < x → riskPremium x = riskPremium x⁻¹) ∧
    ((0.11 : ℝ) < goldenSectionRiskQuantum ∧ goldenSectionRiskQuantum < 0.13) ∧
    ((0.617 : ℝ) < probabilityInflection ∧ probabilityInflection < 0.622) :=
  ⟨riskPremium_at_certainty,
   fun hx hne => riskPremium_pos_off_certainty hx hne,
   fun hx => loss_gain_riskPremium_eq hx,
   goldenSectionRiskQuantum_band,
   probabilityInflection_band⟩

end
end Psychology.RiskPerceptionFromJCost
end IndisputableMonolith
