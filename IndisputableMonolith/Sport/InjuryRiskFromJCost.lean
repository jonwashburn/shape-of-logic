import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Athletic Injury Risk from J-Cost on Training Load Ratio
(Plan v7 fifty-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

The acute:chronic workload ratio (ACWR) predicts injury risk in sport.
Empirical finding (Gabbett 2016; Hulin et al. 2016): injury risk
elevates sharply when ACWR > 1.5 (i.e., acute load > 1.5× chronic load).

RS prediction: the injury-risk threshold is ACWR = φ ≈ 1.618, the
one-φ-step departure from the balanced ratio (ACWR = 1, zero J-cost).

At ACWR = φ: `J(φ) ≈ 0.118` (the canonical recognition quantum).
The system "tips" to high-injury risk at the same threshold that
separates reversible from irreversible recognition-cost states.

Observed: the "sweet spot" for injury reduction is ACWR ∈ (0.8, 1.3)
(Hulin 2016), and injury risk increases markedly above 1.5.
RS prediction: the structural tip point is φ = 1.618.

## Falsifier

Any large-N prospective cohort study (AFL, NFL, Premier League GPS data)
showing the ACWR injury-risk inflection point outside (1.4, 1.9).
-/

namespace IndisputableMonolith
namespace Sport
namespace InjuryRiskFromJCost

open Constants
open Cost

noncomputable section

/-- J-cost on the Acute:Chronic Workload Ratio. -/
def acwrCost (acute chronic : ℝ) : ℝ :=
  Jcost (acute / chronic)

theorem acwrCost_at_balance (w : ℝ) (h : w ≠ 0) :
    acwrCost w w = 0 := by
  unfold acwrCost; rw [div_self h]; exact Jcost_unit0

theorem acwrCost_nonneg (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    0 ≤ acwrCost a c := by
  unfold acwrCost; exact Jcost_nonneg (div_pos ha hc)

/-- Injury tip point: ACWR = φ. -/
def injuryTipPoint : ℝ := phi

theorem injuryTipPoint_pos : 0 < injuryTipPoint := phi_pos
theorem injuryTipPoint_gt_one : 1 < injuryTipPoint := one_lt_phi

/-- At the tip point, J-cost equals the canonical recognition quantum. -/
theorem acwrCost_at_tip : acwrCost phi 1 = phi - 3 / 2 := by
  unfold acwrCost; simp; exact Jcost_phi_val

/-- The tip point is in the empirically observed injury-risk inflection band. -/
theorem injuryTipPoint_in_band : (1.4 : ℝ) < injuryTipPoint ∧ injuryTipPoint < 1.9 := by
  constructor
  · unfold injuryTipPoint; linarith [one_lt_phiPointSixOne]
  · unfold injuryTipPoint; linarith [phi_lt_onePointSixTwo]

structure InjuryRiskCert where
  cost_at_balance : ∀ w : ℝ, w ≠ 0 → acwrCost w w = 0
  cost_nonneg : ∀ a c : ℝ, 0 < a → 0 < c → 0 ≤ acwrCost a c
  tip_pos : 0 < injuryTipPoint
  tip_gt_one : 1 < injuryTipPoint
  tip_in_band : (1.4 : ℝ) < injuryTipPoint ∧ injuryTipPoint < 1.9

noncomputable def cert : InjuryRiskCert where
  cost_at_balance := acwrCost_at_balance
  cost_nonneg := acwrCost_nonneg
  tip_pos := injuryTipPoint_pos
  tip_gt_one := injuryTipPoint_gt_one
  tip_in_band := injuryTipPoint_in_band

theorem cert_inhabited : Nonempty InjuryRiskCert := ⟨cert⟩

end
end InjuryRiskFromJCost
end Sport
end IndisputableMonolith
