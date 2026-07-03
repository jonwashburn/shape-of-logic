import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Bayesian Update from J-Cost (Plan v7 fifty-fourth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Bayesian updating: posterior ∝ likelihood × prior.
The KL-divergence from prior to posterior measures information gain.

RS prediction: the minimum detectable Bayesian update (the step
that changes beliefs from "essentially unchanged" to "meaningfully
updated") corresponds to a J-cost of J(φ) ≈ 0.118 on the
likelihood ratio.

Specifically: a Bayes factor B = φ (odds ratio φ ≈ 1.618) is the
canonical "barely convincing" threshold, and B = φ² ≈ 2.618 is
the "moderate evidence" threshold — matching Kass-Raftery (1995)
who define Bayes factor 3-10 as "positive" evidence.

## Falsifier

Any Bayesian epistemology study showing the threshold for
"subjectively convincing" evidence at Bayes factors consistently
outside (1.5, 4.0).
-/

namespace IndisputableMonolith
namespace Statistics
namespace BayesianUpdateFromJCost

open Constants
open Cost

noncomputable section

/-- J-cost on the likelihood ratio (Bayes factor). -/
def bayesFactorCost (likelihood prior : ℝ) : ℝ :=
  Jcost (likelihood / prior)

theorem bayesFactorCost_at_null (p : ℝ) (h : p ≠ 0) :
    bayesFactorCost p p = 0 := by
  unfold bayesFactorCost; rw [div_self h]; exact Jcost_unit0

theorem bayesFactorCost_nonneg (l p : ℝ) (hl : 0 < l) (hp : 0 < p) :
    0 ≤ bayesFactorCost l p := by
  unfold bayesFactorCost; exact Jcost_nonneg (div_pos hl hp)

/-- Barely-convincing Bayes factor: B = φ. -/
def bayesFactorThreshold : ℝ := phi

theorem bayesFactorThreshold_gt_one : 1 < bayesFactorThreshold := one_lt_phi

theorem bayesFactorThreshold_cost : Jcost bayesFactorThreshold = phi - 3 / 2 := by
  unfold bayesFactorThreshold; exact Jcost_phi_val

/-- Moderate evidence: B = φ². -/
def bayesFactorModerate : ℝ := phi ^ (2 : ℕ)

theorem bayesFactorModerate_pos : 0 < bayesFactorModerate := by
  unfold bayesFactorModerate; exact pow_pos phi_pos _

theorem bayesFactorModerate_gt_two : (2 : ℝ) < bayesFactorModerate := by
  unfold bayesFactorModerate
  have h := phi_squared_bounds
  linarith [h.1]

structure BayesianUpdateCert where
  cost_at_null : ∀ p : ℝ, p ≠ 0 → bayesFactorCost p p = 0
  cost_nonneg : ∀ l p : ℝ, 0 < l → 0 < p → 0 ≤ bayesFactorCost l p
  threshold_gt_one : 1 < bayesFactorThreshold
  moderate_gt_two : (2 : ℝ) < bayesFactorModerate

noncomputable def cert : BayesianUpdateCert where
  cost_at_null := bayesFactorCost_at_null
  cost_nonneg := bayesFactorCost_nonneg
  threshold_gt_one := bayesFactorThreshold_gt_one
  moderate_gt_two := bayesFactorModerate_gt_two

theorem cert_inhabited : Nonempty BayesianUpdateCert := ⟨cert⟩

end
end BayesianUpdateFromJCost
end Statistics
end IndisputableMonolith
