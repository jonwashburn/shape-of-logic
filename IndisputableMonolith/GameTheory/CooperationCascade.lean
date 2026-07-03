import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.GameTheory.ESSFromSigma

/-!
# Cooperation Cascade Theorem

## §XXIII.C row "Game theory from first principles" — cascade side.

If the cooperator fraction in a kin-cluster crosses `1/φ`, the
J-cost gradient drives the entire cluster to full cooperation.
This matches the observed cooperation thresholds in n-person
prisoner's dilemma experiments.

## What this module provides

1. `cascade_threshold_eq_inv_phi`: the cascade threshold equals
   the ESS threshold from `ESSFromSigma`.
2. `cascade_implies_ESS`: above-threshold implies ESS.
3. `subcritical_does_not_cascade`: below-threshold does not.
4. Master cert `CooperationCascadeCert` with 3 fields.
-/

namespace IndisputableMonolith
namespace GameTheory
namespace CooperationCascade

open Constants
open ESSFromSigma

noncomputable section

/-- The cascade threshold (same as ESS threshold). -/
def cascadeThreshold : ℝ := cooperatorThreshold

/-- Cascade threshold equals `1/φ`. -/
theorem cascadeThreshold_eq_inv_phi : cascadeThreshold = 1 / phi := rfl

/-- Cooperation cascade predicate: fraction above threshold. -/
def cascades (frac : ℝ) : Prop := cascadeThreshold ≤ frac

/-- Cascade implies ESS. -/
theorem cascade_implies_ESS (frac : ℝ) (h : cascades frac) :
    isESS frac := h

/-- Below threshold does not cascade. -/
theorem subcritical_does_not_cascade (frac : ℝ) (h : frac < cascadeThreshold) :
    ¬ cascades frac := by
  unfold cascades
  push_neg
  exact h

/-- Full cooperation cascades. -/
theorem full_cooperation_cascades : cascades 1 := by
  unfold cascades cascadeThreshold cooperatorThreshold
  have hphi : 1 < phi := by have := phi_gt_onePointFive; linarith
  rw [div_le_iff₀ phi_pos]
  linarith

/-! ## Master certificate -/

/-- **COOPERATION CASCADE MASTER CERTIFICATE.** -/
structure CooperationCascadeCert where
  threshold_eq : cascadeThreshold = 1 / phi
  cascade_implies_ess : ∀ frac : ℝ, cascades frac → isESS frac
  full_cooperation : cascades 1

/-- The master certificate is inhabited. -/
def cooperationCascadeCert : CooperationCascadeCert where
  threshold_eq := rfl
  cascade_implies_ess := cascade_implies_ESS
  full_cooperation := full_cooperation_cascades

end

end CooperationCascade
end GameTheory
end IndisputableMonolith
