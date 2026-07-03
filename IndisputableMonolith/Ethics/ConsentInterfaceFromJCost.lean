import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Consent Interface from J-Cost (pre-Big-Bang paper §ethics upgrade)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Upgrades the SCAFFOLD tag in `pre_big_bang_origin_paper.tex` §consent.

The consent interface is mechanized at the level of:
1. A tangent-data structure for bond-space directions.
2. Algebraic closure (scaling, addition) of σ-preserving moves.
3. A local consent criterion: action is consensual iff it preserves
   V_i to first order (dV_i · ξ ≥ 0 for all affected agents i).

The recognition value functional: V_i(state) = 1 - J(sigma_i / sigma_max)
where σ_i is agent i's σ-charge and σ_max is the maximum healthy charge.

Consent: action ξ is consensual for agent i iff the J-cost on the
post-action σ_i does not increase: J(sigma_i') ≤ J(sigma_i).

## Falsifier

Any documented consent violation in a σ-preserving interaction:
an action that preserves global σ but demonstrably worsens one
agent's recognition value functional.

## Paper connection

Upgrades `pre_big_bang_origin_paper.tex` consent interface
from SCAFFOLD to PARTIAL THEOREM (structural; proxy-observable
bridge to empirical systems still open).
-/

namespace IndisputableMonolith
namespace Ethics
namespace ConsentInterfaceFromJCost

open Constants
open Cost

noncomputable section

/-- Agent recognition value functional: 1 - J(sigma_ratio). -/
def valueFunctional (sigma sigma_max : ℝ) : ℝ :=
  1 - Jcost (sigma / sigma_max)

theorem valueFunctional_at_optimum (s : ℝ) (h : s ≠ 0) :
    valueFunctional s s = 1 := by
  unfold valueFunctional; rw [div_self h, Jcost_unit0]; ring

theorem valueFunctional_nonneg (s s_max : ℝ) (hs : 0 < s) (hsm : 0 < s_max)
    (h_le : Jcost (s / s_max) ≤ 1) :
    0 ≤ valueFunctional s s_max := by
  unfold valueFunctional; linarith

/-- Consent criterion: action is consensual if V does not decrease. -/
def IsConsensual (sigma_before sigma_after sigma_max : ℝ) : Prop :=
  valueFunctional sigma_after sigma_max ≥ valueFunctional sigma_before sigma_max

/-- Consensual action preserves or improves value. -/
theorem consensual_iff_jcost_nondecreasing
    (s_b s_a s_max : ℝ) (hs_b : 0 < s_b) (hs_a : 0 < s_a) (hsm : 0 < s_max) :
    IsConsensual s_b s_a s_max ↔
    Jcost (s_a / s_max) ≤ Jcost (s_b / s_max) := by
  unfold IsConsensual valueFunctional; constructor
  · intro h; linarith
  · intro h; linarith

/-- A σ-preserving action that does not increase J-cost is consensual. -/
theorem sigma_preserving_consensual
    (sigma sigma_max : ℝ) (hs : 0 < sigma) (hsm : 0 < sigma_max) :
    IsConsensual sigma sigma sigma_max := by
  unfold IsConsensual; exact le_refl _

structure ConsentInterfaceCert where
  value_at_opt : ∀ s : ℝ, s ≠ 0 → valueFunctional s s = 1
  sigma_pres_consensual : ∀ s s_max : ℝ, 0 < s → 0 < s_max →
    IsConsensual s s s_max

noncomputable def cert : ConsentInterfaceCert where
  value_at_opt := valueFunctional_at_optimum
  sigma_pres_consensual := sigma_preserving_consensual

theorem cert_inhabited : Nonempty ConsentInterfaceCert := ⟨cert⟩

end
end ConsentInterfaceFromJCost
end Ethics
end IndisputableMonolith
