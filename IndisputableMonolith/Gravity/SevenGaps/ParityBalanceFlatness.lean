import Mathlib
import IndisputableMonolith.Cost

/-!
# Parity-balance flatness wall (lambda_rec method applied to the bridge)

## Status: THEOREM (0 sorry). Complements `LedgerBridgeNoGo`.

`LedgerBridgeNoGo` proves that J-ratio ledger deficits are even in a
parity-covariant deformation parameter and therefore cannot match a signed
odd linear Regge response. This module records the **balance-level** form of
the same obstruction, which is what the lambda_rec method forces when run
inside the bare admissible class:

* any balance functional `Φ` that is even under global strain reversal
  `t ↦ -t` and has a **unique** global minimizer must have that minimizer
  at the flat configuration `t = 0`;
* the forced J-cost sum `∑ᵢ (cosh tᵢ - 1)` is even;
* any hinge-side cost built only from bare J-ratio / ledger observables is
  even by `Cost.Jcost_symm`;
* therefore a unique balance root in that class is flat, and cannot force a
  signed curved `LedgerToHingeBridge.bridge_assumed`.

The banked escape is already named in `LedgerBridgeNoGo` / `LedgerEnergyBridge`
(quadratic nonnegative energy) and in `StationarityBridgeClosure` (MODEL-tier
oriented source coupling that breaks evenness). This file does not reopen
those; it makes the lambda_rec-method reading kernel-checkable.

Receipt: dual-arm attack 2026-08-05 (Fable 5 committed answer; Codex
adjudication). Holdfast: W / N-route under QG.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ParityBalanceFlatness

open Classical

/-- Pointwise negation of a strain configuration. -/
def negStrain {n : ℕ} (t : Fin n → ℝ) : Fin n → ℝ := fun i => -(t i)

@[simp] theorem negStrain_negStrain {n : ℕ} (t : Fin n → ℝ) :
    negStrain (negStrain t) = t := by
  funext i; simp [negStrain]

/-- **THEOREM.** An even balance with a unique global minimizer is flat.

This is the lambda_rec-method wall inside the bare class: uniqueness plus
evenness forces `t* = -t*`, hence `t* = 0`. -/
theorem even_balance_unique_root_is_flat {n : ℕ}
    (Φ : (Fin n → ℝ) → ℝ)
    (heven : ∀ t, Φ (negStrain t) = Φ t)
    (tstar : Fin n → ℝ)
    (hmin : ∀ t, Φ tstar ≤ Φ t)
    (huniq : ∀ t, Φ t = Φ tstar → t = tstar) :
    tstar = fun _ => 0 := by
  have hneg_min : Φ (negStrain tstar) ≤ Φ tstar := by
    simpa [heven tstar] using hmin (negStrain tstar)
  have hstar_min : Φ tstar ≤ Φ (negStrain tstar) := hmin (negStrain tstar)
  have heq : Φ (negStrain tstar) = Φ tstar := le_antisymm hneg_min hstar_min
  have hneg_eq : negStrain tstar = tstar := huniq _ heq
  funext i
  have hi : -(tstar i) = tstar i := by
    have := congrArg (fun f => f i) hneg_eq
    simp [negStrain] at this
    exact this
  linarith

/-- The forced ledger-side cost on channel strains: `∑ᵢ (cosh tᵢ - 1)`.
Even under `t ↦ -t` because cosh is even. -/
noncomputable def ledCost {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∑ i, (Real.cosh (t i) - 1)

theorem ledCost_even {n : ℕ} (t : Fin n → ℝ) :
    ledCost (negStrain t) = ledCost t := by
  unfold ledCost negStrain
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.cosh_neg]

/-- Any hinge-side cost that depends on strains only through absolute values
(or any even per-channel function) is even. This is the structural form of
"Cost_hinge factors through bare J-ratio data": J(e^{t}) = cosh t - 1 is even.
-/
theorem even_channel_cost_even {n : ℕ}
    (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (t : Fin n → ℝ) :
    (∑ i, f (t i)) = ∑ i, f (negStrain t i) := by
  unfold negStrain
  refine Finset.sum_congr rfl fun i _ => (hf (t i)).symm

/-- **THEOREM.** Adding an even hinge-side cost to `ledCost` preserves evenness. -/
theorem led_plus_even_is_even {n : ℕ}
    (CostH : (Fin n → ℝ) → ℝ)
    (hH : ∀ t, CostH (negStrain t) = CostH t) (t : Fin n → ℝ) :
    ledCost (negStrain t) + CostH (negStrain t) = ledCost t + CostH t := by
  rw [ledCost_even, hH]

/-- **THEOREM (balance-level flatness wall).**
If `Φ = ledCost + CostH` with `CostH` even, and `t*` is the unique global
minimizer of `Φ`, then `t* = 0`. -/
theorem bare_balance_unique_root_is_flat {n : ℕ}
    (CostH : (Fin n → ℝ) → ℝ)
    (hH : ∀ t, CostH (negStrain t) = CostH t)
    (tstar : Fin n → ℝ)
    (hmin : ∀ t, ledCost tstar + CostH tstar ≤ ledCost t + CostH t)
    (huniq : ∀ t, ledCost t + CostH t = ledCost tstar + CostH tstar → t = tstar) :
    tstar = fun _ => 0 :=
  even_balance_unique_root_is_flat
    (fun t => ledCost t + CostH t)
    (fun t => led_plus_even_is_even CostH hH t)
    tstar hmin huniq

/-- Status: the lambda_rec method inside the bare even class derives only the
flat bridge; signed curved matching requires a premise outside that class
(oriented source / quadratic-energy retarget already named elsewhere). -/
structure ParityBalanceFlatnessStatus where
  even_unique_root_is_flat : Bool
  bare_j_cost_sum_is_even : Bool
  redirects_signed_bridge_to_energy_or_oriented_source : Bool

def parityBalanceFlatnessStatus : ParityBalanceFlatnessStatus where
  even_unique_root_is_flat := true
  bare_j_cost_sum_is_even := true
  redirects_signed_bridge_to_energy_or_oriented_source := true

theorem parityBalanceFlatnessStatus_flags :
    parityBalanceFlatnessStatus.even_unique_root_is_flat = true ∧
    parityBalanceFlatnessStatus.bare_j_cost_sum_is_even = true ∧
    parityBalanceFlatnessStatus.redirects_signed_bridge_to_energy_or_oriented_source = true :=
  ⟨rfl, rfl, rfl⟩

end ParityBalanceFlatness
end SevenGaps
end Gravity
end IndisputableMonolith
