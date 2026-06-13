import Mathlib
import IndisputableMonolith.Foundation.VariationalDynamics

namespace IndisputableMonolith
namespace Foundation
namespace GroundStateDynamics

open VariationalDynamics
open InitialCondition

/-!
# Ground State from Stable Variational Dynamics

This module extracts the B4-style dynamic statement from the existing
variational ledger update rule:

- equilibria coincide with variational minimizers;
- in a zero-charge sector, the unique equilibrium is the unity configuration;
- for a one-channel ratio observable, stability therefore forces `r = 1`.
-/

/-- Any equilibrium coincides with the uniform minimizer of its conserved sector. -/
theorem equilibrium_entries_eq_uniform {N : ℕ} (hN : 0 < N)
    (c : Configuration N) (hEq : IsEquilibrium c) :
    c.entries = (uniform_config hN (log_charge c)).entries := by
  exact variational_step_unique hN c c (uniform_config hN (log_charge c))
    hEq (uniform_is_variational_successor hN c)

/-- The zero-charge equilibrium is the unity configuration. -/
theorem zero_charge_equilibrium_is_unity {N : ℕ} (hN : 0 < N)
    (c : Configuration N) (hEq : IsEquilibrium c)
    (hCharge : log_charge c = 0) :
    c.entries = (unity_config N hN).entries := by
  calc
    c.entries = (uniform_config hN (log_charge c)).entries :=
      equilibrium_entries_eq_uniform hN c hEq
    _ = (uniform_config hN 0).entries := by rw [hCharge]
    _ = (unity_config N hN).entries := by
      funext i
      simp [uniform_config, unity_config]

/-- A one-channel ratio packaged as a `Configuration 1`. -/
def ratioConfig (r : ℝ) (hr : 0 < r) : Configuration 1 where
  entries := fun _ => r
  entries_pos := fun _ => hr

@[simp] theorem ratioConfig_entry (r : ℝ) (hr : 0 < r) (i : Fin 1) :
    (ratioConfig r hr).entries i = r := rfl

@[simp] theorem ratioConfig_log_charge (r : ℝ) (hr : 0 < r) :
    log_charge (ratioConfig r hr) = Real.log r := by
  unfold log_charge ratioConfig
  simp

/-- Stable one-channel ratios in the neutral sector are forced to unity. -/
theorem stable_zero_charge_ratio_eq_one (r : ℝ) (hr : 0 < r)
    (hEq : IsEquilibrium (ratioConfig r hr))
    (hCharge : log_charge (ratioConfig r hr) = 0) :
    r = 1 := by
  have hEntries :
      (ratioConfig r hr).entries = (unity_config 1 (by norm_num)).entries :=
    zero_charge_equilibrium_is_unity (N := 1) (by norm_num) (ratioConfig r hr) hEq hCharge
  have h0 := congrFun hEntries ⟨0, by simp⟩
  simpa [ratioConfig, unity_config] using h0

end GroundStateDynamics
end Foundation
end IndisputableMonolith
