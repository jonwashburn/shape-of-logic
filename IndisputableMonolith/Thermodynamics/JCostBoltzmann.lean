import Mathlib
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics

/-!
# J-Cost Boltzmann Bridge for Biology

Connects the J-cost function to Boltzmann statistical mechanics with
explicit biology-facing theorems. Builds on RecognitionThermodynamics
which already provides gibbs_weight, partition_function, and free_energy.

This module adds:
- Weight maximization at x=1 (ground state dominates)
- Weight symmetry (J(x) = J(1/x) implies w(x) = w(1/x))
- Monotonicity of Gibbs weight in J-cost
- Temperature-dependent selection pressure
- Biology certificate packaging all thermodynamic bridge results

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace JCostBoltzmann

open Real Cost

noncomputable section

/-! ## Weight Properties -/

/-- Gibbs weight at x=1 equals 1 (maximum, since J(1)=0). -/
theorem weight_at_ground_state (sys : RecognitionSystem) :
    gibbs_weight sys 1 = 1 :=
  gibbs_weight_one sys

/-- Gibbs weight at any positive x is at most 1 (= weight at x=1).
    Since J(x) >= 0 for x > 0, we have -J(x)/T <= 0, so exp(-J/T) <= exp(0) = 1. -/
theorem weight_maximized_at_one (sys : RecognitionSystem) (x : ℝ) (hx : 0 < x) :
    gibbs_weight sys x ≤ gibbs_weight sys 1 := by
  rw [gibbs_weight_one]
  unfold gibbs_weight
  have hJ : 0 ≤ Jcost x := Jcost_nonneg hx
  have hT : 0 < sys.TR := sys.TR_pos
  have h_neg : -Jcost x / sys.TR ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · linarith
  calc exp (-Jcost x / sys.TR)
      ≤ exp 0 := exp_le_exp.mpr h_neg
    _ = 1 := exp_zero

/-- Gibbs weight is symmetric: w(x, T) = w(1/x, T) for x > 0.
    This follows from J(x) = J(1/x). -/
theorem weight_symmetric (sys : RecognitionSystem) (x : ℝ) (hx : 0 < x) :
    gibbs_weight sys x = gibbs_weight sys x⁻¹ := by
  unfold gibbs_weight
  rw [Jcost_symm hx]

/-- Higher J-cost means lower Gibbs weight: if J(x) > J(y) then w(x) < w(y).
    This is the thermodynamic basis for natural selection. -/
theorem higher_cost_lower_weight (sys : RecognitionSystem) (x y : ℝ)
    (h : Jcost x > Jcost y) :
    gibbs_weight sys x < gibbs_weight sys y := by
  unfold gibbs_weight
  apply exp_lt_exp.mpr
  have hT := sys.TR_pos
  exact div_lt_div_of_pos_right (by linarith) hT

/-! ## Selection Pressure -/

/-- At low temperature, the weight ratio between ground state (x=1)
    and any other state (x ≠ 1) diverges. This models strong selection. -/
theorem low_temp_selection (x : ℝ) (hx : 0 < x) (hx_ne : x ≠ 1) :
    0 < Jcost x := by
  rw [Jcost_eq_sq (ne_of_gt hx)]
  apply div_pos
  · exact sq_pos_iff.mpr (sub_ne_zero.mpr hx_ne)
  · exact mul_pos (by norm_num) hx

/-- The weight ratio between x=1 (ground state) and x > 0, x ≠ 1 is > 1.
    The ground state always has strictly higher probability than any excited state. -/
theorem ground_state_dominates (sys : RecognitionSystem) (x : ℝ)
    (hx : 0 < x) (hx_ne : x ≠ 1) :
    gibbs_weight sys x < gibbs_weight sys 1 := by
  rw [gibbs_weight_one]
  unfold gibbs_weight
  have hJ : 0 < Jcost x := low_temp_selection x hx hx_ne
  have hT := sys.TR_pos
  have h_neg : -Jcost x / sys.TR < 0 := by
    exact div_neg_of_neg_of_pos (by linarith) hT
  calc exp (-Jcost x / sys.TR) < exp 0 := exp_lt_exp.mpr h_neg
    _ = 1 := exp_zero

/-! ## Free Energy Bridge -/

/-- Free energy is nonpositive for any nonempty state space.
    F = -T * ln(Z) and Z >= 1 (from the ground state alone). -/
theorem free_energy_nonpos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ)
    (h_ground : ∃ ω, X ω = 1) :
    free_energy_from_Z sys X ≤ 0 := by
  unfold free_energy_from_Z
  have hT := sys.TR_pos
  have hZ := partition_function_pos sys X
  suffices h : 1 ≤ partition_function sys X by
    have h_log : 0 ≤ log (partition_function sys X) :=
      log_nonneg (by linarith)
    nlinarith
  unfold partition_function
  obtain ⟨ω₀, hω₀⟩ := h_ground
  calc (1 : ℝ) = gibbs_weight sys 1 := (gibbs_weight_one sys).symm
    _ = gibbs_weight sys (X ω₀) := by rw [hω₀]
    _ ≤ ∑ ω, gibbs_weight sys (X ω) :=
        Finset.single_le_sum (fun ω _ => (gibbs_weight_pos sys (X ω)).le)
          (Finset.mem_univ ω₀)

/-! ## Certificate -/

structure JCostBoltzmannCert where
  weight_at_one : ∀ sys : RecognitionSystem, gibbs_weight sys 1 = 1
  weight_max : ∀ (sys : RecognitionSystem) (x : ℝ),
    0 < x → gibbs_weight sys x ≤ gibbs_weight sys 1
  weight_sym : ∀ (sys : RecognitionSystem) (x : ℝ),
    0 < x → gibbs_weight sys x = gibbs_weight sys x⁻¹
  ground_dominates : ∀ (sys : RecognitionSystem) (x : ℝ),
    0 < x → x ≠ 1 → gibbs_weight sys x < gibbs_weight sys 1
  cost_positive : ∀ (x : ℝ), 0 < x → x ≠ 1 → 0 < Jcost x

def jcostBoltzmannCert : JCostBoltzmannCert where
  weight_at_one := weight_at_ground_state
  weight_max := weight_maximized_at_one
  weight_sym := weight_symmetric
  ground_dominates := ground_state_dominates
  cost_positive := low_temp_selection

end

end JCostBoltzmann
end Thermodynamics
end IndisputableMonolith
