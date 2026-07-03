import IndisputableMonolith.Constants

/-!
# D = 2 Ising Model: Onsager Exact Solution Diagnostic

The 2D Ising model is exactly solvable (Onsager, 1944). Its critical exponents
are known exactly as rational numbers. This module verifies the Onsager values
satisfy the scaling relations and tests whether the RS φ-algebraic formulas
extend to D = 2.

## Onsager exact exponents (D = 2):
  ν = 1, η = 1/4, β = 1/8, γ = 7/4, α = 0 (log divergence), δ = 15

## Diagnostic result:
  The RS leading-order formula ν₀ = φ⁻¹ does NOT reproduce ν = 1 for D = 2.
  This is expected since RS derives D = 3 as the unique physical dimension.
-/

namespace IndisputableMonolith
namespace Physics
namespace Ising2D

open Constants

noncomputable section

private lemma phi_gt_1618 : (1.618 : ℝ) < phi := by
  simp only [phi]
  have h5 : (2.236 : ℝ) < Real.sqrt 5 := by
    have h : (2.236 : ℝ) ^ 2 < 5 := by norm_num
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236)]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  linarith

/-! ## Onsager Exact Values -/

def D2 : ℝ := 2
def nu_onsager : ℝ := 1
def eta_onsager : ℝ := 1 / 4
def beta_onsager : ℝ := 1 / 8
def gamma_onsager : ℝ := 7 / 4
def delta_onsager : ℝ := 15

/-! ## Scaling Relations for Onsager Values

We verify all four scaling relations hold for the exact D = 2 exponents.
Note: α = 0 for D = 2 (logarithmic divergence), so we use α = 2 − Dν = 0.
-/

/-- Onsager α = 2 − 2·1 = 0. -/
def alpha_onsager : ℝ := 2 - D2 * nu_onsager

theorem alpha_onsager_eq : alpha_onsager = 0 := by
  unfold alpha_onsager D2 nu_onsager; ring

/-- Rushbrooke: α + 2β + γ = 0 + 2·(1/8) + 7/4 = 0 + 1/4 + 7/4 = 2. -/
theorem rushbrooke_onsager : alpha_onsager + 2 * beta_onsager + gamma_onsager = 2 := by
  unfold alpha_onsager beta_onsager gamma_onsager D2 nu_onsager; ring

/-- Fisher: γ = ν(2 − η) = 1·(2 − 1/4) = 7/4. -/
theorem fisher_onsager : gamma_onsager = nu_onsager * (2 - eta_onsager) := by
  unfold gamma_onsager nu_onsager eta_onsager; ring

/-- Hyperscaling (D = 2): Dν = 2 − α → 2·1 = 2 − 0 = 2. -/
theorem hyperscaling_onsager : D2 * nu_onsager = 2 - alpha_onsager := by
  simp only [D2, nu_onsager, alpha_onsager]; ring

/-- Widom: γ = β(δ − 1) = (1/8)·14 = 14/8 = 7/4. -/
theorem widom_onsager : gamma_onsager = beta_onsager * (delta_onsager - 1) := by
  unfold gamma_onsager beta_onsager delta_onsager; ring

/-- β from scaling: β = ν(D − 2 + η)/2 = 1·(0 + 1/4)/2 = 1/8. -/
theorem beta_from_scaling : beta_onsager = nu_onsager * (D2 - 2 + eta_onsager) / 2 := by
  unfold beta_onsager nu_onsager D2 eta_onsager; ring

/-- δ from scaling: δ = (D + 2 − η)/(D − 2 + η) = (4 − 1/4)/(0 + 1/4) = (15/4)/(1/4) = 15. -/
theorem delta_from_scaling : delta_onsager = (D2 + 2 - eta_onsager) / (D2 - 2 + eta_onsager) := by
  unfold delta_onsager D2 eta_onsager; norm_num

/-! ## RS Leading-Order Fails for D = 2

The RS leading-order ν₀ = φ⁻¹ ≈ 0.618 does not equal the Onsager ν = 1.
This is expected: RS derives D = 3 as the unique physical dimension.
The D = 2 result is a diagnostic, not a contradiction.
-/

/-- RS leading-order ν₀ = φ⁻¹ < 1 = ν_Onsager. -/
theorem rs_leading_order_below_onsager : 1 / phi < nu_onsager := by
  unfold nu_onsager
  have h := one_lt_phi
  have hp := phi_pos
  have : 1 / phi < 1 / 1 := by
    exact (one_div_lt_one_div phi_pos (by norm_num : (0:ℝ) < 1)).mpr h
  linarith

/-- The gap: ν_Onsager − ν₀ > 0.38 (a 38% discrepancy). -/
theorem onsager_rs_gap : (0.38 : ℝ) < nu_onsager - 1 / phi := by
  unfold nu_onsager
  have h_upper : 1 / phi < (0.619 : ℝ) :=
    calc 1 / phi < 1 / (1.618 : ℝ) :=
        (one_div_lt_one_div phi_pos (by norm_num : (0:ℝ) < 1.618)).mpr phi_gt_1618
      _ < (0.619 : ℝ) := by norm_num
  linarith

/-! ## Certificate -/

structure Ising2DCert where
  rushbrooke : alpha_onsager + 2 * beta_onsager + gamma_onsager = 2
  fisher : gamma_onsager = nu_onsager * (2 - eta_onsager)
  widom : gamma_onsager = beta_onsager * (delta_onsager - 1)
  hyperscaling : D2 * nu_onsager = 2 - alpha_onsager
  alpha_zero : alpha_onsager = 0
  rs_fails : 1 / phi < nu_onsager

def ising2DCert : Ising2DCert where
  rushbrooke := rushbrooke_onsager
  fisher := fisher_onsager
  widom := widom_onsager
  hyperscaling := hyperscaling_onsager
  alpha_zero := alpha_onsager_eq
  rs_fails := rs_leading_order_below_onsager

end

end Ising2D
end Physics
end IndisputableMonolith
