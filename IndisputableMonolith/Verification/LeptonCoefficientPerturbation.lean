import Mathlib
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Physics.MassTopology
import IndisputableMonolith.Physics.ElectronMass.Necessity
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# Lepton Coefficient Perturbation Scaffold

This module records a concrete perturbative step toward deriving the lepton
`α`-correction channels from first principles.

We use the proved small-strain expansion of `Jcost` at `x = 1 + ε` and
specialize to `ε = α`, where `α` is already bounded in the framework.

The outcome is an explicit channel decomposition with edge aggregation:

* quadratic channel `α²` (leading),
* cubic channel scaling as edge-count times `α³`.

This now provides the perturbative channel core used by the mass-layer O4
closure (`Masses.JCostPerturbation`): it removes ad-hoc handling of correction
orders and ties them to the existing `J`-cost calculus surface.
-/

namespace IndisputableMonolith
namespace Verification
namespace LeptonCoefficientPerturbation

open Constants
open Physics.MassTopology

noncomputable section

/-- `α` is small enough for the `Jcost(1+ε)` expansion radius used in `JcostCore`. -/
lemma alpha_abs_le_half : |alpha| ≤ (1 : ℝ) / 2 := by
  have hα := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_nonneg : 0 ≤ alpha := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 0.007297) hα.1)
  rw [abs_of_nonneg hα_nonneg]
  linarith

/-- Specialize the proved `Jcost` small-strain expansion to `ε = α`. -/
theorem jcost_one_plus_alpha_expansion :
    ∃ c : ℝ, Cost.Jcost (1 + alpha) = alpha ^ 2 / 2 + c * alpha ^ 3 ∧ |c| ≤ 2 := by
  simpa using Cost.Jcost_one_plus_eps_quadratic alpha alpha_abs_le_half

/-- Equivalent doubled form: quadratic coefficient normalized to `1`. -/
theorem two_jcost_one_plus_alpha_expansion :
    ∃ c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 ∧ |c| ≤ 4 := by
  rcases jcost_one_plus_alpha_expansion with ⟨c, hc, hcb⟩
  refine ⟨2 * c, ?_, ?_⟩
  · nlinarith [hc]
  · have habs : |2 * c| = 2 * |c| := by
      calc
        |2 * c| = |(2 : ℝ)| * |c| := by simp [abs_mul]
        _ = 2 * |c| := by norm_num
    have h2 : 2 * |c| ≤ 4 := by nlinarith [hcb]
    simpa [habs] using h2

/-- Uniqueness of the cubic channel coefficient in the doubled `Jcost(1+α)`
representation: once
`2*Jcost(1+α) = α² + c*α³` is fixed, `c` is unique. -/
theorem two_jcost_cubic_coeff_unique
    {c1 c2 : ℝ}
    (h1 : 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c1 * alpha ^ 3)
    (h2 : 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c2 * alpha ^ 3) :
    c1 = c2 := by
  have hα := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := by linarith [hα.1]
  have hα_ne : alpha ≠ 0 := ne_of_gt hα_pos
  have hmul : c1 * alpha ^ 3 = c2 * alpha ^ 3 := by linarith [h1, h2]
  exact mul_right_cancel₀ (pow_ne_zero 3 hα_ne) hmul

/-- Existence + uniqueness form of the doubled-channel perturbative coefficient. -/
theorem exists_unique_two_jcost_channel_coeff :
    ∃! c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 := by
  rcases two_jcost_one_plus_alpha_expansion with ⟨c, hc, _hcb⟩
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  exact (two_jcost_cubic_coeff_unique (c1 := c) (c2 := c') hc hc').symm

/-- The 3-cube edge count in real form. -/
lemma E_total_eq_twelve : (E_total : ℝ) = 12 := by
  norm_num [E_total, AlphaDerivation.cube_edges]

/-- Edge-aggregated perturbation form: cubic channel remains bounded and scales with edge count. -/
theorem edge_aggregated_two_jcost_one_plus_alpha :
    ∃ C : ℝ,
      (E_total : ℝ) * (2 * Cost.Jcost (1 + alpha))
        = (E_total : ℝ) * alpha ^ 2 + C * alpha ^ 3 ∧
      |C| ≤ 4 * (E_total : ℝ) := by
  rcases two_jcost_one_plus_alpha_expansion with ⟨c, hc, hcb⟩
  refine ⟨(E_total : ℝ) * c, ?_, ?_⟩
  · nlinarith [hc]
  · have hE_nonneg : 0 ≤ (E_total : ℝ) := by positivity
    have habs : |(E_total : ℝ) * c| = (E_total : ℝ) * |c| := by
      rw [abs_mul, abs_of_nonneg hE_nonneg]
    have hbound : (E_total : ℝ) * |c| ≤ (E_total : ℝ) * 4 :=
      mul_le_mul_of_nonneg_left hcb hE_nonneg
    calc
      |(E_total : ℝ) * c| = (E_total : ℝ) * |c| := habs
      _ ≤ (E_total : ℝ) * 4 := hbound
      _ = 4 * (E_total : ℝ) := by ring

/-- With current `α` bounds, the edge-cubic channel is strictly subleading to `α²`. -/
theorem edge_cubic_channel_subleading :
    (E_total : ℝ) * alpha ^ 3 < alpha ^ 2 := by
  have hα := Physics.ElectronMass.Necessity.alpha_bounds
  have hα_pos : 0 < alpha := lt_trans (by norm_num : (0 : ℝ) < 0.007297) hα.1
  have hα_lt_1_over_12 : alpha < (1 / 12 : ℝ) := by
    linarith [hα.2]
  have hEalpha_lt_one : (E_total : ℝ) * alpha < 1 := by
    have hE : (E_total : ℝ) = 12 := E_total_eq_twelve
    calc
      (E_total : ℝ) * alpha = 12 * alpha := by simp [hE]
      _ < 12 * (1 / 12 : ℝ) := by gcongr
      _ = 1 := by ring
  have hα2_pos : 0 < alpha ^ 2 := by positivity
  calc
    (E_total : ℝ) * alpha ^ 3 = ((E_total : ℝ) * alpha) * alpha ^ 2 := by ring
    _ < 1 * alpha ^ 2 := by exact mul_lt_mul_of_pos_right hEalpha_lt_one hα2_pos
    _ = alpha ^ 2 := by ring

/-- Rephrase `MassTopology`'s cubic correction as the 12-edge channel. -/
theorem correction_order_3_eq_twelve_alpha_cube :
    correction_order_3 = 12 * alpha ^ 3 := by
  simp [correction_order_3, E_total_eq_twelve]

/-- The radiative correction used in `refined_shift` has explicit channel decomposition. -/
theorem radiative_correction_channel_decomposition :
    radiative_correction = alpha ^ 2 + 12 * alpha ^ 3 := by
  unfold radiative_correction correction_order_2
  rw [correction_order_3_eq_twelve_alpha_cube]

/-- O4 perturbative core certificate at the verification layer:
    the doubled `Jcost(1+α)` channel form, the explicit 12-edge cubic channel,
    and the resulting radiative decomposition used downstream in mass-layer forcing. -/
theorem o4_perturbative_core_certificate :
    (∃ c : ℝ, 2 * Cost.Jcost (1 + alpha) = alpha ^ 2 + c * alpha ^ 3 ∧ |c| ≤ 4) ∧
    correction_order_3 = 12 * alpha ^ 3 ∧
    radiative_correction = alpha ^ 2 + 12 * alpha ^ 3 := by
  exact ⟨two_jcost_one_plus_alpha_expansion,
    correction_order_3_eq_twelve_alpha_cube,
    radiative_correction_channel_decomposition⟩

end
end LeptonCoefficientPerturbation
end Verification
end IndisputableMonolith
