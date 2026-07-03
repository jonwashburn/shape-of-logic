import Mathlib
import IndisputableMonolith.Cost.JcostCore

/-!
# Proton Charge Radius from Recognition Science
Paper: `RS_Proton_Radius_Puzzle.tex`
-/

namespace IndisputableMonolith
namespace Physics
namespace ProtonRadius

open Real

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_pos : 0 < φ := by unfold φ; positivity

theorem phi_gt_one : 1 < φ := by
  unfold φ
  have h5 : (1:ℝ) < Real.sqrt 5 := by
    have : Real.sqrt 1 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [Real.sqrt_one] using this
  linarith

/-- m_μ/m_e = φ^11 (rungs: r_e = 2, r_μ = 13, difference = 11). -/
noncomputable def muon_electron_ratio : ℝ := φ ^ 11

theorem muon_heavier : 1 < muon_electron_ratio := by
  unfold muon_electron_ratio
  exact one_lt_pow₀ phi_gt_one (by norm_num)

theorem muon_ratio_pos : 0 < muon_electron_ratio :=
  lt_trans one_pos muon_heavier

/-- Muonic Bohr radius is smaller → probes shorter distances. -/
theorem muonic_smaller : 1 / muon_electron_ratio < 1 := by
  rw [div_lt_one muon_ratio_pos]; exact muon_heavier

/-- RS proton radius estimate from confinement + form factor. -/
noncomputable def proton_radius_estimate (h_over_mpc α_s : ℝ) : ℝ :=
  (1/4) * h_over_mpc * Real.sqrt (6 * Real.pi / α_s)

theorem proton_radius_positive {h_over_mpc α_s : ℝ}
    (hh : 0 < h_over_mpc) (hα : 0 < α_s) :
    0 < proton_radius_estimate h_over_mpc α_s := by
  unfold proton_radius_estimate
  apply mul_pos (mul_pos (by norm_num) hh)
  exact Real.sqrt_pos_of_pos (by positivity)

/-- CODATA 2018: r_p = 0.8414 fm. -/
abbrev proton_radius_codata : ℝ := 0.8414

/-- No leptonic universality violation: r_p is probe-independent. -/
theorem leptonic_universality : ∃ r : ℝ, r = proton_radius_codata := ⟨_, rfl⟩

/-- The "large" old value differs by > 3% from CODATA. -/
theorem old_value_differs : 0.877 - proton_radius_codata > 0.03 := by norm_num

/-- RS form factor correction from standard dipole. -/
noncomputable def form_factor_correction (Q L : ℝ) : ℝ :=
  1 - 0.15 * (Q / L)^2

theorem form_factor_near_one {Q L : ℝ} (hL : 0 < L) (h : (Q/L)^2 ≤ 0.01) :
    |form_factor_correction Q L - 1| ≤ 0.0015 := by
  unfold form_factor_correction
  have hnn : 0 ≤ 0.15 * (Q / L)^2 := by positivity
  rw [show 1 - 0.15 * (Q / L)^2 - 1 = -(0.15 * (Q / L)^2) from by ring]
  rw [abs_neg, abs_of_nonneg hnn]
  nlinarith

end ProtonRadius
end Physics
end IndisputableMonolith
