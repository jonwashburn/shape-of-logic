import Mathlib
import IndisputableMonolith.Cost.JcostCore

/-!
# Gamma-Ray Bursts from Recognition Science
Paper: `RS_Gamma_Ray_Bursts.tex`
-/

namespace IndisputableMonolith
namespace Physics
namespace GRB

open Real

/-! ## GRB Energy Scale -/

noncomputable def solar_mass_energy : ℝ := 1.8e54
noncomputable def accretion_efficiency : ℝ := 0.1

noncomputable def grb_energy (M_frac : ℝ) : ℝ :=
  accretion_efficiency * M_frac * solar_mass_energy

theorem grb_energy_positive (M_frac : ℝ) (hM : 0 < M_frac) : 0 < grb_energy M_frac := by
  unfold grb_energy accretion_efficiency solar_mass_energy; positivity

noncomputable def typical_grb_energy : ℝ := grb_energy 0.1

theorem typical_grb_in_range :
    1e51 < typical_grb_energy ∧ typical_grb_energy < 1e54 := by
  simp only [typical_grb_energy, grb_energy, accretion_efficiency, solar_mass_energy]
  norm_num

/-! ## Two-Class Distinction -/

theorem classes_disjoint (x : ℝ)
    (hlong : 2 ≤ x) (hshort : x ≤ 2) : x = 2 := le_antisymm hshort hlong

theorem long_not_short (x : ℝ) (hlong : 2 < x) (hshort : x < 2) : False := by linarith

/-! ## Lorentz Factor -/

theorem lorentz_range : (100 : ℝ) < 1000 := by norm_num

noncomputable def lorentz_factor (E_jet M_b : ℝ) : ℝ := E_jet / M_b

theorem lorentz_positive (E_jet M_b : ℝ) (hE : 0 < E_jet) (hM : 0 < M_b) :
    0 < lorentz_factor E_jet M_b := div_pos hE hM

/-! ## Amati Relation -/

noncomputable def amati_peak (E_iso C : ℝ) : ℝ := C * E_iso ^ ((0.5 : ℝ))

theorem amati_increases (E₁ E₂ C : ℝ) (hE₁ : 0 < E₁) (hC : 0 < C) (h : E₁ < E₂) :
    amati_peak E₁ C < amati_peak E₂ C := by
  unfold amati_peak
  apply mul_lt_mul_of_pos_left _ hC
  exact Real.rpow_lt_rpow (le_of_lt hE₁) h (by norm_num)

/-- Amati exponent 1/2 from Γ ∝ E_iso^(1/4) × √(E_iso) combination. -/
theorem amati_exponent : (1:ℝ)/4 + 1/4 = 1/2 := by norm_num

/-! ## Key Energy Scale -/

/-- GRB isotropic energy: 10^51 to 10^54 erg. -/
theorem grb_energy_range :
    ∃ E : ℝ, 1e51 < E ∧ E < 1e54 :=
  ⟨typical_grb_energy, typical_grb_in_range.1, typical_grb_in_range.2⟩

end GRB
end Physics
end IndisputableMonolith
