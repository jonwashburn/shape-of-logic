import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

namespace RSUnits

/-- Clock-side display definition: τ_rec(display) = (2π·τ₀) / (8 ln φ). -/
@[simp] noncomputable def tau_rec_display (U : RSUnits) : ℝ :=
  (2 * Real.pi * U.tau0) / (8 * Real.log phi)

/-- Length-side (kinematic) display definition: λ_kin(display) = (2π·ℓ₀) / (8 ln φ). -/
@[simp] noncomputable def lambda_kin_display (U : RSUnits) : ℝ :=
  (2 * Real.pi * U.ell0) / (8 * Real.log phi)

/-- The K-gate ratio constant. -/
noncomputable def K_gate_ratio : ℝ := Real.pi / (4 * Real.log phi)

/-- Clock-side ratio equals K_gate_ratio. -/
@[simp] lemma tau_rec_display_ratio (U : RSUnits) (hτ : U.tau0 ≠ 0) :
  (tau_rec_display U) / U.tau0 = K_gate_ratio := by
  unfold tau_rec_display K_gate_ratio
  field_simp [hτ]
  ring

/-- Length-side ratio equals K_gate_ratio. -/
@[simp] lemma lambda_kin_display_ratio (U : RSUnits) (hℓ : U.ell0 ≠ 0) :
  (lambda_kin_display U) / U.ell0 = K_gate_ratio := by
  unfold lambda_kin_display K_gate_ratio
  field_simp [hℓ]
  ring

/-- Kinematic consistency: c · τ_rec(display) = λ_kin(display). -/
lemma lambda_kin_from_tau_rec (U : RSUnits) : U.c * tau_rec_display U = lambda_kin_display U := by
  simp only [tau_rec_display, lambda_kin_display]
  -- Goal: U.c * (2 * π * τ₀ / (8 * log φ)) = 2 * π * ℓ₀ / (8 * log φ)
  have h : U.c * U.tau0 = U.ell0 := U.c_ell0_tau0
  calc U.c * (2 * Real.pi * U.tau0 / (8 * Real.log phi))
      = (2 * Real.pi * (U.c * U.tau0)) / (8 * Real.log phi) := by ring
    _ = (2 * Real.pi * U.ell0) / (8 * Real.log phi) := by rw [h]

/-- Canonical K-gate: both route ratios equal K_gate_ratio. -/
theorem K_gate_eqK (U : RSUnits) (hτ : U.tau0 ≠ 0) (hℓ : U.ell0 ≠ 0) :
  ((tau_rec_display U) / U.tau0 = K_gate_ratio) ∧ ((lambda_kin_display U) / U.ell0 = K_gate_ratio) := by
  exact ⟨tau_rec_display_ratio U hτ, lambda_kin_display_ratio U hℓ⟩

end RSUnits
end Constants
end IndisputableMonolith
