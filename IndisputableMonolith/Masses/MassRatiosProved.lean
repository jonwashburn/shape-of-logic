import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.PhiForcing

/-! 
# Mass Ratios — Rigorous Proofs from φ-Ladder

This module provides calculated proofs for mass ratios derived from
the φ-ladder structure. All ratios are expressed as φ-powers.
-/

namespace IndisputableMonolith
namespace Masses
namespace MassRatiosProved

open Constants
open Real

/-! ## Section 1: Phi Power Bounds for Mass Ratios -/

/-- **CALCULATED**: φ^6 bounds for mass ratios.
    
    From φ^3 = 2φ + 1, we have φ^6 = (2φ + 1)^2.
    With 1.5 < φ < 1.62, this gives 17 < φ^6 < 18. -/
theorem phi_6_bounds_mass_ratio : (17 : ℝ) < (phi : ℝ)^(6 : ℕ) ∧ (phi : ℝ)^(6 : ℕ) < (18 : ℝ) := by
  have h1 : (phi : ℝ)^(6 : ℕ) = ((phi : ℝ)^(3 : ℕ))^2 := by ring
  rw [h1]
  have h2 : (phi : ℝ)^(3 : ℕ) = 2 * phi + 1 := by
    have hphi2 : phi^2 = phi + 1 := phi_sq_eq
    calc
      (phi : ℝ)^(3 : ℕ) = phi * phi^2 := by ring
      _ = phi * (phi + 1) := by rw [hphi2]
      _ = phi^2 + phi := by ring
      _ = (phi + 1) + phi := by rw [hphi2]
      _ = 2 * phi + 1 := by ring
  rw [h2]
  have h3 : phi > (1.5 : ℝ) := phi_gt_onePointFive
  have h4 : phi < (1.62 : ℝ) := phi_lt_onePointSixTwo
  constructor
  · nlinarith
  · nlinarith

/-! ## Section 2: Mass Ratio Structure Proofs -/

/-- **PROOF**: Mass ratio formula from rung difference.
    
    If m₁ ∝ φ^r₁ and m₂ ∝ φ^r₂, then m₂/m₁ = φ^(r₂-r₁). -/
theorem mass_ratio_from_rung_difference (r1 r2 : ℤ) (E_coh : ℝ) (hE : E_coh > 0) :
    let m1 := E_coh * (phi : ℝ)^(r1 : ℝ)
    let m2 := E_coh * (phi : ℝ)^(r2 : ℝ)
    m2 / m1 = (phi : ℝ)^((r2 - r1 : ℝ)) := by
  intro m1 m2
  have h1 : m2 / m1 = (E_coh * (phi : ℝ)^(r2 : ℝ)) / (E_coh * (phi : ℝ)^(r1 : ℝ)) := rfl
  rw [h1]
  have h2 : E_coh ≠ 0 := by linarith
  have h3 : (phi : ℝ)^(r1 : ℝ) ≠ 0 := by
    have hphi : phi > 0 := phi_pos
    have h4 : (phi : ℝ)^(r1 : ℝ) > 0 := by positivity
    linarith
  field_simp
  rw [← Real.rpow_add]
  · congr
    simp
  · exact_mod_cast phi_pos

/-! ## Section 3: Mass Ordering -/

/-- **PROOF**: Mass ordering from rung ordering.
    
    Higher rung → higher mass since φ > 1. -/
theorem mass_ordering_from_rungs (r1 r2 : ℤ) (E_coh : ℝ) (hE : E_coh > 0) (hr : r1 < r2) :
    let m1 := E_coh * (phi : ℝ)^(r1 : ℝ)
    let m2 := E_coh * (phi : ℝ)^(r2 : ℝ)
    m1 < m2 := by
  intro m1 m2
  have h1 : m1 = E_coh * (phi : ℝ)^(r1 : ℝ) := rfl
  have h2 : m2 = E_coh * (phi : ℝ)^(r2 : ℝ) := rfl
  rw [h1, h2]
  have h3 : (phi : ℝ)^(r1 : ℝ) < (phi : ℝ)^(r2 : ℝ) := by
    apply Real.rpow_lt_rpow_of_exponent_lt
    · exact_mod_cast one_lt_phi
    · exact_mod_cast hr
  nlinarith [Real.rpow_pos_of_pos phi_pos r1, Real.rpow_pos_of_pos phi_pos r2]

/-! ## Section 4: Mass Certificate -/

/-- **CERTIFICATE**: Mass ratio predictions with bounds. -/
structure MassRatioCert where
  phi_6_lower : (17 : ℝ) < (phi : ℝ)^(6 : ℕ)
  phi_6_upper : (phi : ℝ)^(6 : ℕ) < (18 : ℝ)

theorem mass_ratio_cert_exists : Nonempty MassRatioCert :=
  ⟨⟨phi_6_bounds_mass_ratio.1, phi_6_bounds_mass_ratio.2⟩⟩


end MassRatiosProved
end Masses
end IndisputableMonolith
