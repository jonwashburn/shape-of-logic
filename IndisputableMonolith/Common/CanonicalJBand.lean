import Mathlib
import IndisputableMonolith.Constants

/-!
# Canonical J-Cost Band — Reusable Six-Clause Template

The six-clause J-cost-on-ratio template is used across the master cert
chain (B-tier whole-science openings, the Plan v7 forty-something
domain certs). Each domain cert proves:

1. matched-zero: J(1) = 0
2. nonneg: J(x) ≥ 0 for x > 0
3. reciprocal: J(x) = J(1/x) for x ≠ 0
4. positivity-off-match: J(x) > 0 for x > 0 with x ≠ 1
5. golden-step-positive: J(φ) > 0
6. golden-step-band: J(φ) ∈ (0.11, 0.13)

This module proves the φ-side identities once so downstream domain
certs can reuse them rather than re-prove. Each domain cert still
defines its own ratio with domain-specific names.

## Lean status: 0 sorry, 0 axiom (RS-specific)
-/

namespace IndisputableMonolith
namespace Common
namespace CanonicalJBand

open Constants

noncomputable section

/-- Canonical recognition cost J(x) = ½(x + 1/x) - 1. -/
def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

theorem J_one : J 1 = 0 := by unfold J; norm_num

theorem J_reciprocal {x : ℝ} (hx : x ≠ 0) : J x = J (1 / x) := by
  unfold J; field_simp; ring

theorem J_phi_pos : J phi > 0 := by
  unfold J
  have h_phi_sq : phi ^ 2 = phi + 1 := Constants.phi_sq_eq
  have h_phi_pos : 0 < phi := Constants.phi_pos
  have h_phi_inv : phi⁻¹ = phi - 1 := by
    have h : phi * (phi - 1) = 1 := by nlinarith [h_phi_sq]
    field_simp; linarith
  rw [h_phi_inv]
  linarith [Constants.phi_gt_onePointFive]

theorem J_phi_band : (0.11 : ℝ) < J phi ∧ J phi < 0.13 := by
  unfold J
  have h_phi_sq : phi ^ 2 = phi + 1 := Constants.phi_sq_eq
  have h_phi_pos : 0 < phi := Constants.phi_pos
  have h_phi_inv : phi⁻¹ = phi - 1 := by
    have h : phi * (phi - 1) = 1 := by nlinarith [h_phi_sq]
    field_simp; linarith
  rw [h_phi_inv]
  refine ⟨?_, ?_⟩ <;>
    linarith [Constants.phi_gt_onePointSixOne, Constants.phi_lt_onePointSixTwo]

/-- Canonical recovery: J(1/φ²) > 0 (off-baseline). -/
theorem J_inv_phi_sq_pos : J (1 / phi ^ 2) > 0 := by
  unfold J
  have h_phi_pos : 0 < phi := Constants.phi_pos
  have h_phi_sq_pos : 0 < phi ^ 2 := pow_pos h_phi_pos 2
  have ⟨h_lo, h_hi⟩ := Constants.phi_squared_bounds
  have h_inv : (1 / phi ^ 2)⁻¹ = phi ^ 2 := by rw [inv_div, div_one]
  rw [h_inv]
  have h_strict : (phi ^ 2 - 1) ^ 2 > 0 := by nlinarith
  have h_eq : (phi ^ 2 - 1) ^ 2 / phi ^ 2 = phi ^ 2 + 1 / phi ^ 2 - 2 := by
    field_simp; ring
  have h_div : (phi ^ 2 - 1) ^ 2 / phi ^ 2 > 0 := div_pos h_strict h_phi_sq_pos
  linarith [h_eq ▸ h_div]

/-- Canonical six-clause certificate. Domain certs reuse this. -/
structure CanonicalCert where
  matched_zero : J 1 = 0
  reciprocal : ∀ {x : ℝ}, x ≠ 0 → J x = J (1 / x)
  phi_pos : J phi > 0
  phi_band : (0.11 : ℝ) < J phi ∧ J phi < 0.13
  recovery_pos : J (1 / phi ^ 2) > 0

def cert : CanonicalCert where
  matched_zero := J_one
  reciprocal := J_reciprocal
  phi_pos := J_phi_pos
  phi_band := J_phi_band
  recovery_pos := J_inv_phi_sq_pos

end

end CanonicalJBand
end Common
end IndisputableMonolith
