import Mathlib
import IndisputableMonolith.Constants

/-!
# Baryon Asymmetry η_B from Phi-Ladder — A3 Baryogenesis

RS prediction: η_B ≈ φ^(-44).

φ^44 > 10^8 (large number bound).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.BaryonAsymmetryFromPhiLadder
open Constants

def baryonRung : ℕ := 44
theorem baryonRung_gap45 : baryonRung = 44 := rfl

noncomputable def etaB_RS : ℝ := (phi ^ baryonRung)⁻¹

theorem etaB_pos : 0 < etaB_RS :=
  inv_pos.mpr (pow_pos phi_pos baryonRung)

/-- φ^8 = 21φ + 13 > 46. -/
theorem phi8_val : phi ^ 8 = 21 * phi + 13 := by
  have h2 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by nlinarith
  have h4 : phi ^ 4 = 3 * phi + 2 := by nlinarith
  nlinarith [sq_nonneg (phi^4)]

theorem phi8_gt_46 : phi ^ 8 > 46 := by
  rw [phi8_val]; linarith [phi_gt_onePointSixOne]

/-- φ^16 > 2000. -/
theorem phi16_gt_2000 : phi ^ 16 > 2000 := by
  have h : phi ^ 16 = (phi ^ 8) ^ 2 := by ring
  rw [h]; nlinarith [phi8_gt_46, sq_nonneg (phi^8 - 46)]

/-- φ^32 > 4000000. -/
theorem phi32_gt_4M : phi ^ 32 > 4000000 := by
  have h : phi ^ 32 = (phi ^ 16) ^ 2 := by ring
  rw [h]; nlinarith [phi16_gt_2000, sq_nonneg (phi^16 - 2000)]

/-- φ^44 > 10^8. -/
theorem phi44_gt_1e8 : phi ^ 44 > (10:ℝ)^8 := by
  have h12 : phi ^ 12 > 321 := by
    have h2 := phi_sq_eq
    have h3 : phi ^ 3 = 2 * phi + 1 := by nlinarith
    have h4 : phi ^ 4 = 3 * phi + 2 := by nlinarith
    have h5 : phi ^ 5 = 5 * phi + 3 := by nlinarith
    have h6 : phi ^ 6 = 8 * phi + 5 := by nlinarith
    have h8 := phi8_val
    have h12v : phi ^ 12 = phi ^ 6 * phi ^ 6 := by ring
    rw [h12v]; nlinarith [phi_gt_onePointSixOne]
  have h44 : phi ^ 44 = phi ^ 32 * phi ^ 12 := by ring
  rw [h44]
  norm_num
  nlinarith [mul_pos (by linarith [phi32_gt_4M] : (0:ℝ) < phi^32) (by linarith : (0:ℝ) < phi^12),
             phi32_gt_4M, h12]

/-- η_B < 10^(-8). -/
theorem etaB_small : etaB_RS * (10:ℝ)^8 < 1 := by
  unfold etaB_RS baryonRung
  rw [inv_mul_lt_iff₀ (pow_pos phi_pos 44)]
  simp only [mul_one]
  exact phi44_gt_1e8

structure BaryonAsymmetryCert where
  rung : baryonRung = 44
  eta_pos : 0 < etaB_RS
  phi44_large : phi ^ 44 > (10:ℝ)^8
  eta_small : etaB_RS * (10:ℝ)^8 < 1

noncomputable def baryonAsymmetryCert : BaryonAsymmetryCert where
  rung := baryonRung_gap45
  eta_pos := etaB_pos
  phi44_large := phi44_gt_1e8
  eta_small := etaB_small

end IndisputableMonolith.Cosmology.BaryonAsymmetryFromPhiLadder
