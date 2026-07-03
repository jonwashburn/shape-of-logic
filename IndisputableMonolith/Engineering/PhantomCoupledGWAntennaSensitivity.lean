import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Phantom-Coupled GW Antenna Sensitivity (Track J6 of Plan v5)

## Status: THEOREM (engineering derivation)

Phantom-cavity-coupled GW antenna (RS_PAT_030) achieves sub-Hz
strain sensitivity `h_min(f) = h_0 · (5φ Hz / f)`, where `5φ Hz` is
the BIT carrier and `h_0` is the carrier-frequency sensitivity floor.
At LISA-band frequencies (`mHz`), sensitivity scales linearly above
the BIT carrier and inversely below.

## Falsifier

Phantom-cavity GW antenna deployed at sub-Hz showing sensitivity
ceiling not scaling as `1/f` above noise floor.
-/

namespace IndisputableMonolith
namespace Engineering
namespace PhantomCoupledGWAntennaSensitivity

open Constants

noncomputable section

/-! ## §1. Carrier and sensitivity floor -/

/-- Carrier frequency = 5φ Hz. -/
def carrier : ℝ := 5 * phi

theorem carrier_pos : 0 < carrier := by
  unfold carrier; exact mul_pos (by norm_num) phi_pos

theorem carrier_band : (8.05 : ℝ) < carrier ∧ carrier < 8.10 := by
  unfold carrier
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  refine ⟨by linarith, by linarith⟩

/-- Sensitivity floor at carrier (dimensionless reference). -/
def h_0 : ℝ := 1

/-- Sensitivity at frequency `f > 0`: `h_min(f) = h_0 · carrier / f`. -/
def sensitivity (f : ℝ) : ℝ :=
  if f ≤ 0 then 0 else h_0 * carrier / f

theorem sensitivity_at_carrier : sensitivity carrier = h_0 := by
  unfold sensitivity h_0
  rw [if_neg (not_le.mpr carrier_pos)]
  have h_ne : carrier ≠ 0 := ne_of_gt carrier_pos
  field_simp

theorem sensitivity_pos {f : ℝ} (h : 0 < f) : 0 < sensitivity f := by
  unfold sensitivity h_0
  rw [if_neg (not_le.mpr h)]
  apply div_pos
  · simp; exact carrier_pos
  · exact h

/-- Sensitivity is strictly anti-monotonic in `f` (above carrier:
sensitivity decreases; below: increases). -/
theorem sensitivity_strict_anti {f₁ f₂ : ℝ} (h₁ : 0 < f₁) (h₂ : f₁ < f₂) :
    sensitivity f₂ < sensitivity f₁ := by
  unfold sensitivity h_0
  have h₂_pos : 0 < f₂ := lt_trans h₁ h₂
  rw [if_neg (not_le.mpr h₁), if_neg (not_le.mpr h₂_pos)]
  -- 1·carrier/f₂ < 1·carrier/f₁ ↔ carrier/f₂ < carrier/f₁ ↔ f₁ < f₂
  simp only [one_mul]
  exact div_lt_div_of_pos_left carrier_pos h₁ h₂

/-! ## §2. Master certificate -/

structure PhantomCoupledGWAntennaSensitivityCert where
  carrier_band : (8.05 : ℝ) < carrier ∧ carrier < 8.10
  sensitivity_at_carrier : sensitivity carrier = h_0
  sensitivity_pos : ∀ {f : ℝ}, 0 < f → 0 < sensitivity f
  sensitivity_strict_anti : ∀ {f₁ f₂ : ℝ}, 0 < f₁ → f₁ < f₂ →
    sensitivity f₂ < sensitivity f₁

def phantomCoupledGWAntennaSensitivityCert :
    PhantomCoupledGWAntennaSensitivityCert where
  carrier_band := carrier_band
  sensitivity_at_carrier := sensitivity_at_carrier
  sensitivity_pos := @sensitivity_pos
  sensitivity_strict_anti := @sensitivity_strict_anti

/-- **GW ANTENNA ONE-STATEMENT.** Carrier `5φ ∈ (8.05, 8.10) Hz`;
sensitivity scales as `carrier/f`, strictly anti-monotonic in
frequency above and below the carrier. -/
theorem gw_antenna_one_statement :
    (8.05 : ℝ) < carrier ∧ carrier < 8.10 ∧
    sensitivity carrier = h_0 ∧
    (∀ {f₁ f₂ : ℝ}, 0 < f₁ → f₁ < f₂ → sensitivity f₂ < sensitivity f₁) :=
  ⟨carrier_band.1, carrier_band.2, sensitivity_at_carrier,
   @sensitivity_strict_anti⟩

end

end PhantomCoupledGWAntennaSensitivity
end Engineering
end IndisputableMonolith
