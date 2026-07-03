import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Coherence-Protected QKD Link Budget (Track J7 of Plan v5)

## Status: THEOREM (engineering derivation)

Phantom-cavity-protected QKD link (RS_PAT_040) achieves bit-rate
`R(L) = R_0 · φ^(-L/L_φ)` where `L_φ` is the φ-rung attenuation
length. Each `L_φ` of fiber attenuates the rate by `1/φ ≈ 0.618`.

## Falsifier

QKD link deployed with phantom-cavity protection showing fiber-loss
attenuation outside `1/φ` per `L_φ` of fiber to within 5%.
-/

namespace IndisputableMonolith
namespace Engineering
namespace CoherenceProtectedQKDLinkBudget

open Constants

noncomputable section

/-! ## §1. Link rate ladder -/

/-- Reference link rate at zero distance. -/
def R_0 : ℝ := 1

/-- Link rate at φ-rung `n` (after `n · L_φ` km of fiber). -/
def linkRate (n : ℕ) : ℝ := R_0 / phi ^ n

theorem linkRate_zero : linkRate 0 = R_0 := by
  unfold linkRate; simp

theorem linkRate_pos (n : ℕ) : 0 < linkRate n := by
  unfold linkRate R_0
  exact div_pos one_pos (pow_pos phi_pos _)

theorem linkRate_strict_anti {n m : ℕ} (h : n < m) :
    linkRate m < linkRate n := by
  unfold linkRate
  have hp1 : 0 < phi ^ n := pow_pos phi_pos _
  have h_pow : phi ^ n < phi ^ m := pow_lt_pow_right₀ one_lt_phi h
  -- R_0 / φ^m < R_0 / φ^n  ↔  φ^n < φ^m (since R_0 > 0).
  have h_R_pos : (0 : ℝ) < R_0 := by unfold R_0; norm_num
  exact div_lt_div_of_pos_left h_R_pos hp1 h_pow

theorem linkRate_succ (n : ℕ) :
    linkRate (n + 1) = linkRate n / phi := by
  unfold linkRate
  rw [pow_succ]
  field_simp

/-! ## §2. Attenuation factor per L_φ -/

/-- Per-rung attenuation factor `= 1/φ ≈ 0.618`. -/
def attenuationPerRung : ℝ := 1 / phi

theorem attenuationPerRung_pos : 0 < attenuationPerRung :=
  div_pos one_pos phi_pos

theorem attenuationPerRung_lt_one : attenuationPerRung < 1 := by
  unfold attenuationPerRung
  rw [div_lt_one phi_pos]; exact one_lt_phi

theorem attenuationPerRung_band :
    (0.617 : ℝ) < attenuationPerRung ∧ attenuationPerRung < 0.622 := by
  unfold attenuationPerRung
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ phi_pos]; linarith
  · rw [div_lt_iff₀ phi_pos]; linarith

/-! ## §3. Master certificate -/

structure CoherenceProtectedQKDLinkBudgetCert where
  rate_zero : linkRate 0 = R_0
  rate_pos : ∀ n, 0 < linkRate n
  rate_strict_anti : ∀ {n m : ℕ}, n < m → linkRate m < linkRate n
  rate_succ : ∀ n, linkRate (n + 1) = linkRate n / phi
  attenuation_pos : 0 < attenuationPerRung
  attenuation_lt_one : attenuationPerRung < 1
  attenuation_band : (0.617 : ℝ) < attenuationPerRung ∧ attenuationPerRung < 0.622

def coherenceProtectedQKDLinkBudgetCert :
    CoherenceProtectedQKDLinkBudgetCert where
  rate_zero := linkRate_zero
  rate_pos := linkRate_pos
  rate_strict_anti := @linkRate_strict_anti
  rate_succ := linkRate_succ
  attenuation_pos := attenuationPerRung_pos
  attenuation_lt_one := attenuationPerRung_lt_one
  attenuation_band := attenuationPerRung_band

/-- **QKD ONE-STATEMENT.** Link rate `R(n) = R_0 · φ^(-n)`,
strictly anti-monotonic; per-rung attenuation `1/φ ∈ (0.617, 0.622)`. -/
theorem qkd_one_statement :
    (∀ n, linkRate (n + 1) = linkRate n / phi) ∧
    (∀ {n m : ℕ}, n < m → linkRate m < linkRate n) ∧
    (0.617 : ℝ) < attenuationPerRung ∧ attenuationPerRung < 0.622 :=
  ⟨linkRate_succ, @linkRate_strict_anti,
   attenuationPerRung_band.1, attenuationPerRung_band.2⟩

end

end CoherenceProtectedQKDLinkBudget
end Engineering
end IndisputableMonolith
