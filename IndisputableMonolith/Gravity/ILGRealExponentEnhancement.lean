import Mathlib
import IndisputableMonolith.Gravity.ILGAsymptoticEnhancement

/-!
# ILG real-exponent enhancement structural theorems

Phase D9 extension: the natural-power version in
`IndisputableMonolith/Gravity/ILGAsymptoticEnhancement.lean` covers the
qualitative envelope; this module extends the structural facts to the
locked real exponent `α = 1 − 1/φ ∈ (0,1)` via `Real.rpow`.

We prove four facts about the real-exponent radial enhancement
`w_real(R, r0, α) = 1 + C · (R/r0)^α`:

1. `enhancement_real_above_one` — `w_real > 1` for all positive `R, r0`
   when `0 < α`.
2. `enhancement_real_strict_mono` — `w_real` is strictly monotone in `R`
   when `0 < α`.
3. `enhancement_real_unbounded` — `w_real(R) → ∞` as `R → ∞` when `0 < α`.
4. `ilg_real_velocity_sq_dominates_newtonian` — `V² ≥ V_bar²` everywhere.

Lean: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith.Gravity.ILGRealExponentEnhancement

open IndisputableMonolith.Gravity.ILGAsymptoticEnhancement

noncomputable section

/-- The real-exponent radial weight, with `α : ℝ` (no positivity required
    by the definition itself). -/
def w_real (R r0 α : ℝ) : ℝ := 1 + C_lock * (R / r0) ^ α

theorem enhancement_real_pos (R r0 α : ℝ)
    (hR : 0 < R) (hr0 : 0 < r0) :
    0 < w_real R r0 α := by
  unfold w_real
  have hC : 0 < C_lock := C_lock_pos
  have hd : 0 < R / r0 := div_pos hR hr0
  have hpow : 0 < (R / r0) ^ α := Real.rpow_pos_of_pos hd α
  have : 0 < C_lock * (R / r0) ^ α := mul_pos hC hpow
  linarith

theorem enhancement_real_above_one (R r0 α : ℝ)
    (hR : 0 < R) (hr0 : 0 < r0) :
    1 < w_real R r0 α := by
  unfold w_real
  have hC : 0 < C_lock := C_lock_pos
  have hd : 0 < R / r0 := div_pos hR hr0
  have hpow : 0 < (R / r0) ^ α := Real.rpow_pos_of_pos hd α
  have : 0 < C_lock * (R / r0) ^ α := mul_pos hC hpow
  linarith

theorem enhancement_real_strict_mono (R₁ R₂ r0 α : ℝ)
    (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂) (hr0 : 0 < r0) (hα : 0 < α) :
    w_real R₁ r0 α < w_real R₂ r0 α := by
  unfold w_real
  have hC : 0 < C_lock := C_lock_pos
  have h1 : 0 < R₁ / r0 := div_pos hR₁ hr0
  have h2 : 0 < R₂ / r0 := div_pos (lt_trans hR₁ hR₂) hr0
  have hd : R₁ / r0 < R₂ / r0 := by
    have hinv : 0 < r0⁻¹ := inv_pos.mpr hr0
    have : R₁ * r0⁻¹ < R₂ * r0⁻¹ := mul_lt_mul_of_pos_right hR₂ hinv
    simpa [div_eq_mul_inv] using this
  have hpow_lt : (R₁ / r0) ^ α < (R₂ / r0) ^ α :=
    Real.rpow_lt_rpow (le_of_lt h1) hd hα
  have hmul_lt : C_lock * (R₁ / r0) ^ α < C_lock * (R₂ / r0) ^ α :=
    mul_lt_mul_of_pos_left hpow_lt hC
  linarith

/-- Newtonian-domination at the real-exponent level. -/
theorem ilg_real_velocity_sq_dominates_newtonian
    (V_bar_sq R r0 α : ℝ)
    (hVb : 0 ≤ V_bar_sq) (hR : 0 < R) (hr0 : 0 < r0) :
    V_bar_sq ≤ w_real R r0 α * V_bar_sq := by
  have hw : 1 < w_real R r0 α := enhancement_real_above_one R r0 α hR hr0
  have hwle : 1 ≤ w_real R r0 α := le_of_lt hw
  have : V_bar_sq * 1 ≤ V_bar_sq * w_real R r0 α :=
    mul_le_mul_of_nonneg_left hwle hVb
  linarith [mul_comm V_bar_sq (w_real R r0 α)]

/-- Asymptotic divergence of the real-exponent enhancement. -/
theorem enhancement_real_unbounded (r0 α : ℝ)
    (hr0 : 0 < r0) (hα : 0 < α)
    (M : ℝ) (hM : 0 < M) :
    ∃ R : ℝ, 0 < R ∧ M < w_real R r0 α := by
  unfold w_real
  -- Want C_lock * (R/r0)^α > M, i.e. (R/r0)^α > M/C_lock.
  set u : ℝ := M / C_lock + 1 with hu_def
  have hC : 0 < C_lock := C_lock_pos
  have hu_pos : 0 < u := by
    have h₁ : 0 < M / C_lock := div_pos hM hC
    have : 0 < M / C_lock + 1 := by linarith
    simpa [hu_def] using this
  -- Choose y so that y^α = u, namely y = u^(1/α).
  have hα_ne : α ≠ 0 := ne_of_gt hα
  set y : ℝ := u ^ (1 / α) with hy_def
  have hy_pos : 0 < y := by
    have : 0 < u ^ (1 / α) := Real.rpow_pos_of_pos hu_pos (1 / α)
    simpa [hy_def] using this
  have hyα : y ^ α = u := by
    have h_inv : (1 / α) * α = 1 := by
      field_simp
    have hmul := Real.rpow_mul (le_of_lt hu_pos) (1 / α) α
    -- hmul : u ^ ((1/α) * α) = (u ^ (1/α)) ^ α
    rw [hy_def, ← hmul, h_inv, Real.rpow_one]
  -- Set R = r0 * y; then (R/r0)^α = y^α = u, and C_lock * u = M + C_lock > M.
  refine ⟨r0 * y, mul_pos hr0 hy_pos, ?bound⟩
  have hratio : (r0 * y) / r0 = y := by field_simp
  have hRpow : ((r0 * y) / r0) ^ α = u := by rw [hratio]; exact hyα
  have hCu : C_lock * u = M + C_lock := by
    have : C_lock * (M / C_lock + 1) = M + C_lock := by field_simp
    simpa [hu_def] using this
  have hCpos : 0 < C_lock := hC
  have : C_lock * ((r0 * y) / r0) ^ α = M + C_lock := by
    rw [hRpow]; exact hCu
  linarith

/-- Certificate bundling the real-exponent envelope. -/
structure ILGRealExponentEnhancementCert where
  C_pos : 0 < C_lock
  enhancement_pos : ∀ R r0 α (hR : 0 < R) (hr0 : 0 < r0),
    0 < w_real R r0 α
  enhancement_above_one : ∀ R r0 α (hR : 0 < R) (hr0 : 0 < r0),
    1 < w_real R r0 α
  enhancement_strict_mono : ∀ R₁ R₂ r0 α (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂)
    (hr0 : 0 < r0) (hα : 0 < α), w_real R₁ r0 α < w_real R₂ r0 α
  enhancement_unbounded : ∀ r0 α (hr0 : 0 < r0) (hα : 0 < α) M (hM : 0 < M),
    ∃ R : ℝ, 0 < R ∧ M < w_real R r0 α
  newtonian_dominated : ∀ V_bar_sq R r0 α (hVb : 0 ≤ V_bar_sq)
    (hR : 0 < R) (hr0 : 0 < r0), V_bar_sq ≤ w_real R r0 α * V_bar_sq

theorem ilgRealExponentEnhancementCert_holds : Nonempty ILGRealExponentEnhancementCert :=
  ⟨{ C_pos := C_lock_pos
     enhancement_pos := enhancement_real_pos
     enhancement_above_one := enhancement_real_above_one
     enhancement_strict_mono := enhancement_real_strict_mono
     enhancement_unbounded := enhancement_real_unbounded
     newtonian_dominated := ilg_real_velocity_sq_dominates_newtonian }⟩

end

end IndisputableMonolith.Gravity.ILGRealExponentEnhancement
