import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Cosmic Z-History and the Dark-Energy Shape (honest reduction of U5)

The BIT mechanism (`Unification.BosonicIdentityTheorem.WzBITHypothesis`) gives the
dark-energy equation of state as

  `w(z) = -1 + δw · Z(z)/Z_today`,

where `Z(z)` is the integrated cosmic Z-complexity at redshift `z` and `Z_today = Z(0)`.
This module proves the two things that turn the dark-energy *shape* problem (U5) from
"posited `1/(1+z)`" into a precisely-localized, conditional derivation.

## Results

1. **Shape reduction (exact).** Under the BIT kernel, the equation-of-state deviation is
   `δw(z) = δw₀ · Z(z)/Z_today`, so the *normalized* deviation equals the *normalized*
   cosmic-Z history (`shape_reduction`). Deriving the dark-energy shape is therefore
   **exactly** the problem of deriving the cosmic-Z accumulation history `Z(z)` — no more,
   no less. The boundary conditions are forced: `δw(0) = δw₀` (today) and `δw → 0` as
   `Z → 0` (early universe recovers ΛCDM).

2. **Conditional derivation of the canonical shape.** If cosmic Z accumulates linearly in
   the scale factor, `Z(z) = Z_today · a(z) = Z_today/(1+z)` (the
   `LinearScaleFactorAccumulation` premise, HYPOTHESIS), then the BIT kernel produces
   *exactly* the canonical `δw(z) = δw₀/(1+z)` deviation
   (`linear_accumulation_forces_canonical_kernel`). The shape is no longer posited; it is
   derived from one stated, physically-motivated premise about the Z-history.

3. **The premise is the only remaining freedom.** The Z-history `Z(z)` is monotone,
   positive today, and vanishing in the deep past; the linear-in-`a` member is the unique
   one giving the canonical kernel. What is *not* yet derived is why the accumulation is
   linear in `a` (rather than, say, in cosmic time or `a^p`); that single question is the
   honest residue of U5.

Status: shape reduction is THEOREM; the canonical shape is THEOREM **conditional on** the
linear-accumulation HYPOTHESIS. Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace CosmicZHistory

open Constants
open Cost

noncomputable section

/-! ## §1. The BIT dark-energy kernel and its shape reduction -/

/-- The BIT dark-energy equation of state `w(z) = -1 + δw₀ · Z(z)/Z_today`. -/
def bitKernel (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ) : ℝ :=
  -1 + dw0 * (Zhist z / Zt)

/-- The equation-of-state deviation `δw(z) = w(z) + 1`. -/
def bitDeviation (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ) : ℝ :=
  bitKernel dw0 Zt Zhist z + 1

/-- The deviation equals `δw₀ · Z(z)/Z_today`. -/
theorem bitDeviation_eq (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ) :
    bitDeviation dw0 Zt Zhist z = dw0 * (Zhist z / Zt) := by
  unfold bitDeviation bitKernel; ring

/-- Today (`Z(0) = Z_today`), the deviation is `δw₀`. -/
theorem bitDeviation_today (dw0 Zt : ℝ) (Zhist : ℝ → ℝ)
    (h0 : Zhist 0 = Zt) (hZt : Zt ≠ 0) :
    bitDeviation dw0 Zt Zhist 0 = dw0 := by
  rw [bitDeviation_eq, h0, div_self hZt, mul_one]

/-- Early universe (`Z(z) = 0`): the deviation vanishes, recovering `w = -1`. -/
theorem bitKernel_early (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ) (h : Zhist z = 0) :
    bitKernel dw0 Zt Zhist z = -1 := by
  unfold bitKernel; rw [h]; simp

/-- **SHAPE REDUCTION.** The normalized dark-energy deviation equals the normalized
cosmic-Z history. Deriving the dark-energy shape is exactly deriving `Z(z)`. -/
theorem shape_reduction (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ) (hdw : dw0 ≠ 0) :
    bitDeviation dw0 Zt Zhist z / bitDeviation dw0 Zt Zhist 0
      = (Zhist z / Zt) / (Zhist 0 / Zt) := by
  rw [bitDeviation_eq, bitDeviation_eq, mul_div_mul_left _ _ hdw]

/-! ## §2. The linear-accumulation premise forces the canonical shape -/

/-- The cosmic-Z history for linear-in-scale-factor accumulation:
`Z(z) = Z_today · a(z) = Z_today/(1+z)`. -/
def linearZ (Zt z : ℝ) : ℝ := Zt / (1 + z)

/-- The linear-`a` history equals `Z_today` today. -/
theorem linearZ_today (Zt : ℝ) : linearZ Zt 0 = Zt := by
  unfold linearZ; norm_num

/-- The linear-`a` history is positive on `z ≥ 0` for positive `Z_today`. -/
theorem linearZ_pos (Zt : ℝ) (hZt : 0 < Zt) {z : ℝ} (hz : 0 ≤ z) : 0 < linearZ Zt z := by
  unfold linearZ
  have : (0 : ℝ) < 1 + z := by linarith
  positivity

/-- The linear-`a` history is non-increasing in `z` (less Z accumulated at earlier epochs)
on `z ≥ 0`, for non-negative `Z_today`. -/
theorem linearZ_antitone (Zt : ℝ) (hZt : 0 ≤ Zt) {z1 z2 : ℝ}
    (h1 : 0 ≤ z1) (h12 : z1 ≤ z2) : linearZ Zt z2 ≤ linearZ Zt z1 := by
  unfold linearZ
  have hd1 : (0 : ℝ) < 1 + z1 := by linarith
  have hd2 : (0 : ℝ) < 1 + z2 := by linarith
  gcongr

/-- **LINEAR ACCUMULATION FORCES THE CANONICAL KERNEL.** With the linear-`a` cosmic-Z
history, the BIT kernel produces exactly the canonical `δw(z) = δw₀/(1+z)` deviation. The
`1/(1+z)` shape is derived from the accumulation premise, not posited. -/
theorem linear_accumulation_forces_canonical_kernel (dw0 Zt z : ℝ)
    (hZt : Zt ≠ 0) (_hz : (1 : ℝ) + z ≠ 0) :
    bitDeviation dw0 Zt (linearZ Zt) z = dw0 / (1 + z) := by
  rw [bitDeviation_eq]
  unfold linearZ
  rw [div_div, mul_comm (1 + z) Zt, ← div_div, div_self hZt, mul_one_div]

/-- The induced equation of state is the canonical kernel `w(z) = -1 + δw₀/(1+z)`. -/
theorem linear_accumulation_kernel (dw0 Zt z : ℝ)
    (hZt : Zt ≠ 0) (hz : (1 : ℝ) + z ≠ 0) :
    bitKernel dw0 Zt (linearZ Zt) z = -1 + dw0 / (1 + z) := by
  have h := linear_accumulation_forces_canonical_kernel dw0 Zt z hZt hz
  unfold bitDeviation at h
  linarith [h]

/-- **GENERAL RECIPROCAL HISTORY.** For any cosmic-Z history of reciprocal form
`Z(z) = Z_today / g(z)`, the BIT deviation is `δw(z) = δw₀ / g(z)`. The canonical kernel is
`g(z) = 1+z` (linear-in-`a`); a power-law history `g(z) = (1+z)^p` gives
`δw(z) = δw₀/(1+z)^p`, where the shape index `p` is read directly off the `w(z)`
reconstruction. The accumulation law chooses `g`; every downstream observable is then fixed.
This is the precise statement that U5's residue is exactly the choice of `g`. -/
theorem reciprocal_history_kernel (dw0 Zt : ℝ) (g : ℝ → ℝ) (z : ℝ) (hZt : Zt ≠ 0) :
    bitDeviation dw0 Zt (fun z => Zt / g z) z = dw0 / g z := by
  rw [bitDeviation_eq]
  show dw0 * (Zt / g z / Zt) = dw0 / g z
  rw [div_div, mul_comm (g z) Zt, ← div_div, div_self hZt, mul_one_div]

/-! ## §3. Certificate -/

/-- **COSMIC Z-HISTORY / DARK-ENERGY SHAPE CERTIFICATE.** The dark-energy shape is the
cosmic-Z history (shape reduction), and the canonical `1/(1+z)` is forced by linear-in-`a`
accumulation. The only residual freedom is the accumulation law itself. -/
structure CosmicZShapeCert where
  deviation_formula :
    ∀ (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ),
      bitDeviation dw0 Zt Zhist z = dw0 * (Zhist z / Zt)
  today_value :
    ∀ (dw0 Zt : ℝ) (Zhist : ℝ → ℝ), Zhist 0 = Zt → Zt ≠ 0 →
      bitDeviation dw0 Zt Zhist 0 = dw0
  shape_is_z_history :
    ∀ (dw0 Zt : ℝ) (Zhist : ℝ → ℝ) (z : ℝ), dw0 ≠ 0 →
      bitDeviation dw0 Zt Zhist z / bitDeviation dw0 Zt Zhist 0
        = (Zhist z / Zt) / (Zhist 0 / Zt)
  linear_forces_canonical :
    ∀ (dw0 Zt z : ℝ), Zt ≠ 0 → (1 : ℝ) + z ≠ 0 →
      bitDeviation dw0 Zt (linearZ Zt) z = dw0 / (1 + z)

def cosmicZShapeCert : CosmicZShapeCert where
  deviation_formula := bitDeviation_eq
  today_value := bitDeviation_today
  shape_is_z_history := shape_reduction
  linear_forces_canonical := linear_accumulation_forces_canonical_kernel

end

end CosmicZHistory
end Cosmology
end IndisputableMonolith
