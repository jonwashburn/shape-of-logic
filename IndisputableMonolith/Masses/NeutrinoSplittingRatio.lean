import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.NeutrinoMajoranaLadder
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# Neutrino mass-squared splitting ratio: the yardstick-free RS prediction and its falsifier

Oscillation experiments do not measure the neutral yardstick `Y`; they measure the two
mass-squared splittings `Δm²₂₁` (solar) and `Δm²₃₁` (atmospheric). Their **ratio** is the clean
observable, because the absolute scale `Y` cancels.

From the Majorana half-loop ladder (`NeutrinoMajoranaLadder`), the three neutral masses are
`mᵢ = Y · φ^((rungᵢ − 8)/2)` with rungs `[0, 11, 19]`, i.e. `m₁ : m₂ : m₃ = φ⁻⁴ : φ^{3/2} : φ^{11/2}`.
The squared masses are `Y²·φ⁻⁸, Y²·φ³, Y²·φ¹¹`. Therefore

  Δm²₂₁ / Δm²₃₁ = (φ³ − φ⁻⁸)/(φ¹¹ − φ⁻⁸) = (φ¹¹ − 1)/(φ¹⁹ − 1) ,

a pure number, independent of `Y` and of any external unit. We prove this exactly and bracket it:
`0.021 < Δm²₂₁/Δm²₃₁ < 0.0212`.

Honest empirical status (named falsifier). The measured value is
`Δm²₂₁/Δm²₃₁ ≈ 7.42×10⁻⁵ / 2.517×10⁻³ ≈ 0.0295` (NuFIT, normal ordering). The RS half-loop
prediction `≈ 0.0212` sits about 28% below it. This is the same unforced sub-leading residual the
ladder module already flags for `m₃/m₂` (predicted `φ⁴ ≈ 6.85` vs data `≈ 5.79`). So this module
does **not** claim agreement: it pins the exact parameter-free RS number and proves it is strictly
below the observed ratio, making the half-loop ladder falsifiable on a yardstick-free observable.

Falsifier: if a future neutral-sector sub-leading operator cannot raise `(φ¹¹−1)/(φ¹⁹−1)` to the
observed `≈ 0.0295`, the half-loop rung assignment `[0,11,19]` is wrong.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutrinoSplittingRatio

open Constants Real
open NeutrinoMajoranaLadder

noncomputable section

/-- Squared Majorana neutrino mass. -/
def msq (Y : ℝ) (i : Fin 3) : ℝ := (majMass Y i) ^ 2

private lemma msq_eq (Y : ℝ) (i : Fin 3) : msq Y i = Y ^ 2 * phi ^ (2 * majExp i) := by
  unfold msq majMass
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast (phi ^ majExp i) 2, ← Real.rpow_mul phi_pos.le]
  congr 1
  push_cast; ring

/-- `m₁² = Y²·φ⁻⁸` in nat-power form `Y² / φ⁸`. -/
private lemma msq0 (Y : ℝ) : msq Y 0 = Y ^ 2 / phi ^ (8 : ℕ) := by
  rw [msq_eq, show 2 * majExp 0 = -((8 : ℕ) : ℝ) from by simp [majExp]; norm_num,
      Real.rpow_neg phi_pos.le, Real.rpow_natCast]
  rw [div_eq_mul_inv]

/-- `m₂² = Y²·φ³`. -/
private lemma msq1 (Y : ℝ) : msq Y 1 = Y ^ 2 * phi ^ (3 : ℕ) := by
  rw [msq_eq, show 2 * majExp 1 = ((3 : ℕ) : ℝ) from by simp [majExp]; norm_num,
      Real.rpow_natCast]

/-- `m₃² = Y²·φ¹¹`. -/
private lemma msq2 (Y : ℝ) : msq Y 2 = Y ^ 2 * phi ^ (11 : ℕ) := by
  rw [msq_eq, show 2 * majExp 2 = ((11 : ℕ) : ℝ) from by simp [majExp]; norm_num,
      Real.rpow_natCast]

/-- The measured solar / atmospheric mass-squared splitting ratio `Δm²₂₁ / Δm²₃₁`. -/
def deltaMsqRatio (Y : ℝ) : ℝ :=
  (msq Y 1 - msq Y 0) / (msq Y 2 - msq Y 0)

/-! ## Fibonacci closed forms for the bracket -/

private lemma phi8 : phi ^ (8 : ℕ) = 21 * phi + 13 := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h3 : phi ^ 3 = 2 * phi + 1 := by rw [pow_succ, h2]; ring_nf; rw [h2]; ring_nf
  have h4 : phi ^ 4 = 3 * phi + 2 := by rw [pow_succ, h3]; ring_nf; rw [h2]; ring_nf
  have h5 : phi ^ 5 = 5 * phi + 3 := by rw [pow_succ, h4]; ring_nf; rw [h2]; ring_nf
  have h6 : phi ^ 6 = 8 * phi + 5 := by rw [pow_succ, h5]; ring_nf; rw [h2]; ring_nf
  have h7 : phi ^ 7 = 13 * phi + 8 := by rw [pow_succ, h6]; ring_nf; rw [h2]; ring_nf
  rw [pow_succ, h7]; ring_nf; rw [h2]; ring_nf

private lemma phi11 : phi ^ (11 : ℕ) = 89 * phi + 55 := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h8 : phi ^ 8 = 21 * phi + 13 := phi8
  have h9 : phi ^ 9 = 34 * phi + 21 := by rw [pow_succ, h8]; ring_nf; rw [h2]; ring_nf
  have h10 : phi ^ 10 = 55 * phi + 34 := by rw [pow_succ, h9]; ring_nf; rw [h2]; ring_nf
  rw [pow_succ, h10]; ring_nf; rw [h2]; ring_nf

private lemma phi19 : phi ^ (19 : ℕ) = 4181 * phi + 2584 := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h11 : phi ^ 11 = 89 * phi + 55 := phi11
  have h12 : phi ^ 12 = 144 * phi + 89 := by rw [pow_succ, h11]; ring_nf; rw [h2]; ring_nf
  have h13 : phi ^ 13 = 233 * phi + 144 := by rw [pow_succ, h12]; ring_nf; rw [h2]; ring_nf
  have h14 : phi ^ 14 = 377 * phi + 233 := by rw [pow_succ, h13]; ring_nf; rw [h2]; ring_nf
  have h15 : phi ^ 15 = 610 * phi + 377 := by rw [pow_succ, h14]; ring_nf; rw [h2]; ring_nf
  have h16 : phi ^ 16 = 987 * phi + 610 := by rw [pow_succ, h15]; ring_nf; rw [h2]; ring_nf
  have h17 : phi ^ 17 = 1597 * phi + 987 := by rw [pow_succ, h16]; ring_nf; rw [h2]; ring_nf
  have h18 : phi ^ 18 = 2584 * phi + 1597 := by rw [pow_succ, h17]; ring_nf; rw [h2]; ring_nf
  rw [pow_succ, h18]; ring_nf; rw [h2]; ring_nf

private lemma phi_lo : (1.618 : ℝ) < phi := by
  rw [show phi = Real.goldenRatio from rfl]; exact Numerics.phi_gt_1618

private lemma phi_hi : phi < (1.6185 : ℝ) := by
  rw [show phi = Real.goldenRatio from rfl]; exact Numerics.phi_lt_16185

private lemma phi11_pos_bounds : (199 : ℝ) < phi ^ (11 : ℕ) ∧ phi ^ (11 : ℕ) < (199.05 : ℝ) := by
  rw [phi11]; constructor <;> [nlinarith [phi_lo]; nlinarith [phi_hi]]

private lemma phi19_pos_bounds :
    (9348 : ℝ) < phi ^ (19 : ℕ) ∧ phi ^ (19 : ℕ) < (9351 : ℝ) := by
  rw [phi19]; constructor <;> [nlinarith [phi_lo]; nlinarith [phi_hi]]

/-! ## The yardstick-independent ratio -/

/-- **The splitting ratio is yardstick-independent.** For any positive neutral yardstick, the
measured ratio `Δm²₂₁/Δm²₃₁` equals the pure number `(φ¹¹ − 1)/(φ¹⁹ − 1)`. -/
theorem deltaMsqRatio_eq (Y : ℝ) (hY : Y ≠ 0) :
    deltaMsqRatio Y = (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) := by
  have hYsq : Y ^ 2 ≠ 0 := pow_ne_zero 2 hY
  have h8 : phi ^ (8 : ℕ) ≠ 0 := pow_ne_zero 8 (ne_of_gt phi_pos)
  have h8' := phi8
  have hp11 := phi11_pos_bounds.1
  have hp19 := phi19_pos_bounds.1
  have hden19 : phi ^ (19 : ℕ) - 1 ≠ 0 := by nlinarith [phi19_pos_bounds.1]
  unfold deltaMsqRatio
  rw [msq0, msq1, msq2]
  rw [div_eq_div_iff (by
        -- denominator Y²φ¹¹ − Y²/φ⁸ > 0
        have hpos : (0:ℝ) < Y ^ 2 := lt_of_le_of_ne (sq_nonneg Y) (Ne.symm hYsq)
        have : Y ^ 2 / phi ^ (8:ℕ) < Y ^ 2 * phi ^ (11:ℕ) := by
          rw [div_lt_iff₀ (by positivity)]
          have : (1:ℝ) < phi ^ (8:ℕ) * phi ^ (11:ℕ) := by nlinarith [phi8, phi11, phi_lo]
          nlinarith [hpos, this]
        intro hcontra; nlinarith [this, hcontra]) hden19]
  -- cross-multiplied polynomial identity in Y², φ⁸, φ¹¹, φ¹⁹
  have hfactor : phi ^ (19:ℕ) = phi ^ (8:ℕ) * phi ^ (11:ℕ) := by rw [← pow_add]
  have hfactor2 : phi ^ (11:ℕ) = phi ^ (8:ℕ) * phi ^ (3:ℕ) := by rw [← pow_add]
  rw [hfactor, hfactor2]
  field_simp

/-- **Numeric bracket.** The RS half-loop splitting ratio is in `(0.021, 0.0212)`. -/
theorem deltaMsqRatio_bracket :
    (0.021 : ℝ) < (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) ∧
    (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) < (0.0212 : ℝ) := by
  have h11lo := phi11_pos_bounds.1
  have h11hi := phi11_pos_bounds.2
  have h19lo := phi19_pos_bounds.1
  have h19hi := phi19_pos_bounds.2
  have hden : (0:ℝ) < phi ^ (19 : ℕ) - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hden]; nlinarith
  · rw [div_lt_iff₀ hden]; nlinarith

/-- The observed solar/atmospheric ratio (NuFIT central values, normal ordering):
`7.42×10⁻⁵ / 2.517×10⁻³`. -/
def observedRatio : ℝ := (7.42e-5 : ℝ) / (2.517e-3 : ℝ)

theorem observedRatio_gt : (0.029 : ℝ) < observedRatio := by
  unfold observedRatio; rw [lt_div_iff₀ (by norm_num)]; norm_num

/-- **The RS prediction sits strictly below the data (named falsifier).** The parameter-free
half-loop ratio is below `0.0212`, while the observed ratio exceeds `0.029` — a standing ~28%
tension on a yardstick-free observable. -/
theorem rs_ratio_below_observed :
    (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) < observedRatio := by
  have h := deltaMsqRatio_bracket.2
  have ho := observedRatio_gt
  linarith

/-- Certificate for the yardstick-free neutrino splitting ratio. -/
structure NeutrinoSplittingRatioCert where
  yardstick_independent :
    ∀ Y : ℝ, Y ≠ 0 → deltaMsqRatio Y = (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1)
  bracket :
    (0.021 : ℝ) < (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) ∧
    (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) < (0.0212 : ℝ)
  below_observed :
    (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1) < observedRatio

theorem neutrinoSplittingRatioCert_holds : NeutrinoSplittingRatioCert where
  yardstick_independent := deltaMsqRatio_eq
  bracket := deltaMsqRatio_bracket
  below_observed := rs_ratio_below_observed

end

end NeutrinoSplittingRatio
end Masses
end IndisputableMonolith
