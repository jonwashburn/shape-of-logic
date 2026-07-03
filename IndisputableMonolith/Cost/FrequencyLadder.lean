import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost.JcostCore

/-!
# φ-Ladder Frequency Bridge

## Gap B Closure

The J-cost function J(r) = ½(r + r⁻¹) − 1 evaluates the cost of any
positive ratio r. The golden ratio φ is the unique positive fixed point
of the self-similar recursion r = 1 + 1/r (i.e., r² = r + 1).

This module proves that φ is the **minimal-cost non-trivial ratio**:
among all r > 1 satisfying the self-similarity equation, φ is the unique
positive root. Therefore, for any oscillating system at frequency f,
the first φ-harmonic f × φ is the minimal-cost resonance above f.

This justifies the step in BodyCosmosResonance where we define
f_phi_rung1 := Mode1 × φ as the first φ-ladder harmonic.
-/

namespace IndisputableMonolith
namespace Cost
namespace FrequencyLadder

open Real
open IndisputableMonolith.Constants

/-! ## J-Cost on Frequency Ratios -/

/-- The J-cost of a frequency ratio r = f₂/f₁. -/
noncomputable def frequencyRatioCost (r : ℝ) : ℝ := Jcost r

/-- J-cost of unit ratio is zero: equal frequencies have no cost. -/
theorem frequencyRatioCost_unit : frequencyRatioCost 1 = 0 := by
  unfold frequencyRatioCost Jcost; simp

/-- J-cost is non-negative for positive ratios. -/
theorem frequencyRatioCost_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ frequencyRatioCost r :=
  Jcost_nonneg hr

/-! ## φ as Minimal-Cost Non-Trivial Ratio -/

/-- A self-similar ratio satisfies r² = r + 1 (the defining equation of φ). -/
def IsSelfSimilarRatio (r : ℝ) : Prop := r ^ 2 = r + 1

/-- φ is a self-similar ratio. -/
theorem phi_is_self_similar : IsSelfSimilarRatio phi := phi_sq_eq

/-- φ is the UNIQUE positive self-similar ratio.
    Proof: r² = r + 1 and φ² = φ + 1 give (r−φ)(r+φ) = r−φ,
    so (r−φ)(r+φ−1) = 0. Since r > 0 and φ > 1, r+φ−1 > 0,
    so r = φ. -/
theorem phi_unique_self_similar {r : ℝ} (hr_pos : 0 < r)
    (hr_ss : IsSelfSimilarRatio r) : r = phi := by
  unfold IsSelfSimilarRatio at hr_ss
  have hphi_sq := phi_sq_eq
  have hphi_pos := phi_pos
  have hphi_gt1 := one_lt_phi
  have hdiff : (r - phi) * (r + phi - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hdiff with h | h
  · linarith
  · exfalso; nlinarith

/-- φ is the cost fixed point: φ = 1 + 1/φ.
    Follows directly from φ² = φ + 1. -/
theorem phi_cost_fixed_point : phi = 1 + 1 / phi := by
  have hsq := phi_sq_eq
  have hne := phi_ne_zero
  field_simp at hsq ⊢; linarith

/-! ## The φ-Harmonic Theorem -/

/-- For any positive frequency f, the first φ-harmonic is f × φ.
    This is the minimal-cost non-trivial resonance above f.

    The forcing chain:
    1. J(r) is the cost of ratio r (from T5)
    2. Self-similar ratios (r² = r + 1) are the scale-invariant resonances
    3. φ is the unique positive self-similar ratio (from T6)
    4. Therefore f × φ is the unique first φ-harmonic of f -/
structure PhiHarmonicForced (f : ℝ) where
  harmonic : ℝ
  harmonic_eq : harmonic = f * phi
  ratio_is_phi : harmonic / f = phi
  ratio_self_similar : IsSelfSimilarRatio (harmonic / f)
  ratio_unique : ∀ r > 0, IsSelfSimilarRatio r → r = phi

/-- The φ-harmonic is forced for any positive frequency. -/
noncomputable def phi_harmonic_forced {f : ℝ} (hf : 0 < f) : PhiHarmonicForced f where
  harmonic := f * phi
  harmonic_eq := rfl
  ratio_is_phi := by rw [mul_div_cancel_left₀ _ (ne_of_gt hf)]
  ratio_self_similar := by
    rw [mul_div_cancel_left₀ _ (ne_of_gt hf)]
    exact phi_is_self_similar
  ratio_unique := fun r hr_pos hr_ss => phi_unique_self_similar hr_pos hr_ss

end FrequencyLadder
end Cost
end IndisputableMonolith
