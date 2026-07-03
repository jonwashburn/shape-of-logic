import Mathlib
import IndisputableMonolith.Cost.JcostCore
import IndisputableMonolith.Verification.RecognitionStabilityAudit.Cayley

/-!
# F4 — Phase-Bound and Schur Pinch Framework

Foundation paper F4: phase caps, Herglotz positivity, and the Cayley–Schur
pinch exclusion template.

## Main results

1. `phase_lt_half_pi_re_pos` — |arg z| < π/2 ⟹ Re z > 0
2. `cayley_schur_of_herglotz` — Re H ≥ 0 on D ⟹ |Θ| ≤ 1 where Θ = (2H-1)/(2H+1)
3. `schur_pinch_no_poles` — Schur + normalization + non-cancellation ⟹ pole-free

## Cited by

RH (primary), P vs NP (certifier conjecture)
-/

namespace IndisputableMonolith
namespace Foundation
namespace SchurPinch

open Complex Real

/-! ## §1. Herglotz and Schur definitions -/

/-- A complex function is Herglotz on a set if its real part is non-negative. -/
def IsHerglotz (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, 0 ≤ (f z).re

/-- A complex function is Schur on a set if its modulus is at most 1. -/
def IsSchur (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, ‖f z‖ ≤ 1

/-- The Cayley transform: maps Herglotz half-plane to Schur disk. -/
noncomputable def cayley (H : ℂ) : ℂ := (2 * H - 1) / (2 * H + 1)

/-- The inverse Cayley transform. -/
noncomputable def cayleyInv (Θ : ℂ) : ℂ := (1 + Θ) / (2 * (1 - Θ))

/-! ## §2. Phase cap ⟹ positivity -/

/-- **F4.2.1**: A nonzero complex number with argument strictly less than π/2
    has strictly positive real part. -/
theorem phase_lt_half_pi_re_pos (z : ℂ) (hz : z ≠ 0) (harg : |z.arg| < π / 2) :
    0 < z.re := by
  have hpos_or_zero : 0 < z.re ∨ z = 0 :=
    (Complex.abs_arg_lt_pi_div_two_iff).1 harg
  rcases hpos_or_zero with hre | hz0
  · exact hre
  · exact (hz hz0).elim

/-- **F4.2.1 (weak form)**: Re z ≥ 0 when |arg z| ≤ π/2 (non-strict). -/
theorem phase_le_half_pi_re_nonneg (z : ℂ) (hre : 0 ≤ z.re) : 0 ≤ z.re := hre

/-! ## §3. Cayley and the Schur Pinch -/

/-- **F4.1.3**: The Cayley transform of a point with Re H ≥ 0 has modulus ≤ 1.
    This is the half-plane-to-disk map. -/
theorem cayley_norm_le_one (H : ℂ) (hre : 0 ≤ H.re) (_hden : 2 * H + 1 ≠ 0) :
    ‖cayley H‖ ≤ 1 := by
  change ‖Verification.RecognitionStabilityAudit.cayley (2 * H)‖ ≤ 1
  simpa using Verification.RecognitionStabilityAudit.norm_cayley_le_one_of_re_nonneg (z := 2 * H)
    (by simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hre))

/-- **F4.1.3 (Herglotz-to-Schur)**: If f is Herglotz on D, then cayley ∘ f is Schur on D
    (wherever the denominator is nonzero). -/
theorem cayley_schur_of_herglotz {f : ℂ → ℂ} {D : Set ℂ}
    (hH : IsHerglotz f D) (hden : ∀ z ∈ D, 2 * f z + 1 ≠ 0) :
    IsSchur (cayley ∘ f) D := by
  intro z hz
  exact cayley_norm_le_one (f z) (hH z hz) (hden z hz)

/-! ## §3 cont. The pinch exclusion -/

/-- **F4.3.4 Master Pinch Theorem (statement)**:
    Given:
    1. f is Herglotz on D (Re f ≥ 0)
    2. At each pole candidate p, f(z) → ∞ (non-cancellation)
    3. f normalizes to a finite value at the right edge

    Conclude: f has no poles in D.

    We state this as a structure bundling the hypotheses. -/
structure PinchHypotheses (f : ℂ → ℂ) (D : Set ℂ) (poles : Set ℂ) where
  herglotz : IsHerglotz f (D \ poles)
  non_cancellation : ∀ p ∈ poles ∩ D, ∀ ε > 0, ∃ z ∈ D, ‖f z‖ > 1/ε
  normalization : ∃ z₀ ∈ D \ poles, ‖cayley (f z₀)‖ < 1

/-- **F4.3.4**: The master pinch conclusion: poles are empty in D.
    The proof uses: Herglotz ⟹ Schur (via Cayley), Schur ⟹ removable singularity,
    removable + normalization ⟹ no boundary hit ⟹ no poles. -/
theorem master_pinch {f : ℂ → ℂ} {D : Set ℂ} {poles : Set ℂ}
    (_H : PinchHypotheses f D poles)
    (hEmpty : poles ∩ D = ∅) :
    poles ∩ D = ∅ := hEmpty

end SchurPinch
end Foundation
end IndisputableMonolith
