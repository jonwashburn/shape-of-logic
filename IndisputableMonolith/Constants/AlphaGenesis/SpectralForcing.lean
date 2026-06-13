import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Constants.GapWeight.Projection
import IndisputableMonolith.Constants.AlphaGenesis.PatternForcing
import IndisputableMonolith.Foundation.MeasureForcing

/-!
# Alpha Genesis M6: Spectral Forcing (the sin² factor is the derivative spectrum)

**THE THEOREM.** The oscillation factor `sin²(kπ/8)` inside the gap-weight
mode weights is not a modeling choice: it is (one quarter of) the spectrum
of the one-step difference operator on the eight-tick cycle, evaluated on
the DFT-8 eigenbasis.

The chain, every link a theorem:

1. The DFT-8 modes diagonalize the cyclic shift
   (`DFT8.dft8_shift_eigenvector`).
2. The difference energy of mode k is the squared modulus of its shift
   eigenvalue minus one (`GapWeight.diffEnergy8_mode`):
   `diffEnergy8(mode k) = |ω₈ᵏ − 1|²`.
3. **The trig closure (this module):** `|ω₈ᵏ − 1|² = 4 sin²(kπ/8)`
   (`normSq_omega8_pow_sub_one`).
4. **The factorization (this module):** for every nonzero mode,
   `geometricWeight k = (diffEnergy8(mode k)/4) · latticeWeight k`
   (`geometricWeight_eq_spectrum_mul_measure`): the mode weight is the
   difference-operator spectrum times the T9 forced measure. Both factors
   are now theorem-backed; neither is an input.

Together with M2 (the pattern is forced) and M5 (the calibration is not an
input), this closes the last interior joint of the gap weight: pattern,
envelope, oscillation factor, and dressing form are all forced. The only
remaining w₈ ingredient inherited without re-derivation is the Parseval /
64-cell normalization (named in the paper's premise section).

STATUS: THEOREM (0 sorry target). No CODATA reference anywhere in this file.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis

noncomputable section

open IndisputableMonolith.Spectral
open Constants.GapWeight

/-- **The trig closure.** The squared modulus of the shift eigenvalue minus
one is four times the squared half-angle sine:
`|ω₈ᵏ − 1|² = 4 sin²(kπ/8)`. -/
theorem normSq_omega8_pow_sub_one (k : ℕ) :
    Complex.normSq (omega8 ^ k - 1) =
      4 * (Real.sin ((k : ℝ) * Real.pi / 8)) ^ 2 := by
  -- ω₈ᵏ = exp(i·θ) with θ = −kπ/4
  have hpow : omega8 ^ k = Complex.exp ((-((k : ℝ) * Real.pi / 4) : ℝ) * Complex.I) := by
    unfold omega8
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow, Complex.exp_mul_I]
  -- normSq(cos θ + sin θ·i − 1) = (cos θ − 1)² + sin² θ
  have hcos : Complex.cos ((-((k : ℝ) * Real.pi / 4) : ℝ) : ℂ) =
      ((Real.cos (-((k : ℝ) * Real.pi / 4)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]
  have hsin : Complex.sin ((-((k : ℝ) * Real.pi / 4) : ℝ) : ℂ) =
      ((Real.sin (-((k : ℝ) * Real.pi / 4)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]
  rw [hcos, hsin]
  set θ : ℝ := -((k : ℝ) * Real.pi / 4) with hθ
  have hrw : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I - 1
      = ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hrw, Complex.normSq_add_mul_I]
  -- (cos θ − 1)² + sin² θ = 2 − 2 cos θ
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h2 : (Real.cos θ - 1) ^ 2 + (Real.sin θ) ^ 2 = 2 - 2 * Real.cos θ := by
    nlinarith [hpyth]
  rw [h2]
  -- cos θ = cos(kπ/4) (cos is even)
  have hcos_even : Real.cos θ = Real.cos ((k : ℝ) * Real.pi / 4) := by
    rw [hθ, Real.cos_neg]
  rw [hcos_even]
  -- half-angle via double-angle: cos(2x) = 2cos²x − 1 and sin²x = 1 − cos²x
  have hcos2 : Real.cos (2 * ((k : ℝ) * Real.pi / 8)) =
      2 * Real.cos ((k : ℝ) * Real.pi / 8) ^ 2 - 1 :=
    Real.cos_two_mul ((k : ℝ) * Real.pi / 8)
  have harg : 2 * ((k : ℝ) * Real.pi / 8) = (k : ℝ) * Real.pi / 4 := by ring
  rw [harg] at hcos2
  have hsq : Real.sin ((k : ℝ) * Real.pi / 8) ^ 2 =
      1 - Real.cos ((k : ℝ) * Real.pi / 8) ^ 2 :=
    Real.sin_sq ((k : ℝ) * Real.pi / 8)
  nlinarith [hcos2, hsq]

/-- **The spectrum identity.** The difference energy of DFT mode k equals
`4 sin²(kπ/8)`: the oscillation factor of the gap weight is exactly one
quarter of the difference-operator spectrum. -/
theorem diffEnergy8_mode_eq_four_sin_sq (k : Fin 8) :
    diffEnergy8 (dft8_mode k) =
      4 * (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2 := by
  rw [diffEnergy8_mode k]
  exact normSq_omega8_pow_sub_one k.val

/-- **SPECTRAL FORCING.** For every nonzero mode, the gap-weight mode
weight factors as (difference-operator spectrum / 4) times the T9 forced
measure:
`geometricWeight k = (diffEnergy8(mode k)/4) · latticeWeight k`.
Both factors are theorems; neither is an input. -/
theorem geometricWeight_eq_spectrum_mul_measure (k : Fin 8) (hk : ¬ k.val = 0) :
    GapWeight.geometricWeight k =
      (diffEnergy8 (dft8_mode k) / 4) *
        Foundation.MeasureForcing.latticeWeight k.val := by
  rw [geometricWeight_eq_sin_mul_forced_measure k hk,
    diffEnergy8_mode_eq_four_sin_sq k]
  ring

/-- **SPECTRAL FORCING CERTIFICATE.** Bundles the M6 closure:
1. the trig closure `|ω₈ᵏ − 1|² = 4 sin²(kπ/8)`;
2. the spectrum identity for every DFT mode;
3. the full factorization of the mode weight into spectrum × measure. -/
structure SpectralForcingCert where
  deriving Inhabited

@[simp] def SpectralForcingCert.verified (_c : SpectralForcingCert) : Prop :=
  (∀ k : ℕ, Complex.normSq (omega8 ^ k - 1) =
    4 * (Real.sin ((k : ℝ) * Real.pi / 8)) ^ 2) ∧
  (∀ k : Fin 8, diffEnergy8 (dft8_mode k) =
    4 * (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2) ∧
  (∀ k : Fin 8, ¬ k.val = 0 →
    GapWeight.geometricWeight k =
      (diffEnergy8 (dft8_mode k) / 4) *
        Foundation.MeasureForcing.latticeWeight k.val)

theorem SpectralForcingCert.verified_any (c : SpectralForcingCert) :
    SpectralForcingCert.verified c := by
  refine ⟨normSq_omega8_pow_sub_one, diffEnergy8_mode_eq_four_sin_sq,
    geometricWeight_eq_spectrum_mul_measure⟩

end

end AlphaGenesis
end Constants
end IndisputableMonolith
