import Mathlib

/-!
# Recognition Stability Audit (RSA): Cayley plumbing (algebraic core)

This file is the **purely algebraic** part of the Recognition Stability Audit described in
`papers/tex/Recognition_Stability_Audit.tex`.

RSA repeatedly uses the Cayley transform that maps:

- the (closed) right half-plane `Re(z) ≥ 0`
- into the (closed) unit disk `‖·‖ ≤ 1`.

We provide:

- `cayley z = (z - 1)/(z + 1)`
- the paper-facing variant `theta J = (2J - 1)/(2J + 1)`
- the explicit inverse `invTheta ξ = ((1+ξ)/(1-ξ))/2`

These are small, local lemmas that are ideal “RL training targets”: they are self-contained
and give immediate, checkable progress in the RSA pipeline.
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open scoped Real

/-! ## Cayley: right half-plane → unit disk -/

/-- Cayley transform sending the right half-plane to the unit disk. -/
noncomputable def cayley (z : ℂ) : ℂ :=
  (z - 1) / (z + 1)

theorem normSq_add_one_sub_normSq_sub_one (z : ℂ) :
    Complex.normSq (z + 1) - Complex.normSq (z - 1) = 4 * z.re := by
  simp [Complex.normSq_apply]
  ring

/-- If `Re z ≥ 0`, then `‖cayley z‖ ≤ 1`. -/
theorem norm_cayley_le_one_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    ‖cayley z‖ ≤ 1 := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hzneg : z = (-1 : ℂ) := by
      have : z = -(1 : ℂ) := eq_neg_of_add_eq_zero_left h
      simpa using this
    have : (0 : ℝ) ≤ (-1 : ℂ).re := by simpa [hzneg] using hz
    have : (0 : ℝ) ≤ (-1 : ℝ) := by simpa using this
    nlinarith
  have hpos : 0 < Complex.normSq (z + 1) :=
    (Complex.normSq_pos).2 hz1

  have hle : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
    have : 0 ≤ Complex.normSq (z + 1) - Complex.normSq (z - 1) := by
      have : 0 ≤ 4 * z.re := by nlinarith [hz]
      simpa [normSq_add_one_sub_normSq_sub_one z] using this
    exact (sub_nonneg).1 this

  have hnSq : Complex.normSq ((z - 1) / (z + 1)) ≤ 1 := by
    have : Complex.normSq (z - 1) / Complex.normSq (z + 1) ≤ 1 :=
      (div_le_one hpos).2 hle
    simpa [Complex.normSq_div] using this
  have hsq : ‖(z - 1) / (z + 1)‖ ^ 2 ≤ 1 := by
    calc
      ‖(z - 1) / (z + 1)‖ ^ 2 = Complex.normSq ((z - 1) / (z + 1)) := by
        simpa using (Complex.sq_norm ((z - 1) / (z + 1)))
      _ ≤ 1 := hnSq
  have hw : 0 ≤ ‖(z - 1) / (z + 1)‖ := norm_nonneg _
  have : ‖(z - 1) / (z + 1)‖ ≤ 1 := by
    nlinarith [hsq, hw]
  simpa [cayley] using this

/-! ## Paper-facing `Θ(J) = (2J - 1)/(2J + 1)` -/

/-- RSA’s paper-facing Cayley transform. -/
noncomputable def theta (J : ℂ) : ℂ :=
  cayley (2 * J)

@[simp] lemma theta_eq_div (J : ℂ) :
    theta J = (2 * J - 1) / (2 * J + 1) := by
  simp [theta, cayley]

theorem norm_theta_le_one_of_re_nonneg {J : ℂ} (hJ : 0 ≤ J.re) :
    ‖theta J‖ ≤ 1 := by
  have : 0 ≤ (2 * J).re := by
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ)
  simpa [theta] using (norm_cayley_le_one_of_re_nonneg (z := 2 * J) this)

/-! ## Explicit inverse (for the “Cayley inverse” step) -/

/-- Inverse of the paper-facing Cayley transform:
`2J = (1+Ξ)/(1-Ξ)` so `J = ((1+Ξ)/(1-Ξ))/2`. -/
noncomputable def invTheta (Ξ : ℂ) : ℂ :=
  ((1 + Ξ) / (1 - Ξ)) / 2

theorem invTheta_theta {J : ℂ} (h : (2 * J + 1) ≠ 0) :
    invTheta (theta J) = J := by
  -- A direct field computation; `field_simp` uses `h` to clear the only real denominator.
  have h' : (1 - (2 * J - 1) / (2 * J + 1)) ≠ 0 := by
    -- `1 - (2J-1)/(2J+1) = 2/(2J+1)` and `2/(2J+1) ≠ 0` since `2 ≠ 0` and `2J+1 ≠ 0`.
    have : (1 - (2 * J - 1) / (2 * J + 1)) = (2 : ℂ) / (2 * J + 1) := by
      field_simp [h]
      ring
    -- Rewrite by this identity and reduce to `2/(2J+1) ≠ 0`.
    intro h0
    have : (2 : ℂ) / (2 * J + 1) = 0 := by simpa [this] using h0
    -- `a / b = 0` forces `a = 0` or `b = 0`.
    have h2 : (2 : ℂ) ≠ 0 := by
      norm_num
    have : (2 : ℂ) = 0 ∨ (2 * J + 1) = 0 := (div_eq_zero_iff).1 this
    cases this with
    | inl h20 => exact h2 h20
    | inr hb  => exact h hb

  -- Main identity.
  -- Note: we explicitly expand `theta` to avoid any `simp` unfolding surprises.
  -- `field_simp` generates a ring goal.
  simp [invTheta, theta_eq_div]
  field_simp [h, h']
  ring

theorem theta_invTheta {Ξ : ℂ} (h : Ξ ≠ 1) :
    theta (invTheta Ξ) = Ξ := by
  have h' : (1 - Ξ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  -- Direct algebra.
  simp [theta_eq_div, invTheta]
  field_simp [h']
  ring

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith
