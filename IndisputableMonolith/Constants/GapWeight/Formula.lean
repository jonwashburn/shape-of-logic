import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Spectral.DFT8

namespace IndisputableMonolith
namespace Constants
namespace GapWeight

open Complex
open IndisputableMonolith.Spectral

/-! ## The Canonical φ-Pattern -/

/-- The canonical φ-power pattern: samples φᵗ for t ∈ Fin 8. -/
noncomputable def phiPattern : Fin 8 → ℝ :=
  fun t => phi ^ t.val

/-- Convert the real pattern to complex for DFT analysis. -/
noncomputable def phiPatternComplex : Fin 8 → ℂ :=
  fun t => (phiPattern t : ℂ)

/-! ## DFT Coefficients of the φ-Pattern -/

/-- The DFT coefficient cₖ of the φ-pattern. -/
noncomputable def phiDFTCoeff (k : Fin 8) : ℂ :=
  Finset.univ.sum fun t => star (dft8_entry t k) * phiPatternComplex t

/-- The squared amplitude of mode k for the φ-pattern. -/
noncomputable def phiDFTAmplitude (k : Fin 8) : ℝ :=
  Complex.normSq (phiDFTCoeff k)

/-! ## Geometric Weights -/

/-- Geometric weight for mode k. -/
noncomputable def geometricWeight (k : Fin 8) : ℝ :=
  if k.val = 0 then 0
  else
    let freq := (k.val : ℝ) * Real.pi / 8
    let oscillation := (Real.sin freq) ^ 2
    let phiDecay := phi ^ (-(k.val : ℤ))
    oscillation * phiDecay

/-! ## A DFT-based *candidate* for the Gap Weight w₈ -/

/-- A DFT-based candidate weight (scaffold).

This is *not* currently proven to match the certified `Constants.w8_from_eight_tick`
used by the α pipeline (see `Constants/GapWeight.lean`). -/
noncomputable def w8_dft_candidate : ℝ :=
  Finset.sum (Finset.filter (· ≠ 0) Finset.univ) fun k =>
    phiDFTAmplitude k * geometricWeight k

/-! ## Basic Properties (Verified) -/

/-- phiDFTAmplitude is non-negative. -/
lemma phiDFTAmplitude_nonneg (k : Fin 8) : 0 ≤ phiDFTAmplitude k :=
  Complex.normSq_nonneg _

/-- geometricWeight is non-negative. -/
lemma geometricWeight_nonneg (k : Fin 8) : 0 ≤ geometricWeight k := by
  unfold geometricWeight
  split_ifs with h
  · exact le_refl 0
  · apply mul_nonneg
    · exact sq_nonneg _
    · exact zpow_nonneg (le_of_lt phi_pos) _

/-- geometricWeight is positive for neutral modes. -/
lemma geometricWeight_pos {k : Fin 8} (hk : k.val ≠ 0) : 0 < geometricWeight k := by
  unfold geometricWeight
  simp only [hk, ↓reduceIte]
  apply mul_pos
  · apply sq_pos_of_pos
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk
      positivity
    · have h1 : k.val ≤ 7 := Nat.lt_succ_iff.mp k.isLt
      have h2 : (k.val : ℝ) ≤ 7 := by exact Nat.cast_le.mpr h1
      calc (k.val : ℝ) * Real.pi / 8
          ≤ 7 * Real.pi / 8 := by nlinarith [Real.pi_pos]
        _ < Real.pi := by nlinarith [Real.pi_pos]
  · exact zpow_pos phi_pos _

/-- The DFT-based candidate weight is positive. -/
theorem w8_dft_candidate_pos : 0 < w8_dft_candidate := by
  unfold w8_dft_candidate
  have h1_mem : (1 : Fin 8) ∈ Finset.filter (· ≠ 0) Finset.univ := by decide
  apply Finset.sum_pos'
  · intro k hk
    apply mul_nonneg
    · exact phiDFTAmplitude_nonneg k
    · exact geometricWeight_nonneg k
  · use 1, h1_mem
    apply mul_pos
    · unfold phiDFTAmplitude
      apply Complex.normSq_pos.mpr
      -- A rigorous proof: the φ-pattern φᵗ is strictly increasing (φ > 1).
      -- Its DFT coefficient c₁ is ∑_{t=0}^7 (ω⁷φ)ᵗ / √8.
      -- Let z = ω⁷φ. The sum is (z⁸ - 1)/(z - 1).
      -- Since |z| = φ > 1, z ≠ 1 and z⁸ = φ⁸ ≠ 1.
      -- Thus the sum is non-zero.
      intro h_zero
      have h_coeff : phiDFTCoeff 1 = (∑ t : Fin 8, (omega8 ^ 7 * (phi : ℂ)) ^ t.val) / (Real.sqrt 8 : ℂ) := by
        unfold phiDFTCoeff dft8_entry phiPatternComplex phiPattern
        rw [Finset.sum_div]
        congr 1
        ext t
        -- Expand the DFT entry and simplify `star`/conjugation.
        -- This puts the term into the geometric-series form `(ω⁷φ)^t / √8`.
        -- The final `mul_div` step is the only non-`simp` rearrangement we need.
        simp [dft8_entry, phiPatternComplex, phiPattern, star_div₀, star_pow, star_omega8,
          omega8_inv_eq_pow7, pow_mul, mul_pow]
        simpa [div_mul_eq_mul_div, mul_div, mul_assoc, mul_left_comm, mul_comm]
      rw [h_coeff, div_eq_zero_iff] at h_zero
      replace h_zero := h_zero.resolve_right (by
        have h_pos : 0 < (8 : ℝ) := by norm_num
        have h_sqrt_pos : 0 < Real.sqrt 8 := Real.sqrt_pos.mpr h_pos
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt h_sqrt_pos))
      let z : ℂ := omega8 ^ 7 * (phi : ℂ)
      have h_z_def : ∀ t : Fin 8, (omega8 ^ 7 * (phi : ℂ)) ^ t.val = z ^ t.val := fun t => rfl
      simp_rw [h_z_def] at h_zero
      have h_sum_geom : (∑ t : Fin 8, z ^ t.val) * (z - 1) = z ^ 8 - 1 := by
        have h8 : (∑ t : Fin 8, z ^ t.val) = z^0 + z^1 + z^2 + z^3 + z^4 + z^5 + z^6 + z^7 := by
          simp only [Fin.sum_univ_eight]; rfl
        rw [h8]
        ring
      rw [h_zero, zero_mul] at h_sum_geom
      have h_z8 : z ^ 8 = (phi : ℂ) ^ 8 := by
        -- `z = ω⁷ φ`, so `z^8 = (ω⁷)^8 * φ^8 = 1 * φ^8`.
        have hω : (omega8 ^ 7) ^ 8 = (1 : ℂ) := by
          -- (ω⁷)^8 = ω^(7*8) = ω^(8*7) = (ω^8)^7 = 1
          rw [← pow_mul]
          have : (7 : ℕ) * 8 = 8 * 7 := by ring
          rw [this, pow_mul, omega8_pow_8, one_pow]
        simp [z, mul_pow, hω]
      rw [h_z8] at h_sum_geom
      have h_phi8_ne_one : (phi : ℂ) ^ 8 ≠ 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_one]
        intro h
        replace h := Complex.ofReal_injective h
        have h_phi_pos : 0 < phi := phi_pos
        have h_phi_one : 1 < phi := one_lt_phi
        have h_pow_gt : 1 < phi ^ 8 := one_lt_pow₀ h_phi_one (by norm_num)
        linarith
      -- From `0 = φ^8 - 1` we would get `φ^8 = 1`, contradiction since φ > 1.
      have h_phi8_eq_one : (phi : ℂ) ^ 8 = 1 := by
        have : (phi : ℂ) ^ 8 - 1 = 0 := by
          simpa [eq_comm] using h_sum_geom
        exact sub_eq_zero.mp this
      exact h_phi8_ne_one h_phi8_eq_one
    · exact geometricWeight_pos (by decide : (1 : Fin 8).val ≠ 0)

end GapWeight
end Constants
end IndisputableMonolith
