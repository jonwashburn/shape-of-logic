import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Spectral.DFT8

namespace IndisputableMonolith
namespace Constants
namespace GapWeight

open scoped BigOperators

open Complex
open IndisputableMonolith.Spectral

/-!
# GapWeight.Projection — closing the “weights + normalization” ambiguity

This module defines, explicitly, the two pieces that were historically left implicit:

1) **Why the geometric weights have a `sin²(πk/8)` factor.**
   This is the spectral (eigenvalue) weight induced by the *discrete derivative / Laplacian*
   on the 8-tick cyclic shift. In DFT language, it is forced by shift-diagonalization.

2) **Why the normalization uses a factor of `64`.**
   `64 = 8×8` is the cardinality of the fundamental RS interface cell when we take:
   - 8 ticks (the octave clock), and
   - 8 spatial vertices (the Q₃ cell has 8 vertices).
   The normalization converts a scale-invariant *fraction* into a per-cell integrated weight.

This is claim hygiene: we’re making the operator/measure choice explicit, so there is no
hidden degree of freedom.
-/

/-! ## Canonical counts (no ambiguity) -/

/-- Number of ticks in the fundamental octave. -/
@[simp] def N_ticks : ℕ := Fintype.card (Fin 8)

@[simp] theorem N_ticks_eq : N_ticks = 8 := by
  decide

/-- Number of spatial vertices in a `Q₃` cell (8 vertices). We model this as `Fin 8`. -/
@[simp] def N_vertices : ℕ := Fintype.card (Fin 8)

@[simp] theorem N_vertices_eq : N_vertices = 8 := by
  decide

/-- Size of the fundamental “cell index” set: ticks × vertices = 8×8 = 64. -/
@[simp] def N_cell : ℕ := Fintype.card (Fin 8 × Fin 8)

@[simp] theorem N_cell_eq : N_cell = 64 := by
  -- card (Fin 8 × Fin 8) = 8 * 8
  decide

/-- The projection scaling used to convert a dimensionless fraction into a per-cell weight. -/
@[simp] def projectionScale : ℝ := (N_cell : ℝ)

@[simp] theorem projectionScale_eq : projectionScale = 64 := by
  simp [projectionScale, N_cell_eq]

/-! ## A canonical normalization denominator -/

/-- Total DFT energy of the φ-pattern (Parseval denominator). -/
noncomputable def phiDFTEnergyTotal : ℝ :=
  Finset.univ.sum fun k : Fin 8 => phiDFTAmplitude k

lemma phiDFTEnergyTotal_nonneg : 0 ≤ phiDFTEnergyTotal := by
  unfold phiDFTEnergyTotal
  apply Finset.sum_nonneg
  intro k _
  exact phiDFTAmplitude_nonneg k

/-! ## The explicit projection operator (minimal actionable closure) -/

/-- **Projection weight** of the φ-pattern onto the 8-tick basis:

`projectionScale * (rawWeightedNeutralEnergy / totalEnergy)`.

This makes the normalization and measure choice explicit. -/
noncomputable def w8_projected : ℝ :=
  projectionScale * (w8_dft_candidate / phiDFTEnergyTotal)

lemma w8_projected_nonneg : 0 ≤ w8_projected := by
  unfold w8_projected
  have hscale : 0 ≤ projectionScale := by simp [projectionScale]
  have hnum : 0 ≤ w8_dft_candidate := le_of_lt w8_dft_candidate_pos
  have hden : 0 ≤ phiDFTEnergyTotal := phiDFTEnergyTotal_nonneg
  -- If total energy is 0, then the ratio is 0 (since numerator is 0 as well). Otherwise nonneg by div_nonneg.
  by_cases hE : phiDFTEnergyTotal = 0
  · simp [hE, hnum, hscale]
  · have hdiv : 0 ≤ w8_dft_candidate / phiDFTEnergyTotal := div_nonneg hnum (le_of_lt (lt_of_le_of_ne' hden hE))
    exact mul_nonneg hscale hdiv

/-!
## Important note

At present, the pipeline constant `Constants.w8_from_eight_tick` is defined in a closed form
in `Constants/GapWeight.lean` and evaluates to ≈ 2.49056927545.

The operator `w8_projected` above is the *definition-level closure* of what “projection weight”
means: it makes explicit the normalization and the 8×8 measure.

Proving `w8_projected = Constants.w8_from_eight_tick` inside Lean is a tractable (but nontrivial)
algebraic/trigonometric reduction problem and is tracked as a follow-up theorem.
-/

/-! ## Why `sin²(πk/8)` is canonical (spectral footprint of the 8-tick derivative) -/

/-- Discrete one-step difference on the 8-tick cycle: `(S - I)v`. -/
def diff8 (v : Fin 8 → ℂ) : Fin 8 → ℂ :=
  fun t => cyclic_shift v t - v t

/-- Total squared energy of the discrete difference (a canonical local, shift-invariant quadratic form). -/
noncomputable def diffEnergy8 (v : Fin 8 → ℂ) : ℝ :=
  ∑ t : Fin 8, Complex.normSq (diff8 v t)

lemma diffEnergy8_nonneg (v : Fin 8 → ℂ) : 0 ≤ diffEnergy8 v := by
  unfold diffEnergy8
  exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- DFT-8 mode `k` has unit norm (columns are orthonormal). -/
lemma dft8_mode_normSq_sum (k : Fin 8) :
    (∑ t : Fin 8, Complex.normSq (dft8_mode k t)) = 1 := by
  -- ⟨column k, column k⟩ = 1, and ⟨v,v⟩ = ∑ conj(v_t) * v_t = ∑ normSq(v_t).
  have hcol := dft8_column_orthonormal k k
  have h1 : (∑ t : Fin 8, star (dft8_entry t k) * dft8_entry t k) = (1 : ℂ) := by
    simpa using (by simpa using hcol)
  -- Rewrite each term `star z * z` as `(normSq z : ℂ)`.
  have h1' : (∑ t : Fin 8, ((Complex.normSq (dft8_entry t k) : ℝ) : ℂ)) = (1 : ℂ) := by
    simpa [Complex.normSq_eq_conj_mul_self] using h1
  -- Pull the cast out of the sum.
  have h1'' : ((∑ t : Fin 8, (Complex.normSq (dft8_entry t k) : ℝ)) : ℂ) = (1 : ℂ) := by
    simpa [Complex.ofReal_sum] using h1'
  -- Back to ℝ, and rewrite `dft8_mode`.
  have hreal : (∑ t : Fin 8, (Complex.normSq (dft8_entry t k) : ℝ)) = (1 : ℝ) :=
    Complex.ofReal_injective (by simpa using h1'')
  simpa [dft8_mode] using hreal

/-- Discrete difference energy of a DFT mode is the squared magnitude of its shift eigenvalue minus 1.

This is the precise mathematical reason a `sin²(πk/8)` factor appears: it is (up to a fixed factor 4)
the spectrum of the 8-tick discrete derivative/Laplacian. -/
lemma diffEnergy8_mode (k : Fin 8) :
    diffEnergy8 (dft8_mode k) = Complex.normSq (omega8 ^ k.val - 1) := by
  unfold diffEnergy8 diff8
  -- Use that cyclic_shift (mode k) = ω^k • mode k.
  have hshift := dft8_shift_eigenvector k
  -- rewrite the difference pointwise
  have hpoint : ∀ t : Fin 8, cyclic_shift (dft8_mode k) t - dft8_mode k t =
      (omega8 ^ k.val - 1) * dft8_mode k t := by
    intro t
    have ht := congrArg (fun f => f t) hshift
    -- ht : cyclic_shift (dft8_mode k) t = (omega8 ^ k.val) • dft8_mode k t
    simp [Pi.smul_apply, smul_eq_mul] at ht
    -- subtract and factor
    calc
      cyclic_shift (dft8_mode k) t - dft8_mode k t
          = (omega8 ^ k.val) * dft8_mode k t - dft8_mode k t := by simpa [ht]
      _   = (omega8 ^ k.val - 1) * dft8_mode k t := by ring
  -- push through normSq and sum
  have hns : ∀ t : Fin 8, Complex.normSq (cyclic_shift (dft8_mode k) t - dft8_mode k t) =
      Complex.normSq (omega8 ^ k.val - 1) * Complex.normSq (dft8_mode k t) := by
    intro t
    -- use hpoint and normSq_mul
    simp [hpoint t, Complex.normSq_mul]
  simp_rw [hns]
  -- factor out the constant eigenvalue term
  have hfac :
      (∑ t : Fin 8, Complex.normSq (omega8 ^ k.val - 1) * Complex.normSq (dft8_mode k t)) =
        Complex.normSq (omega8 ^ k.val - 1) * (∑ t : Fin 8, Complex.normSq (dft8_mode k t)) := by
    -- `Finset.mul_sum` gives the reverse direction, so we use `.symm`.
    simpa using
      (Finset.mul_sum
        (s := (Finset.univ : Finset (Fin 8)))
        (f := fun t : Fin 8 => Complex.normSq (dft8_mode k t))
        (a := Complex.normSq (omega8 ^ k.val - 1))).symm
  rw [hfac, dft8_mode_normSq_sum]
  ring

end GapWeight
end Constants
end IndisputableMonolith
