import IndisputableMonolith.NumberTheory.StripZeroFreeRegion

/-!
  ClassicalZeroFreeRegion.lean

  Track B1 of the RH unconditional-closure plan.

  Mathlib currently gives the boundary theorem
  `riemannZeta_ne_zero_of_one_le_re`, re-exported in
  `StripZeroFreeRegion.lean`. It does not yet contain a formal
  Hadamard-de la Vallee-Poussin logarithmic zero-free strip.

  This module starts the classical port without pretending that the hard
  analytic theorem is already in the library:

  * it proves the elementary trigonometric positivity kernel
    `3 + 4 cos θ + cos 2θ = 2(cos θ + 1)^2 ≥ 0`;
  * it isolates the exact analytic input whose proof would inhabit
    `LogZeroFreeStrip`;
  * it provides the conversion from that input to `StripZeroFreeBridge`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ClassicalZeroFreeRegion

open StripZeroFreeRegion

noncomputable section

/-! ## 1. The de la Vallee-Poussin positivity kernel -/

/-- The classical nonnegative trigonometric kernel used in the
Hadamard-de la Vallee-Poussin argument. -/
theorem deLaValleePoussin_trig_kernel_eq_square (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) =
      2 * (Real.cos θ + 1) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

/-- Positivity of the de la Vallee-Poussin trigonometric kernel. -/
theorem deLaValleePoussin_trig_kernel_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [deLaValleePoussin_trig_kernel_eq_square θ]
  nlinarith [sq_nonneg (Real.cos θ + 1)]

/-! ## 2. Exact analytic input needed for the logarithmic strip -/

/-- The classical Hadamard-de la Vallee-Poussin zero-free strip, stated in the
same shape as `StripZeroFreeRegion.LogZeroFreeStrip`.

This is intentionally a structure, not an axiom. Supplying an inhabitant is the
real Mathlib-grade analytic work: logarithmic derivative estimates for `ζ`,
the positivity kernel above, and control of the pole at `s = 1`. -/
structure DeLaValleePoussinZeroFreeRegion where
  c : ℝ
  T : ℝ
  c_pos : 0 < c
  T_gt_one : 1 < T
  zero_free :
    ∀ s : ℂ, T ≤ |s.im| →
      1 - c / Real.log |s.im| < s.re →
        riemannZeta s ≠ 0

/-- The classical zero-free-region input directly inhabits the Phase 5
`LogZeroFreeStrip` bridge object. -/
def logZeroFreeStrip_of_deLaValleePoussin
    (zfr : DeLaValleePoussinZeroFreeRegion) :
    LogZeroFreeStrip where
  c := zfr.c
  T := zfr.T
  c_pos := zfr.c_pos
  T_gt_one := zfr.T_gt_one
  zero_free := zfr.zero_free

/-- The de la Vallee-Poussin theorem, once formalized, supplies the named
`StripZeroFreeBridge`. -/
theorem stripZeroFreeBridge_of_deLaValleePoussin
    (zfr : DeLaValleePoussinZeroFreeRegion) :
    StripZeroFreeBridge :=
  ⟨logZeroFreeStrip_of_deLaValleePoussin zfr⟩

/-! ## 3. B1 status bundle -/

/-- Machine-readable Track B1 status. The elementary positivity kernel is
proved; the remaining field is exactly the classical analytic zero-free-region
input. -/
structure ClassicalZeroFreeRegionAttackSurface where
  trig_kernel_nonneg :
    ∀ θ : ℝ, 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ)
  open_deLaValleePoussin :
    DeLaValleePoussinZeroFreeRegion → StripZeroFreeBridge

def classicalZeroFreeRegionAttackSurface :
    ClassicalZeroFreeRegionAttackSurface where
  trig_kernel_nonneg := deLaValleePoussin_trig_kernel_nonneg
  open_deLaValleePoussin := stripZeroFreeBridge_of_deLaValleePoussin

end

end ClassicalZeroFreeRegion
end NumberTheory
end IndisputableMonolith
