import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-!
# Hostile probe for the A15 J-Ehrhart span NO-GO (review 2026-07-30)

Adversarial module written by the hostile reviewer of `Gap2JEhrhartSpan`.  It
edits nothing and attacks the reviewed module from four sides; every attack
that fails to land is itself evidence for the reviewed claim.

1. **Uniqueness of the obstruction.**  `cert4_left_null_unique` and
   `cert3_left_null_unique`: every functional annihilating the census columns
   is a scalar multiple of the exhibited certificate, so the kill does not
   rest on one lucky find among many candidate functionals.
2. **Exact residuals, kernel-checked.**  `residual4_with_const_exact`,
   `residual4_no_const_exact`, `residual3_no_const_exact`: the least-squares
   residuals the report quotes (`4096` with the constant column,
   `5154048/1093` without it, `648/23` in three dimensions) are reproduced
   inside the kernel with explicit projection coefficients, and each residual
   is orthogonal to every census column, which is what makes it *the*
   residual rather than an arbitrary nonzero vector.
3. **Hypothesis tightness.**  `jCost_at_zero_kappa_is_fixedKindTotals`: at
   Casimir zero every letter costs `0`, so the `kappa ≠ 0` hypothesis of
   `jCost_not_fixedKindTotals` cannot be dropped.
4. **The `j0 ≠ c_V` content.**  `probe_3D_solution_reconstructs` and
   `probe_3D_inversion_numbers`: the published inversion really does return
   `c_V = -4` on `J`'s measured moments while `j0 = 2`.
5. **Concrete instantiation.**  `probe_edge_cost_at_two`: a single edge costs
   `1/2` at Casimir `2`, so the letter-cost theorems talk about a live object.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2JEhrhartSpanHostileProbe

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan

/-- **The 4D obstruction is the only one.**  The left null space of the four
census columns is one-dimensional, spanned by `cert4`. -/
theorem cert4_left_null_unique (u : Fin 5 → ℚ)
    (hV : dot4 u mV4 = 0) (hE : dot4 u mE4 = 0)
    (hT : dot4 u mT4 = 0) (hC : dot4 u mC4 = 0) :
    u = (u 1) • cert4 := by
  simp [dot4, mV4, Fin.sum_univ_five] at hV
  simp [dot4, mE4, Fin.sum_univ_five] at hE
  simp [dot4, mT4, Fin.sum_univ_five] at hT
  simp [dot4, mC4, Fin.sum_univ_five] at hC
  funext i
  fin_cases i <;> simp [Pi.smul_apply, cert4] <;> linarith

/-- **The 3D obstruction is the only one.** -/
theorem cert3_left_null_unique (u : Fin 4 → ℚ)
    (hV : dot3 u mV3 = 0) (hE : dot3 u mE3 = 0) (hT : dot3 u mT3 = 0) :
    u = (u 1) • cert3 := by
  simp [dot3, mV3, Fin.sum_univ_four] at hV
  simp [dot3, mE3, Fin.sum_univ_four] at hE
  simp [dot3, mT3, Fin.sum_univ_four] at hT
  funext i
  fin_cases i <;> simp [Pi.smul_apply, cert3] <;> linarith

/-- **Kernel-checked 4D residual with the constant column.**  The projection of
`mJ4` onto the four census columns leaves exactly the residual the report
quotes, and it is orthogonal to every column. -/
theorem residual4_with_const_exact :
    mJ4 = ((-212 : ℚ) / 9) • mV4 + ((188 : ℚ) / 9) • mE4
        + ((-326 : ℚ) / 27) • mT4 + ((230 : ℚ) / 9) • mC4
        + ![0, 64 / 3, -128 / 3, 128 / 3, 0]
      ∧ dot4 (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ) mV4 = 0
      ∧ dot4 (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ) mE4 = 0
      ∧ dot4 (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ) mT4 = 0
      ∧ dot4 (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ) mC4 = 0
      ∧ dot4 (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ)
          (![0, 64 / 3, -128 / 3, 128 / 3, 0] : Fin 5 → ℚ) = 4096 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [mV4, mE4, mT4, mC4, mJ4] <;> norm_num
  · simp [dot4, mV4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, mE4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, mT4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, mC4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, Fin.sum_univ_five] <;> norm_num

/-- **Kernel-checked 4D residual without the constant column.** -/
theorem residual4_no_const_exact :
    mJ4 = ((-24310 : ℚ) / 1093) • mV4 + ((22530 : ℚ) / 1093) • mE4
        + ((-39205 : ℚ) / 3279) • mT4
        + ![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093]
      ∧ dot4 (![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093] :
          Fin 5 → ℚ) mV4 = 0
      ∧ dot4 (![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093] :
          Fin 5 → ℚ) mE4 = 0
      ∧ dot4 (![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093] :
          Fin 5 → ℚ) mT4 = 0
      ∧ dot4 (![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093] :
          Fin 5 → ℚ)
          (![0, 26016 / 1093, -49824 / 1093, 42096 / 1093, 26496 / 1093] :
          Fin 5 → ℚ) = 5154048 / 1093 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [mV4, mE4, mT4, mJ4] <;> norm_num
  · simp [dot4, mV4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, mE4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, mT4, Fin.sum_univ_five] <;> norm_num
  · simp [dot4, Fin.sum_univ_five] <;> norm_num

/-- **Kernel-checked 3D residual without the constant column.** -/
theorem residual3_no_const_exact :
    mJ3 = ((-62 : ℚ) / 23) • mV3 + ((264 : ℚ) / 23) • mE3
        + ((-893 : ℚ) / 69) • mT3 + ![0, 18 / 23, -54 / 23, 108 / 23]
      ∧ dot3 (![0, 18 / 23, -54 / 23, 108 / 23] : Fin 4 → ℚ) mV3 = 0
      ∧ dot3 (![0, 18 / 23, -54 / 23, 108 / 23] : Fin 4 → ℚ) mE3 = 0
      ∧ dot3 (![0, 18 / 23, -54 / 23, 108 / 23] : Fin 4 → ℚ) mT3 = 0
      ∧ dot3 (![0, 18 / 23, -54 / 23, 108 / 23] : Fin 4 → ℚ)
          (![0, 18 / 23, -54 / 23, 108 / 23] : Fin 4 → ℚ) = 648 / 23 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [mV3, mE3, mT3, mJ3] <;> norm_num
  · simp [dot3, mV3, Fin.sum_univ_four] <;> norm_num
  · simp [dot3, mE3, Fin.sum_univ_four] <;> norm_num
  · simp [dot3, mT3, Fin.sum_univ_four] <;> norm_num
  · simp [dot3, Fin.sum_univ_four] <;> norm_num

/-- **The `kappa ≠ 0` hypothesis cannot be dropped.**  At Casimir zero every
letter costs nothing, and the all-zero rates witness `FixedKindTotals`. -/
theorem jCost_at_zero_kappa_is_fixedKindTotals : FixedKindTotals (jCost 0) := by
  refine ⟨0, 0, 0, fun B K => ⟨?_, ?_, ?_⟩⟩ <;> simp [jCost]

/-- **The published 3D inversion applied to `J`'s moments.**  The exhibited
solution of `census3_with_const_is_onto` is exactly the JSON's
`(c_V, c_E, c_T, c_0) = (-4, 12, -40/3, 6)`, and it reconstructs `mJ3`. -/
theorem probe_3D_solution_reconstructs :
    ∀ i : Fin 4, (-4 : ℚ) * mV3 i + 12 * mE3 i + (-40 / 3) * mT3 i
      + 6 * mC3 i = mJ3 i := by
  intro i
  fin_cases i <;> simp [mV3, mE3, mT3, mC3, mJ3] <;> norm_num

/-- **The `j0 ≠ c_V` numbers.**  `c_V = -4` by the published formula,
`j0 = 2`. -/
theorem probe_3D_inversion_numbers :
    (3 * mJ3 2 - mJ3 1) / 6 = -4 ∧ mJ3 3 = 2 ∧ (2 : ℚ) ≠ -4 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mJ3] <;> norm_num

/-- **A live instantiation.**  The single edge costs `1/2` at Casimir `2`. -/
theorem probe_edge_cost_at_two :
    historyCost (jCost 2) 4 edgeComplex = 1 / 2 := by
  rw [historyCost_jCost, blockSum_edge 2 (by norm_num : (2 : ℝ) ≠ 0)]

end Gap2JEhrhartSpanHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
