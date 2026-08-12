import IndisputableMonolith.Gravity.SevenGaps.Gap2LetterCostDichotomy

/-!
Hostile review probe for `Gap2LetterCostDichotomy` (A1.7).
Uncommitted by design; primary commits only if review is not FATAL.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LetterCostDichotomyHostileProbe

open Gap2LetterCostDichotomy
open PathSumMeasure ExactShellGaugePreflight Gap2GaugeVolume Gap2GluingDerivation
open Gap2PostingCostDerivation GaugeHistoryMeasure

/-! ## Axiom audit: every report-named theorem -/

#print axioms surface_and_kindTotals_force_zero
#print axioms the_measure_is_exactly_the_gauge_divisor
#print axioms atom_normalizations_are_derived
#print axioms equivariance_is_not_load_bearing
#print axioms fixed_kind_totals_is_load_bearing
#print axioms bulk_cancellation_is_load_bearing
#print axioms purity_of_the_surface_term_is_load_bearing
#print axioms the_two_relaxations_cannot_be_combined
#print axioms the_letter_level_fibre_is_not_a_point
#print axioms surface_at_positive_dilates_forces_zero
#print axioms surfaceArea_and_kindTotals_force_zero
#print axioms surface_and_fixedKindTotals_force_zero_historyCost
#print axioms letterCostDichotomyVerdict
#print axioms indexTiltCost_not_equivariant
#print axioms surfaceCost_surfaceTotal
#print axioms surfaceCost_not_fixedKindTotals
#print axioms index_no_triple
#print axioms index_flag_unmoved

/-! ## Quantifier shape of the headline (type-level, no Equivariant binder) -/

/-- The headline binders are family + KindTotalRates + SurfaceTotal; no Equivariant. -/
theorem headline_binders_are_as_claimed :
    ∀ (F : CensusDilateFamily) (c : LetterCost) (cV cE cT a e : ℝ),
      KindTotalRates c cV cE cT → SurfaceTotal F c a e →
        cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0 :=
  fun F _c _ _ _ _ _ hk hs => surface_and_kindTotals_force_zero F hk hs

/-- SurfaceTotal is universal in N, not a five-point sample. -/
theorem surfaceTotal_is_forall_N (F : CensusDilateFamily) (c : LetterCost) (a e : ℝ) :
    SurfaceTotal F c a e ↔
      ∀ N : ℕ, historyCost c (F.cap N) (F.K N) = a * (N : ℝ) ^ 3 + e :=
  Iff.rfl

/-- The history-zero corollary really quantifies over every complex and cap. -/
theorem history_zero_is_global (F : CensusDilateFamily) {c : LetterCost} {a e : ℝ}
    (h : FixedKindTotals c) (hs : SurfaceTotal F c a e) :
    ∀ (B : ℕ) (K : BoundedComplex B), historyCost c B K = 0 :=
  surface_and_fixedKindTotals_force_zero_historyCost F h hs

/-! ## Witness recomputation by the kernel -/

/-- Census closed forms at N = 0..5, kernel-checked. -/
theorem census_samples :
    censusV 0 = 1 ∧ censusE 0 = 0 ∧ censusT 0 = 0 ∧
    censusV 1 = 16 ∧ censusE 1 = 65 ∧ censusT 1 = 24 ∧
    censusV 2 = 81 ∧ censusE 2 = 544 ∧ censusT 2 = 384 ∧
    censusV 3 = 256 ∧ censusE 3 = 2145 ∧ censusT 3 = 1944 ∧
    censusV 4 = 625 ∧ censusE 4 = 5936 ∧ censusT 4 = 6144 ∧
    censusV 5 = 1296 ∧ censusE 5 = 13345 ∧ censusT 5 = 15000 := by
  simp [censusV, censusE, censusT]


/-- Rates (1,0,-1/24) give 4N³+6N²+4N+1 on flatFamily at N=0..5. -/
theorem purity_witness_samples :
    (∀ N ∈ ([0,1,2,3,4,5] : List ℕ),
      historyCost (kindRateCost 1 0 (-(1/24))) (flatFamily.cap N) (flatFamily.K N)
        = 4 * (N : ℝ) ^ 3 + 6 * (N : ℝ) ^ 2 + 4 * (N : ℝ) + 1) := by
  intro N hN
  have := (purity_of_the_surface_term_is_load_bearing flatFamily).2.2.2 N
  exact this

/-- Rates (1,-1,7/12) give -24N³-12N²+1 on flatFamily. -/
theorem combined_relaxation_witness (N : ℕ) :
    historyCost (kindRateCost 1 (-1) (7/12)) (flatFamily.cap N) (flatFamily.K N)
      = (-24) * (N : ℝ) ^ 3 + (-12) * (N : ℝ) ^ 2 + 1 :=
  (the_two_relaxations_cannot_be_combined flatFamily).2.2.2 N

/-- surfaceCost t totals exactly t·N³ on the census family. -/
theorem surfaceCost_total_is_tN3 (t : ℝ) (N : ℕ) :
    historyCost (surfaceCost t) (flatFamily.cap N) (flatFamily.K N) = t * (N : ℝ) ^ 3 := by
  have := surfaceCost_surfaceTotal flatFamily t N
  simpa using this

/-- indexTiltCost fails equivariance: concrete letter values on two-point dust. -/
theorem indexTilt_concrete_charges (t : ℝ) :
    indexTiltCost t 2 (dust 2) (Sum.inl v0Dust2) = t ∧
    indexTiltCost t 2 (dust 2) (Sum.inl v1Dust2) = -t :=
  ⟨indexTiltCost_at_v0 t, indexTiltCost_at_v1 t⟩

theorem indexTilt_block_sums_zero (t : ℝ) :
    KindTotalRates (indexTiltCost t) 0 0 0 :=
  indexTiltCost_kindTotalRates t

/-- kindRateCost 1 0 0 has history 1 on one-vertex dust and is not surface-total. -/
theorem bulk_witness_dust :
    historyCost (kindRateCost 1 0 0) 1 (dust 1) = 1 := by
  simpa using historyCost_kindRateCost_dust_one (1 : ℝ) 0 0

theorem bulk_witness_not_surface :
    ¬ ∃ a e : ℝ, SurfaceTotal flatFamily (kindRateCost 1 0 0) a e :=
  (bulk_cancellation_is_load_bearing flatFamily).2.2.2

/-- FixedKindTotals inhabited (nonzero rates) and fibre member inhabited. -/
theorem fixedKindTotals_inhabited :
    FixedKindTotals (kindRateCost 1 0 0) :=
  kindRateCost_fixedKindTotals 1 0 0

theorem fibre_member_centered (t : ℝ) (ht : t ≠ 0) :
    Equivariant (centeredIncidenceCost t) ∧
    FixedKindTotals (centeredIncidenceCost t) ∧
    SurfaceTotal flatFamily (centeredIncidenceCost t) 0 0 ∧
    historyCost (centeredIncidenceCost t) 1 (dust 1) = 0 := by
  have h := the_letter_level_fibre_is_not_a_point flatFamily ht
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2 1 (dust 1)⟩

/-- Flags unmoved, rfl-checked. -/
theorem flags_unmoved :
    dichotomyIndex.triple_derived = false ∧
    dichotomyIndex.measure_flag_moved = false ∧
    dichotomyIndex.equivariance_used = false :=
  ⟨index_no_triple, index_flag_unmoved, index_equivariance_unused⟩

/-- Headline proof does not mention Equivariant in its type. -/
example : ∀ (F : CensusDilateFamily) {c : LetterCost} {cV cE cT a e : ℝ},
    KindTotalRates c cV cE cT → SurfaceTotal F c a e →
      cV = 0 ∧ cE = 0 ∧ cT = 0 ∧ a = 0 ∧ e = 0 :=
  surface_and_kindTotals_force_zero

#print axioms headline_binders_are_as_claimed
#print axioms census_samples
#print axioms combined_relaxation_witness
#print axioms surfaceCost_total_is_tN3
#print axioms indexTilt_concrete_charges
#print axioms fibre_member_centered
#print axioms flags_unmoved

end Gap2LetterCostDichotomyHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
