/-
Hostile probe for Gap2LedgerCohomology (C18). Uncommitted. Read-only of production.
Checks: key theorems are inhabitations the kernel accepts; flag unmoved;
measured dims match the claimed 3/4/4 vs 3; no sorry in the production module
is re-checked by forcing the verdict package.
-/
import IndisputableMonolith.Gravity.SevenGaps.Gap2LedgerCohomology

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2LedgerCohomologyHostileProbe

open Gap2LedgerCohomology Gap2SizeBlindnessReach Gap2PostingCostDerivation
open Gap2LetterCostDichotomy Gap2GaugeVolume Gap2GluingDerivation

noncomputable section

/-- Probe: genuine-class package is inhabited. -/
theorem probe_incidence_genuine :
    Equivariant (incidenceCost (1 : ℝ))
      ∧ ¬ IsLedgerCoboundary (incidenceCost (1 : ℝ))
      ∧ ¬ IsCountLinear (incidenceCost (1 : ℝ))
      ∧ historyCost (incidenceCost (1 : ℝ)) 2 twoLoops = 0
      ∧ historyCost (incidenceCost (1 : ℝ)) 2 twoBridges = 2 :=
  ⟨(incidence_is_genuine_H1_class).1,
    (incidence_is_genuine_H1_class).2.2.1,
    (incidence_is_genuine_H1_class).2.2.2.1,
    (incidence_is_genuine_H1_class).2.2.2.2.1,
    (incidence_is_genuine_H1_class).2.2.2.2.2.1⟩

/-- Probe: A1.7 escape decomposes as count rates (1, 0, -1/24). -/
theorem probe_a17_count_decomp :
    IsCountLinear (kindRateCost 1 0 (-(1 / 24)))
      ∧ KindRates (kindRateCost 1 0 (-(1 / 24))) 1 0 (-(1 / 24))
      ∧ ¬ IsLedgerCoboundary (kindRateCost 1 0 (-(1 / 24))) :=
  ⟨(a17_escape_is_count_combination).1,
    (a17_escape_is_count_combination).2.2.2.2,
    (a17_escape_is_count_combination).2.2.1⟩

/-- Probe: measured dims 3/4/4 vs count span 3, and flag unmoved. -/
theorem probe_measured_and_flag :
    measuredH1Dim 1 = 3 ∧ measuredH1Dim 2 = 4 ∧ measuredH1Dim 3 = 4
      ∧ measuredCountSpanDim 2 = 3 ∧ measuredCountSpanDim 2 < measuredH1Dim 2
      ∧ ledgerCohomologyVerdict.measure_flag_moved = false :=
  ⟨rfl, rfl, rfl, rfl, measured_H1_exceeds_count_at_cap2,
    Gap2LedgerCohomology.index_flag_unmoved⟩

/-- Probe: centered fibre is a coboundary; count span rank three. -/
theorem probe_coboundary_and_rank :
    IsLedgerCoboundary (centeredIncidenceCost (1 : ℝ))
      ∧ (∀ cV cE cT : ℝ,
          historyCost (kindRateCost cV cE cT) 1 (dust 1) = 0 →
          historyCost (kindRateCost cV cE cT) 2 (bouquet 1 0) = 0 →
          historyCost (kindRateCost cV cE cT) 2 (bouquet 0 1) = 0 →
          cV = 0 ∧ cE = 0 ∧ cT = 0) :=
  ⟨centeredIncidence_is_coboundary 1, count_span_rank_three⟩

/-- Witness sizes match the (2,2,0) obstruction pair. -/
theorem probe_witness_counts :
    twoLoops.nV = 2 ∧ twoLoops.nE = 2 ∧ twoLoops.nT = 0
      ∧ twoBridges.nV = 2 ∧ twoBridges.nE = 2 ∧ twoBridges.nT = 0
      ∧ properEdgeCount twoLoops = 0 ∧ properEdgeCount twoBridges = 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact properEdgeCount_twoLoops
  · exact properEdgeCount_twoBridges

end

#print axioms probe_incidence_genuine
#print axioms probe_a17_count_decomp
#print axioms probe_measured_and_flag
#print axioms probe_coboundary_and_rank
#print axioms probe_witness_counts

end Gap2LedgerCohomologyHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith
