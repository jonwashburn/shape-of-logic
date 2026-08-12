import IndisputableMonolith.Gravity.SevenGaps.Gap2IncidenceSilenceVerdict

/-!
# Outside-module probe for Gap2 incidence-silence verdict
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap2IncidenceSilenceVerdict
open IndisputableMonolith.Gravity.SevenGaps.Gap2PostingCostDerivation
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check fixedKindTotals_not_forced_in_letter_cost
#check ledger_does_not_force_countsOnly
#check incidenceSilenceVerdictCert
#check namedFurtherPremises

example :
    CostSizeBlind pairCost ∧ ¬ FixedKindTotals pairCost :=
  ⟨fixedKindTotals_not_forced_in_letter_cost.2.1,
    fixedKindTotals_not_forced_in_letter_cost.2.2⟩

example : fullTheoryBenchmarks.gap2_measure_derived = true :=
  gap2_measure_derived_unmoved

example : IncidenceSilenceVerdictCert :=
  incidenceSilenceVerdictCert

example :
    namedFurtherPremises.schedule_law =
      "CountsOnlySchedule: law about the actual posting run, not the space of runs" :=
  rfl
