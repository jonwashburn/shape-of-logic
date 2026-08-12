import IndisputableMonolith.Gravity.SevenGaps.Gap2DynamicsKindRule
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

/-!
# Gap 2 incidence-silence verdict: aggregate linearity is not forced

The OPEN target `C-gap2-does-the-substrate-force-incidence-silence` asked whether
the ledger layer forces aggregate linearity by kind (`FixedKindTotals`) on the
posting cost. Letter-level incidence silence as the boundary premise is already
dead (`N-route-gap2-letter-level-incidence-silence-as-the-named-premise`). This
module banks the scoped no-go for the corrected aggregate question.

**Verdict, stated first: no.** Across the three ledger layers the library
examines, nothing forces `FixedKindTotals` / counts-only:

1. **Letter-cost space** (`Gap2PostingCostDerivation`, `Gap2KindRule`):
   `pairCost` is equivariant and size-blind at totals, yet
   `¬ FixedKindTotals pairCost` (`costSizeBlind_not_fixedKindTotals`).
2. **Lattice state type** (`Gap2LatticeKindRule`): incidence-reading lattice
   charges need not be counts-only.
3. **Posting dynamics** (`Gap2DynamicsKindRule`): every nonnegative ledger is
   reachable; an explicit schedule on `twoBridges` is not counts-only
   (`ledger_forces_countsOnly_at_no_layer`).

**Named further premises (not derived here).** Discharging aggregate linearity
or counts-only therefore needs structure the examined layers do not supply:

* `CountsOnlySchedule`: a physical law about the actual posting run nature
  executes (named in `Gap2DynamicsKindRule`), not a theorem about the space of
  runs.
* Label indifference / Gibbs `1/|Aut|`: the measure-selection premise named by
  the A1.2 floor (`Gap2PostingLayerFloor`), independent of charge restrictions.

**What this module does not do.** It does not flip
`gap2_measure_derived` (already true under its banked close). It does not revive
letter-level incidence silence as the boundary. It does not claim a deeper
layer than the posting step is impossible; it says the library carries none,
and the live form of the premise is physical rather than ledger-forced.

Companion report:
`QG/attack_full_theory_20260729/A69_Gap2_Incidence_Silence_Verdict_20260804.html`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2IncidenceSilenceVerdict

open PathSumMeasure ExactShellGaugePreflight GaugeHistoryMeasure
open Gap2SizeBlindnessReach
open Gap2PostingCostDerivation
open Gap2KindRule
open Gap2LatticeKindRule
open Gap2DynamicsKindRule
open FullTheoryLedger

noncomputable section

/-! ## §1. Letter-cost layer: FixedKindTotals is not forced -/

/-- **SCOPED NO-GO (letter-cost layer).** Aggregate linearity by kind is not
forced among equivariant, total-size-blind letter costs: `pairCost` is a
witness with `¬ FixedKindTotals`. THEOREM (re-export with named scope). -/
theorem fixedKindTotals_not_forced_in_letter_cost :
    Equivariant pairCost ∧ CostSizeBlind pairCost ∧ ¬ FixedKindTotals pairCost :=
  ⟨pairCost_equivariant, costSizeBlind_not_fixedKindTotals.1,
    costSizeBlind_not_fixedKindTotals.2⟩

/-- Kind-only fails independently by counting and by incidence. THEOREM. -/
theorem kind_rule_fails_twice :
    (Equivariant pairCost ∧ ¬ KindOnly pairCost ∧ CostSizeBlind pairCost) ∧
      (Equivariant (incidenceCost 1) ∧ ¬ KindOnly (incidenceCost 1)) :=
  ⟨kind_rule_fails_by_counting,
   ⟨incidenceCost_equivariant 1, incidenceCost_not_kindOnly one_ne_zero⟩⟩

/-! ## §2. Three-layer ledger no-go (counts-only) -/

/-- **SCOPED NO-GO (three layers).** Counts-only / aggregate-linearity forcing
fails at letter-cost, lattice, and dynamics layers already examined. THEOREM. -/
theorem ledger_does_not_force_countsOnly :
    (¬ ChargesCountsOnly (incidenceCost 1)) ∧
    (¬ ChargesCountsOnly (incidencePhiLattice.toLetterCost)) ∧
    (∃ (sched : Schedule (PostingAlphabet twoBridges)),
      ¬ CountsOnlySchedule twoBridges sched) :=
  ledger_forces_countsOnly_at_no_layer

/-! ## §3. Named further premises -/

/-- The physical schedule law named when dynamics fails to force counts-only. -/
def namedSchedulePremise : String :=
  "CountsOnlySchedule: law about the actual posting run, not the space of runs"

/-- The measure-selection premise named by the A1.2 posting-layer floor. -/
def namedMeasurePremise : String :=
  "label indifference / Gibbs weight 1/|Aut K|"

/-- Both named further premises the incidence-silence OPEN hands forward. -/
structure NamedFurtherPremises where
  schedule_law : String
  measure_selection : String

def namedFurtherPremises : NamedFurtherPremises where
  schedule_law := namedSchedulePremise
  measure_selection := namedMeasurePremise

/-! ## §4. Measure flag unmoved -/

/-- `gap2_measure_derived` stays at its banked value; this verdict flips nothing.
THEOREM (`rfl`). -/
theorem gap2_measure_derived_unmoved :
    fullTheoryBenchmarks.gap2_measure_derived = true :=
  rfl

/-! ## §5. Certificate -/

structure IncidenceSilenceVerdictCert : Prop where
  fixedKindTotals_not_forced :
    Equivariant pairCost ∧ CostSizeBlind pairCost ∧ ¬ FixedKindTotals pairCost
  three_layer_nogo :
    (¬ ChargesCountsOnly (incidenceCost 1)) ∧
    (¬ ChargesCountsOnly (incidencePhiLattice.toLetterCost)) ∧
    (∃ (sched : Schedule (PostingAlphabet twoBridges)),
      ¬ CountsOnlySchedule twoBridges sched)
  measure_flag_unmoved :
    fullTheoryBenchmarks.gap2_measure_derived = true
  further_premises_named :
    namedFurtherPremises.schedule_law = namedSchedulePremise ∧
      namedFurtherPremises.measure_selection = namedMeasurePremise

theorem incidenceSilenceVerdictCert : IncidenceSilenceVerdictCert where
  fixedKindTotals_not_forced := fixedKindTotals_not_forced_in_letter_cost
  three_layer_nogo := ledger_does_not_force_countsOnly
  measure_flag_unmoved := gap2_measure_derived_unmoved
  further_premises_named := ⟨rfl, rfl⟩

end
end Gap2IncidenceSilenceVerdict
end SevenGaps
end Gravity
end IndisputableMonolith
