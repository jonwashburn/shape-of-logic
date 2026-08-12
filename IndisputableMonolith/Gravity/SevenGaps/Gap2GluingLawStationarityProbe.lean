import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingLawStationarity

/-!
# Outside-module probe for Gap2 gluing-law stationarity
-/

open IndisputableMonolith
open IndisputableMonolith.Gravity.SevenGaps
open IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure
open IndisputableMonolith.Gravity.SevenGaps.ExactShellGaugePreflight
open IndisputableMonolith.Gravity.SevenGaps.Gap2GaugeVolume
open IndisputableMonolith.Gravity.SevenGaps.Gap2GluingLawStationarity
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check InsertionStationarity
#check LabelInsertionKernel
#check gluingLaw_iff_insertionStationarity
#check no_bare_posting_degree_supplies_interleave
#check bare_posting_does_not_force_insertion_stationarity
#check gluingLawStationarityCert

example :
    GluingLaw (fun n => 1 / (Nat.factorial n : ℝ)) :=
  inverseFactorial_gluingLaw

example :
    InsertionStationarity (fun n => 1 / (Nat.factorial n : ℝ)) :=
  factorialWorld_stationary

example :
    ¬ InsertionStationarity (fun _ => (1 : ℝ)) :=
  constantWorld_not_stationary

example :
    Fintype.card (BarePostingMove 2) ≠
      Fintype.card (LabelInsertionSlot 2) :=
  bare_posting_degree_not_insertion_degree_at_two

example :
    Fintype.card (BareUnionPostingMove 1 0 0 1 0 0) ≠
      Gap2GluingDerivation.interleave 1 0 0 1 0 0 :=
  bare_union_posting_degree_not_interleave_two_vertices

example :
    fullTheoryBenchmarks.gap2_measure_derived = true :=
  gap2_measure_derived_unmoved

example : GluingLawStationarityCert :=
  gluingLawStationarityCert
