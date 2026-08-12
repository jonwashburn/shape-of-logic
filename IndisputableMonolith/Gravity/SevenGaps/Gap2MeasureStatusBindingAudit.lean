import IndisputableMonolith.Gravity.SevenGaps.Gap2MeasureStatusBinding

/-!
# Axiom audit: measure status retraction (2026-07-26)

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.

Renamed from the Wave C1 R6 binding audit. The audited theorems now record
that the two measure-side status Bools are `false` and that the R6 witness is
parameter-inert, rather than that the Bools are `true`.
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap2MeasureStatusBinding
open IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure
open IndisputableMonolith.Gravity.SevenGaps.ExactShellGaugePreflight

#check gap2_measure_status_retracted
#check history_discharge_is_prior_theorem_rewritten
#check historyMeasure_is_parameter_inert
#check historyCarrier_equiv_plainCarrier
#check historyMeasure_is_the_old_measure
#check continuum_limit_still_open
#check gap2_rollup_closed_after_flag9
#check status_substrate_measure_open
#check status_counting_principle_open

#print axioms gap2_measure_status_retracted
#print axioms history_discharge_is_prior_theorem_rewritten
#print axioms historyMeasure_is_parameter_inert
#print axioms historyCarrier_equiv_plainCarrier
#print axioms historyMeasure_is_the_old_measure
#print axioms continuum_limit_still_open
#print axioms gap2_rollup_closed_after_flag9
#print axioms status_substrate_measure_open
#print axioms status_counting_principle_open
