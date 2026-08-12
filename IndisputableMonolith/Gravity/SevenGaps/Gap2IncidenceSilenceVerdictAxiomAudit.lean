import IndisputableMonolith.Gravity.SevenGaps.Gap2IncidenceSilenceVerdict

/-!
# Axiom audit for Gap2 incidence-silence verdict

Named theorems and the certificate must remain within the ordinary Mathlib
logical basis: exactly `propext`, `Classical.choice`, `Quot.sound`
(or axiom-free for `rfl` certificates).
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap2IncidenceSilenceVerdict

#print axioms fixedKindTotals_not_forced_in_letter_cost
#print axioms kind_rule_fails_twice
#print axioms ledger_does_not_force_countsOnly
#print axioms gap2_measure_derived_unmoved
#print axioms incidenceSilenceVerdictCert
