import IndisputableMonolith.Gravity.SevenGaps.Gap2TailAutFiberParityBlocker

/-!
# Axiom audit: Gap2 R4 Aut-fiber parity blocker

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap2TailAutFiberParityBlocker

#check AutFiberBucket
#check TailAutFiberEven
#check TailAutFiberParityBlocker
#check classMu_eq_one_div_shellAutCard
#check shellAutCard_eq_of_classMu_eq
#check even_card_of_tick_add_four
#check tailAutFiberEven_of_tailAntipodalShift
#check no_tailAntipodalShift_of_parityBlocker
#check BareR5DecoyCertificate
#check bareR5DecoyCertificate
#check bareR5DecoyCertificate_banked
#check gap2TailAutFiberParityBlockerStatus_flags

#print axioms classMu_eq_one_div_shellAutCard
#print axioms shellAutCard_eq_of_classMu_eq
#print axioms even_card_of_tick_add_four
#print axioms tailAutFiberEven_of_tailAntipodalShift
#print axioms no_tailAntipodalShift_of_parityBlocker
#print axioms bareR5DecoyCertificate_banked
#print axioms gap2TailAutFiberParityBlockerStatus_flags
