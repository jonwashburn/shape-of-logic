import IndisputableMonolith.Gravity.SevenGaps.Gap2PostingCocycleCarrier

/-!
# Axiom audit: Gap2 posting-cocycle carrier (STOP A)

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.Gap2PostingCocycleCarrier

#check PostingEnrichedPathClass
#check forgetPostingPhase
#check postingPhase
#check FactorsThroughPostingForget
#check carrier_forgets_posting_phase
#check postingPhase_not_factors_through_forget
#check PostingEnrichedExactHistory
#check exact_carrier_forgets_posting_phase
#check exact_postingPhase_not_factors_through_forget
#check TypedResidual_carrier_forgets_posting_phase
#check typedResidual_carrier_forgets_posting_phase
#check PostingCocycleExactPathBridge
#check TypedResidual_posting_cocycle_bridge
#check certifiedRecipe_of_bridge
#check gap2PostingCocycleCarrierStatus_flags

#print axioms carrier_forgets_posting_phase
#print axioms postingPhase_not_factors_through_forget
#print axioms exact_carrier_forgets_posting_phase
#print axioms exact_postingPhase_not_factors_through_forget
#print axioms typedResidual_carrier_forgets_posting_phase
#print axioms gap2PostingCocycleCarrierStatus_flags
