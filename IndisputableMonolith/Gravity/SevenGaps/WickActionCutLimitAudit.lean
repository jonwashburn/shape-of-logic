import IndisputableMonolith.Gravity.SevenGaps.WickActionCutLimit

/-!
# Axiom audit: Wave C4 N4 WickActionCutLimit

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge

#check csqrt_of_im_neg
#check tendsto_pentHingeCosPath_one
#check tendsto_csqrt_sq_sub_one_one
#check eventually_carccos_log_arg_eq
#check eventually_im_log_arg_nonneg
#check carccos_tendsto_at_cut_one_holds
#check carccos_tendsto_at_cut_one_inhabited
#check lorentzAnchor_one_holds
#check lorentzAnchor_one_inhabited
#check wickActionCutLimitStatus_flags

#print axioms csqrt_of_im_neg
#print axioms tendsto_pentHingeCosPath_one
#print axioms tendsto_csqrt_sq_sub_one_one
#print axioms carccos_tendsto_at_cut_one_holds
#print axioms lorentzAnchor_one_holds
#print axioms wickActionCutLimitStatus_flags
