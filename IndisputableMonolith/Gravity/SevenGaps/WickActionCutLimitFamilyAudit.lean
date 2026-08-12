import IndisputableMonolith.Gravity.SevenGaps.WickActionCutLimitFamily

/-!
# Axiom audit: Wave C4 F1 WickActionCutLimitFamily

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge

#check lorentzK_gt_one
#check lorentzCos_eq_neg_lorentzK
#check rapidityPinned_of_causal
#check tendsto_pentHingeCosPath_of_causal
#check tendsto_csqrt_sq_sub_one_of_causal
#check eventually_carccos_log_arg_eq_of_causal
#check eventually_im_log_arg_nonneg_of_causal
#check carccos_tendsto_at_cut_of_causal
#check carccos_tendsto_at_cut_family_holds
#check lorentzAnchor_of_causal
#check continuousOn_wickActionPath_Ioc_of_causal
#check wickActionCutLimitFamilyStatus_flags

#print axioms rapidityPinned_of_causal
#print axioms carccos_tendsto_at_cut_of_causal
#print axioms lorentzAnchor_of_causal
#print axioms continuousOn_wickActionPath_Ioc_of_causal
#print axioms carccos_tendsto_at_cut_family_holds
#print axioms wickActionCutLimitFamilyStatus_flags
