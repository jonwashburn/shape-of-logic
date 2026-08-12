import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHingeConfinement

/-!
# Axiom audit: Wave C4 N3 (+ N4 fallback) WickActionInteriorHingeConfinement

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge

#check pentHingeCosPath_eq_moebius
#check pentHingeCosPath_eq_euclidCos
#check pentHingeCosPath_eq_lorentzCos
#check im_pentHingeCosPath_neg
#check branchRegularSum_of_causal
#check branchRegularSum_one
#check carccos_tendsto_at_cut_one
#check carccos_tendsto_at_cut_family
#check lorentzAnchor_one
#check rapidityPinned_one
#check lorentz_endpoint_not_real
#check wickActionInteriorHingeStatus_flags

#print axioms pentHingeCosPath_eq_moebius
#print axioms im_pentHingeCosPath_neg
#print axioms branchRegularSum_one
#print axioms rapidityPinned_one
#print axioms lorentz_endpoint_not_real
#print axioms wickActionInteriorHingeStatus_flags
