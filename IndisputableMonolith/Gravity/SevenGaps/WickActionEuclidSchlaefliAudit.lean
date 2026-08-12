import IndisputableMonolith.Gravity.SevenGaps.WickActionEuclidSchlaefli

/-!
# Axiom audit: Wave C4 R4 WickActionEuclidSchlaefli

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check euclidCos_mem_Ioo
#check hasDerivAt_euclidCos
#check hasDerivAt_euclidArea
#check euclidAngleDeriv
#check hasDerivAt_euclidAngle
#check wickActionPath_re_eq_euclidRegge
#check hasDerivAt_euclidAngleWeightedArea
#check euclid_angle_deriv_term_ne_zero_at_one
#check euclidSchlaefli_holds
#check euclidSchlaefli_field_inhabited
#check euclidSchlaefli_field_inhabited_one
#check wickActionEuclidSchlaefliStatus_flags

#print axioms euclidCos_mem_Ioo
#print axioms hasDerivAt_euclidCos
#print axioms hasDerivAt_euclidAngle
#print axioms euclidSchlaefli_holds
#print axioms euclidSchlaefli_field_inhabited
#print axioms euclid_angle_deriv_term_ne_zero_at_one
#print axioms wickActionEuclidSchlaefliStatus_flags
