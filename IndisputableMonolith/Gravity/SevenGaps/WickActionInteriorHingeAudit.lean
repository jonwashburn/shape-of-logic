import IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge

/-!
# Axiom audit: Wave C4 R2 WickActionInteriorHinge (schema + N1/N2)

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.WickActionInteriorHinge
open IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger

#check carccos
#check pentHingeCosPath
#check dihedralSumPath
#check hingeArea
#check wickActionPath
#check euclidCos
#check lorentzCos
#check lorentzRapidity
#check lorentzAngleRe
#check euclidArea
#check euclidAngle
#check WickActionContinuationCert
#check wick_action_continuation_4d
#check offArccosCut_slitPlane
#check continuousOn_carccos
#check carccos_real_eq_arccos
#check wickActionInteriorHingeStatus_flags

#print axioms offArccosCut_slitPlane
#print axioms continuousOn_carccos
#print axioms carccos_real_eq_arccos
#print axioms wickActionInteriorHingeStatus_flags
