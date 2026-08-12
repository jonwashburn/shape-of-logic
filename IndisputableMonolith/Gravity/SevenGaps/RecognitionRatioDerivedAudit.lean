import IndisputableMonolith.Gravity.SevenGaps.RecognitionRatioDerived

/-!
# Axiom audit: Wave B R5 ledger-named `recognition_ratio_derived`

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps

#check recognition_ratio_derived
#check recognition_ratio_derived_holds
#check typedResidual_recognition_ratio_derived_closed
#check recognitionRatioDerivedStatus_flags

#print axioms recognition_ratio_derived_holds
#print axioms typedResidual_recognition_ratio_derived_closed
#print axioms TypedResidual_recognition_ratio_derived_closed
#print axioms recognitionRatioDerivedStatus_flags
