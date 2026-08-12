import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket

/-!
# Axiom audit: Wave C2 R0+R1 dynamic structure bracket

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
open IndisputableMonolith.Gravity.SevenGaps.DynamicStructureFunctionBlocker

#check TypedResidual_naive_dynamic_HamW_decoy_fails
#check bracket_HamDyn_HamDyn
#check typedResidual_dynamic_bracket_concrete_two_site
#check concreteDynamicHamiltonianConstruction
#check phaseSpaceDependentDiracPremise_two_site

#print axioms TypedResidual_naive_dynamic_HamW_decoy_fails
#print axioms bracket_HamDyn_HamDyn
#print axioms typedResidual_dynamic_bracket_concrete_two_site
#print axioms phaseSpaceDependentDiracPremise_two_site
