import IndisputableMonolith.Gravity.Analysis.RecognitionMeshHingeKappa4D

/-!
# Axiom audit: RecognitionMeshHingeKappa4D (Wave B R2)

Closure theorem and decoys must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.RecognitionMeshHingeKappa4D

#check TypedResidual_hinge_kappa_identified
#check typedResidual_hinge_kappa_identified_closed
#check meshHingeKappa
#check meshHingeKappa_source_dominated
#check decoy_zero_kappa_fails_nontrivial
#check decoy_log_ratio_over_deficit_ne_meshHingeKappa
#check adversarial_decoys_hinge_kappa
#check recognitionMeshHingeKappa4DStatus_flags

#print axioms typedResidual_hinge_kappa_identified_closed
#print axioms TypedResidual_hinge_kappa_identified_closed
#print axioms meshHingeKappa_source_dominated
#print axioms meshGeometricDeficit_abs_le_two_pi
#print axioms abs_arcsin_le_pi_div_two
#print axioms decoy_zero_kappa_fails_nontrivial
#print axioms decoy_log_ratio_over_deficit_ne_meshHingeKappa
#print axioms adversarial_decoys_hinge_kappa
#print axioms recognitionMeshHingeKappa4DStatus_flags
