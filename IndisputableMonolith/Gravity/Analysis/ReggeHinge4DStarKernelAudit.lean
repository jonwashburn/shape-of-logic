import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel

/-!
# Axiom audit for `ReggeHinge4DStarKernel`

Every public theorem must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel

#print axioms starMembers_length
#print axioms starMembers_complete
#print axioms star_cardinality
#print axioms cosDihedral_opp_flat
#print axioms cosDihedral_orth_flat
#print axioms arccos_one_div_sqrt_two
#print axioms star_flat_angle_sum_two_pi
#print axioms starFlatCosines_match_orbits
#print axioms hasDerivAt_opp_coord
#print axioms hasDerivAt_orth_coord
#print axioms oppDeficitKernel_eq_chain
#print axioms orthDeficitKernel_eq_chain
#print axioms fullStarClassKernel_eq
#print axioms fullStarClassKernel_values
#print axioms fullStarClassKernel_zero_off
#print axioms fullStarClassKernel_nonvacuous
#print axioms fullStarClassKernel_swap23
#print axioms fullStar_uniformScale_decoy
#print axioms fullStar_homothety_stationary
#print axioms hinge4DStarKernelStatus_flags
