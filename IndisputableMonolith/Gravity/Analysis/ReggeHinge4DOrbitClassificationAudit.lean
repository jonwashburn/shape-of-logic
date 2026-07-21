import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification

/-!
# Axiom audit: `ReggeHinge4DOrbitClassification`

`#print axioms` for every public theorem of the 4D triangle-hinge orbit
classification.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification

#print axioms hingeTypePop_is_orbitType
#print axioms hingeOrbitType_toPop
#print axioms triangle_diff_masks_ok
#print axioms cellTriangleCount_t11
#print axioms cellTriangleCount_t12
#print axioms cellTriangleCount_t21
#print axioms cellTriangleCount_t13
#print axioms cellTriangleCount_t31
#print axioms cellTriangleCount_t22
#print axioms cellTriangleCount_values
#print axioms cellTriangleCount_sum
#print axioms oriented_slot_total
#print axioms disjoint_implies_realizable
#print axioms decoy_overlapping_not_realizable
#print axioms decoy_overlapping_is_not_disjoint
#print axioms seed_slot_masks
#print axioms seed_hinge_type_t11
#print axioms coordPerm_preserves_pop
#print axioms coordPerm_preserves_type
#print axioms orbitRep_realizable
#print axioms orbitRep_type
#print axioms realizable_in_type_orbit
#print axioms realizable_matches_rep_orbit
#print axioms complement_preserves_kuhn
#print axioms complement_swaps_diff_pair
#print axioms complement_swaps_type
#print axioms orbit_count_S4
#print axioms orbit_count_S4_complement
#print axioms absolute_t11_not_S4_transitive
#print axioms orbitLocalSq_values
#print axioms slot_localSq
#print axioms hinge4DOrbitClassificationStatus_flags
