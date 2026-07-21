import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel

/-!
# Axiom audit: `ReggeHinge4DFlatKernel`

`#print axioms` for every public theorem of the 4D Freudenthal hinge
incidence / flat-Hessian assembly skeleton.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel

#print axioms vertexMask_start
#print axioms vertexMask_end
#print axioms localEdgeMask_bounds
#print axioms localEdgeClass_mask
#print axioms permOf_eq_of_eq
#print axioms containsSeedHinge_iff
#print axioms seedHinge_simplex_count
#print axioms seedHinge_simplices
#print axioms simplex0Classes_correct
#print axioms simplex1Classes_correct
#print axioms simplex0Classes_complete
#print axioms simplex1Classes_complete
#print axioms seedHingeIncidenceNat_values
#print axioms sum_seedHingeIncidenceNat
#print axioms seedHingeIncidence_nonvacuous
#print axioms swap23Mask_bounds
#print axioms seedHingeIncidence_swap23
#print axioms seedHingeIncidence_decoy_zero
#print axioms hingeBoundary_incidence_pos
#print axioms simplex_class_count
#print axioms cell_covers_all_classes
#print axioms seedOrbitAssembly_decoy_area
#print axioms seedOrbitAssembly_support_projection
#print axioms hinge4DFlatKernelStatus_flags
