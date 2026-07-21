import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel13

/-!
# Axiom audit for `ReggeHinge4DStarKernel13`

Under the worktree shared-`.lake` symlink, `lake build` may no-op and new
modules do not emit oleans.  The binding axiom audit is therefore the
`#print axioms` block at the end of
`ReggeHinge4DStarKernel13.lean`, verified by

```
lake env lean IndisputableMonolith/Gravity/Analysis/ReggeHinge4DStarKernel13.lean
```

Every public theorem must print within
`[propext, Classical.choice, Quot.sound]`.

When an olean is available (non-symlink build), the block below is the
standalone audit surface.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel13

#print axioms cubeContainsHinge_origin
#print axioms star_cube_cardinality
#print axioms only_origin_contains_hinge
#print axioms starMembers_length
#print axioms starMembers_complete
#print axioms star_cardinality
#print axioms cosDihedral_t13_flat
#print axioms arccos_one_half
#print axioms star_flat_angle_sum_two_pi
#print axioms starFlatCosines_match
#print axioms hasDerivAt_t13_coord
#print axioms chainT13_eq
#print axioms t13DeficitKernel_eq_chain
#print axioms swap12Class_eq_table
#print axioms fullStarClassKernel_eq
#print axioms fullStarClassKernel_values
#print axioms fullStarClassKernel_zero_off
#print axioms fullStarClassKernel_nonvacuous
#print axioms fullStarClassKernel_swap12
#print axioms fullStar_uniformScale_decoy
#print axioms fullStar_homothety_stationary
#print axioms hinge4DStarKernel13Status_flags
