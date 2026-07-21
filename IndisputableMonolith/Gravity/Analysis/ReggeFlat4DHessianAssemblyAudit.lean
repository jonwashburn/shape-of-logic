import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly

/-!
# Axiom audit for `ReggeFlat4DHessianAssembly`

Every public theorem must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly

#print axioms hasDerivAt_heronSq_a
#print axioms hasDerivAt_heronSq_b
#print axioms hasDerivAt_heronSq_c
#print axioms hasDerivAt_hingeArea_a
#print axioms hasDerivAt_hingeArea_b
#print axioms hasDerivAt_hingeArea_c
#print axioms heronSq_t11
#print axioms heronSq_t12
#print axioms heronSq_t13
#print axioms heronSq_t22
#print axioms hingeArea_t11
#print axioms hingeArea_t12
#print axioms hingeArea_t13
#print axioms hingeArea_t22
#print axioms areaGradA_t11
#print axioms areaGradB_t11
#print axioms areaGradC_t11
#print axioms areaGradA_t12
#print axioms areaGradB_t12
#print axioms areaGradC_t12
#print axioms areaGradA_t13
#print axioms areaGradB_t13
#print axioms areaGradC_t13
#print axioms areaGradA_t22
#print axioms areaGradB_t22
#print axioms areaGradC_t22
#print axioms hasDerivAt_area_t11_a
#print axioms hasDerivAt_area_t11_b
#print axioms hasDerivAt_area_t11_c
#print axioms hasDerivAt_area_t12_a
#print axioms hasDerivAt_area_t12_b
#print axioms hasDerivAt_area_t12_c
#print axioms hasDerivAt_area_t13_a
#print axioms hasDerivAt_area_t13_b
#print axioms hasDerivAt_area_t13_c
#print axioms hasDerivAt_area_t22_a
#print axioms hasDerivAt_area_t22_b
#print axioms hasDerivAt_area_t22_c
#print axioms complement_preserves_edge_mask
#print axioms kernel21_eq_kernel12
#print axioms kernel31_eq_kernel13
#print axioms complement_swaps_type_reexport
#print axioms areaCov11_eq_grads
#print axioms areaCov12_eq_grads
#print axioms areaCov22_eq_grads
#print axioms orbitCellCount_eq_classification
#print axioms classDot_add
#print axioms classDot_smul
#print axioms orbitZeroMomQuadratic_eq_bilinear
#print axioms trueWeightZeroMomQuadratic_eq_bilinear
#print axioms trueWeightZeroMomBilinear_symm
#print axioms trueWeightZeroMomBilinear_add_left
#print axioms trueWeightZeroMomBilinear_smul_left
#print axioms trueWeightZeroMomQuadratic_add
#print axioms classCoeff_axisTTPlus_int
#print axioms classCoeff_decoyGauge_bit
#print axioms kernel11_eq_sign
#print axioms kernel12_eq_sign
#print axioms kernel13_eq_sign
#print axioms kernel22_eq_sign
#print axioms signDotAxis_kernel11
#print axioms signDotAxis_kernel12
#print axioms signDotAxis_kernel13
#print axioms signDotAxis_kernel22
#print axioms signDotGauge_kernel11
#print axioms signDotGauge_kernel12
#print axioms signDotGauge_kernel13
#print axioms signDotGauge_kernel22
#print axioms deficitKernel11_dot_axisTTPlus
#print axioms deficitKernel12_dot_axisTTPlus
#print axioms deficitKernel13_dot_axisTTPlus
#print axioms deficitKernel22_dot_axisTTPlus
#print axioms deficitKernel11_dot_decoyGauge
#print axioms deficitKernel12_dot_decoyGauge
#print axioms deficitKernel13_dot_decoyGauge
#print axioms deficitKernel22_dot_decoyGauge
#print axioms deficitKernel11_dot_decoyTrace
#print axioms deficitKernel12_dot_decoyTrace
#print axioms deficitKernel13_dot_decoyTrace
#print axioms deficitKernel22_dot_decoyTrace
#print axioms deficitKernel11_dot_homothety
#print axioms deficitKernel12_dot_homothety
#print axioms deficitKernel13_dot_homothety
#print axioms deficitKernel22_dot_homothety
#print axioms orbitDeficit_dot_axisTTPlus
#print axioms orbitDeficit_dot_decoyGauge
#print axioms orbitDeficit_dot_decoyTrace
#print axioms trueWeightZeroMomQuadratic_axisTTPlus
#print axioms trueWeightZeroMomQuadratic_decoyGauge
#print axioms trueWeightZeroMomQuadratic_decoyTrace
#print axioms trueWeightZeroMomQuadratic_homothety
#print axioms trueWeight_kills_gauge_at_zero_momentum
#print axioms flat4DHessianAssemblyStatus_flags
