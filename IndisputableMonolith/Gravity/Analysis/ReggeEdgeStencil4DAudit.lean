import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Axiom audit: `ReggeEdgeStencil4D`

`#print axioms` for every public theorem of the 4D Regge edge-stencil /
provisional finite-quadratic layer.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

#print axioms classWeightNat_pos
#print axioms classDisp_ne_zero
#print axioms classDispSq_eq_weight
#print axioms classCoeff_add
#print axioms classCoeff_smul
#print axioms classCoeff_neg
#print axioms classCoeff_sub
#print axioms planeWaveClassPert_add
#print axioms planeWaveClassPert_smul
#print axioms finiteTTQuadratic_eq_bilinear
#print axioms finiteTTBilinear_symm
#print axioms finiteTTBilinear_add_left
#print axioms finiteTTBilinear_smul_left
#print axioms finiteTTQuadratic_add
#print axioms finiteTTQuadratic_smul
#print axioms finiteTTQuadratic_neg
#print axioms classCoeff_gaugePart
#print axioms finiteTTQuadratic_gaugePart
#print axioms classCoeff_gaugePart_axis
#print axioms sum_hasBit0
#print axioms finiteTTQuadratic_gaugePart_axisWave
#print axioms finiteTTQuadratic_gaugePart_axisWave_ne_zero
#print axioms classCoeff_axisTTPlus
#print axioms classCoeff_axisTTPlus_sq
#print axioms sum_axisTTPlusSqNat
#print axioms finiteTTQuadratic_axisTTPlus
#print axioms finiteTTQuadratic_axisTTPlus_ne_zero
#print axioms finiteTTQuadratic_axisTTPlus_isTT_seed
#print axioms sum_crossNat
#print axioms finiteTTBilinear_axisTTPlus_gauge
#print axioms finiteTTQuadratic_not_gauge_invariant_on_axisTTPlus
#print axioms finiteTTQuadratic_decoyGauge
#print axioms classCoeff_decoyTrace
#print axioms classCoeff_decoyTrace_sq
#print axioms sum_weightSqNat
#print axioms finiteTTQuadratic_decoyTrace
#print axioms decoy_values_distinct
#print axioms classDisp_axis0
#print axioms classCoeff_axis0
#print axioms planeWaveClassPert_axis0
