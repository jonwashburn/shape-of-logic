import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D

/-!
# Axiom audit for `ReggeBlochFold4D`

Every public theorem must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D

#print axioms phasedClassDot_add
#print axioms phasedClassDot_smul
#print axioms phasedClassDot_zeroMomentum
#print axioms isT11_iff_pop
#print axioms factorizedBlochFold11_zeroMomentum
#print axioms blochFold11_eq_bilinear
#print axioms blochFold11Bilinear_symm
#print axioms blochFold11Bilinear_add_left
#print axioms blochFold11Bilinear_smul_left
#print axioms transportedSlotTerm_zeroMomentum
#print axioms classCoeff_axisTTPlus_mask_1
#print axioms classCoeff_axisTTPlus_mask_2
#print axioms classCoeff_axisTTPlus_mask_3
#print axioms slotAreaCov_support
#print axioms phasedClassDot_area_axis_of_masks_1_2
#print axioms phasedClassDot_area_axis_of_masks_2_1
#print axioms transportedSlotTerm_axis_seedMasks
#print axioms axisStarKind_count1
#print axioms axisStarKind_count2
#print axioms gaugeStarKind_count1
#print axioms sum_axisStarContrib
#print axioms sum_gaugeStarContrib
#print axioms classMidpointPhase_waveStar
#print axioms cos_quarterTurns
#print axioms phasedClassDot_transportedDeficit
#print axioms phasedA_waveStar
#print axioms phasedK_waveStar
#print axioms transportedSlotTerm_waveStar_eval
#print axioms slotN_axis_match
#print axioms slotN_gauge_match
#print axioms classCoeff_decoyGauge_int
#print axioms transportedSlotTerm_axis_waveStar
#print axioms transportedSlotTerm_gauge_waveStar
#print axioms blochFold11_axisTTPlus_waveStar
#print axioms blochFold11_axisTTPlus_waveStar_ne_zero
#print axioms blochFold11_decoyGauge_waveStar
#print axioms blochFold11_decoyGauge_waveStar_ne_zero
#print axioms blochFold4DStatus_flags
