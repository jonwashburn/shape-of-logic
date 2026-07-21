import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D

/-!
# Axiom audit: `EdgeTTDecomposition4D`

`#print axioms` for every public theorem of the algebraic 4D TT
decomposition layer.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D

#print axioms gaugePart_symmetric
#print axioms outerSq_symmetric
#print axioms transverseProjector_symmetric
#print axioms load_gaugePart
#print axioms load_smul
#print axioms load_sub
#print axioms load_one
#print axioms load_outerSq
#print axioms load_transverseProjector
#print axioms dot_gaugeVector
#print axioms load_gaugePart_gaugeVector
#print axioms gaugeCorrected_transverse
#print axioms gaugeCorrected_symmetric
#print axioms euclideanTrace_smul
#print axioms euclideanTrace_sub
#print axioms euclideanTrace_one
#print axioms euclideanTrace_outerSq
#print axioms euclideanTrace_transverseProjector
#print axioms ttProject_symmetric
#print axioms ttProject_transverse
#print axioms ttProject_traceless
#print axioms ttProject_isTT
#print axioms exists_edgeTTDecomposition
#print axioms exists_edgeTTDecomposition'
#print axioms axisWave_momentumSq
#print axioms axisTTPlus_isTT
#print axioms axisTTCross_isTT
#print axioms axisTTPlus_ne_zero
#print axioms axisTTCross_ne_zero
#print axioms axisTT_independent
#print axioms decoyLongitudinal_symmetric
#print axioms decoyLongitudinal_not_transverse
#print axioms decoy_ttProject_isTT
#print axioms decoy_projection_restores_transverse
#print axioms zero_wave_momentumSq
#print axioms decomposition_hypothesis_fails_at_zero
