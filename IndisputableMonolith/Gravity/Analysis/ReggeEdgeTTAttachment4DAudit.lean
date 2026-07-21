import IndisputableMonolith.Gravity.Analysis.ReggeEdgeTTAttachment4D

/-!
# Axiom audit: `ReggeEdgeTTAttachment4D`

`#print axioms` for every public theorem of the 4D Regge edge TT
attachment layer.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.ReggeEdgeTTAttachment4D

#print axioms axisDisp_apply
#print axioms edgeLoad_axis
#print axioms edgeLoad_add
#print axioms edgeLoad_smul
#print axioms edgeLoad_neg
#print axioms edgeLoad_sub
#print axioms planeWaveAxisEdgePert_add
#print axioms planeWaveAxisEdgePert_smul
#print axioms edgeLoad_gaugePart
#print axioms edgeLoad_gaugePart_axis
#print axioms shiftAxis_dot
#print axioms sin_add_sub_sin
#print axioms discreteLieAxis_eq
#print axioms planeWaveAxisEdgePert_gaugePart
#print axioms planeWaveAxisEdgePert_gaugePart_eq_discreteLie
#print axioms edgeLoad_decomposition
#print axioms planeWaveAxisEdgePert_decomposition
#print axioms load_eq_zero_of_isTT
#print axioms gaugeVector_eq_zero_of_isTT
#print axioms gaugePart_zero
#print axioms gaugeCorrected_eq_of_isTT
#print axioms residualTrace_eq_zero_of_isTT
#print axioms ttProject_eq_of_isTT
#print axioms decoyTT_edgeLoad_axis2
#print axioms decoyTT_not_gaugeDiscreteLie_axis2
#print axioms decoyTT_isTT
#print axioms witness_isTT
#print axioms witness_momentumSq
#print axioms witness_ttProject_eq
#print axioms witness_edgeLoad_tt_ne_zero
#print axioms witness_tt_edge_ne_zero
