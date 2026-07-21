import IndisputableMonolith.Gravity.Analysis.EdgeTTDecompositionLorentz4D

/-!
# Axiom audit: `EdgeTTDecompositionLorentz4D`

`#print axioms` for every public theorem of the Lorentzian algebraic 4D TT
decomposition layer.  Expected footprint:
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.Analysis.EdgeTTDecompositionLorentz4D

#print axioms lorentzLoad_eq
#print axioms IsLorentzTransverse_iff_lorentzLoad
#print axioms minkowskiDot_eq_sum
#print axioms minkowskiDot_comm
#print axioms minkowskiTrace_eq_sum
#print axioms gaugePart_symmetric
#print axioms outerSq_symmetric
#print axioms symmetrizedOuter_symmetric
#print axioms raise_raise
#print axioms lorentzLoad_smul
#print axioms lorentzLoad_sub
#print axioms lorentzLoad_eta
#print axioms lorentzLoad_outerSq
#print axioms lorentzLoad_symmetrizedOuter
#print axioms lorentzLoad_symmetrizedOuter_l
#print axioms lorentzLoad_gaugePart
#print axioms minkowskiTrace_smul
#print axioms minkowskiTrace_sub
#print axioms minkowskiTrace_add
#print axioms minkowskiTrace_eta
#print axioms minkowskiTrace_outerSq
#print axioms minkowskiTrace_symmetrizedOuter
#print axioms minkowskiDot_eq_MinkowskiNull
#print axioms minkowskiEta_symmetric
#print axioms transverseProjector_symmetric
#print axioms lorentzLoad_transverseProjector
#print axioms minkowskiDot_gaugeVector
#print axioms lorentzLoad_gaugePart_gaugeVector
#print axioms gaugeCorrected_transverse
#print axioms gaugeCorrected_symmetric
#print axioms minkowskiTrace_transverseProjector
#print axioms ttProject_symmetric
#print axioms ttProject_transverse
#print axioms ttProject_traceless
#print axioms ttProject_isLorentzTT
#print axioms exists_lorentzTTDecomposition
#print axioms exists_lorentzTTDecomposition'
#print axioms nullProjector_symmetric
#print axioms nullProjector_minkowskiTrace
#print axioms lorentzLoad_nullProjector_m
#print axioms lorentzLoad_nullProjector_l
#print axioms sum_kron_left
#print axioms sum_kron_right
#print axioms nullPhp_expand_algebra
#print axioms sum_kron_H_kron
#print axioms sum_S_H_kron
#print axioms sum_kron_H_S
#print axioms nullPhp_entry
#print axioms sum_nullSMixed_H_col
#print axioms sum_H_nullSMixed_row
#print axioms nullGap_entry
#print axioms null_gap_expansion
#print axioms nullPhp_symmetric
#print axioms sum_nullSMixed_raise_m
#print axioms sum_nullPMixed_raise_m
#print axioms sum_nullSMixed_raise_l
#print axioms sum_nullPMixed_raise_l
#print axioms nullPhp_lorentzLoad_m
#print axioms nullPhp_transverse_m
#print axioms nullPhp_lorentzLoad_l
#print axioms nullPhp_transverse_l
#print axioms nullTTProject_symmetric
#print axioms nullTTProject_traceless
#print axioms nullTTProject_transverse_m
#print axioms nullTTProject_transverse_l
#print axioms nullTTProject_isLorentzTT
#print axioms exists_nullLorentzTTDecomposition
#print axioms nullAxisWave_dot
#print axioms nullAxisAux_dot
#print axioms nullAxis_cross_dot
#print axioms nullAxisWave_ne_zero
#print axioms nullAxis_MinkowskiNull
#print axioms nullAxisTTPlus_isLorentzTT
#print axioms nullAxisTTCross_isLorentzTT
#print axioms nullAxisTTPlus_ne_zero
#print axioms nullAxisTTCross_ne_zero
#print axioms nullAxisTT_independent
#print axioms nullAxis_euclideanMomentumSq
#print axioms lorentzLoad_one
#print axioms euclideanProjector_not_lorentzTransverse_on_nullAxis
#print axioms naive_lorentz_projector_hypothesis_fails_on_nullAxis
#print axioms zero_wave_minkowskiDot
#print axioms decomposition_hypothesis_fails_at_zero
