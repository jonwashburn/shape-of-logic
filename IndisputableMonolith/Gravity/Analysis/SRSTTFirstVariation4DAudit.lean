import IndisputableMonolith.Gravity.Analysis.SRSTTFirstVariation4D

/-!
# Audit: SRSTTFirstVariation4D

Public axiom audit for the Euclidean weak-field TT midpoint first-variation
increment. Expected: clean triple
`[propext, Classical.choice, Quot.sound]` on the headline, key derivatives,
and packaged certificate.
-/

open IndisputableMonolith.Gravity.Analysis.SRSTTFirstVariation4D

#check frobeniusPairing4D
#check exactMidpointBlochFirstVariation
#check exactMidpointBlochSymbol_line
#check hasDerivAt_exactMidpointBlochSymbol_line
#check exactMidpointBlochFirstVariation_polarization
#check continuumFace_polarization_eq_neg_quarter_frobenius
#check hasDerivAt_finiteExactMidpointBlochSymbol_normalized
#check continuumTTFirstVariation_closed
#check srsTTFirstVariation4D_cert

#print axioms hasDerivAt_exactMidpointBlochSymbol_line
#print axioms exactMidpointBlochFirstVariation_polarization
#print axioms continuumFace_polarization_eq_neg_quarter_frobenius
#print axioms hasDerivAt_finiteExactMidpointBlochSymbol_normalized
#print axioms continuumTTFirstVariation_closed
#print axioms srsTTFirstVariation4D_cert
