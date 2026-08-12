import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuumBinding

/-!
# Axiom audit: Wave C2 R4 repaired Dirac algebra continuum limit

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuumBinding

#check sampledPhasePoint
#check sampledLapse
#check periodicSampledDynamicBracketSum
#check continuumLatticeBracket
#check bracket_HamDynN_eq_periodicSampled
#check periodicSampled_eq_sampled_of_periodic
#check dirac_algebra_continuum_limit
#check dirac_algebra_continuum_limit_hamDynN

#print axioms bracket_HamDynN_eq_periodicSampled
#print axioms periodicSampled_eq_sampled_of_periodic
#print axioms dirac_algebra_continuum_limit
#print axioms dirac_algebra_continuum_limit_hamDynN
