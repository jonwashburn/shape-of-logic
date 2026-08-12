import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuum

/-!
# Axiom audit: Wave C2 R4 dynamic bracket shape continuum

Ledger name `dirac_algebra_continuum_limit` is held free pending HamDynN
binding repair. Audit the real rate-`h` / shape theorems.

Headline theorems must print within
`[propext, Classical.choice, Quot.sound]`.
-/

open IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuum

#check continuumWronskian
#check continuumMomentumFlux
#check continuumDiracDensity
#check sampledDynamicBracketSum
#check discrete_wronskian_mvt
#check wronskian_rate_h_tendsto
#check forward_diff_mvt
#check forward_density_uniform
#check dynamic_bracket_shape_continuum_limit
#check frozen_structure_differs_from_dynamic_id
#check frozen_continuum_density_differs_from_dynamic

#print axioms discrete_wronskian_mvt
#print axioms wronskian_rate_h_tendsto
#print axioms forward_diff_mvt
#print axioms forward_density_uniform
#print axioms dynamic_bracket_shape_continuum_limit
#print axioms frozen_structure_differs_from_dynamic_id
#print axioms frozen_continuum_density_differs_from_dynamic
