import IndisputableMonolith.Gravity.Analysis.ContinuumTTSecondVariation4D
import IndisputableMonolith.Gravity.Analysis.ReggeNormalizationDerived4D

/-!
# Axiom audit: arc 2 step 7

Every named theorem of `ContinuumTTSecondVariation4D` (the continuum derivation)
and `ReggeNormalizationDerived4D` (the comparison and the pinning of Regge's
constant) must report exactly `[propext, Classical.choice, Quot.sound]`.

The banked dictionary identity this step compares against is audited here too,
so a reader can see the whole chain in one log.

Reminder (`institute-identity.mdc`): the base triple is a claim about postulates,
not about prior structure.  The ambient theory still supplies the universe
hierarchy, inductive types, recursors, function types, definitional equality, and
`Decidable` instances.
-/

namespace IndisputableMonolith.Gravity.Analysis.ReggeNormalizationDerived4DAudit

open ContinuumTTSecondVariation4D
open ReggeNormalizationDerived4D

/-! ## §1. The continuum derivation -/

#print axioms ContinuumTTSecondVariation4D.phase_update
#print axioms ContinuumTTSecondVariation4D.hasDerivAt_phase_update
#print axioms ContinuumTTSecondVariation4D.phase_update_self
#print axioms ContinuumTTSecondVariation4D.pd_cos
#print axioms ContinuumTTSecondVariation4D.pd_sin
#print axioms ContinuumTTSecondVariation4D.linChristoffel_eq
#print axioms ContinuumTTSecondVariation4D.linRicci_eq
#print axioms ContinuumTTSecondVariation4D.sum_k_mul_row
#print axioms ContinuumTTSecondVariation4D.sum_k_chrAmp
#print axioms ContinuumTTSecondVariation4D.sum_chrAmp_trace
#print axioms ContinuumTTSecondVariation4D.ricciAmp_tt
#print axioms ContinuumTTSecondVariation4D.linRicci_tt
#print axioms ContinuumTTSecondVariation4D.linRicciScalar_tt
#print axioms ContinuumTTSecondVariation4D.linEinstein_tt
#print axioms ContinuumTTSecondVariation4D.ehSecondVariationDensity_tt
#print axioms ContinuumTTSecondVariation4D.phaseAverage_const_mul
#print axioms ContinuumTTSecondVariation4D.phaseAverage_cos_sq
#print axioms ContinuumTTSecondVariation4D.density_factors_through_phase
#print axioms ContinuumTTSecondVariation4D.ehFace_eq_phaseAverage
#print axioms ContinuumTTSecondVariation4D.ehFace_eq_average_of_density
#print axioms ContinuumTTSecondVariation4D.ehFace_rigid

/-! ## §2. The comparison, the pinning, and the discrimination -/

#print axioms ReggeNormalizationDerived4D.frobSq_eq
#print axioms ReggeNormalizationDerived4D.momentumSq_eq
#print axioms ReggeNormalizationDerived4D.reggeFace_eq
#print axioms ReggeNormalizationDerived4D.reggeFace_eq_dictionary
#print axioms ReggeNormalizationDerived4D.regge_normalization_pinned
#print axioms ReggeNormalizationDerived4D.frobeniusNormSq_axisTTPlus
#print axioms ReggeNormalizationDerived4D.waveNormSq_axisWave
#print axioms ReggeNormalizationDerived4D.witness_nonzero
#print axioms ReggeNormalizationDerived4D.dictionary_witness_value
#print axioms ReggeNormalizationDerived4D.rho_one_fails
#print axioms ReggeNormalizationDerived4D.rho_pinned_at_witness

/-! ## §3. A4 checked in two dimensions -/

#print axioms ReggeNormalizationDerived4D.tetrahedron_deficit_sum
#print axioms ReggeNormalizationDerived4D.octahedron_deficit_sum
#print axioms ReggeNormalizationDerived4D.regge_constant_from_gauss_bonnet
#print axioms ReggeNormalizationDerived4D.gauss_bonnet_refutes_rho_one

/-! ## §4. The second route -/

#print axioms ReggeNormalizationDerived4D.phaseAverage_sin_sq
#print axioms ReggeNormalizationDerived4D.lagrangian_route_same_face
#print axioms ReggeNormalizationDerived4D.two_routes_differ_pointwise

/-! ## §5. What the tree's constants are -/

#print axioms ReggeNormalizationDerived4D.discreteBookkeepingFactor_is_inverse_regge
#print axioms ReggeNormalizationDerived4D.frozen_preflight_is_the_eh_integral_face
#print axioms ReggeNormalizationDerived4D.exact_unit_coefficient_is_the_regge_face

/-! ## §6. The composite certificate and the discriminating gate -/

#print axioms ReggeNormalizationDerived4D.normalizationGateDischarged
#print axioms ReggeNormalizationDerived4D.step7Cert

/-! ## §7. The banked identity being compared against -/

#print axioms
  IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D.exactMidpointBlochM2_eq_neg_eighth_frobenius_tt

end IndisputableMonolith.Gravity.Analysis.ReggeNormalizationDerived4DAudit
