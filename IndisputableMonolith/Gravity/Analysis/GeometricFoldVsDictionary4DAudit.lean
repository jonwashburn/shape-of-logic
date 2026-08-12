import IndisputableMonolith.Gravity.Analysis.GeometricFoldVsDictionary4D
import IndisputableMonolith.Gravity.Analysis.SRSConvergesScope4D

/-!
# Axiom audit: arc 2 step 8

Every declaration of `GeometricFoldVsDictionary4D` printed here.  Expected axiom
set throughout is the base triple `[propext, Classical.choice, Quot.sound]`.

The dictionary side descends from `exactMidpointBlochM2_eq_neg_eighth_frobenius_tt`,
whose coefficient-table certificates are kernel-lifted from banked `Int` `decide`
chunks with no `native_decide`.  The geometric side descends from the edge-origin
`decide` certificates over `Fin 24 × Fin 10`, also kernel-checked.  Neither side
introduces a new axiom, so a clean triple here is a statement about postulates
only: the ambient theory still supplies the universe hierarchy, inductive types
and their recursors, function and dependent types, definitional reduction, and
the `Decidable` instances the `decide` calls consume.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace GeometricFoldVsDictionary4D

#print axioms frobId_axisTTPlus
#print axioms frobId_axisTTCross
#print axioms waveId_symbolDir
#print axioms axisTTPlus_isTT_symbolDir
#print axioms axisTTCross_isTT_symbolDir
#print axioms dict_m2_axisTTPlus_symbolDir
#print axioms dict_m2_axisTTCross_symbolDir
#print axioms geom_m2_axisTTPlus_symbolDir
#print axioms geom_m2_axisTTCross_symbolDir
#print axioms geom_m2_decoyGauge_symbolDir
#print axioms geom_ne_dict_axisTTPlus
#print axioms geom_ne_dict_axisTTCross
#print axioms dict_eq_two_geom_axisTTPlus
#print axioms dict_eq_two_geom_axisTTCross
#print axioms factor_pinned_axisTTPlus
#print axioms factor_pinned_axisTTCross
#print axioms factor_one_fails
#print axioms factor_four_fails
#print axioms doubled_fold_is_the_named_object
#print axioms two_distinct_bookkeeping_factors
#print axioms ehFace_axisTTPlus_symbolDir
#print axioms ehFace_eq_four_times_geom
#print axioms reggeFace_between
#print axioms vanishing_witness_admits_every_factor
#print axioms decoyGauge_admits_every_factor
#print axioms tt_witness_is_informative
#print axioms banked_coefficient_is_not_the_certificate_value
#print axioms the_numerals_coincide
#print axioms foldTimesTwoEqDictionaryAtBankedWitnesses_holds
#print axioms foldDictionaryFactorDischarged_holds
#print axioms convergenceReachesDictionaryNotTheHingeMoment_holds

/-- Audit package: the discriminating gate holds and the two refutations that make
it discriminating are both present. -/
theorem step8_audit_package :
    FoldDictionaryFactorDischarged ∧
      ConvergenceReachesDictionaryNotTheHingeMoment :=
  ⟨foldDictionaryFactorDischarged_holds,
    convergenceReachesDictionaryNotTheHingeMoment_holds⟩

#print axioms step8_audit_package

end GeometricFoldVsDictionary4D

namespace SRSConvergesScope4D

#print axioms srs_limit_value
#print axioms eh_face_value
#print axioms srs_limit_is_regge_normalization_times_eh
#print axioms srs_limit_ne_eh_face
#print axioms mesh_sequence_does_not_converge_to_eh_face
#print axioms mesh_sequence_converges_to_the_regge_face
#print axioms R1_fails_if_the_moments_read_their_symbols
#print axioms the_collision_is_real
#print axioms step8ScopedVerdict_holds

end SRSConvergesScope4D
end Analysis
end Gravity
end IndisputableMonolith
