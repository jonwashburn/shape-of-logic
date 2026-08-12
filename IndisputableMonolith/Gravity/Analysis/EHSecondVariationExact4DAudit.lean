import IndisputableMonolith.Gravity.Analysis.EHSecondVariationExact4D

/-!
# Axiom audit for `EHSecondVariationExact4D`

Every named result, one `#print axioms` each.  Expected footprint for all of them
is `[propext, Classical.choice, Quot.sound]`, and the base-triple reading is a
claim about postulates only: the ambient theory still supplies the universe
hierarchy, inductive types, function types, equality and definitional reduction.

Check the output with a parser that joins wrapped lines
(`holography/scratch/audit_check.py`), because long axiom lists wrap.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace EHSecondVariationExact4DAudit

open EHSecondVariationExact4D

#print axioms phaseAverage_const
#print axioms phaseAverage_sin_sq
#print axioms phaseAverage_sin_sq_affine
#print axioms exactDensityTT_average
#print axioms exactDensityTrace_average
#print axioms exactDensityLongitudinal_average
#print axioms exact_average_eq_ehFace
#print axioms a3_agrees_with_exact
#print axioms trace_decoy_misses_the_face
#print axioms longitudinal_decoy_misses_the_face
#print axioms exact_density_rigid

end EHSecondVariationExact4DAudit
end Analysis
end Gravity
end IndisputableMonolith
