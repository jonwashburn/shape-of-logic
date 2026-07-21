import IndisputableMonolith.Gravity.Analysis.Regge4DAlgebraicCloser

/-!
Axiom / honesty audit for `Regge4DAlgebraicCloser`.
Expected footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DAlgebraicCloserAudit

open Regge4DAlgebraicCloser

#print axioms decoy_one_orbit_m2_ne_eh_coefficient
#print axioms plus_normalized_isTTPolarization
#print axioms cross_normalized_isTTPolarization
#print axioms tt_witnesses_nonvacuous
#print axioms gauge_m2Symbol_vanishes_on_decoy
#print axioms one_orbit_m2Symbol_axis_ne_zero
#print axioms eh_tt_coefficient_eq
#print axioms fullMomentZeroMomentum_eq_trueWeight
#print axioms fullMomentZeroMomentum_eq_bilinear
#print axioms fullMomentZeroMomentum_axisTTPlus
#print axioms fullMomentZeroMomentum_decoyGauge
#print axioms fullMomentZeroMomentum_decoyTrace
#print axioms fullMomentOrbitContribution_axisTTPlus
#print axioms fullMomentOrbitContribution_decoyGauge
#print axioms fullTTIsotropyTarget_mentions_eh_coefficient
#print axioms regge4DAlgebraicCloserStatus_flags
#print axioms banked_does_not_flip_gap_or_isotropy

end Regge4DAlgebraicCloserAudit
end Analysis
end Gravity
end IndisputableMonolith
