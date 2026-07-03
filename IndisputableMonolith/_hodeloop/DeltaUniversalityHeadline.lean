import IndisputableMonolith.Mathematics.HodgeDeltaBridge.RefereeGradeClosure

namespace IndisputableMonolith._hodeloop

open IndisputableMonolith.Mathematics.HodgeDeltaBridge

universe u

/-- Referee-grade Hodge is reduced to δ-Hodge universality (the honest headline). -/
theorem hodge_loop_delta_universality_headline
    (hδ : DeltaHodgeUniversality.{u}) :
    hodge_conjecture_unconditional_referee_grade.{u} :=
  referee_grade_hodge_reduced_to_delta_universality hδ

end IndisputableMonolith._hodeloop
