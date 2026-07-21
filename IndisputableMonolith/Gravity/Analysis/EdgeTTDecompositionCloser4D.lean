import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeTTAttachment4D

/-!
# Named closer: `edge_tt_decomposition`

Inhabits the preflight Prop `edge_tt_decomposition` by composing:
1. algebraic TT decomposition (`exists_edgeTTDecomposition`);
2. Frobenius-normalized plus/cross witnesses;
3. pure-gauge non-transverse decoy;
4. plane-wave edge attachment already proved in `ReggeEdgeTTAttachment4D`.

Honest scope: this is the ledger algebraic+attachment layer for the named
closer.  Full multi-orbit true-weight continuum recovery remains the
`S_RS_converges_EH_4d` gate.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace EdgeTTDecompositionCloser4D

open Regge4DContinuumPreflight
open EdgeTTDecomposition4D
open ReggeEdgeStencil4D

noncomputable section

theorem decoyGauge_eq_decoyLongitudinal : decoyGauge = decoyLongitudinal := by
  unfold decoyGauge decoyLongitudinal axisGaugeVector
  funext i j
  fin_cases i <;> fin_cases j <;> simp [gaugePart, axisWave]

theorem decoyGauge_not_transverse :
    ¬ IsTransverse axisWave decoyGauge := by
  rw [decoyGauge_eq_decoyLongitudinal]
  exact decoyLongitudinal_not_transverse

/-- **THEOREM (named ledger closer, algebraic+attachment layer).** -/
theorem edge_tt_decomposition :
    Regge4DContinuumPreflight.edge_tt_decomposition := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m H hH hm
    have hm' : momentumSq m ≠ 0 := by
      simpa [waveNormSq_eq_momentumSq] using hm
    exact exists_edgeTTDecomposition m H hH hm'
  · exact axisTTPlusNormalized_isTTPolarization
  · exact axisTTCrossNormalized_isTTPolarization
  · exact decoyGauge_not_transverse

theorem edge_tt_decomposition_holds :
    Regge4DContinuumPreflight.edge_tt_decomposition :=
  edge_tt_decomposition

end

end EdgeTTDecompositionCloser4D
end Analysis
end Gravity
end IndisputableMonolith
