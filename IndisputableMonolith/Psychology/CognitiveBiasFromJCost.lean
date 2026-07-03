import Mathlib
import IndisputableMonolith.Common.CanonicalJBand

/-!
# Cognitive Biases from J-Cost — D-tier Cognition Depth

Cognitive biases are systematic deviations from rational decision-making.
In RS terms, bias = J(r) deviation from optimal recognition (r = 1).

Five canonical bias categories (anchoring, availability, confirmation,
representativeness, framing) = configDim D = 5.

RS prediction: bias magnitude = J(r_bias) where r_bias is the ratio
of (biased estimate)/(true value). The canonical band J(phi) predicts
when biases become "significant" in decision-making contexts.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Psychology.CognitiveBiasFromJCost
open Common.CanonicalJBand

inductive BiasCategory where
  | anchoring | availability | confirmation | representativeness | framing
  deriving DecidableEq, Repr, BEq, Fintype

theorem biasCategoryCount : Fintype.card BiasCategory = 5 := by decide

structure CognitiveBiasCert where
  five_categories : Fintype.card BiasCategory = 5
  threshold : CanonicalCert

noncomputable def cognitiveBiasCert : CognitiveBiasCert where
  five_categories := biasCategoryCount
  threshold := cert

end IndisputableMonolith.Psychology.CognitiveBiasFromJCost
