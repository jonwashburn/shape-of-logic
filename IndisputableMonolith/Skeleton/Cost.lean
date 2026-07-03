import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.DAlembert.FactorizationForcing

/-!
# Skeleton chapter: The Cost Keystone (J and the RCL)

Foundation's T5 guidepost says "J is unique." This chapter is the keystone itself, the two
theorems that make T5 true and that everything in Recognition Science is downstream of. If
you read one pair of theorems to understand WHY the framework is forced rather than chosen,
read these. Drill down: `Cost.FunctionalEquation`, `Foundation.DAlembert.FactorizationForcing`.
-/

namespace IndisputableMonolith
namespace Skeleton

/-- **The recognition cost J(x)=½(x+1/x)−1 is the UNIQUE possibility.**
Given any F that is reciprocal-symmetric, normalized (F(1)=0), satisfies the Recognition
Composition Law, is calibrated (log-second-derivative 1 at the origin), and continuous on
(0,∞), then F = J. No RS-specific axiom; this is Aczél/d'Alembert functional-equation
theory applied to recognition. Everything else (φ, ℏ, the mass ladder, the constants) is a
shadow of this one cost. Tier: THEOREM (0 sorry). Drill down:
`Cost.FunctionalEquation.law_of_logic_forces_jcost`, `Cost.AczelProof`. -/
alias guidepost_cost_is_unique :=
  IndisputableMonolith.Cost.FunctionalEquation.law_of_logic_forces_jcost

/-- **The Recognition Composition Law is itself forced, not assumed.**
Among symmetric, right-affine combiners with the natural boundary conditions, the RCL
polynomial `2uv+2u+2v` is the unique result. So the composition law that pins J down is not
a modeling choice either, it is forced one level deeper. This closes the obvious objection
"you chose the RCL." Tier: THEOREM. Drill down:
`Foundation.DAlembert.FactorizationForcing.gate_forces_rcl`. -/
alias guidepost_rcl_is_forced :=
  IndisputableMonolith.Foundation.DAlembert.FactorizationForcing.gate_forces_rcl

end Skeleton
end IndisputableMonolith
