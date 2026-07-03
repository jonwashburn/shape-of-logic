import Mathlib

namespace IndisputableMonolith
namespace ILG

/-- Minimal parameter record used by downstream ILG modules outside the sealed Relativity subtree. -/
structure Params where
  alpha : ℝ := 1
  Clag  : ℝ := 0

/-- Basic positivity properties for ILG parameters. -/
structure ParamProps (P : Params) : Prop :=
  (alpha_nonneg : 0 ≤ P.alpha)
  (Clag_nonneg : 0 ≤ P.Clag)

end ILG
end IndisputableMonolith


