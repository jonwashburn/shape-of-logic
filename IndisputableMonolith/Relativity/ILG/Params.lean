import Mathlib

namespace IndisputableMonolith
namespace Relativity
namespace ILG

/-- Minimal parameter record used by downstream modules. -/
structure Params where
  alpha : ℝ := 1
  Clag  : ℝ := 0

structure ParamProps (P : Params) : Prop :=
  (alpha_nonneg : 0 ≤ P.alpha)
  (Clag_nonneg : 0 ≤ P.Clag)

end ILG
end Relativity
end IndisputableMonolith
