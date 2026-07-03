import Mathlib
import IndisputableMonolith.Gravity.ILG

namespace IndisputableMonolith
namespace TruthCore

noncomputable section

@[simp] noncomputable def ILG_w_t_display
  (P : IndisputableMonolith.Gravity.ILG.Params)
  (B : IndisputableMonolith.Gravity.ILG.BridgeData) (Tdyn : ℝ) : ℝ :=
  IndisputableMonolith.Gravity.ILG.w_t_display P B Tdyn

end

end TruthCore
end IndisputableMonolith
