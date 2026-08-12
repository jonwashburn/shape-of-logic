import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4DKernelCert

/-!
# Kernel Int certificate: midpoint Bloch symbolZero quartic coefficients vanish

Reuses the banked `KernelCert.couplingZList` (Int-encoded coupling table).
Clears denominators by scale 16; the ℚ quartic coefficient is `qNum / 32`.

Kernel `decide` only (no `native_decide`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochSymbolZero4D
namespace KernelCert

open ReggeExactMidpointM2TTIdentity4D.KernelCert
  (CZ De Dep couplingZList)

set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

/-- Every Int-encoded coupling denominator divides the fixed scale 16. -/
theorem couplingZ_den_dvd_16 : ∀ z ∈ couplingZList, z.den ∣ 16 := by
  decide

/-- Integer contribution of one coupling to the cleared-denominator quartic
coefficient: `num · De_a · De_b · Dep_c · Dep_d · (16/den)`. -/
@[inline] def qContrib (z : CZ) (a b c d : Fin 4) : Int :=
  z.num * De z a * De z b * Dep z c * Dep z d * (↑(16 / z.den) : Int)

/-- Cleared-denominator quartic numerator over the full coupling table. -/
def qNum (a b c d : Fin 4) : Int :=
  couplingZList.foldl (fun acc z => acc + qContrib z a b c d) 0

/-- **THEOREM (kernel):** every cleared-denominator quartic numerator vanishes. -/
theorem qNum_eq_zero : ∀ (a b c d : Fin 4), qNum a b c d = 0 := by
  decide

end KernelCert
end ReggeExactFlatHessianBlochSymbolZero4D
end Analysis
end Gravity
end IndisputableMonolith
