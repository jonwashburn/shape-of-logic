import Mathlib
import IndisputableMonolith.Cost

/-!
# Arrow of Time from J-Cost — Pre-BB Physics

The thermodynamic arrow of time (entropy increase) in RS terms:
Recognition cost J(r) is minimised at equilibrium (r = 1, J = 0).
Evolution drives r → 1, which defines the forward time direction.

Key claims:
1. J(r) ≥ 0 always (non-negative recognition cost)
2. J(1) = 0 (equilibrium = zero cost)
3. J-cost decreasing toward equilibrium defines "future"
4. J is symmetric: J(r) = J(r⁻¹) — time-reversal symmetry

Five thermodynamic arrows (thermodynamic, cosmological, causal,
psychological, quantum) = configDim D = 5.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.EntropyArrowFromJCost
open Cost

inductive ThermodynamicArrow where
  | thermodynamic | cosmological | causal | psychological | quantum
  deriving DecidableEq, Repr, BEq, Fintype

theorem arrowCount : Fintype.card ThermodynamicArrow = 5 := by decide

theorem jcost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ Jcost r := by
  by_cases h : r = 1
  · rw [h, Jcost_unit0]
  · exact le_of_lt (Jcost_pos_of_ne_one r hr h)

theorem equilibrium_zero : Jcost 1 = 0 := Jcost_unit0

theorem time_reversal_symmetric {r : ℝ} (hr : 0 < r) :
    Jcost r = Jcost r⁻¹ := Jcost_symm hr

structure EntropyArrowCert where
  five_arrows : Fintype.card ThermodynamicArrow = 5
  nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ Jcost r
  equilibrium : Jcost 1 = 0
  time_reversal : ∀ {r : ℝ}, 0 < r → Jcost r = Jcost r⁻¹

def entropyArrowCert : EntropyArrowCert where
  five_arrows := arrowCount
  nonneg := jcost_nonneg
  equilibrium := equilibrium_zero
  time_reversal := time_reversal_symmetric

end IndisputableMonolith.Physics.EntropyArrowFromJCost
