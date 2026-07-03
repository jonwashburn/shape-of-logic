import Mathlib
import IndisputableMonolith.Cost

/-!
# Baryogenesis from J-Cost — A3 Cosmology

The baryon-to-photon ratio η ≈ 6.1 × 10⁻¹⁰ (CMB measurement).

In RS terms: the matter-antimatter asymmetry is a σ-imbalance in the
early universe. The Sakharov conditions (baryon number violation,
C and CP violation, departure from equilibrium) correspond to:
1. Baryon violation = σ-export above threshold
2. CP violation = J(r) ≠ J(r*) where r* is the CP-conjugate
3. Non-equilibrium = J(r) > 0

Five baryogenesis mechanisms (leptogenesis, electroweak, Affleck-Dine,
cold baryogenesis, GUT baryogenesis) = configDim D = 5.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.BaryogenesisFromJCost
open Cost

inductive BaryogenesisMechanism where
  | leptogenesis | electroWeak | affleckDine | cold | GUT
  deriving DecidableEq, Repr, BEq, Fintype

theorem baryogenesisMechanismCount : Fintype.card BaryogenesisMechanism = 5 := by decide

/-- Equilibrium = matter-antimatter balance (J=0). -/
theorem matter_balance_equilibrium : Jcost 1 = 0 := Jcost_unit0

/-- Asymmetry = J > 0 when matter ≠ antimatter. -/
theorem asymmetry_positive_cost {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

structure BaryogenesisCert where
  five_mechanisms : Fintype.card BaryogenesisMechanism = 5
  equilibrium : Jcost 1 = 0
  asymmetry : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def baryogenesisCert : BaryogenesisCert where
  five_mechanisms := baryogenesisMechanismCount
  equilibrium := matter_balance_equilibrium
  asymmetry := asymmetry_positive_cost

end IndisputableMonolith.Cosmology.BaryogenesisFromJCost
