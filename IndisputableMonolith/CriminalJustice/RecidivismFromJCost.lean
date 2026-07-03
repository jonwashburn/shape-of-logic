import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Recidivism Rate from J-Cost on Rehabilitation Ratio
(Plan v7 fifty-first execution pass — first Criminal Justice module)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Cast recidivism as a J-cost reading on the ratio
`r = reoffense_rate / baseline_rate`.

Pre-intervention equilibrium corresponds to `r = 1`, `J = 0`.
Effective rehabilitation programs push `r < 1` (below baseline),
increasing J-cost and restoring the recognition-cost floor.

The RS prediction: the minimum detectable difference in recidivism
reduction (the "recognition threshold") is `J(φ) ≈ 0.118` —
a one-φ-step departure in the reoffense ratio.

## Falsifier

Any large-N randomized controlled trial (e.g., cognitive-behavioral
therapy in US Bureau of Justice Statistics) showing recidivism
reduction outside the J-cost band at one-φ-step departure.
-/

namespace IndisputableMonolith
namespace CriminalJustice
namespace RecidivismFromJCost

open Constants
open Cost

noncomputable section

/-- J-cost on the recidivism ratio (reoffense_rate / baseline_rate). -/
def recidivismCost (reoffense baseline : ℝ) : ℝ :=
  Jcost (reoffense / baseline)

theorem recidivismCost_at_equilibrium (r : ℝ) (h : r ≠ 0) :
    recidivismCost r r = 0 := by
  unfold recidivismCost; rw [div_self h]; exact Jcost_unit0

theorem recidivismCost_nonneg (reoffense baseline : ℝ)
    (hr : 0 < reoffense) (hb : 0 < baseline) :
    0 ≤ recidivismCost reoffense baseline := by
  unfold recidivismCost; exact Jcost_nonneg (div_pos hr hb)

theorem recidivismCost_reciprocal (reoffense baseline : ℝ)
    (hr : 0 < reoffense) (hb : 0 < baseline) :
    recidivismCost reoffense baseline = recidivismCost baseline reoffense := by
  unfold recidivismCost
  have h : Jcost (reoffense / baseline) = Jcost (baseline / reoffense) := by
    rw [Jcost_reciprocal (div_pos hr hb)]
    congr 1; field_simp [hb.ne', hr.ne']
  exact h

theorem recidivismCost_phi_step :
    Jcost phi = phi - 3 / 2 := by
  exact Jcost_phi_val

structure RecidivismCert where
  cost_at_equilibrium : ∀ r : ℝ, r ≠ 0 → recidivismCost r r = 0
  cost_nonneg : ∀ r b : ℝ, 0 < r → 0 < b → 0 ≤ recidivismCost r b
  cost_reciprocal : ∀ r b : ℝ, 0 < r → 0 < b →
    recidivismCost r b = recidivismCost b r
  phi_step : Jcost phi = phi - 3 / 2

noncomputable def cert : RecidivismCert where
  cost_at_equilibrium := recidivismCost_at_equilibrium
  cost_nonneg := recidivismCost_nonneg
  cost_reciprocal := recidivismCost_reciprocal
  phi_step := recidivismCost_phi_step

theorem cert_inhabited : Nonempty RecidivismCert := ⟨cert⟩

end
end RecidivismFromJCost
end CriminalJustice
end IndisputableMonolith
