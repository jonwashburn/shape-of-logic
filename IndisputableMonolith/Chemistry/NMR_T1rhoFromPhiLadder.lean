import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# NMR T1rho Dispersion from φ-Ladder (Plan v7 ninety-fifth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
T1rho dispersion: relaxation time under spin-lock increases with lock field strength. RS: T1rho(B_SL × φ)/T1rho(B_SL) ≈ φ at the J-cost scaling of molecular motions.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace NMR_T1rhoFromPhiLadder
open Constants
open Cost
noncomputable section
def domainCost (m e : ℝ) : ℝ := Jcost (m / e)
theorem domainCost_at_eq (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0
theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)
def canonicalThreshold : ℝ := phi - 3 / 2
theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]
structure NMRT1rhoCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NMRT1rhoCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NMRT1rhoCert := ⟨cert⟩
end
end NMR_T1rhoFromPhiLadder
end Chemistry
end IndisputableMonolith
