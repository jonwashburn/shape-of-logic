import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.ClosedObservableFramework
import IndisputableMonolith.Foundation.HierarchyRealization
import IndisputableMonolith.Foundation.LinkingNecessity

/-!
# Least-cost selection of k = 1 and |lk| = 1

A complete pass on the process-k cube must visit every vertex, so its
length is at least `2^{2k+1}`. That bound is 8 at k=1 and 32 at k=2.
Among process dimensions k ≥ 1, the unique minimizer is k = 1.

Independently, a nonzero integer linking charge costs `|n| · J(φ)`.
The unique minimizers are n = ±1. The realized debit/credit pair already
has windings 1 and −1.

The five-dimensional alternative remains an inhabitant; it is the more
expensive one.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LeastCostUnitLinking

open Patterns
open ClosedFramework
open HierarchyRealization
open CircleWinding
open LinkingFromHierarchy
open LinkingNecessity

/-- Ambient dimension of a k-parameter recognizer: D = 2k+1. -/
def processAmbient (k : ℕ) : ℕ := 2 * k + 1

/-- Lower bound on the length of a complete pass at process dimension k. -/
def minCompletePassCost (k : ℕ) : ℕ := 2 ^ (2 * k + 1)

theorem minCompletePassCost_eq (k : ℕ) :
    minCompletePassCost k = 2 ^ processAmbient k :=
  rfl

/-- Any surjective pass on the (2k+1)-cube is at least this long. -/
theorem complete_pass_costs_at_least
    {k T : ℕ} (pass : Fin T → Pattern (2 * k + 1))
    (h : Function.Surjective pass) :
    minCompletePassCost k ≤ T :=
  min_ticks_cover pass h

theorem three_cube_costs_eight : minCompletePassCost 1 = 8 := by
  decide

theorem five_cube_costs_thirty_two : minCompletePassCost 2 = 32 := by
  decide

theorem five_cube_strictly_dearer :
    minCompletePassCost 1 < minCompletePassCost 2 := by
  decide

/-- Among k ≥ 1, the unique cheapest complete-pass bound is k = 1. -/
theorem least_cost_selects_k_one
    {k : ℕ} (hk : 1 ≤ k)
    (hle : minCompletePassCost k ≤ minCompletePassCost 1) : k = 1 := by
  have hpow : 2 ^ (2 * k + 1) ≤ 2 ^ 3 := by
    simpa [minCompletePassCost] using hle
  have hle' : 2 * k + 1 ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by decide : (1 : ℕ) < 2)).mp hpow
  omega

/-- J-cost of realizing integer linking charge n. -/
noncomputable def chargeCost (n : ℤ) : ℝ :=
  (Int.natAbs n : ℝ) * Cost.Jcost Constants.phi

theorem chargeCost_one :
    chargeCost 1 = Cost.Jcost Constants.phi := by
  simp [chargeCost]

theorem chargeCost_neg_one :
    chargeCost (-1) = Cost.Jcost Constants.phi := by
  simp [chargeCost]

/-- Among nonzero charges, |n| = 1 is the unique least J-cost. -/
theorem unit_charge_least
    {n : ℤ} (hn : n ≠ 0)
    (hle : chargeCost n ≤ chargeCost 1) :
    Int.natAbs n = 1 := by
  have hJ : 0 < Cost.Jcost Constants.phi := Constants.Jcost_phi_pos
  have hmul : (Int.natAbs n : ℝ) * Cost.Jcost Constants.phi ≤
      (1 : ℝ) * Cost.Jcost Constants.phi := by
    simpa [chargeCost] using hle
  have hnat : (Int.natAbs n : ℝ) ≤ 1 :=
    le_of_mul_le_mul_right hmul hJ
  have hleN : Int.natAbs n ≤ 1 := by exact_mod_cast hnat
  have hpos : 0 < Int.natAbs n := Int.natAbs_pos.mpr hn
  omega

theorem least_cost_unit_linking
    {n : ℤ} (hn : n ≠ 0)
    (hle : chargeCost n ≤ chargeCost 1) :
    n = 1 ∨ n = -1 :=
  (Int.natAbs_eq_iff (n := 1)).mp (unit_charge_least hn hle)

/-- The realized debit/credit pair already occupies the unit-charge minimizers. -/
theorem realized_pair_has_unit_windings
    (F : ClosedObservableFramework)
    (H : RealizedHierarchy F) :
    pathWinding (recognitionCircleLoop F H) = 1 ∧
      pathWinding (creditLoop F H) = -1 :=
  ⟨recognitionCircleLoop_winding_one F H, creditLoop_winding_neg_one F H⟩

theorem realized_pair_is_least_cost_charge
    (F : ClosedObservableFramework)
    (H : RealizedHierarchy F) :
    pathWinding (recognitionCircleLoop F H) = 1 ∧
      pathWinding (creditLoop F H) = -1 ∧
      chargeCost 1 = Cost.Jcost Constants.phi ∧
      chargeCost (-1) = Cost.Jcost Constants.phi :=
  let h := realized_pair_has_unit_windings F H
  ⟨h.1, h.2, chargeCost_one, chargeCost_neg_one⟩

end LeastCostUnitLinking
end Foundation
end IndisputableMonolith
