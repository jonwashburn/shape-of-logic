import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Casimir Recognition Boundary

Recognition Science reads the Casimir effect as a boundary-mode inventory
imbalance.  Conducting plates restrict admissible modes inside the gap; the
renormalized cost-gradient of that restricted inventory is the pressure.

This module proves the structural statements and keeps the electromagnetic
boundary identification as a named bridge hypothesis.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirRecognitionBoundary

open Cost
open CasimirPlateModes

noncomputable section

/-- A boundary-mode inventory compares the admissible interior mode weight with
an exterior/reference mode weight. -/
structure BoundaryModeInventory where
  interior : ℝ
  exterior : ℝ
  interior_pos : 0 < interior
  exterior_pos : 0 < exterior

/-- The raw inventory deficit: exterior admissible weight minus interior
admissible weight.  Positive deficit is the parallel-plate Casimir case. -/
noncomputable def modeInventoryDeficit (I : BoundaryModeInventory) : ℝ :=
  I.exterior - I.interior

/-- The positive exterior/interior ratio seen by the canonical reciprocal cost. -/
noncomputable def inventoryRatio (I : BoundaryModeInventory) : ℝ :=
  I.exterior / I.interior

/-- Renormalized RS boundary cost for the inventory mismatch. -/
noncomputable def renormalizedBoundaryCost (I : BoundaryModeInventory) : ℝ :=
  Jcost (inventoryRatio I)

/-- The inventory ratio is positive. -/
theorem inventoryRatio_pos (I : BoundaryModeInventory) :
    0 < inventoryRatio I := by
  unfold inventoryRatio
  exact div_pos I.exterior_pos I.interior_pos

/-- Renormalized boundary cost is nonnegative. -/
theorem renormalizedBoundaryCost_nonneg (I : BoundaryModeInventory) :
    0 ≤ renormalizedBoundaryCost I := by
  unfold renormalizedBoundaryCost
  exact Jcost_nonneg (inventoryRatio_pos I)

/-- Equal interior/exterior inventories have zero boundary cost. -/
theorem renormalizedBoundaryCost_eq_zero_of_balanced
    (I : BoundaryModeInventory) (h : I.exterior = I.interior) :
    renormalizedBoundaryCost I = 0 := by
  unfold renormalizedBoundaryCost inventoryRatio
  rw [h, div_self (ne_of_gt I.interior_pos)]
  exact Jcost_unit0

/-- A positive inventory deficit is exactly `interior < exterior`. -/
theorem deficit_pos_iff (I : BoundaryModeInventory) :
    0 < modeInventoryDeficit I ↔ I.interior < I.exterior := by
  unfold modeInventoryDeficit
  constructor <;> intro h <;> linarith

/-- If the exterior inventory is larger, the RS ratio exceeds one. -/
theorem inventoryRatio_gt_one_of_deficit_pos
    (I : BoundaryModeInventory) (h : 0 < modeInventoryDeficit I) :
    1 < inventoryRatio I := by
  have hlt : I.interior < I.exterior := (deficit_pos_iff I).mp h
  unfold inventoryRatio
  rw [one_lt_div I.interior_pos]
  exact hlt

/-- A nonzero positive deficit gives a strictly positive recognition cost. -/
theorem renormalizedBoundaryCost_pos_of_deficit_pos
    (I : BoundaryModeInventory) (h : 0 < modeInventoryDeficit I) :
    0 < renormalizedBoundaryCost I := by
  have hratio_pos := inventoryRatio_pos I
  have hratio_gt : 1 < inventoryRatio I :=
    inventoryRatio_gt_one_of_deficit_pos I h
  unfold renormalizedBoundaryCost
  exact Jcost_pos_of_ne_one (inventoryRatio I) hratio_pos (ne_of_gt hratio_gt)

/-- A pressure gradient is a positive outward cost-gradient with pressure
defined as minus that gradient. -/
noncomputable def pressureFromCostGradient (gradient : ℝ) : ℝ :=
  -gradient

/-- Positive cost-gradient produces attractive pressure. -/
theorem attractive_of_positive_cost_gradient
    (gradient : ℝ) (hgradient : 0 < gradient) :
    pressureFromCostGradient gradient < 0 := by
  unfold pressureFromCostGradient
  exact neg_neg_of_pos hgradient

/-- Bridge hypothesis: electromagnetic conducting-boundary admissibility is
represented by a boundary-mode inventory, and its regularized energy gradient
matches the RS boundary-cost gradient. -/
structure EMRecognitionBoundaryBridge where
  inventory : PlateSeparation → BoundaryModeInventory
  costGradient : PlateSeparation → ℝ
  inducedPressure : PlateSeparation → ℝ
  admissibility_matches_inventory : Prop
  regularized_energy_matches_cost_gradient :
    ∀ a : PlateSeparation, inducedPressure a = pressureFromCostGradient (costGradient a)

/-- Under the bridge, a positive cost-gradient at a separation gives attractive
pressure at that separation. -/
theorem bridge_attractive_of_positive_gradient
    (B : EMRecognitionBoundaryBridge) (a : PlateSeparation)
    (hgradient : 0 < B.costGradient a) :
    B.inducedPressure a < 0 := by
  rw [B.regularized_energy_matches_cost_gradient a]
  exact attractive_of_positive_cost_gradient (B.costGradient a) hgradient

/-- Structural certificate for the RS boundary interpretation. -/
structure RecognitionBoundaryCert where
  cost_nonnegative :
    ∀ I : BoundaryModeInventory, 0 ≤ renormalizedBoundaryCost I
  balanced_zero :
    ∀ I : BoundaryModeInventory,
      I.exterior = I.interior → renormalizedBoundaryCost I = 0
  deficit_positive_cost :
    ∀ I : BoundaryModeInventory,
      0 < modeInventoryDeficit I → 0 < renormalizedBoundaryCost I
  positive_gradient_attractive :
    ∀ gradient : ℝ, 0 < gradient → pressureFromCostGradient gradient < 0

/-- Certificate for the theorem-level part of the boundary-mode reading. -/
def recognitionBoundaryCert : RecognitionBoundaryCert where
  cost_nonnegative := renormalizedBoundaryCost_nonneg
  balanced_zero := renormalizedBoundaryCost_eq_zero_of_balanced
  deficit_positive_cost := renormalizedBoundaryCost_pos_of_deficit_pos
  positive_gradient_attractive := attractive_of_positive_cost_gradient

end

end CasimirRecognitionBoundary
end QFT
end IndisputableMonolith
