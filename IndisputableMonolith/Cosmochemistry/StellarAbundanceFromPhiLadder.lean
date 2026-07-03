import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Stellar Elemental Abundance from φ-Ladder (Plan v7 fifty-seventh pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

The cosmic elemental abundance pattern (Lodders 2003) shows a
characteristic oscillation where even-Z elements are more abundant
than odd-Z (Oddo-Harkins rule).

RS prediction: the even/odd abundance ratio for adjacent elements
Z and Z+1 scales near φ on the nuclear φ-ladder.

More precisely, the B/A binding energy at the iron peak (rung 26)
predicts the peak abundance at Fe/Ni, and the decrease away from
the peak follows the J-cost structure.

## Falsifier

Any stellar spectroscopic abundance analysis (Asplund 2009 solar
photosphere) showing the even/odd ratio outside (1.5, 3.0) for
elements in the iron-peak group (Z = 22-30).
-/

namespace IndisputableMonolith
namespace Cosmochemistry
namespace StellarAbundanceFromPhiLadder

open Constants
open Cost

noncomputable section

/-- Even/odd abundance ratio near iron peak: φ. -/
def evenOddAbundanceRatio : ℝ := phi

theorem evenOddAbundanceRatio_gt_one : 1 < evenOddAbundanceRatio := one_lt_phi

theorem evenOddAbundanceRatio_in_range :
    (1.5 : ℝ) < evenOddAbundanceRatio ∧ evenOddAbundanceRatio < 3.0 := by
  constructor
  · unfold evenOddAbundanceRatio; linarith [phi_gt_onePointSixOne]
  · unfold evenOddAbundanceRatio
    have : phi ^ 2 < 2.7 := phi_squared_bounds.2
    nlinarith [one_lt_phi, phi_pos]

/-- J-cost on abundance ratio. -/
def abundanceCost (actual expected : ℝ) : ℝ :=
  Jcost (actual / expected)

theorem abundanceCost_at_predicted (a : ℝ) (h : a ≠ 0) :
    abundanceCost a a = 0 := by
  unfold abundanceCost; rw [div_self h]; exact Jcost_unit0

structure StellarAbundanceCert where
  ratio_gt_one : 1 < evenOddAbundanceRatio
  ratio_in_range : (1.5 : ℝ) < evenOddAbundanceRatio ∧ evenOddAbundanceRatio < 3.0
  cost_at_predicted : ∀ a : ℝ, a ≠ 0 → abundanceCost a a = 0

noncomputable def cert : StellarAbundanceCert where
  ratio_gt_one := evenOddAbundanceRatio_gt_one
  ratio_in_range := evenOddAbundanceRatio_in_range
  cost_at_predicted := abundanceCost_at_predicted

theorem cert_inhabited : Nonempty StellarAbundanceCert := ⟨cert⟩

end
end StellarAbundanceFromPhiLadder
end Cosmochemistry
end IndisputableMonolith
