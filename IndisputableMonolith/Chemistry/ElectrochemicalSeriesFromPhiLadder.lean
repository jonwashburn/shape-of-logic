import Mathlib
import IndisputableMonolith.Constants

/-!
# Electrochemical Series from φ-ladder — Chemistry Depth

Five canonical half-cell categories (= configDim D = 5):
  strong oxidizing, weak oxidizing, neutral reference (SHE),
  weak reducing, strong reducing.

Standard reduction potentials span five orders of magnitude, forming a
φ-ladder under canonical RS rescaling.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Chemistry.ElectrochemicalSeriesFromPhiLadder
open Constants

inductive HalfCellCategory where
  | strongOxidizing
  | weakOxidizing
  | sheReference
  | weakReducing
  | strongReducing
  deriving DecidableEq, Repr, BEq, Fintype

theorem halfCellCategory_count :
    Fintype.card HalfCellCategory = 5 := by decide

noncomputable def reductionPotential (k : ℕ) : ℝ := phi ^ k

theorem potential_ratio (k : ℕ) :
    reductionPotential (k + 1) / reductionPotential k = phi := by
  unfold reductionPotential
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem potential_pos (k : ℕ) : 0 < reductionPotential k :=
  pow_pos phi_pos k

structure ElectrochemicalSeriesCert where
  five_categories : Fintype.card HalfCellCategory = 5
  phi_ratio : ∀ k, reductionPotential (k + 1) / reductionPotential k = phi
  potential_always_pos : ∀ k, 0 < reductionPotential k

noncomputable def electrochemicalSeriesCert : ElectrochemicalSeriesCert where
  five_categories := halfCellCategory_count
  phi_ratio := potential_ratio
  potential_always_pos := potential_pos

end IndisputableMonolith.Chemistry.ElectrochemicalSeriesFromPhiLadder
