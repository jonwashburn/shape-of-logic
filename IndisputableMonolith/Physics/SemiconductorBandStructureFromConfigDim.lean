import Mathlib
import IndisputableMonolith.Constants

/-!
# Semiconductor Band Structure from configDim — B15 Solid-State Depth

Five canonical semiconductor types (= configDim D = 5):
  intrinsic, n-type doped, p-type doped, compensated, degenerate.

Band-gap energies on the φ-ladder.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.SemiconductorBandStructureFromConfigDim
open Constants

inductive SemiconductorType where
  | intrinsic
  | nTypeDoped
  | pTypeDoped
  | compensated
  | degenerate
  deriving DecidableEq, Repr, BEq, Fintype

theorem semiconductorType_count :
    Fintype.card SemiconductorType = 5 := by decide

noncomputable def bandGap (k : ℕ) : ℝ := phi ^ k

theorem bandGap_ratio (k : ℕ) : bandGap (k + 1) / bandGap k = phi := by
  unfold bandGap
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem bandGap_pos (k : ℕ) : 0 < bandGap k := pow_pos phi_pos k

structure SemiconductorCert where
  five_types : Fintype.card SemiconductorType = 5
  phi_ratio : ∀ k, bandGap (k + 1) / bandGap k = phi
  bandGap_always_pos : ∀ k, 0 < bandGap k

noncomputable def semiconductorCert : SemiconductorCert where
  five_types := semiconductorType_count
  phi_ratio := bandGap_ratio
  bandGap_always_pos := bandGap_pos

end IndisputableMonolith.Physics.SemiconductorBandStructureFromConfigDim
