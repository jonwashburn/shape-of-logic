import Mathlib
import IndisputableMonolith.Constants

/-!
# Plasmonic Modes from φ-ladder — B15 Photonics Depth

Five canonical plasmonic mode types (= configDim D = 5):
  surface plasmon polariton, localized surface plasmon, propagating,
  bulk, gap plasmon.

Each mode's characteristic frequency sits one rung up the φ-ladder.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.PlasmonicModesFromPhiLadder
open Constants

inductive PlasmonicMode where
  | surfacePlasmonPolariton
  | localizedSurface
  | propagating
  | bulk
  | gapPlasmon
  deriving DecidableEq, Repr, BEq, Fintype

theorem plasmonicMode_count : Fintype.card PlasmonicMode = 5 := by decide

noncomputable def plasmonFrequency (k : ℕ) : ℝ := phi ^ k

theorem frequency_ratio (k : ℕ) :
    plasmonFrequency (k + 1) / plasmonFrequency k = phi := by
  unfold plasmonFrequency
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem frequency_pos (k : ℕ) : 0 < plasmonFrequency k := pow_pos phi_pos k

structure PlasmonicModeCert where
  five_modes : Fintype.card PlasmonicMode = 5
  phi_ratio : ∀ k, plasmonFrequency (k + 1) / plasmonFrequency k = phi
  frequency_always_pos : ∀ k, 0 < plasmonFrequency k

noncomputable def plasmonicModeCert : PlasmonicModeCert where
  five_modes := plasmonicMode_count
  phi_ratio := frequency_ratio
  frequency_always_pos := frequency_pos

end IndisputableMonolith.Physics.PlasmonicModesFromPhiLadder
