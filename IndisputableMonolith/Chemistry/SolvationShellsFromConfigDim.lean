import Mathlib
import IndisputableMonolith.Constants

/-!
# Solvation Shells from configDim — B10 Chemistry Depth

Five canonical solvation shells for an ionic solute in water
(= configDim D = 5):
  primary hydration, secondary hydration, tertiary hydration,
  bulk-boundary layer, far bulk.

Shell radius on the φ-ladder: adjacent-shell ratio = φ.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Chemistry.SolvationShellsFromConfigDim
open Constants

inductive SolvationShell where
  | primaryHydration
  | secondaryHydration
  | tertiaryHydration
  | bulkBoundary
  | farBulk
  deriving DecidableEq, Repr, BEq, Fintype

theorem solvationShell_count : Fintype.card SolvationShell = 5 := by decide

noncomputable def shellRadius (k : ℕ) : ℝ := phi ^ k

theorem shellRadius_ratio (k : ℕ) : shellRadius (k + 1) / shellRadius k = phi := by
  unfold shellRadius
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem shellRadius_pos (k : ℕ) : 0 < shellRadius k := pow_pos phi_pos k

structure SolvationShellCert where
  five_shells : Fintype.card SolvationShell = 5
  phi_ratio : ∀ k, shellRadius (k + 1) / shellRadius k = phi
  radius_always_pos : ∀ k, 0 < shellRadius k

noncomputable def solvationShellCert : SolvationShellCert where
  five_shells := solvationShell_count
  phi_ratio := shellRadius_ratio
  radius_always_pos := shellRadius_pos

end IndisputableMonolith.Chemistry.SolvationShellsFromConfigDim
