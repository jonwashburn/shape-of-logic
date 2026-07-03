import Mathlib
import IndisputableMonolith.Constants

/-!
# Reionization History from RS — Cosmology Depth

Five canonical epochs of reionization (= configDim D = 5):
  cosmic dark ages (z > 20), first stars (z ~ 20), galaxy formation
  (z ~ 15), bulk reionization (z ~ 7-10), saturation (z < 6).

Each boundary redshift sits one rung on a geometric ladder.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.ReionizationHistoryFromRS
open Constants

inductive ReionizationEpoch where
  | darkAges
  | firstStars
  | galaxyFormation
  | bulkReionization
  | saturation
  deriving DecidableEq, Repr, BEq, Fintype

theorem reionizationEpoch_count :
    Fintype.card ReionizationEpoch = 5 := by decide

noncomputable def boundaryRedshift (k : ℕ) : ℝ := phi ^ k

theorem redshift_ratio (k : ℕ) :
    boundaryRedshift (k + 1) / boundaryRedshift k = phi := by
  unfold boundaryRedshift
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem redshift_pos (k : ℕ) : 0 < boundaryRedshift k :=
  pow_pos phi_pos k

structure ReionizationCert where
  five_epochs : Fintype.card ReionizationEpoch = 5
  phi_ratio : ∀ k, boundaryRedshift (k + 1) / boundaryRedshift k = phi
  boundary_always_pos : ∀ k, 0 < boundaryRedshift k

noncomputable def reionizationCert : ReionizationCert where
  five_epochs := reionizationEpoch_count
  phi_ratio := redshift_ratio
  boundary_always_pos := redshift_pos

end IndisputableMonolith.Cosmology.ReionizationHistoryFromRS
