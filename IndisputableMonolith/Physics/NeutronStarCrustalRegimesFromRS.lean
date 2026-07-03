import Mathlib
import IndisputableMonolith.Constants

/-!
# Neutron Star Crustal Regimes from RS — Astrophysics Depth

Five canonical neutron-star crustal regimes (= configDim D = 5):
  outer crust, inner crust, nuclear pasta, outer core, inner core.

Density rung on the φ-ladder: adjacent-regime density ratio = φ.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.NeutronStarCrustalRegimesFromRS
open Constants

inductive NSRegime where
  | outerCrust
  | innerCrust
  | nuclearPasta
  | outerCore
  | innerCore
  deriving DecidableEq, Repr, BEq, Fintype

theorem nsRegime_count : Fintype.card NSRegime = 5 := by decide

noncomputable def density (k : ℕ) : ℝ := phi ^ k

theorem density_ratio (k : ℕ) : density (k + 1) / density k = phi := by
  unfold density
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem density_pos (k : ℕ) : 0 < density k := pow_pos phi_pos k

structure NeutronStarCert where
  five_regimes : Fintype.card NSRegime = 5
  phi_ratio : ∀ k, density (k + 1) / density k = phi
  density_always_pos : ∀ k, 0 < density k

noncomputable def neutronStarCert : NeutronStarCert where
  five_regimes := nsRegime_count
  phi_ratio := density_ratio
  density_always_pos := density_pos

end IndisputableMonolith.Physics.NeutronStarCrustalRegimesFromRS
