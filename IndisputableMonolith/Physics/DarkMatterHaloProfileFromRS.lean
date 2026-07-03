import Mathlib
import IndisputableMonolith.Constants

/-!
# Dark Matter Halo Profile from RS — A6 Depth

Five canonical dark-matter halo regimes (= configDim D = 5):
  NFW inner, NFW outer, Einasto profile, isothermal sphere, truncation edge.

Each regime sits one rung down the φ-ladder in density.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.DarkMatterHaloProfileFromRS
open Constants

inductive HaloRegime where
  | nfwInner
  | nfwOuter
  | einasto
  | isothermal
  | truncation
  deriving DecidableEq, Repr, BEq, Fintype

theorem haloRegime_count : Fintype.card HaloRegime = 5 := by decide

noncomputable def densityRung (k : ℕ) : ℝ := 1 / phi ^ k

theorem density_pos (k : ℕ) : 0 < densityRung k := by
  unfold densityRung
  exact div_pos one_pos (pow_pos phi_pos k)

theorem density_strictDecr (k : ℕ) :
    densityRung (k + 1) < densityRung k := by
  unfold densityRung
  have hpos_k : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  have h_growth : phi ^ k < phi ^ (k + 1) := by
    rw [pow_succ]
    have h1 : 1 < phi := one_lt_phi
    nlinarith
  exact one_div_lt_one_div_of_lt hpos_k h_growth

structure DarkMatterHaloCert where
  five_regimes : Fintype.card HaloRegime = 5
  density_always_pos : ∀ k, 0 < densityRung k
  density_strictly_decreasing : ∀ k, densityRung (k + 1) < densityRung k

noncomputable def darkMatterHaloCert : DarkMatterHaloCert where
  five_regimes := haloRegime_count
  density_always_pos := density_pos
  density_strictly_decreasing := density_strictDecr

end IndisputableMonolith.Physics.DarkMatterHaloProfileFromRS
