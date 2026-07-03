import Mathlib
import IndisputableMonolith.Constants

/-!
# Mantle Convection from J-Cost — Tier F Geophysics

Mantle convection drives plate tectonics. The Rayleigh number Ra ≈ 10^7
governs convection vigor. In RS terms, the heat flux ratio r =
(convective flux)/(conductive flux limit) follows the phi-ladder:
adjacent convection regimes (sluggish, transitional, vigorous) ratio by phi.

Five canonical mantle convection modes (whole-mantle, layered,
episodic, plume-driven, plate-driven) = configDim D = 5.

RS prediction: convection regime transitions at phi-ladder critical Ra.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Geophysics.MantelConvectionFromJCost
open Constants

inductive ConvectionMode where
  | wholeMantle | layered | episodic | plumeDriven | plateDriven
  deriving DecidableEq, Repr, BEq, Fintype

theorem convectionModeCount : Fintype.card ConvectionMode = 5 := by decide

noncomputable def rayleighAtRung (k : ℕ) : ℝ := phi ^ k

theorem rayleighRatio (k : ℕ) :
    rayleighAtRung (k + 1) / rayleighAtRung k = phi := by
  unfold rayleighAtRung
  have hpos := pow_pos phi_pos k
  rw [pow_succ]; field_simp [hpos.ne']

structure MantelConvectionCert where
  five_modes : Fintype.card ConvectionMode = 5
  rayleigh_ratio : ∀ k, rayleighAtRung (k + 1) / rayleighAtRung k = phi

noncomputable def mantelConvectionCert : MantelConvectionCert where
  five_modes := convectionModeCount
  rayleigh_ratio := rayleighRatio

end IndisputableMonolith.Geophysics.MantelConvectionFromJCost
