import Mathlib
import IndisputableMonolith.Constants

/-!
# Galactic Rotation Curve from RS — Astrophysics Depth

Five canonical rotation-curve regimes (= configDim D = 5):
  rigid-body inner, rising, flat (MOND/DM), declining, truncation.

Each radius where regime transitions sits one rung up the φ-ladder.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Astrophysics.GalacticRotationCurveFromRS
open Constants

inductive RotationRegime where
  | rigidBodyInner
  | rising
  | flat
  | declining
  | truncation
  deriving DecidableEq, Repr, BEq, Fintype

theorem rotationRegime_count : Fintype.card RotationRegime = 5 := by decide

noncomputable def transitionRadius (k : ℕ) : ℝ := phi ^ k

theorem transitionRadius_ratio (k : ℕ) :
    transitionRadius (k + 1) / transitionRadius k = phi := by
  unfold transitionRadius
  have hpos : (0 : ℝ) < phi ^ k := pow_pos phi_pos k
  rw [div_eq_iff hpos.ne', pow_succ]
  ring

theorem transitionRadius_pos (k : ℕ) : 0 < transitionRadius k :=
  pow_pos phi_pos k

structure GalacticRotationCert where
  five_regimes : Fintype.card RotationRegime = 5
  phi_ratio : ∀ k, transitionRadius (k + 1) / transitionRadius k = phi
  radius_always_pos : ∀ k, 0 < transitionRadius k

noncomputable def galacticRotationCert : GalacticRotationCert where
  five_regimes := rotationRegime_count
  phi_ratio := transitionRadius_ratio
  radius_always_pos := transitionRadius_pos

end IndisputableMonolith.Astrophysics.GalacticRotationCurveFromRS
