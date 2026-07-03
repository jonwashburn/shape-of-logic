import Mathlib
import IndisputableMonolith.Masses.RSBridge.Anchor

/-!
# Heavy Quark Anchor Derivation

This module derives the heavy-quark anchor-scale masses directly from the
RSBridge formula

  `massAtAnchor f = M0 * exp(((rung f : ℝ) - 8 + gap (ZOf f)) * log φ)`.

No PDG masses enter. The result is RS-native and dimensionless.
-/

namespace IndisputableMonolith.Masses.QuarkAnchorDerivation

open IndisputableMonolith.RSBridge

noncomputable section

def charm_anchor_native : ℝ := massAtAnchor Fermion.c
def bottom_anchor_native : ℝ := massAtAnchor Fermion.b
def top_anchor_native : ℝ := massAtAnchor Fermion.t

theorem charm_anchor_eq_massAtAnchor :
    charm_anchor_native = massAtAnchor Fermion.c := rfl

theorem bottom_anchor_eq_massAtAnchor :
    bottom_anchor_native = massAtAnchor Fermion.b := rfl

theorem top_anchor_eq_massAtAnchor :
    top_anchor_native = massAtAnchor Fermion.t := rfl

theorem charm_rung_eq : rung Fermion.c = 15 := rfl
theorem bottom_rung_eq : rung Fermion.b = 21 := rfl
theorem top_rung_eq : rung Fermion.t = 21 := rfl

theorem charm_Z_eq : ZOf Fermion.c = 276 := rfl
theorem bottom_Z_eq : ZOf Fermion.b = 24 := rfl
theorem top_Z_eq : ZOf Fermion.t = 276 := rfl

theorem heavy_anchor_positive :
    0 < charm_anchor_native ∧
    0 < bottom_anchor_native ∧
    0 < top_anchor_native := by
  unfold charm_anchor_native bottom_anchor_native top_anchor_native massAtAnchor
  constructor
  · exact mul_pos M0_pos (Real.exp_pos _)
  constructor
  · exact mul_pos M0_pos (Real.exp_pos _)
  · exact mul_pos M0_pos (Real.exp_pos _)

structure QuarkAnchorDerivationCert where
  charm_rung : rung Fermion.c = 15
  bottom_rung : rung Fermion.b = 21
  top_rung : rung Fermion.t = 21
  charm_Z : ZOf Fermion.c = 276
  bottom_Z : ZOf Fermion.b = 24
  top_Z : ZOf Fermion.t = 276
  positive : 0 < charm_anchor_native ∧
    0 < bottom_anchor_native ∧
    0 < top_anchor_native

theorem quarkAnchorDerivationCert_holds : QuarkAnchorDerivationCert :=
{ charm_rung := charm_rung_eq
  bottom_rung := bottom_rung_eq
  top_rung := top_rung_eq
  charm_Z := charm_Z_eq
  bottom_Z := bottom_Z_eq
  top_Z := top_Z_eq
  positive := heavy_anchor_positive }

end

end IndisputableMonolith.Masses.QuarkAnchorDerivation
