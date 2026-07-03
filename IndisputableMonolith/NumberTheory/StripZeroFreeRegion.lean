import Mathlib
import IndisputableMonolith.NumberTheory.WeakZeroFreeRegion
import IndisputableMonolith.NumberTheory.ZetaFromTheta

/-!
  StripZeroFreeRegion.lean

  Phase 5 of the RS-native zeta program.

  This module does two things:

  1. It records the proven Mathlib zero-free result on the line/half-plane
     `Re(s) ≥ 1`.
  2. It names the genuine strip-zero-free theorem still needed for RH-quality
     closure.

  We do not assert the strip theorem as proved.  It is packaged as the next
  bridge object, with a theorem showing that if the bridge exists then the
  corresponding zero-free conclusion follows.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace StripZeroFreeRegion

noncomputable section

/-! ## 1. Proven classical boundary region -/

/-- Mathlib's de la Vallée-Poussin/Hadamard line theorem: `riemannZeta` is
nonzero on `Re(s) ≥ 1`. -/
theorem riemannZeta_ne_zero_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- The corresponding strict half-plane theorem. -/
theorem riemannZeta_ne_zero_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

/-- Certificate for the proved boundary zero-free region. -/
structure BoundaryZeroFreeCert where
  ge_one : ∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0
  gt_one : ∀ s : ℂ, 1 < s.re → riemannZeta s ≠ 0

def boundaryZeroFreeCert : BoundaryZeroFreeCert where
  ge_one := fun _ hs => riemannZeta_ne_zero_re_ge_one hs
  gt_one := fun _ hs => riemannZeta_ne_zero_re_gt_one hs

/-! ## 2. The true strip target -/

/-- A logarithmic zero-free strip with constants `c` and `T`.

For `|Im(s)| ≥ T`, the region
`Re(s) > 1 - c / log(|Im(s)|)` is zero-free. This is the classical
Hadamard-de la Vallée-Poussin shape, stated as the exact bridge needed by
the RS program. -/
structure LogZeroFreeStrip where
  c : ℝ
  T : ℝ
  c_pos : 0 < c
  T_gt_one : 1 < T
  zero_free :
    ∀ s : ℂ, T ≤ |s.im| →
      1 - c / Real.log |s.im| < s.re →
        riemannZeta s ≠ 0

/-- The strip theorem as the next named bridge. -/
def StripZeroFreeBridge : Prop :=
  Nonempty LogZeroFreeStrip

/-- Any strip bridge gives the corresponding zero-free conclusion. -/
theorem riemannZeta_ne_zero_in_log_strip
    (bridge : StripZeroFreeBridge) :
    ∃ c T : ℝ, 0 < c ∧ 1 < T ∧
      ∀ s : ℂ, T ≤ |s.im| →
        1 - c / Real.log |s.im| < s.re →
          riemannZeta s ≠ 0 := by
  rcases bridge with ⟨strip⟩
  exact ⟨strip.c, strip.T, strip.c_pos, strip.T_gt_one, strip.zero_free⟩

/-! ## 3. Relation to the weak zero-free-region module -/

/-- A proven boundary certificate and a named open strip bridge are exactly the
honest Phase 5 state. -/
structure StripPhase5Cert where
  boundary : BoundaryZeroFreeCert
  strip_bridge : StripZeroFreeBridge → Prop

def stripPhase5Cert : StripPhase5Cert where
  boundary := boundaryZeroFreeCert
  strip_bridge := fun _ => True

/-- The current unconditional zero-free region available to the RS zeta program
is the boundary region `Re ≥ 1`; the logarithmic strip is the named bridge. -/
theorem phase5_current_state :
    (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) ∧
      (StripZeroFreeBridge → ∃ c T : ℝ, 0 < c ∧ 1 < T ∧
        ∀ s : ℂ, T ≤ |s.im| →
          1 - c / Real.log |s.im| < s.re →
            riemannZeta s ≠ 0) := by
  exact ⟨fun s hs => riemannZeta_ne_zero_re_ge_one hs,
    riemannZeta_ne_zero_in_log_strip⟩

/-! ## 4. Phase 7: critical-strip zero-free bridge

The `LogZeroFreeStrip` above is the classical de la Vallée-Poussin shape and
is not enough to close the recovered RH chain. The chain is built around
witnessed defect sensors with `1/2 < Re(ρ) < 1`, so vacuous closure requires
zero-freeness on the open right half of the critical strip. That bridge is
the actual analytic input sitting between the recovered chain and a
million-dollar theorem.

We name it explicitly here. We do not inhabit it. We do prove that it is
implied by Mathlib's formal Riemann hypothesis, so callers can see the
irreducible analytic content. -/

/-- Critical-strip zero-free witness: `riemannZeta s ≠ 0` for every
`s` with `1/2 < Re(s) < 1`. -/
structure CriticalStripZeroFree where
  zero_free : ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0

/-- The critical-strip bridge as a named target. -/
def CriticalStripZeroFreeBridge : Prop :=
  Nonempty CriticalStripZeroFree

/-- Mathlib's `RiemannHypothesis` (every nontrivial nonpole zero is on the
critical line) implies the open right half-strip is zero-free. -/
theorem criticalStrip_zero_free_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∀ s : ℂ, 1/2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  intro s hlow hhigh hzero
  have hs1 : s ≠ 1 := by
    intro h
    have : s.re = 1 := by simp [h]
    linarith
  have hntriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      have := congrArg Complex.re hn
      simpa using this
    have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    have hneg : s.re < 0 := by rw [hre]; linarith
    linarith
  have hrhalf : s.re = 1 / 2 := hRH s hzero hntriv hs1
  linarith

/-- Mathlib's RH implies the critical-strip bridge. -/
theorem criticalStripZeroFreeBridge_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CriticalStripZeroFreeBridge :=
  ⟨{ zero_free := criticalStrip_zero_free_of_riemannHypothesis hRH }⟩

/-- Phase 7 honest state: the boundary region is proved, the critical-strip
bridge is named as a target, and we record that it is no stronger than RH. -/
structure StripPhase7Cert where
  boundary : BoundaryZeroFreeCert
  log_strip_bridge_named : True
  critical_strip_bridge_named : True
  critical_strip_implied_by_RH :
    RiemannHypothesis → CriticalStripZeroFreeBridge

def stripPhase7Cert : StripPhase7Cert where
  boundary := boundaryZeroFreeCert
  log_strip_bridge_named := trivial
  critical_strip_bridge_named := trivial
  critical_strip_implied_by_RH :=
    criticalStripZeroFreeBridge_of_riemannHypothesis

end

end StripZeroFreeRegion
end NumberTheory
end IndisputableMonolith
