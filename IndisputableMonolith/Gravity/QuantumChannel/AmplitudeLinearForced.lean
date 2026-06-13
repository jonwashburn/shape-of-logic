import Mathlib
import IndisputableMonolith.Foundation.ComplexStructureForcing

/-!
# Gravity Track 2.C: Amplitude-Linear Forced (substrate dichotomy)

Track 2.C of the quantum-gravity master plan is the deepest physics step of
Track 2: the amplitude-linear gravitational channel must be *forced* from
substrate linearity, not chosen as a modeling assumption. This is the upgrade
of paper IV's T2 from `MODEL` to `THEOREM`.

This module opens Track 2.C with the **substrate dichotomy on a single
channel factor**. On the canonical `Foundation.ComplexStructureForcing.Signal8`
state space, a candidate channel response `R : Signal8 → Signal8` cannot be
simultaneously

* `IsAmplitudeLinear` (it agrees with some `ℂ`-linear map), and
* `IsDensityOnly` (it is invariant under multiplication by unit-modulus
  complex scalars, i.e. it depends only on the density matrix `|ψ�⟩⟨ψ|`)

unless it is identically zero on `Signal8`. The contrapositive form
`not_isDensityOnly_of_isAmplitudeLinear_of_ne_zero` is the first Lean
substrate-forcing statement of Track 2.C: a nontrivial amplitude-linear
channel response does *not* factor through a density-only readout.

Subsequent Track 2.C work will lift this single-factor dichotomy to the
joint matter-plus-channel `MacroscopicLedger` substrate to force
amplitude-linearity of the gravitational channel from the joint linearity
of the recognition operator (`Foundation.SchrodingerDerivation.schrodinger_linear`
composed factor-wise via `Gravity.MacroscopicLedger.MacroscopicShift`).

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

/-- Local abbreviation for the eight-tick analytic signal carrier
`Fin 8 → ℂ`, identified with the canonical
`Foundation.ComplexStructureForcing.Signal8`. -/
abbrev Signal8 : Type :=
  IndisputableMonolith.Foundation.ComplexStructureForcing.Signal8

/-- A candidate gravitational-channel response on `Signal8` is
**amplitude-linear** when it agrees with some `ℂ`-linear map.
Amplitude-linear responses preserve coherent superpositions of ledger
states. -/
def IsAmplitudeLinear (R : Signal8 → Signal8) : Prop :=
  ∃ L : Signal8 →ₗ[ℂ] Signal8, ∀ ψ : Signal8, R ψ = L ψ

/-- A candidate response is **phase-equivariant** when it commutes with
arbitrary complex scaling. Amplitude-linear responses are phase-equivariant. -/
def IsPhaseEquivariant (R : Signal8 → Signal8) : Prop :=
  ∀ (c : ℂ) (ψ : Signal8), R (c • ψ) = c • R ψ

/-- A candidate response is **density-only** when it is invariant under
multiplication by unit-modulus complex scalars. This is the structural
footprint of a CPTP-classical readout: the density matrix `|ψ⟩⟨ψ|` is
invariant under `ψ ↦ c · ψ` whenever `‖c‖ = 1`, so any response computed from
the density matrix alone must agree on `c • ψ` and `ψ`. -/
def IsDensityOnly (R : Signal8 → Signal8) : Prop :=
  ∀ (c : ℂ), ‖c‖ = 1 → ∀ ψ : Signal8, R (c • ψ) = R ψ

/-- Amplitude-linear responses are phase-equivariant. -/
theorem isPhaseEquivariant_of_isAmplitudeLinear
    {R : Signal8 → Signal8} (h : IsAmplitudeLinear R) :
    IsPhaseEquivariant R := by
  rcases h with ⟨L, hL⟩
  intro c ψ
  rw [hL (c • ψ), hL ψ, L.map_smul]

/-- **Substrate dichotomy on a single channel factor.** If a candidate
gravitational-channel response is simultaneously amplitude-linear and
density-only, then it is identically zero on `Signal8`. The proof tests the
two structural conditions against each other at the unit-modulus scalar
`c = -1`. -/
theorem eq_zero_of_isAmplitudeLinear_isDensityOnly
    {R : Signal8 → Signal8}
    (hLin : IsAmplitudeLinear R) (hDen : IsDensityOnly R)
    (ψ : Signal8) : R ψ = 0 := by
  have hPhase : IsPhaseEquivariant R :=
    isPhaseEquivariant_of_isAmplitudeLinear hLin
  have hcnorm : ‖((-1 : ℂ))‖ = 1 := by
    rw [norm_neg, norm_one]
  -- Amplitude-linear / phase-equivariant: `R(-ψ) = (-1) • R ψ`.
  have hAmp : R ((-1 : ℂ) • ψ) = (-1 : ℂ) • R ψ := hPhase (-1) ψ
  -- Density-only: `R(-ψ) = R(ψ)` since `‖-1‖ = 1`.
  have hDen' : R ((-1 : ℂ) • ψ) = R ψ := hDen (-1) hcnorm ψ
  -- Combine: `R ψ = - R ψ`.
  have hEq : R ψ = - R ψ := by
    have h := hDen'.symm.trans hAmp
    rwa [neg_one_smul] at h
  -- Hence `2 • R ψ = 0` in the `ℂ`-module `Signal8`.
  have h2 : (2 : ℂ) • R ψ = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hEq]
    exact neg_add_cancel _
  -- `(2 : ℂ) ≠ 0`, and `Signal8 = Fin 8 → ℂ` is a `NoZeroSMulDivisors ℂ`
  -- module, so `R ψ = 0`.
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h h2ne
  · exact h

/-- **Contrapositive substrate-forcing statement (Track 2.C seed).** A
nontrivial amplitude-linear channel response on `Signal8` is *not*
density-only. Equivalently: on a single channel factor, no nontrivial
gravitational-channel response can be simultaneously consistent with
substrate linearity (`Foundation.SchrodingerDerivation.schrodinger_linear`)
and with a CPTP-classical density-only readout. -/
theorem not_isDensityOnly_of_isAmplitudeLinear_of_ne_zero
    {R : Signal8 → Signal8}
    (hLin : IsAmplitudeLinear R)
    {ψ : Signal8} (hψ : R ψ ≠ 0) :
    ¬ IsDensityOnly R := by
  intro hDen
  exact hψ (eq_zero_of_isAmplitudeLinear_isDensityOnly hLin hDen ψ)

/-- **No-go for amplitude-linear-and-density-only nontrivial responses.**
Existence form of the substrate dichotomy: there is no channel response on
`Signal8` that is simultaneously amplitude-linear, density-only, and
nontrivial (i.e. nonzero on some ledger state). -/
theorem not_exists_nontrivial_isAmplitudeLinear_and_isDensityOnly :
    ¬ ∃ (R : Signal8 → Signal8),
      IsAmplitudeLinear R ∧ IsDensityOnly R ∧ (∃ ψ : Signal8, R ψ ≠ 0) := by
  rintro ⟨R, hLin, hDen, ψ, hψ⟩
  exact hψ (eq_zero_of_isAmplitudeLinear_isDensityOnly hLin hDen ψ)

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
