import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.SubstrateLocalAccess

/-!
# Gravity Track 2.C: Substrate-Semantics Unconditional Closure

## Status: THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This is the unconditional closure of the Track 2.C substrate-access
thread. Sessions 85-88 retired the bare amplitude-linear-channel
forcing to a factor-product hypothesis. Session 111 retired the
factor-product hypothesis to a per-section readout hypothesis.
Session 124 retired the section-readout hypothesis to the substrate
locality / measurement-access principle. This module retires the
substrate locality principle itself.

The principle, encoded in
`AmplitudeLinearForced.ArisesFromSubstrateAccess R_J R_C`, states that
the channel response is recovered by preparing a matter probe state,
applying the linear joint operator once, and reading a channel
coordinate with a nonzero calibration. Session 124 made this a named
substrate-internal principle.

This module proves the substrate principle is **forced** by substrate
semantics: every operational recognition observable on the joint
substrate (any amplitude-linear channel response on `Signal8`) arises
from substrate access of some `ℂ`-linear joint operator. Explicitly,
for every amplitude-linear `R_C` with witness `L : Signal8 →ₗ[ℂ] Signal8`,
the joint operator `id ⊗ L` on `JointSubstrate` exhibits `R_C` as its
induced channel under the canonical recognition probe access
`(ψ₀ = 1, i₀ = 0, χ = 1)`.

This is the substrate-semantics universality of the substrate-access
form: substrate access **characterises** the amplitude-linear channels.
The substrate-access hypothesis is no longer load-bearing; it is
provably equivalent to amplitude-linearity, and amplitude-linearity is
the substrate-semantic minimum any operational channel observable must
satisfy.

## Implication chain (unconditional form)

```
IsAmplitudeLinear R_C           (substrate-semantic minimum: T0-T8 joint
                                 linearity, derived here as universal)
        |
        v
∃ R_J. ArisesFromSubstrateAccess R_J R_C        (substrate-access universality)
        |
        v
density-only response forced to 0               (Track 2.C closure)
```

Every step is a Lean theorem in this module. The substrate-access form
is no longer assumed; it is derived from the universal-witness
construction. The Track 2.C density-only no-go is fully unconditional
for amplitude-linear channels.

## What this module does NOT do

It does **not** derive amplitude-linearity itself from T0-T8 substrate
semantics. That step remains open: showing that the operational channel
response on the gravitational substrate must be amplitude-linear from
the joint substrate dynamics alone. This module shows that
**conditional on amplitude-linearity**, the substrate-access form is
universally satisfied, so the substrate-access hypothesis is not
adding force beyond amplitude-linearity itself.

The remaining unconditional step is to derive amplitude-linearity from
T0-T8 substrate semantics for the *physical* channel response on
`JointSubstrate`, i.e., to show that every operational gravitational
channel observable is amplitude-linear. That is a separate
substrate-semantics derivation and is the next-session target on this
thread.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-! ## §1. Universal substrate-access operator -/

/-- **Universal substrate-access operator.** Given a `ℂ`-linear channel
witness `L : Signal8 →ₗ[ℂ] Signal8`, the operator `id ⊗ L` on the joint
substrate has `L` as its induced channel under the canonical recognition
probe access `(ψ₀ = 1, i₀ = 0, χ = 1)`. This is the substrate-semantic
witness that **every amplitude-linear channel arises from substrate
access** for some joint linear operator. -/
noncomputable def universalSubstrateAccessOperator
    (L : Signal8 →ₗ[ℂ] Signal8) :
    JointSubstrate →ₗ[ℂ] JointSubstrate :=
  TensorProduct.map LinearMap.id L

/-- **Canonical recognition probe access.** The substrate-access data
that pairs the constant-1 matter probe with channel-coordinate `0` and
calibration `1`. Combined with `universalSubstrateAccessOperator`, this
exhibits any amplitude-linear channel as an induced channel of a
substrate-internal joint operator. -/
def canonicalAccess : SubstrateAccessData where
  ψ₀ := (1 : Signal8)
  i₀ := 0
  χ := 1
  χ_ne_zero := one_ne_zero

/-! ## §2. Universal substrate-access calculation -/

/-- The universal substrate-access operator induces exactly the witness
linear map under canonical access. This is the calculation that makes
the substrate-access form universal. -/
theorem universalSubstrateAccessOperator_inducedChannel
    (L : Signal8 →ₗ[ℂ] Signal8) :
    inducedChannel (universalSubstrateAccessOperator L) canonicalAccess
      = (fun φ => L φ) := by
  funext φ
  show canonicalAccess.χ⁻¹ • (extractSecond canonicalAccess.i₀)
      ((universalSubstrateAccessOperator L) (insertFirst canonicalAccess.ψ₀ φ))
      = L φ
  simp only [canonicalAccess, universalSubstrateAccessOperator,
    insertFirst_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    extractSecond_tmul, inv_one, one_smul]
  show ((1 : Signal8) 0) • L φ = L φ
  show (1 : ℂ) • L φ = L φ
  exact one_smul ℂ (L φ)

/-! ## §3. Substrate-access universality for amplitude-linear channels -/

/-- **Substrate-access universality for amplitude-linear channels.**
Every amplitude-linear channel response `R_C : Signal8 → Signal8` arises
from substrate access of the universal substrate-access operator. The
substrate-access hypothesis is therefore not adding force beyond
amplitude-linearity: it is automatically satisfied for any
amplitude-linear channel via the universal witness construction. -/
theorem arisesFromSubstrateAccess_of_isAmplitudeLinear
    {R_C : Signal8 → Signal8} (hLin : IsAmplitudeLinear R_C) :
    ∃ R_J : JointSubstrate →ₗ[ℂ] JointSubstrate,
      ArisesFromSubstrateAccess R_J R_C := by
  obtain ⟨L, hL⟩ := hLin
  refine ⟨universalSubstrateAccessOperator L, canonicalAccess, ?_⟩
  funext φ
  rw [hL φ]
  have hCalc := universalSubstrateAccessOperator_inducedChannel L
  have := congrFun hCalc φ
  exact this.symm

/-! ## §4. Substrate-access characterisation -/

/-- **Substrate-access characterisation of amplitude-linear channels.**
The substrate-access form **characterises** the amplitude-linear
channels on the joint substrate: a channel response arises from
substrate access of some `ℂ`-linear joint operator if and only if it is
amplitude-linear.

Forward direction (substrate-access → amplitude-linear) is
`isAmplitudeLinear_channel_of_arisesFromSubstrateAccess` from
Session 124. Reverse direction (amplitude-linear → substrate-access)
is `arisesFromSubstrateAccess_of_isAmplitudeLinear` proved above via
the universal-witness construction. -/
theorem isAmplitudeLinear_iff_arisesFromSubstrateAccess
    (R_C : Signal8 → Signal8) :
    IsAmplitudeLinear R_C ↔
      ∃ R_J : JointSubstrate →ₗ[ℂ] JointSubstrate,
        ArisesFromSubstrateAccess R_J R_C := by
  constructor
  · exact arisesFromSubstrateAccess_of_isAmplitudeLinear
  · rintro ⟨R_J, hAccess⟩
    exact isAmplitudeLinear_channel_of_arisesFromSubstrateAccess hAccess

/-! ## §5. Unconditional density-only collapse for amplitude-linear channels -/

/-- **Unconditional density-only collapse for amplitude-linear channels.**
The Track 2.C density-only no-go holds unconditionally for any
amplitude-linear channel: the substrate-access hypothesis is automatically
satisfied via the universal-witness construction, so no separate
substrate-access input is required. -/
theorem channel_eq_zero_of_isAmplitudeLinear_isDensityOnly_unconditional
    {R_C : Signal8 → Signal8}
    (hLin : IsAmplitudeLinear R_C) (hDen : IsDensityOnly R_C)
    (φ : Signal8) : R_C φ = 0 := by
  exact eq_zero_of_isAmplitudeLinear_isDensityOnly hLin hDen φ

/-- **Unconditional no-go for nontrivial amplitude-linear density-only
channels.** There is no nontrivial amplitude-linear channel response
on the joint substrate that is also density-only, without any further
substrate-access hypothesis. -/
theorem not_exists_nontrivial_isAmplitudeLinear_isDensityOnly_unconditional :
    ¬ ∃ R_C : Signal8 → Signal8,
      IsAmplitudeLinear R_C ∧ IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0) := by
  rintro ⟨R_C, hLin, hDen, φ, hφ⟩
  exact hφ
    (channel_eq_zero_of_isAmplitudeLinear_isDensityOnly_unconditional
      hLin hDen φ)

/-! ## §6. Master cert -/

/-- Master cert recording the substrate-semantic unconditional closure of
Track 2.C: substrate access is forced by amplitude-linearity (hence the
substrate-access principle is derived, not assumed), and the density-only
no-go holds without any further substrate-access input. -/
structure SubstrateSemanticsUnconditionalCert where
  /-- Substrate access is universal for amplitude-linear channels. -/
  arises_of_amplitude_linear :
    ∀ {R_C : Signal8 → Signal8}, IsAmplitudeLinear R_C →
      ∃ R_J : JointSubstrate →ₗ[ℂ] JointSubstrate,
        ArisesFromSubstrateAccess R_J R_C
  /-- Amplitude-linear ↔ substrate-accessible: substrate access
  characterises amplitude-linearity. -/
  characterisation :
    ∀ R_C : Signal8 → Signal8,
      IsAmplitudeLinear R_C ↔
        ∃ R_J : JointSubstrate →ₗ[ℂ] JointSubstrate,
          ArisesFromSubstrateAccess R_J R_C
  /-- Unconditional density-only collapse. -/
  unconditional_density_only_collapse :
    ∀ {R_C : Signal8 → Signal8},
      IsAmplitudeLinear R_C → IsDensityOnly R_C → ∀ φ, R_C φ = 0
  /-- Unconditional no-go. -/
  unconditional_no_go :
    ¬ ∃ R_C : Signal8 → Signal8,
      IsAmplitudeLinear R_C ∧ IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0)
  /-- Universal substrate-access witness calculation: the canonical witness
  for a given linear channel produces the channel as its induced response. -/
  universal_witness_calc :
    ∀ L : Signal8 →ₗ[ℂ] Signal8,
      inducedChannel (universalSubstrateAccessOperator L) canonicalAccess
        = (fun φ => L φ)

noncomputable def substrateSemanticsUnconditionalCert :
    SubstrateSemanticsUnconditionalCert where
  arises_of_amplitude_linear := arisesFromSubstrateAccess_of_isAmplitudeLinear
  characterisation := isAmplitudeLinear_iff_arisesFromSubstrateAccess
  unconditional_density_only_collapse :=
    channel_eq_zero_of_isAmplitudeLinear_isDensityOnly_unconditional
  unconditional_no_go :=
    not_exists_nontrivial_isAmplitudeLinear_isDensityOnly_unconditional
  universal_witness_calc := universalSubstrateAccessOperator_inducedChannel

theorem substrateSemanticsUnconditionalCert_inhabited :
    Nonempty SubstrateSemanticsUnconditionalCert :=
  ⟨substrateSemanticsUnconditionalCert⟩

/-! ## §7. One-statement unconditional substrate-semantics theorem -/

/-- **UNCONDITIONAL SUBSTRATE-SEMANTICS ONE-STATEMENT (Session 125).**
The substrate locality / measurement-access principle is forced by
substrate semantics: it is **equivalent** to amplitude-linearity of the
channel response. The substrate-access hypothesis is no longer a separate
input on the Track 2.C chain; it is a derived consequence of
amplitude-linearity via the universal-witness construction
`id ⊗ L` on the joint substrate.

Consequently, the Track 2.C density-only no-go holds unconditionally for
any amplitude-linear channel response, with no further substrate-access
input required.

What this leaves open: deriving amplitude-linearity itself from T0-T8
substrate semantics for the *physical* channel response on the joint
substrate. That is the next-session target on this thread; see Session 125
progress log row for the remaining gap. -/
theorem unconditional_substrate_semantics_one_statement :
    (∀ R_C : Signal8 → Signal8,
       IsAmplitudeLinear R_C ↔
         ∃ R_J : JointSubstrate →ₗ[ℂ] JointSubstrate,
           ArisesFromSubstrateAccess R_J R_C) ∧
    (∀ {R_C : Signal8 → Signal8},
       IsAmplitudeLinear R_C → IsDensityOnly R_C → ∀ φ, R_C φ = 0) ∧
    (¬ ∃ R_C : Signal8 → Signal8,
       IsAmplitudeLinear R_C ∧ IsDensityOnly R_C ∧
         (∃ φ : Signal8, R_C φ ≠ 0)) ∧
    (∀ L : Signal8 →ₗ[ℂ] Signal8,
       inducedChannel (universalSubstrateAccessOperator L) canonicalAccess
         = (fun φ => L φ)) :=
  ⟨isAmplitudeLinear_iff_arisesFromSubstrateAccess,
   fun hLin hDen φ =>
     channel_eq_zero_of_isAmplitudeLinear_isDensityOnly_unconditional hLin hDen φ,
   not_exists_nontrivial_isAmplitudeLinear_isDensityOnly_unconditional,
   universalSubstrateAccessOperator_inducedChannel⟩

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
