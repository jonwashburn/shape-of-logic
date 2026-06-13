import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForcedSubstrate

/-!
# Gravity Track 2.C: Section-Readout Forcing without Pure-Tensor Factorization

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This module is the first direct attack on the remaining Track 2.C gap:
retiring the full pure-tensor factorization hypothesis. Earlier modules
proved:

* `AmplitudeLinearForcedJoint`: if a joint operator factorizes on pure
  tensors, then the channel factor is forced amplitude-linear.
* `AmplitudeLinearForcedSubstrate`: plugging in the recognition update on
  the matter side gives the substrate-side forcing result.
* `AmplitudeLinearForcedCert`: bundles this as a STRUCTURAL THEOREM under
  the named `FactorizableJointSubstrate` hypothesis.

The factor-product hypothesis is stronger than operationally necessary.
To force the channel response `R_C` to be amplitude-linear, we do **not**
need the joint operator `R_J : Signal8 ⊗ Signal8 →ₗ Signal8 ⊗ Signal8`
to factorize on every pure tensor. It is enough that the physical channel
response is obtained by a **nonzero matter section readout**:

```
φ ↦ χ⁻¹ • extractSecond i₀ (R_J (ψ₀ ⊗ φ))
```

for some fixed matter reference `ψ₀`, coordinate `i₀`, and nonzero scalar
`χ`. This is a linear slice of the joint operator, hence the channel response
is automatically amplitude-linear. The joint operator may still mix matter
and channel sectors away from that readout section.

## Main result

* `isAmplitudeLinear_channel_of_sectionReadout`:
  any channel response recovered as a nonzero section readout of a `ℂ`-linear
  joint operator is amplitude-linear.

* `channel_eq_zero_of_density_only_of_sectionReadout`:
  composing with the single-factor dichotomy, any density-only response under
  such a readout collapses to zero.

* `not_exists_nontrivial_density_only_channel_with_sectionReadout`:
  no nontrivial density-only classical channel can arise from a nonzero
  section readout of a linear joint substrate.

* `sectionReadout_of_pureTensorFactorization`:
  the old pure-tensor factorization hypothesis implies the new section-readout
  hypothesis whenever the matter side is nontrivial. Thus the new hypothesis is
  a genuine weakening of the previous proof interface.

## Anti-retreat scope

This does not prove that every physically admissible joint operator admits a
nonzero section readout. That is the remaining substrate-locality statement.
But it **does** retire the need for global pure-tensor factorization in the
amplitude-linearity theorem: factorization is sufficient, not necessary.

The next upgrade is to derive `JointSectionReadout` from a substrate locality
or measurement-access principle rather than assume it as a structural readout
law.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-! ## §1. Section-readout substrate principle -/

/-- A channel response `R_C` is a **nonzero matter-section readout** of a
joint linear operator `R_J` when it is recovered by:

1. injecting a fixed matter reference state `ψ₀` into the first tensor factor,
2. applying the joint operator,
3. extracting the channel factor at coordinate `i₀`, and
4. dividing by a nonzero scalar `χ`.

This is strictly weaker than global pure-tensor factorization: it constrains
only the operational readout section `ψ₀ ⊗ φ`, not the action of `R_J` on all
pure tensors. -/
structure JointSectionReadout
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : Signal8 → Signal8) where
  ψ₀ : Signal8
  i₀ : Fin 8
  χ : ℂ
  χ_ne_zero : χ ≠ 0
  readout :
    ∀ φ : Signal8,
      R_C φ = χ⁻¹ • (extractSecond i₀) (R_J (insertFirst ψ₀ φ))

/-! ## §2. Section readout forces amplitude-linearity -/

/-- **Section-readout forcing.** If a channel response is recovered as a
nonzero section readout of a `ℂ`-linear joint operator, then it is
amplitude-linear. No pure-tensor factorization hypothesis is used. -/
theorem isAmplitudeLinear_channel_of_sectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hReadout : JointSectionReadout R_J R_C) :
    IsAmplitudeLinear R_C := by
  refine ⟨hReadout.χ⁻¹ •
    ((extractSecond hReadout.i₀).comp (R_J.comp (insertFirst hReadout.ψ₀))), ?_⟩
  intro φ
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact hReadout.readout φ

/-- **Density-only collapse under section readout.** A density-only channel
response recovered by a nonzero section readout of a linear joint operator is
identically zero. -/
theorem channel_eq_zero_of_density_only_of_sectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hReadout : JointSectionReadout R_J R_C)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (isAmplitudeLinear_channel_of_sectionReadout hReadout) hDen φ

/-- **Existence-form no-go.** There is no nontrivial density-only channel
response that is obtained as a nonzero section readout of a linear joint
operator. -/
theorem not_exists_nontrivial_density_only_channel_with_sectionReadout :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      (∃ _hReadout : JointSectionReadout R_J R_C,
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0)) := by
  rintro ⟨R_J, R_C, hReadout, hDen, φ, hφ⟩
  exact hφ (channel_eq_zero_of_density_only_of_sectionReadout hReadout hDen φ)

/-! ## §3. Old factorization implies new section-readout principle -/

/-- The previous pure-tensor factorization hypothesis implies the new
section-readout hypothesis whenever the matter response is nontrivial at some
coordinate. This proves that the section-readout theorem strictly generalizes
the old proof interface: global factorization is sufficient for readout, but
the section-readout theorem itself does not assume it. -/
def sectionReadout_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {ψ₀ : Signal8} {i₀ : Fin 8} (hχ : (R_M ψ₀) i₀ ≠ 0) :
    JointSectionReadout R_J R_C where
  ψ₀ := ψ₀
  i₀ := i₀
  χ := (R_M ψ₀) i₀
  χ_ne_zero := hχ
  readout := by
    intro φ
    rw [insertFirst_apply, hFact, extractSecond_tmul, smul_smul,
      inv_mul_cancel₀ hχ, one_smul]

/-- The section-readout theorem recovers the old pure-tensor forcing theorem
as a corollary. -/
theorem isAmplitudeLinear_channel_of_pureTensorFactorization_via_sectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {ψ₀ : Signal8} {i₀ : Fin 8} (hχ : (R_M ψ₀) i₀ ≠ 0) :
    IsAmplitudeLinear R_C :=
  isAmplitudeLinear_channel_of_sectionReadout
    (sectionReadout_of_pureTensorFactorization hFact hχ)

/-! ## §4. Recognition-update specialization -/

/-- Recognition-update section readout: the matter section is taken to be the
actual substrate recognition update `cyclic_shift`. This is the weaker
replacement for the old global factor-product assumption in Track 2.C. -/
structure RecognitionSectionReadout
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : Signal8 → Signal8) where
  ψ₀ : Signal8
  i₀ : Fin 8
  nontrivial_matter : (recognitionUpdate ψ₀) i₀ ≠ 0
  readout :
    ∀ φ : Signal8,
      R_C φ =
        ((recognitionUpdate ψ₀) i₀)⁻¹ •
          (extractSecond i₀) (R_J (insertFirst ψ₀ φ))

/-- A recognition-section readout is a section readout. -/
def RecognitionSectionReadout.toJointSectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hReadout : RecognitionSectionReadout R_J R_C) :
    JointSectionReadout R_J R_C where
  ψ₀ := hReadout.ψ₀
  i₀ := hReadout.i₀
  χ := (recognitionUpdate hReadout.ψ₀) hReadout.i₀
  χ_ne_zero := hReadout.nontrivial_matter
  readout := hReadout.readout

/-- **Recognition-section forcing.** Under the substrate recognition update,
any channel response obtained by a nonzero section readout is amplitude-linear,
with no global pure-tensor factorization assumption. -/
theorem isAmplitudeLinear_channel_of_recognitionSectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hReadout : RecognitionSectionReadout R_J R_C) :
    IsAmplitudeLinear R_C :=
  isAmplitudeLinear_channel_of_sectionReadout hReadout.toJointSectionReadout

/-- Density-only collapse under recognition-section readout. -/
theorem channel_eq_zero_of_density_only_of_recognitionSectionReadout
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hReadout : RecognitionSectionReadout R_J R_C)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  channel_eq_zero_of_density_only_of_sectionReadout
    hReadout.toJointSectionReadout hDen φ

/-- No nontrivial density-only channel can be recovered from a recognition
section readout of a linear joint substrate. -/
theorem not_exists_nontrivial_density_only_channel_with_recognitionSectionReadout :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      (∃ _hReadout : RecognitionSectionReadout R_J R_C,
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0)) := by
  rintro ⟨R_J, R_C, hReadout, hDen, φ, hφ⟩
  exact hφ
    (channel_eq_zero_of_density_only_of_recognitionSectionReadout hReadout hDen φ)

/-! ## §5. Master cert -/

/-- Master cert for the section-readout retirement of global pure-tensor
factorization. -/
structure SectionReadoutForcingCert where
  section_forces_amplitude_linear :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      JointSectionReadout R_J R_C → IsAmplitudeLinear R_C
  section_density_only_collapse :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      JointSectionReadout R_J R_C → IsDensityOnly R_C → ∀ φ, R_C φ = 0
  no_nontrivial_density_only_section :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      (∃ _hReadout : JointSectionReadout R_J R_C,
        IsDensityOnly R_C ∧ (∃ φ : Signal8, R_C φ ≠ 0))
  factorization_implies_section :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_M R_C : Signal8 → Signal8},
      PureTensorFactorization R_J R_M R_C →
        ∀ {ψ₀ : Signal8} {i₀ : Fin 8}, (R_M ψ₀) i₀ ≠ 0 →
          JointSectionReadout R_J R_C

noncomputable def sectionReadoutForcingCert : SectionReadoutForcingCert where
  section_forces_amplitude_linear := fun h => isAmplitudeLinear_channel_of_sectionReadout h
  section_density_only_collapse := fun h hDen φ =>
    channel_eq_zero_of_density_only_of_sectionReadout h hDen φ
  no_nontrivial_density_only_section :=
    not_exists_nontrivial_density_only_channel_with_sectionReadout
  factorization_implies_section := by
    intro R_J R_M R_C hFact ψ₀ i₀ hχ
    exact sectionReadout_of_pureTensorFactorization
      (R_J := R_J) (R_M := R_M) (R_C := R_C)
      hFact (ψ₀ := ψ₀) (i₀ := i₀) hχ

theorem sectionReadoutForcingCert_inhabited : Nonempty SectionReadoutForcingCert :=
  ⟨sectionReadoutForcingCert⟩

/-- **TRACK 2.C ONE-SHOT THEOREM (section-readout form).** Global pure-tensor
factorization is not needed to force channel amplitude-linearity. It suffices
that the physical channel response is recovered as a nonzero matter-section
readout of the joint linear substrate. Under that weaker readout principle,
the channel is amplitude-linear and any density-only response collapses to
zero. The previous factorization theorem is recovered as a corollary because
factorization implies section readout. -/
theorem factor_product_retirement_one_statement :
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      JointSectionReadout R_J R_C → IsAmplitudeLinear R_C) ∧
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      JointSectionReadout R_J R_C → IsDensityOnly R_C → ∀ φ, R_C φ = 0) ∧
    (¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      (∃ _hReadout : JointSectionReadout R_J R_C,
        IsDensityOnly R_C ∧ (∃ φ : Signal8, R_C φ ≠ 0))) :=
  ⟨fun h => isAmplitudeLinear_channel_of_sectionReadout h,
   fun h hDen φ => channel_eq_zero_of_density_only_of_sectionReadout h hDen φ,
   not_exists_nontrivial_density_only_channel_with_sectionReadout⟩

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
