import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForced

/-!
# Gravity Track 2.C: Joint-Substrate Lift of the Amplitude-Linear Forcing

Session 85 (`AmplitudeLinearForced`) closed the **single-factor substrate
dichotomy** on `Signal8`: no nontrivial channel response is simultaneously
amplitude-linear and density-only.

This module lifts that result to the **joint matter-plus-channel substrate**
modelled as the binary tensor product
`JointSubstrate := Signal8 ⊗[ℂ] Signal8`. The substantive theorems:

* `isAmplitudeLinear_matter_of_pureTensorFactorization` — if a `ℂ`-linear
  joint operator `R_J` factorizes on pure tensors as
  `R_J(ψ ⊗ φ) = R_M(ψ) ⊗ R_C(φ)`, and the channel response is nontrivial
  in the sense that some coordinate `(R_C φ₀) i₀ ≠ 0`, then the matter-side
  response `R_M` is amplitude-linear.

* `isAmplitudeLinear_channel_of_pureTensorFactorization` — symmetric, with
  the channel-side amplitude-linear under nontrivial matter coupling.

* `isAmplitudeLinear_both_of_pureTensorFactorization` — composite: both
  factor responses are amplitude-linear under bilateral nontriviality.

* `channel_eq_zero_of_density_only_of_pureTensorFactorization` — the
  **Track 2.C closure step** under the binary-tensor model. Composing the
  joint-substrate lift with the Session 85 single-factor dichotomy, no joint
  substrate with nontrivial matter coupling admits a nontrivial density-only
  channel response. Equivalently, on the joint substrate, a candidate
  channel-side CPTP-classical readout collapses to the zero response.

The full Track 2.C closure of paper IV T2 (upgrade from `MODEL` to `THEOREM`)
requires combining this lift with
`Foundation.SchrodingerDerivation.schrodinger_linear` (the joint recognition
operator is `ℂ`-linear on the joint substrate by lifting the single-factor
Schrodinger linearity via `PiTensorProduct.map`), which is the next
subsessions of Track 2.C.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-- The joint matter-plus-channel substrate as a binary tensor product over `ℂ`.
The first factor is the matter ledger, the second factor is the channel ledger;
both are copies of `Signal8`. -/
abbrev JointSubstrate : Type := Signal8 ⊗[ℂ] Signal8

/-- **Pure-tensor factorization** of a joint operator. The joint operator
`R_J` acts on pure-tensor states as the factor-wise application of separate
matter and channel responses. This is the physical content of the joint
substrate being a tensor product of matter and channel ledgers. -/
def PureTensorFactorization
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_M R_C : Signal8 → Signal8) : Prop :=
  ∀ (ψ φ : Signal8), R_J (ψ ⊗ₜ[ℂ] φ) = (R_M ψ) ⊗ₜ[ℂ] (R_C φ)

/-- Coordinate-evaluation linear functional on `Signal8 = Fin 8 → ℂ`. -/
def evalAt (i : Fin 8) : Signal8 →ₗ[ℂ] ℂ := LinearMap.proj i

@[simp]
theorem evalAt_apply (i : Fin 8) (v : Signal8) : evalAt i v = v i := rfl

/-- Insert a fixed channel state into the second factor of the joint
substrate, as a `ℂ`-linear map `Signal8 →ₗ[ℂ] JointSubstrate` taking
`ψ ↦ ψ ⊗ₜ[ℂ] φ`. -/
noncomputable def insertSecond (φ : Signal8) : Signal8 →ₗ[ℂ] JointSubstrate :=
  (TensorProduct.mk ℂ Signal8 Signal8).flip φ

@[simp]
theorem insertSecond_apply (φ ψ : Signal8) :
    insertSecond φ ψ = ψ ⊗ₜ[ℂ] φ := rfl

/-- Insert a fixed matter state into the first factor of the joint substrate,
as a `ℂ`-linear map `Signal8 →ₗ[ℂ] JointSubstrate` taking `φ ↦ ψ ⊗ₜ[ℂ] φ`. -/
noncomputable def insertFirst (ψ : Signal8) : Signal8 →ₗ[ℂ] JointSubstrate :=
  TensorProduct.mk ℂ Signal8 Signal8 ψ

@[simp]
theorem insertFirst_apply (ψ φ : Signal8) :
    insertFirst ψ φ = ψ ⊗ₜ[ℂ] φ := rfl

/-- Extract the first factor of a pure tensor, scaled by the coordinate-`i`
component of the second factor. Linear on the whole `JointSubstrate` by the
universal property of the tensor product. -/
noncomputable def extractFirst (i : Fin 8) : JointSubstrate →ₗ[ℂ] Signal8 :=
  (TensorProduct.rid ℂ Signal8).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : Signal8 →ₗ[ℂ] Signal8) (evalAt i))

@[simp]
theorem extractFirst_tmul (i : Fin 8) (ψ φ : Signal8) :
    extractFirst i (ψ ⊗ₜ[ℂ] φ) = (φ i) • ψ := by
  simp [extractFirst, TensorProduct.map_tmul, TensorProduct.rid_tmul]

/-- Extract the second factor of a pure tensor, scaled by the coordinate-`i`
component of the first factor. -/
noncomputable def extractSecond (i : Fin 8) : JointSubstrate →ₗ[ℂ] Signal8 :=
  (TensorProduct.lid ℂ Signal8).toLinearMap.comp
    (TensorProduct.map (evalAt i) (LinearMap.id : Signal8 →ₗ[ℂ] Signal8))

@[simp]
theorem extractSecond_tmul (i : Fin 8) (ψ φ : Signal8) :
    extractSecond i (ψ ⊗ₜ[ℂ] φ) = (ψ i) • φ := by
  simp [extractSecond, TensorProduct.map_tmul, TensorProduct.lid_tmul]

/-- **Track 2.C forward direction (matter side).** If a `ℂ`-linear joint
operator `R_J` factorizes on pure tensors through factor-wise responses
`R_M, R_C`, and the channel response is nontrivial at some coordinate
`(R_C φ₀) i₀`, then the matter-side response `R_M` is amplitude-linear. -/
theorem isAmplitudeLinear_matter_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {φ₀ : Signal8} {i₀ : Fin 8} (hNontrivial : (R_C φ₀) i₀ ≠ 0) :
    IsAmplitudeLinear R_M := by
  refine ⟨((R_C φ₀) i₀)⁻¹ •
    ((extractFirst i₀).comp (R_J.comp (insertSecond φ₀))), ?_⟩
  intro ψ
  show R_M ψ = _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      insertSecond_apply, hFact, extractFirst_tmul,
      smul_smul, inv_mul_cancel₀ hNontrivial, one_smul]

/-- **Track 2.C forward direction (channel side).** If a `ℂ`-linear joint
operator `R_J` factorizes on pure tensors through factor-wise responses
`R_M, R_C`, and the matter response is nontrivial at some coordinate
`(R_M ψ₀) i₀`, then the channel-side response `R_C` is amplitude-linear. -/
theorem isAmplitudeLinear_channel_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {ψ₀ : Signal8} {i₀ : Fin 8} (hNontrivial : (R_M ψ₀) i₀ ≠ 0) :
    IsAmplitudeLinear R_C := by
  refine ⟨((R_M ψ₀) i₀)⁻¹ •
    ((extractSecond i₀).comp (R_J.comp (insertFirst ψ₀))), ?_⟩
  intro φ
  show R_C φ = _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      insertFirst_apply, hFact, extractSecond_tmul,
      smul_smul, inv_mul_cancel₀ hNontrivial, one_smul]

/-- **Composite forward direction.** Under joint `ℂ`-linearity, pure-tensor
factorization, and bilateral nontriviality, both factor responses are
amplitude-linear. -/
theorem isAmplitudeLinear_both_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {φ₀ : Signal8} {i_C : Fin 8} (hC : (R_C φ₀) i_C ≠ 0)
    {ψ₀ : Signal8} {i_M : Fin 8} (hM : (R_M ψ₀) i_M ≠ 0) :
    IsAmplitudeLinear R_M ∧ IsAmplitudeLinear R_C :=
  ⟨isAmplitudeLinear_matter_of_pureTensorFactorization hFact hC,
   isAmplitudeLinear_channel_of_pureTensorFactorization hFact hM⟩

/-- **Track 2.C closure step (no density-only channel under nontrivial matter
coupling).** If `R_J` is `ℂ`-linear, factorizes on pure tensors through
`R_M, R_C`, the matter response is nontrivial, and the channel response is
density-only (the structural footprint of a CPTP-classical readout), then
the channel response is identically zero.

This is the substantive Track 2.C dichotomy at the joint substrate level:
no joint substrate with nontrivial matter coupling admits a nontrivial
density-only channel response. Composing the joint-substrate lift
(`isAmplitudeLinear_channel_of_pureTensorFactorization`) with the Session 85
single-factor dichotomy (`eq_zero_of_isAmplitudeLinear_isDensityOnly`). -/
theorem channel_eq_zero_of_density_only_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {ψ₀ : Signal8} {i₀ : Fin 8} (hM : (R_M ψ₀) i₀ ≠ 0)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (isAmplitudeLinear_channel_of_pureTensorFactorization hFact hM) hDen φ

/-- Symmetric closure: under nontrivial channel coupling, no density-only
matter response is admissible. -/
theorem matter_eq_zero_of_density_only_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {φ₀ : Signal8} {i₀ : Fin 8} (hC : (R_C φ₀) i₀ ≠ 0)
    (hDen : IsDensityOnly R_M) (ψ : Signal8) :
    R_M ψ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (isAmplitudeLinear_matter_of_pureTensorFactorization hFact hC) hDen ψ

/-- **No-go (existence form).** On the joint substrate, there is no candidate
joint recognition operator that factorizes through nontrivial matter coupling
*and* a nontrivial density-only channel response. The hypotheses cannot be
simultaneously satisfied. -/
theorem not_exists_pureTensorFactorization_nontrivial_matter_density_only_channel :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_M R_C : Signal8 → Signal8),
      PureTensorFactorization R_J R_M R_C ∧
        (∃ ψ₀ : Signal8, ∃ i₀ : Fin 8, (R_M ψ₀) i₀ ≠ 0) ∧
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0) := by
  rintro ⟨R_J, R_M, R_C, hFact, ⟨ψ₀, i₀, hM⟩, hDen, φ, hCφ⟩
  exact hCφ (channel_eq_zero_of_density_only_of_pureTensorFactorization
    hFact hM hDen φ)

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
