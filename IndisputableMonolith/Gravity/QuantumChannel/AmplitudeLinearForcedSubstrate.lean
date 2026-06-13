import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForcedJoint
import IndisputableMonolith.Gravity.MacroscopicLedger

/-!
# Gravity Track 2.C: Substrate-Side Closure

Sessions 85 (`AmplitudeLinearForced`) and 86 (`AmplitudeLinearForcedJoint`)
established:

* the single-factor substrate dichotomy `IsAmplitudeLinear ∧ IsDensityOnly → 0`
  (Session 85), and

* the joint-substrate lift `R_J ℂ-linear ∧ PureTensorFactorization R_J R_M R_C ∧
  (R_M nontrivial) → IsAmplitudeLinear R_C` (Session 86).

Both prior sessions were modulo the assumption that the joint operator
factorizes on pure tensors through factor-wise responses. This session
substantiates Track 2.C by plugging in the actual substrate dynamics
`cyclic_shift` (the unique `ℂ`-linear single-tick recognition update on
`Signal8` from `Foundation.SchrodingerDerivation`, packaged as
`Gravity.MacroscopicLedger.cyclicShiftLinear`) on the matter side.

Substantive theorems:

* `recognitionUpdate_nontrivial` — the substrate recognition update is
  nontrivial: `(cyclic_shift 1) 0 = 1 ≠ 0`. Hence the Session 86 lift's
  nontriviality hypothesis is satisfied by substrate-default matter dynamics.

* `isAmplitudeLinear_channel_of_recognitionUpdate` — under the substrate
  recognition update on the matter side, any candidate channel response
  participating in a `ℂ`-linear joint operator via pure-tensor factorization
  is forced to be amplitude-linear. This is the **Track 2.C substrate-side
  forcing** restricted to the binary-tensor model.

* `channel_eq_zero_of_density_only_of_recognitionUpdate` — composing with
  Session 85's dichotomy: a density-only channel response under substrate
  matter dynamics is identically zero.

* `not_exists_density_only_channel_with_recognitionUpdate` — no-go theorem
  (existence form): no joint recognition operator on the binary tensor
  substrate factorizes through cyclic-shift matter dynamics and a
  nontrivial density-only channel response simultaneously.

* `canonicalCyclicJointOperator` — concrete witness that the hypothesis
  space of the forcing theorem is nonempty: `TensorProduct.map cyclicShiftLinear
  cyclicShiftLinear` factorizes through the recognition update on both sides.

The remaining gap in the master-plan §4 Track 2.C step 5 ("in any joint
extension that preserves `schrodinger_linear`, `R_channel` must be
amplitude-linear") is that the pure-tensor factorization hypothesis is
*assumed*, not *derived* from substrate Schrodinger linearity alone. A general
`ℂ`-linear endomorphism of `Signal8 ⊗[ℂ] Signal8` need not be of the form
`f ⊗ g`; the tensor-product structure of the joint substrate plus the matter
side being constrained to `cyclic_shift` is the additional physical input
needed. Subsequent sessions will address this last step (either by
restricting to operators that factorize, or by deriving factorization from
stricter substrate axioms).

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-- The substrate recognition update on a single `Signal8` factor:
`Foundation.SchrodingerDerivation.cyclic_shift` (an `abbrev` for
`Spectral.cyclic_shift`), expressed as a function `Signal8 → Signal8`. -/
abbrev recognitionUpdate : Signal8 → Signal8 :=
  IndisputableMonolith.Spectral.cyclic_shift

/-- The substrate recognition update is amplitude-linear, witnessed by
`Gravity.MacroscopicLedger.cyclicShiftLinear`. This packages the
`schrodinger_linear` content for the single-factor side. -/
theorem isAmplitudeLinear_recognitionUpdate :
    IsAmplitudeLinear recognitionUpdate :=
  ⟨IndisputableMonolith.Gravity.MacroscopicLedger.cyclicShiftLinear,
   fun _ => rfl⟩

/-- The substrate recognition update is nontrivial. Concrete witness: the
constant-1 signal maps to itself under the cyclic shift, so
`(recognitionUpdate 1) 0 = 1 ≠ 0`. -/
theorem recognitionUpdate_nontrivial :
    ∃ (ψ₀ : Signal8) (i₀ : Fin 8), (recognitionUpdate ψ₀) i₀ ≠ 0 := by
  refine ⟨(1 : Signal8), 0, ?_⟩
  -- `recognitionUpdate 1 0` unfolds to `(1 : Signal8) ⟨(0+1)%8, _⟩ = 1 ⟨1, _⟩ = 1`.
  show (1 : Signal8) ⟨1, by decide⟩ ≠ (0 : ℂ)
  exact one_ne_zero

/-- **Track 2.C substrate-side forcing.** If a `ℂ`-linear joint operator
factorizes on pure tensors with the substrate recognition update on the
matter side, then the channel response is necessarily amplitude-linear.
This is the substantive forcing step: substrate dynamics on the matter
factor inherits amplitude-linearity to the channel factor via the joint
linearity of `R_J`. -/
theorem isAmplitudeLinear_channel_of_recognitionUpdate
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J recognitionUpdate R_C) :
    IsAmplitudeLinear R_C := by
  obtain ⟨ψ₀, i₀, hNontrivial⟩ := recognitionUpdate_nontrivial
  exact isAmplitudeLinear_channel_of_pureTensorFactorization
    (R_M := recognitionUpdate) (R_C := R_C) hFact hNontrivial

/-- **Track 2.C closure step under substrate dynamics.** Under the substrate
recognition update on the matter side, no density-only channel response is
admissible: any such response is identically zero. Composes the joint-substrate
lift with Session 85's single-factor dichotomy, and substantiates the lift's
nontriviality hypothesis with the actual cyclic-shift recognition update.

This is the binary-tensor-model upgrade of paper IV's T2 from MODEL to
THEOREM, modulo the pure-tensor factorization assumption that the joint
operator is of product form. The remaining MODEL tag concerns precisely
that factorization: a general `ℂ`-linear endomorphism of `Signal8 ⊗[ℂ]
Signal8` need not factorize; deriving the factorization from substrate
axioms alone is the next subsession. -/
theorem channel_eq_zero_of_density_only_of_recognitionUpdate
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J recognitionUpdate R_C)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (isAmplitudeLinear_channel_of_recognitionUpdate hFact) hDen φ

/-- **No-go theorem (existence form).** No joint recognition operator on
`JointSubstrate` factorizes through cyclic-shift matter dynamics and a
nontrivial density-only channel response. -/
theorem not_exists_density_only_channel_with_recognitionUpdate :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      PureTensorFactorization R_J recognitionUpdate R_C ∧
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0) := by
  rintro ⟨R_J, R_C, hFact, hDen, φ, hCφ⟩
  exact hCφ
    (channel_eq_zero_of_density_only_of_recognitionUpdate hFact hDen φ)

/-- **Canonical joint operator from substrate dynamics.** Concrete witness
that the hypothesis space of the forcing theorem is nonempty:
`TensorProduct.map cyclicShiftLinear cyclicShiftLinear` is a `ℂ`-linear
endomorphism of `JointSubstrate` that factorizes through `recognitionUpdate`
on both factors. -/
noncomputable def canonicalCyclicJointOperator :
    JointSubstrate →ₗ[ℂ] JointSubstrate :=
  TensorProduct.map
    IndisputableMonolith.Gravity.MacroscopicLedger.cyclicShiftLinear
    IndisputableMonolith.Gravity.MacroscopicLedger.cyclicShiftLinear

/-- The canonical joint operator factorizes through the recognition update on
both factors. -/
theorem canonicalCyclicJointOperator_pureTensorFactorization :
    PureTensorFactorization canonicalCyclicJointOperator
      recognitionUpdate recognitionUpdate := by
  intro ψ φ
  show (TensorProduct.map _ _) (ψ ⊗ₜ[ℂ] φ) =
       (recognitionUpdate ψ) ⊗ₜ[ℂ] (recognitionUpdate φ)
  rw [TensorProduct.map_tmul]
  rfl

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
