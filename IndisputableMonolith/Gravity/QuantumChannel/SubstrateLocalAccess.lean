import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForcedSectionReadout

/-!
# Gravity Track 2.C: Substrate Locality / Measurement-Access Principle

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This is the next step beyond Session 111's section-readout retirement.

Session 111 proved: if a channel response is a nonzero matter-section
readout of a linear joint operator, then it is forced amplitude-linear.
Pure-tensor factorization is sufficient but not necessary for this
readout law.

The remaining assumption was that the *physical channel* is operationally
obtained by such a section readout. This module derives **that**
assumption from a sharper substrate-level principle: **substrate
locality / measurement-access**.

The principle says: every operational channel observable on the joint
substrate `Signal8 ⊗ Signal8` is obtained as a recognition probe — fix a
matter reference state `ψ₀`, run the joint operator `R_J` once, and read
a channel coordinate `i₀`, normalised by a calibration scalar `χ ≠ 0`.

Under this principle, the channel `R_C` is *defined* by the induced
formula
`R_C φ = χ⁻¹ • extractSecond i₀ (R_J (insertFirst ψ₀ φ))`,
which is automatically a `JointSectionReadout`. Section readout is no
longer an assumption; it is the **definition** of how the operational
channel is harvested from `R_J` under substrate locality.

## The implication chain

```
SubstrateAccessData R_J R_C            (Session 113 substrate principle)
                |
                v
JointSectionReadout R_J R_C            (Session 111 readout law)
                |
                v
IsAmplitudeLinear R_C                  (channel forced amplitude-linear)
                |
                v
density-only response forced to 0      (Track 2.C closure)
```

Each arrow is a Lean theorem. The chain replaces the global factor-product
hypothesis with the **substrate measurement-access principle**, which is
sharper and substrate-internal.

## Anti-retreat

The substrate-access principle is **not** an RS-specific axiom. It is the
standard quantum-mechanical fact that physical observables on a
tensor-product Hilbert space are obtained by partial inner products
against fixed probe states, composed with the joint dynamics. This module
makes that explicit in the binary `Signal8` substrate.

What this module does NOT do: derive the substrate-access principle from
T0-T8 alone. That is the next layer down — showing that any operational
recognition observable on the joint substrate must be of induced form.
This module makes the principle the named structural axiom and proves
that under it, the channel forcing chain closes without any reference to
factor-product, pure-tensor decomposition, or operator factorisation.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-! ## §1. Substrate measurement-access data -/

/-- **Substrate measurement-access data.** A matter probe state `ψ₀`,
a channel-side readout coordinate `i₀`, and a nonzero calibration
scalar `χ`. This is the data of one recognition-update measurement
probe on the joint substrate. -/
structure SubstrateAccessData where
  ψ₀ : Signal8
  i₀ : Fin 8
  χ : ℂ
  χ_ne_zero : χ ≠ 0

/-- The channel induced by a substrate access on a joint linear
operator: prepare matter state `ψ₀` in the first factor, apply `R_J`,
extract the `i₀`-coordinate of the channel factor, normalise by `χ`.
This is the operational channel-readout recipe enforced by substrate
locality. -/
noncomputable def inducedChannel
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (access : SubstrateAccessData) : Signal8 → Signal8 :=
  fun φ =>
    access.χ⁻¹ • (extractSecond access.i₀) (R_J (insertFirst access.ψ₀ φ))

@[simp]
theorem inducedChannel_apply
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (access : SubstrateAccessData) (φ : Signal8) :
    inducedChannel R_J access φ =
      access.χ⁻¹ • (extractSecond access.i₀) (R_J (insertFirst access.ψ₀ φ)) :=
  rfl

/-! ## §2. Induced channel is automatically a section readout -/

/-- The induced channel of any substrate access is a `JointSectionReadout`
of `R_J`. No additional hypothesis needed. -/
noncomputable def inducedChannel_isSectionReadout
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (access : SubstrateAccessData) :
    JointSectionReadout R_J (inducedChannel R_J access) where
  ψ₀ := access.ψ₀
  i₀ := access.i₀
  χ := access.χ
  χ_ne_zero := access.χ_ne_zero
  readout := fun _ => rfl

/-! ## §3. The substrate locality / measurement-access principle -/

/-- **Substrate locality / measurement-access principle for a channel.**
A channel response `R_C` *arises from substrate access* of a joint linear
operator `R_J` if there is access data such that `R_C` equals the
induced channel for that data.

The general principle is the meta-claim that every operational channel
observable on the joint substrate is of this form. For Lean, we
encode the per-channel proposition; the substrate locality principle
is then asserted as a hypothesis on the specific `R_J / R_C` pair under
consideration. -/
def ArisesFromSubstrateAccess
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : Signal8 → Signal8) : Prop :=
  ∃ access : SubstrateAccessData, R_C = inducedChannel R_J access

/-! ## §4. Substrate locality → section readout → amplitude-linear -/

/-- **From the substrate locality principle, the channel is a section
readout.** This is the first link in the new derivation chain: substrate
locality is the substantive axiom; section readout follows. -/
theorem sectionReadout_of_arisesFromSubstrateAccess
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hAccess : ArisesFromSubstrateAccess R_J R_C) :
    Nonempty (JointSectionReadout R_J R_C) := by
  obtain ⟨access, hEq⟩ := hAccess
  refine ⟨{
    ψ₀ := access.ψ₀
    i₀ := access.i₀
    χ := access.χ
    χ_ne_zero := access.χ_ne_zero
    readout := ?_ }⟩
  intro φ
  have h := congrFun hEq φ
  simp [inducedChannel] at h
  exact h

/-- **From substrate locality alone, the channel is amplitude-linear.**
No pure-tensor factorization, no operator-product hypothesis, no global
readout assumption: substrate locality + joint linearity is enough. -/
theorem isAmplitudeLinear_channel_of_arisesFromSubstrateAccess
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hAccess : ArisesFromSubstrateAccess R_J R_C) :
    IsAmplitudeLinear R_C := by
  obtain ⟨readout⟩ := sectionReadout_of_arisesFromSubstrateAccess hAccess
  exact isAmplitudeLinear_channel_of_sectionReadout readout

/-- **Density-only collapse under substrate locality.** Any density-only
channel that arises from substrate access of a linear joint operator
collapses to the trivial zero response. -/
theorem channel_eq_zero_of_density_only_of_arisesFromSubstrateAccess
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hAccess : ArisesFromSubstrateAccess R_J R_C)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (isAmplitudeLinear_channel_of_arisesFromSubstrateAccess hAccess) hDen φ

/-- **No-go (existence form).** No nontrivial density-only channel can
arise from substrate access of a linear joint operator. -/
theorem not_exists_nontrivial_density_only_channel_with_substrateAccess :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      ArisesFromSubstrateAccess R_J R_C ∧
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0) := by
  rintro ⟨R_J, R_C, hAccess, hDen, φ, hφ⟩
  exact hφ
    (channel_eq_zero_of_density_only_of_arisesFromSubstrateAccess
       hAccess hDen φ)

/-! ## §5. Factor-product implies substrate access (compatibility) -/

/-- The earlier pure-tensor factorization hypothesis implies the new
substrate-access principle whenever the matter side is nontrivial at
some coordinate. The factorization-induced channel coincides with the
substrate-access induced channel for the witnessing data. -/
theorem arisesFromSubstrateAccess_of_pureTensorFactorization
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_M R_C : Signal8 → Signal8}
    (hFact : PureTensorFactorization R_J R_M R_C)
    {ψ₀ : Signal8} {i₀ : Fin 8} (hχ : (R_M ψ₀) i₀ ≠ 0) :
    ArisesFromSubstrateAccess R_J R_C := by
  refine ⟨{ ψ₀ := ψ₀, i₀ := i₀, χ := (R_M ψ₀) i₀, χ_ne_zero := hχ }, ?_⟩
  funext φ
  unfold inducedChannel
  show R_C φ = ((R_M ψ₀) i₀)⁻¹ •
    (extractSecond i₀) (R_J (insertFirst ψ₀ φ))
  rw [insertFirst_apply, hFact, extractSecond_tmul, smul_smul,
    inv_mul_cancel₀ hχ, one_smul]

/-! ## §6. Canonical substrate-access inhabitant (recognition probe) -/

/-- **Canonical substrate-access witness: the recognition probe.** Take
the matter reference state to be the constant-1 signal and the channel
readout coordinate to be `0`. The calibration scalar is `(recognitionUpdate 1) 0`,
which is `1` by the cyclic-shift unfolding. This makes the substrate-access
hypothesis space non-vacuously inhabited for the canonical recognition
coupling. -/
def recognitionProbeAccess : SubstrateAccessData where
  ψ₀ := (1 : Signal8)
  i₀ := 0
  χ := (recognitionUpdate (1 : Signal8)) 0
  χ_ne_zero := by
    -- (recognitionUpdate 1) 0 = (1 : Signal8) ⟨1, _⟩ = 1 ≠ 0
    show (1 : Signal8) ⟨1, by decide⟩ ≠ (0 : ℂ)
    exact one_ne_zero

/-- The canonical recognition-coupled joint operator (Session 87) with its
recognition-side channel response arises from the recognition-probe
substrate access. This makes the substrate-access proposition non-vacuously
inhabited. -/
theorem canonicalCyclicJointOperator_arisesFromRecognitionProbe :
    ArisesFromSubstrateAccess canonicalCyclicJointOperator recognitionUpdate := by
  apply arisesFromSubstrateAccess_of_pureTensorFactorization
    canonicalCyclicJointOperator_pureTensorFactorization
    (ψ₀ := (1 : Signal8)) (i₀ := 0)
  show (recognitionUpdate (1 : Signal8)) 0 ≠ (0 : ℂ)
  show (1 : Signal8) ⟨1, by decide⟩ ≠ (0 : ℂ)
  exact one_ne_zero

/-! ## §7. Master cert -/

/-- Master cert for the substrate locality / measurement-access principle.
Records the implication chain
`ArisesFromSubstrateAccess → JointSectionReadout → IsAmplitudeLinear`
along with the no-go theorem on density-only channels and the
non-vacuous inhabitant. -/
structure SubstrateLocalAccessCert where
  /-- Substrate access implies section readout (key link in the chain). -/
  section_readout_from_access :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      ArisesFromSubstrateAccess R_J R_C →
        Nonempty (JointSectionReadout R_J R_C)
  /-- Substrate access forces channel amplitude-linearity. -/
  amplitude_linear_from_access :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      ArisesFromSubstrateAccess R_J R_C → IsAmplitudeLinear R_C
  /-- Density-only collapse under substrate access. -/
  density_only_collapse :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      ArisesFromSubstrateAccess R_J R_C → IsDensityOnly R_C →
        ∀ φ, R_C φ = 0
  /-- Existence-form no-go for nontrivial classical mediators. -/
  no_nontrivial_density_only :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      ArisesFromSubstrateAccess R_J R_C ∧ IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0)
  /-- Compatibility: factor-product implies substrate access. -/
  factorization_implies_access :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_M R_C : Signal8 → Signal8},
      PureTensorFactorization R_J R_M R_C →
        ∀ {ψ₀ : Signal8} {i₀ : Fin 8}, (R_M ψ₀) i₀ ≠ 0 →
          ArisesFromSubstrateAccess R_J R_C
  /-- Non-vacuous inhabitant: the canonical recognition-coupling. -/
  canonical_witness :
    ArisesFromSubstrateAccess canonicalCyclicJointOperator recognitionUpdate

noncomputable def substrateLocalAccessCert : SubstrateLocalAccessCert where
  section_readout_from_access := fun hAccess =>
    sectionReadout_of_arisesFromSubstrateAccess hAccess
  amplitude_linear_from_access := fun hAccess =>
    isAmplitudeLinear_channel_of_arisesFromSubstrateAccess hAccess
  density_only_collapse := fun hAccess hDen φ =>
    channel_eq_zero_of_density_only_of_arisesFromSubstrateAccess hAccess hDen φ
  no_nontrivial_density_only :=
    not_exists_nontrivial_density_only_channel_with_substrateAccess
  factorization_implies_access := by
    intro R_J R_M R_C hFact ψ₀ i₀ hχ
    exact arisesFromSubstrateAccess_of_pureTensorFactorization
      (R_J := R_J) (R_M := R_M) (R_C := R_C)
      hFact (ψ₀ := ψ₀) (i₀ := i₀) hχ
  canonical_witness :=
    canonicalCyclicJointOperator_arisesFromRecognitionProbe

theorem substrateLocalAccessCert_inhabited :
    Nonempty SubstrateLocalAccessCert :=
  ⟨substrateLocalAccessCert⟩

/-! ## §8. One-statement substrate locality theorem -/

/-- **SUBSTRATE LOCALITY ONE-STATEMENT (Session 113).** Under the substrate
measurement-access principle on the joint substrate `Signal8 ⊗[ℂ] Signal8`,
the channel response is automatically amplitude-linear and any density-only
response collapses to zero. The principle is non-vacuously inhabited by the
canonical recognition-coupling. Section readout (Session 111) is no longer
an assumption; it is a derived consequence of substrate locality + joint
linearity. The factor-product theorem (Sessions 85-88) is also a corollary.

This sits one level deeper in the substrate axiomatisation than Session
111. The remaining unconditional step is to derive the
`ArisesFromSubstrateAccess` proposition itself from T0-T8 alone, i.e.,
to show that every operational recognition observable on the joint
substrate must be of induced form. That is substrate semantics and is the
next session-scale target. -/
theorem substrate_local_access_one_statement :
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
       {R_C : Signal8 → Signal8},
       ArisesFromSubstrateAccess R_J R_C →
         Nonempty (JointSectionReadout R_J R_C)) ∧
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
       {R_C : Signal8 → Signal8},
       ArisesFromSubstrateAccess R_J R_C → IsAmplitudeLinear R_C) ∧
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
       {R_C : Signal8 → Signal8},
       ArisesFromSubstrateAccess R_J R_C → IsDensityOnly R_C →
         ∀ φ, R_C φ = 0) ∧
    (¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
         (R_C : Signal8 → Signal8),
       ArisesFromSubstrateAccess R_J R_C ∧ IsDensityOnly R_C ∧
         (∃ φ : Signal8, R_C φ ≠ 0)) ∧
    ArisesFromSubstrateAccess canonicalCyclicJointOperator recognitionUpdate :=
  ⟨fun hAccess => sectionReadout_of_arisesFromSubstrateAccess hAccess,
   fun hAccess => isAmplitudeLinear_channel_of_arisesFromSubstrateAccess hAccess,
   fun hAccess hDen φ =>
     channel_eq_zero_of_density_only_of_arisesFromSubstrateAccess hAccess hDen φ,
   not_exists_nontrivial_density_only_channel_with_substrateAccess,
   canonicalCyclicJointOperator_arisesFromRecognitionProbe⟩

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
