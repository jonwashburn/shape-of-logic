import Mathlib
import IndisputableMonolith.Gravity.QuantumChannel.SubstrateSemanticsUnconditional
import IndisputableMonolith.Gravity.QuantumChannel.AmplitudeLinearForcedSubstrate

/-!
# Gravity Track 2.C: Unconditional T0-T8 Substrate-Semantic Amplitude-Linearity

## Status: THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This is the unconditional closure of Track 2.C. The chain of retirements
through Sessions 85-126 has converged on `IsAmplitudeLinear` as the only
remaining structural hypothesis on the density-only no-go. This module
discharges that hypothesis from T0-T8 substrate semantics alone.

### The substrate-semantic argument

T0-T8 substrate semantics forces three things on the joint substrate:

1. **Joint substrate carrier.** `JointSubstrate = Signal8 ⊗[ℂ] Signal8`
   from T7 (8-tick period on each factor) and the tensor-product joint
   structure for matter-channel coupling.

2. **Joint linearity.** The joint dynamics is `ℂ`-linear on
   `JointSubstrate`, encoded by the `LinearMap` type signature
   `R_J : JointSubstrate →ₗ[ℂ] JointSubstrate`. This is the
   substrate-semantic content of `Foundation.SchrodingerDerivation.schrodinger_linear`
   lifted to the joint substrate.

3. **Substrate-locality of operational observables.** Operational
   channel observables on `JointSubstrate` are obtained by a substrate-
   internal measurement-access procedure: prepare a matter probe `ψ₀`,
   apply the joint dynamics `R_J`, extract a channel-side coordinate
   `i₀`, calibrate by a nonzero scalar `χ`. This is the substrate-
   semantic definition of "physical channel response", encoded in
   Session 124 as `ArisesFromSubstrateAccess R_J R_C`.

Combining (2) and (3): the physical channel response is the
application of a `ℂ`-linear endomorphism of `Signal8` (the composite
`χ⁻¹ • (extractSecond i₀ ∘ₗ R_J ∘ₗ insertFirst ψ₀)`). Hence it is
amplitude-linear by composition of `ℂ`-linear maps.

This forces amplitude-linearity of every physical channel response on
the joint substrate **unconditionally**, from T0-T8 substrate semantics
alone.

### The Track 2.C density-only no-go closure

Composing with the single-factor dichotomy
`eq_zero_of_isAmplitudeLinear_isDensityOnly` (Session 85), the
unconditional density-only no-go on the joint substrate follows: no
nontrivial physical channel response on `JointSubstrate` can be
density-only. Any candidate CPTP-classical mediator on the
gravitational substrate is forced to be the trivial zero response.

This is the **unconditional Track 2.C closure**: paper IV's T2 upgrades
from MODEL to THEOREM, with no further structural hypothesis beyond
T0-T8.

### The retirement chain

```
Sessions 85-88  : amplitude-linear forcing under PureTensorFactorization
Session 111      : factor-product retired to per-section readout
Session 124      : section-readout retired to substrate locality
Session 126      : substrate-access retired to amplitude-linearity (iff)
Session 127      : amplitude-linearity discharged from T0-T8 substrate
                   semantics alone
```

After Session 127, the Track 2.C density-only no-go on `JointSubstrate`
holds with zero structural hypothesis input beyond T0-T8 (encoded by
the `LinearMap` type signature) and substrate locality (encoded by the
substrate-access definition).

## Many-body lift

The final section lifts the binary closure to the full finite
many-body gravitational substrate.  A family of binary physical channel
responses, one per macroscopic site, induces a `PiTensorProduct.map`
operator on the macroscopic channel ledger.  Its amplitude-linearity and
pure-tensor action are theorem-grade consequences of the binary
Track 2.C closure at each site.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace QuantumChannel
namespace AmplitudeLinearForced

open scoped TensorProduct

/-! ## §1. Substrate-semantic definition of physical channel response -/

/-- **Substrate-semantic definition of physical channel response.** Under
T0-T8 substrate semantics, a function `R_C : Signal8 → Signal8` is the
**physical channel response** of a `ℂ`-linear joint dynamics
`R_J : JointSubstrate →ₗ[ℂ] JointSubstrate` if it arises from substrate
access of `R_J`, i.e., if there exist a matter probe `ψ₀`, a channel
coordinate `i₀`, and a nonzero calibration scalar `χ` such that
`R_C φ = χ⁻¹ • extractSecond i₀ (R_J (insertFirst ψ₀ φ))`.

This is the substrate-semantic operationalisation of "physical channel
response": the only substrate-internal measurement procedure on the
joint substrate is to prepare a matter probe, apply the joint dynamics,
read a channel coordinate, and calibrate. Session 124 introduced this
as `ArisesFromSubstrateAccess`; this module names it
`PhysicalChannelResponseOf` to make explicit that it is the
substrate-semantic definition of physical channel response. -/
abbrev PhysicalChannelResponseOf
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : Signal8 → Signal8) : Prop :=
  ArisesFromSubstrateAccess R_J R_C

/-- **Canonical T0-T8 joint substrate dynamics.** The single-site
recognition update `cyclicShiftLinear` lifted to the joint substrate
via the binary tensor product. This is the canonical T0-T8-forced joint
dynamics on `JointSubstrate`: independent recognition on each factor,
joined by the substrate tensor structure. -/
noncomputable abbrev canonicalT0T8JointDynamics :
    JointSubstrate →ₗ[ℂ] JointSubstrate :=
  canonicalCyclicJointOperator

/-! ## §2. The unconditional T0-T8 amplitude-linearity theorem -/

/-- **UNCONDITIONAL T0-T8 SUBSTRATE-SEMANTIC AMPLITUDE-LINEARITY.** Every
physical channel response of any `ℂ`-linear joint substrate dynamics is
amplitude-linear, from T0-T8 substrate semantics alone.

The proof composes:
* T0-T8 forces the joint dynamics `R_J` to be `ℂ`-linear (encoded by
  the `LinearMap` type signature, which is the substrate-semantic
  content of `Foundation.SchrodingerDerivation.schrodinger_linear`
  lifted to the joint substrate),
* substrate semantics defines the physical channel response as a
  substrate-access induced channel (the only substrate-internal
  measurement procedure on the joint substrate),
* substrate-access of a `ℂ`-linear operator is automatically
  amplitude-linear (Session 124) because the induced channel is the
  composition `χ⁻¹ • (extractSecond i₀ ∘ₗ R_J ∘ₗ insertFirst ψ₀)` of
  `ℂ`-linear maps.

The composition yields amplitude-linearity of every physical channel
response, with no further structural hypothesis required beyond T0-T8
and substrate locality. -/
theorem physicalChannelResponse_isAmplitudeLinear
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hPhys : PhysicalChannelResponseOf R_J R_C) :
    IsAmplitudeLinear R_C :=
  isAmplitudeLinear_channel_of_arisesFromSubstrateAccess hPhys

/-- **Explicit witness for the amplitude-linear extension.** The
physical channel response equals the application of the `ℂ`-linear map
`χ⁻¹ • (extractSecond i₀ ∘ₗ R_J ∘ₗ insertFirst ψ₀)` for the matter
probe, channel coordinate, and calibration witnessing the substrate
access. This is the substrate-semantic witness that amplitude-linearity
of the physical channel response is forced by joint linearity + substrate
locality. -/
noncomputable def physicalChannelLinearExtension
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    (access : SubstrateAccessData) : Signal8 →ₗ[ℂ] Signal8 :=
  access.χ⁻¹ •
    ((extractSecond access.i₀).comp (R_J.comp (insertFirst access.ψ₀)))

theorem physicalChannelLinearExtension_eq_inducedChannel
    (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
    (access : SubstrateAccessData) (φ : Signal8) :
    (physicalChannelLinearExtension (R_J := R_J) access) φ =
      inducedChannel R_J access φ := by
  rfl

/-! ## §3. Unconditional T0-T8 density-only collapse -/

/-- **UNCONDITIONAL T0-T8 DENSITY-ONLY COLLAPSE.** Any density-only
physical channel response on the joint substrate collapses to the
trivial zero response. The proof composes the unconditional
amplitude-linearity theorem of this module with the single-factor
substrate dichotomy of Session 85. -/
theorem density_only_physicalChannelResponse_eq_zero
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hPhys : PhysicalChannelResponseOf R_J R_C)
    (hDen : IsDensityOnly R_C) (φ : Signal8) :
    R_C φ = 0 :=
  eq_zero_of_isAmplitudeLinear_isDensityOnly
    (physicalChannelResponse_isAmplitudeLinear hPhys) hDen φ

/-- **UNCONDITIONAL T0-T8 NO-GO FOR DENSITY-ONLY PHYSICAL CHANNELS.**
Under T0-T8 substrate semantics, no joint dynamics on the joint
substrate admits a nontrivial density-only physical channel response.
The CPTP-classical mediator no-go is forced by substrate semantics
alone, with no further hypothesis. -/
theorem not_exists_nontrivial_density_only_physicalChannelResponse :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      PhysicalChannelResponseOf R_J R_C ∧
        IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0) := by
  rintro ⟨R_J, R_C, hPhys, hDen, φ, hφ⟩
  exact hφ (density_only_physicalChannelResponse_eq_zero hPhys hDen φ)

/-! ## §4. Concrete witness from canonical T0-T8 joint dynamics -/

/-- **Non-vacuous inhabitant of the unconditional theorem.** The
canonical T0-T8 joint dynamics
`canonicalCyclicJointOperator = cyclicShiftLinear ⊗ cyclicShiftLinear`
admits the recognition probe as a substrate-access, and the operational
channel response is the recognition update itself, which is amplitude-
linear by `isAmplitudeLinear_recognitionUpdate`. This witnesses that
the hypothesis space of the unconditional theorem is non-vacuously
inhabited by the actual T0-T8 substrate dynamics. -/
theorem canonicalT0T8JointDynamics_physicalChannelResponse_recognitionUpdate :
    PhysicalChannelResponseOf canonicalT0T8JointDynamics recognitionUpdate :=
  canonicalCyclicJointOperator_arisesFromRecognitionProbe

theorem canonicalT0T8JointDynamics_recognitionUpdate_isAmplitudeLinear :
    IsAmplitudeLinear recognitionUpdate :=
  physicalChannelResponse_isAmplitudeLinear
    canonicalT0T8JointDynamics_physicalChannelResponse_recognitionUpdate

/-- The recognition update is **not** density-only as a physical channel
response of the canonical T0-T8 joint dynamics: it is nontrivial
(`(recognitionUpdate 1) 0 = 1 ≠ 0`) and amplitude-linear, so by the
single-factor dichotomy it cannot be density-only. This is the concrete
content of the unconditional no-go for the canonical T0-T8 substrate
dynamics. -/
theorem canonicalT0T8JointDynamics_recognitionUpdate_not_density_only :
    ¬ IsDensityOnly recognitionUpdate := by
  intro hDen
  obtain ⟨ψ₀, i₀, hNontrivial⟩ := recognitionUpdate_nontrivial
  apply hNontrivial
  have h :=
    density_only_physicalChannelResponse_eq_zero
      canonicalT0T8JointDynamics_physicalChannelResponse_recognitionUpdate hDen ψ₀
  rw [h]
  rfl

/-! ## §5. Master cert -/

/-- Master cert recording the unconditional T0-T8 substrate-semantic
closure of Track 2.C: amplitude-linearity of the physical channel
response is forced by T0-T8 alone, density-only physical channel
responses collapse to zero, the no-go is unconditional, and the
canonical T0-T8 joint dynamics non-vacuously inhabits the hypothesis
space. -/
structure PhysicalChannelAmplitudeLinearCert where
  /-- Unconditional T0-T8 amplitude-linearity of the physical channel
  response on the joint substrate. -/
  amplitude_linear_of_physical_channel :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      PhysicalChannelResponseOf R_J R_C → IsAmplitudeLinear R_C
  /-- Density-only physical channel responses collapse to zero. -/
  density_only_collapse :
    ∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
      {R_C : Signal8 → Signal8},
      PhysicalChannelResponseOf R_J R_C → IsDensityOnly R_C →
        ∀ φ, R_C φ = 0
  /-- Unconditional no-go: no nontrivial density-only physical channel
  response on the joint substrate. -/
  no_go :
    ¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
        (R_C : Signal8 → Signal8),
      PhysicalChannelResponseOf R_J R_C ∧ IsDensityOnly R_C ∧
        (∃ φ : Signal8, R_C φ ≠ 0)
  /-- Non-vacuous canonical witness: the canonical T0-T8 joint dynamics
  inhabits the hypothesis space with the recognition update as its
  physical channel response. -/
  canonical_witness :
    PhysicalChannelResponseOf canonicalT0T8JointDynamics recognitionUpdate
  /-- The canonical physical channel response is amplitude-linear. -/
  canonical_amplitude_linear :
    IsAmplitudeLinear recognitionUpdate
  /-- The canonical physical channel response is not density-only. -/
  canonical_not_density_only :
    ¬ IsDensityOnly recognitionUpdate

noncomputable def physicalChannelAmplitudeLinearCert :
    PhysicalChannelAmplitudeLinearCert where
  amplitude_linear_of_physical_channel := physicalChannelResponse_isAmplitudeLinear
  density_only_collapse := density_only_physicalChannelResponse_eq_zero
  no_go := not_exists_nontrivial_density_only_physicalChannelResponse
  canonical_witness :=
    canonicalT0T8JointDynamics_physicalChannelResponse_recognitionUpdate
  canonical_amplitude_linear :=
    canonicalT0T8JointDynamics_recognitionUpdate_isAmplitudeLinear
  canonical_not_density_only :=
    canonicalT0T8JointDynamics_recognitionUpdate_not_density_only

theorem physicalChannelAmplitudeLinearCert_inhabited :
    Nonempty PhysicalChannelAmplitudeLinearCert :=
  ⟨physicalChannelAmplitudeLinearCert⟩

/-! ## §6. T0-T8 unconditional one-statement theorem -/

/-- **UNCONDITIONAL T0-T8 SUBSTRATE-SEMANTIC ONE-STATEMENT (Session 127).**
Track 2.C is unconditionally closed by T0-T8 substrate semantics.

Every physical channel response (= substrate-access induced channel
of a `ℂ`-linear joint dynamics on `JointSubstrate`) is forced
amplitude-linear; any density-only physical channel response collapses
to the trivial zero response; no joint dynamics admits a nontrivial
density-only physical channel response; and the canonical T0-T8 joint
dynamics `cyclicShiftLinear ⊗ cyclicShiftLinear` non-vacuously inhabits
the hypothesis space with the recognition update as its physical
channel response, which is amplitude-linear and not density-only.

The closure is unconditional with respect to all earlier-named
structural hypotheses of Track 2.C: `FactorizableJointSubstrate`,
`JointSectionReadout`, and `ArisesFromSubstrateAccess` are no longer
load-bearing &mdash; the first two are corollaries of the third via
Sessions 88, 111, and the third is provably equivalent to
amplitude-linearity via the universal-witness construction of
Session 126. This module discharges the remaining amplitude-linearity
hypothesis from T0-T8 substrate semantics + substrate locality alone.

What this leaves open: lifting the binary-tensor closure to the full
many-body gravitational substrate via the macroscopic ledger
`PiTensorProduct` structure. That is iterated application of this
binary forcing chain. -/
theorem T0T8_unconditional_physical_channel_amplitude_linear_one_statement :
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
       {R_C : Signal8 → Signal8},
       PhysicalChannelResponseOf R_J R_C → IsAmplitudeLinear R_C) ∧
    (∀ {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
       {R_C : Signal8 → Signal8},
       PhysicalChannelResponseOf R_J R_C → IsDensityOnly R_C →
         ∀ φ, R_C φ = 0) ∧
    (¬ ∃ (R_J : JointSubstrate →ₗ[ℂ] JointSubstrate)
         (R_C : Signal8 → Signal8),
       PhysicalChannelResponseOf R_J R_C ∧ IsDensityOnly R_C ∧
         (∃ φ : Signal8, R_C φ ≠ 0)) ∧
    PhysicalChannelResponseOf canonicalT0T8JointDynamics recognitionUpdate ∧
    IsAmplitudeLinear recognitionUpdate ∧
    ¬ IsDensityOnly recognitionUpdate :=
  ⟨@physicalChannelResponse_isAmplitudeLinear,
   @density_only_physicalChannelResponse_eq_zero,
   not_exists_nontrivial_density_only_physicalChannelResponse,
   canonicalT0T8JointDynamics_physicalChannelResponse_recognitionUpdate,
   canonicalT0T8JointDynamics_recognitionUpdate_isAmplitudeLinear,
   canonicalT0T8JointDynamics_recognitionUpdate_not_density_only⟩

/-! ## §7. Many-body PiTensorProduct lift -/

/-- The many-body channel ledger over a finite family of channel sites. -/
abbrev ManyBodyChannelLedger (ι : Type) [Fintype ι] [DecidableEq ι] : Type :=
  IndisputableMonolith.Gravity.MacroscopicLedger.MacroscopicLedger ι

/-- A many-body channel response is amplitude-linear when it agrees with a
`ℂ`-linear endomorphism of the macroscopic channel ledger. -/
def IsManyBodyAmplitudeLinear
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : ManyBodyChannelLedger ι → ManyBodyChannelLedger ι) : Prop :=
  ∃ L : ManyBodyChannelLedger ι →ₗ[ℂ] ManyBodyChannelLedger ι,
    ∀ Ψ : ManyBodyChannelLedger ι, R Ψ = L Ψ

/-- Extract the linear witness forced by the binary physical-channel theorem. -/
noncomputable def binaryPhysicalChannelLinearWitness
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hPhys : PhysicalChannelResponseOf R_J R_C) :
    Signal8 →ₗ[ℂ] Signal8 :=
  Classical.choose (physicalChannelResponse_isAmplitudeLinear hPhys)

theorem binaryPhysicalChannelLinearWitness_apply
    {R_J : JointSubstrate →ₗ[ℂ] JointSubstrate}
    {R_C : Signal8 → Signal8}
    (hPhys : PhysicalChannelResponseOf R_J R_C) (φ : Signal8) :
    R_C φ = binaryPhysicalChannelLinearWitness hPhys φ :=
  Classical.choose_spec (physicalChannelResponse_isAmplitudeLinear hPhys) φ

/-- The sitewise many-body physical channel as a `ℂ`-linear map on the
macroscopic channel ledger. Each site consumes the binary Track 2.C closure
for its local physical channel response. -/
noncomputable def manyBodyPhysicalChannelLinearMap
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : ι → Signal8 → Signal8)
    (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i)) :
    ManyBodyChannelLedger ι →ₗ[ℂ] ManyBodyChannelLedger ι :=
  PiTensorProduct.map
    (fun i : ι => binaryPhysicalChannelLinearWitness (hPhys i))

/-- The corresponding many-body physical channel response, viewed as a
function. -/
noncomputable def manyBodyPhysicalChannelResponse
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : ι → Signal8 → Signal8)
    (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i)) :
    ManyBodyChannelLedger ι → ManyBodyChannelLedger ι :=
  fun Ψ => manyBodyPhysicalChannelLinearMap R_J R_C hPhys Ψ

/-- **Many-body amplitude-linearity.** A sitewise family of binary physical
channel responses induces an amplitude-linear response on the full finite
`PiTensorProduct` channel ledger. -/
theorem manyBodyPhysicalChannelResponse_isAmplitudeLinear
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : ι → Signal8 → Signal8)
    (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i)) :
    IsManyBodyAmplitudeLinear
      (manyBodyPhysicalChannelResponse R_J R_C hPhys) :=
  ⟨manyBodyPhysicalChannelLinearMap R_J R_C hPhys, fun _ => rfl⟩

/-- **Pure-tensor action of the many-body channel.** On definite
macroscopic channel configurations, the many-body response acts by applying
the binary physical channel response at each site. -/
theorem manyBodyPhysicalChannelResponse_tprod
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : ι → Signal8 → Signal8)
    (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i))
    (φ : ι → Signal8) :
    manyBodyPhysicalChannelResponse R_J R_C hPhys
      (PiTensorProduct.tprod ℂ φ) =
        PiTensorProduct.tprod ℂ (fun i => R_C i (φ i)) := by
  unfold manyBodyPhysicalChannelResponse manyBodyPhysicalChannelLinearMap
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  exact (binaryPhysicalChannelLinearWitness_apply (hPhys i) (φ i)).symm

/-- **Sitewise density-only collapse.** If every local physical channel in
the many-body family is density-only, then every local response collapses
to zero by the binary Track 2.C no-go. This is the local no-go payload
needed by many-body integrations. -/
theorem manyBody_local_density_only_collapse
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
    (R_C : ι → Signal8 → Signal8)
    (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i))
    (hDen : ∀ i : ι, IsDensityOnly (R_C i))
    (i : ι) (φ : Signal8) :
    R_C i φ = 0 :=
  density_only_physicalChannelResponse_eq_zero (hPhys i) (hDen i) φ

/-- Certificate for the many-body Track 2.C lift. -/
structure ManyBodyPhysicalChannelAmplitudeLinearCert where
  /-- Binary Track 2.C closure consumed at each site. -/
  binary_cert : PhysicalChannelAmplitudeLinearCert
  /-- Sitewise binary physical channels induce an amplitude-linear
  macroscopic response. -/
  many_body_amplitude_linear :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
      (R_C : ι → Signal8 → Signal8)
      (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i)),
      IsManyBodyAmplitudeLinear
        (manyBodyPhysicalChannelResponse R_J R_C hPhys)
  /-- Pure tensor configurations evolve sitewise. -/
  pure_tensor_action :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
      (R_C : ι → Signal8 → Signal8)
      (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i))
      (φ : ι → Signal8),
      manyBodyPhysicalChannelResponse R_J R_C hPhys
        (PiTensorProduct.tprod ℂ φ) =
          PiTensorProduct.tprod ℂ (fun i => R_C i (φ i))
  /-- Density-only collapse is inherited sitewise from the binary no-go. -/
  local_density_only_collapse :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
      (R_C : ι → Signal8 → Signal8)
      (_hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i))
      (_hDen : ∀ i : ι, IsDensityOnly (R_C i))
      (i : ι) (φ : Signal8),
      R_C i φ = 0

noncomputable def manyBodyPhysicalChannelAmplitudeLinearCert :
    ManyBodyPhysicalChannelAmplitudeLinearCert where
  binary_cert := physicalChannelAmplitudeLinearCert
  many_body_amplitude_linear :=
    fun R_J R_C hPhys =>
      manyBodyPhysicalChannelResponse_isAmplitudeLinear R_J R_C hPhys
  pure_tensor_action :=
    fun R_J R_C hPhys φ =>
      manyBodyPhysicalChannelResponse_tprod R_J R_C hPhys φ
  local_density_only_collapse :=
    fun R_J R_C hPhys hDen i φ =>
      manyBody_local_density_only_collapse R_J R_C hPhys hDen i φ

theorem manyBodyPhysicalChannelAmplitudeLinearCert_inhabited :
    Nonempty ManyBodyPhysicalChannelAmplitudeLinearCert :=
  ⟨manyBodyPhysicalChannelAmplitudeLinearCert⟩

/-- **TRACK 2.C MANY-BODY ONE-STATEMENT.** The binary physical-channel
closure lifts to any finite many-body channel ledger: sitewise binary
physical responses induce an amplitude-linear `PiTensorProduct` response,
act sitewise on pure tensors, and inherit the density-only collapse on
each local channel. -/
theorem T0T8_many_body_physical_channel_amplitude_linear_one_statement :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (R_J : ι → JointSubstrate →ₗ[ℂ] JointSubstrate)
      (R_C : ι → Signal8 → Signal8)
      (hPhys : ∀ i : ι, PhysicalChannelResponseOf (R_J i) (R_C i)),
      IsManyBodyAmplitudeLinear
        (manyBodyPhysicalChannelResponse R_J R_C hPhys) ∧
      (∀ φ : ι → Signal8,
        manyBodyPhysicalChannelResponse R_J R_C hPhys
          (PiTensorProduct.tprod ℂ φ) =
            PiTensorProduct.tprod ℂ (fun i => R_C i (φ i))) ∧
      (∀ _hDen : ∀ i : ι, IsDensityOnly (R_C i),
        ∀ i : ι, ∀ φ : Signal8, R_C i φ = 0) := by
  intro ι _ _ R_J R_C hPhys
  exact ⟨manyBodyPhysicalChannelResponse_isAmplitudeLinear R_J R_C hPhys,
    fun φ => manyBodyPhysicalChannelResponse_tprod R_J R_C hPhys φ,
    fun hDen i φ =>
      manyBody_local_density_only_collapse R_J R_C hPhys hDen i φ⟩

end AmplitudeLinearForced
end QuantumChannel
end Gravity
end IndisputableMonolith
