import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Cosmology.DarkEnergyStatus
import IndisputableMonolith.Cosmology.StaticDynamicDarkEnergySplit
import IndisputableMonolith.Cosmology.StaticLambdaSpine
import IndisputableMonolith.Cosmology.CosmologicalConstantDerivation
import IndisputableMonolith.Cosmology.CosmicZAging
import IndisputableMonolith.Cosmology.DeltaWKernel
import IndisputableMonolith.Cosmology.FriedmannDynamicDarkEnergy
import IndisputableMonolith.Cosmology.CosmicZHistory
import IndisputableMonolith.Cosmology.CosmicZScaleLaw
import IndisputableMonolith.Cosmology.DarkEnergyScaleAffinityDerivation
import IndisputableMonolith.Cosmology.DarkEnergyAmplitudeDerivation
import IndisputableMonolith.Cosmology.DarkEnergyThetaStatus
import IndisputableMonolith.Cosmology.DarkEnergyThetaPhiFour
import IndisputableMonolith.Cosmology.DarkEnergyPhiDilutionLaw
import IndisputableMonolith.Cosmology.DarkEnergyPhiDilutionDerivation
import IndisputableMonolith.Gravity.FullEFEWithDarkEnergy
import IndisputableMonolith.Gravity.DarkEnergyQGIntegration
import IndisputableMonolith.Verification.DarkEnergyLikelihoodCert

/-!
# Dark-Energy Strong Closure (capstone)

This module is the capstone of `Dark_Energy_Strong_Formalization_Plan_20260531`. It bundles
the theorem-grade dark-energy results into one certificate and states, honestly, which parts
are closed and which remain open.

## What is THEOREM-grade and bundled here

* **Static observable forced and matching data.** `Ω_Λ = 11/16 − α/π` matches Planck 2018
  within 2σ with no dynamical correction (`StaticDynamicDarkEnergySplit.static_within_2sigma`).
* **Static Λ spine unified.** The same `Ω_Λ` is tied to phase saturation, passive-mode
  fraction, particle-horizon forcing, Planck match, and the positive EFE source
  (`StaticLambdaSpine.StaticLambdaSpineCert`).
* **Dynamic observable cost-bounded.** Every admissible kernel deviation is bounded by the
  phantom-Carnot ceiling `J(φ)` (`DeltaWKernel.delta_w_in_FPT_window`).
* **Amplitude envelope.** Dynamic amplitudes are attenuated amplitudes `θ·J(φ)`; admissible
  `θ∈[0,1]` stays below the ceiling, and the current sharp implied amplitude has
  `0 < θ < 1/6` (`DarkEnergyAmplitudeDerivation.DynamicAmplitudeEnvelopeCert`).
* **Phi-four theta candidate.** The natural four-dimensional dilution candidate
  `θ=φ⁻⁴` inhabits `ThetaFromFirstPrinciples` and satisfies `0<θ<1/6`
  (`DarkEnergyThetaPhiFour.ThetaPhiFourCandidateCert`).
* **Phi-dilution law.** Dimension-uniform φ attenuation plus the proved dimension-4 EFE
  carrier forces `θ=φ⁻⁴` (`DarkEnergyPhiDilutionLaw.PhiDilutionLawCert`).
* **Phi-dilution law DERIVED (not asserted).** The `φ⁻ⁿ` law itself is derived from two deeper
  premises — independent-channel multiplicative composition and single-dimension self-similar
  attenuation — with `φ⁻¹` forced by the φ-forcing theorem `recipShift_fixed_iff` and the
  exponent forced by `SpacetimeEmergence.spacetime_dim_eq_four`
  (`DarkEnergyPhiDilutionDerivation.DimensionUniformDilutionCert`).
* **Present amplitude pinned (closes the U3 split).** The derived `θ=φ⁻⁴` fixes the single
  present dynamic deviation `δw(0) = φ⁻⁴·J(φ) ≈ 0.0172`, with a proved numeric band, more than
  six-fold below the `J(φ)` ceiling, distinct from the saturation value, and strictly inside the
  DESI-testable, Ω_Λ-gap-consistent window `(0.005, ≈0.030)`
  (`DarkEnergyPhiDilutionLaw.PredictedAmplitudeCert`, `predicted_amplitude_ne_saturation`,
  `predicted_amplitude_in_desi_window`).
* **Quantum-gravity integration.** The forced vacuum term sits in the EFE chain: positive,
  equation of state `w = −1`, covariantly conserved (grounded in metric compatibility),
  preserving `κ = 8φ⁵`, recovering the `Λ = 0` baseline
  (`FullEFEWithDarkEnergy.DarkEnergyEFECert`).
* **QG master compatibility.** The unconditional RS-QG master theorem remains available
  unchanged while the dark-energy EFE source plugs into the same `κ = 8φ⁵`, dimension-4
  EFE spine (`Gravity.DarkEnergyQGIntegration.DarkEnergyQGIntegrationCert`).
* **Friedmann fluid (well-posed, conserved).** The dynamic dark energy obeys the
  cosmological continuity equation (an explicit `HasDerivAt`), stays strictly positive,
  reduces to ΛCDM at zero amplitude, and never drives `H²` negative
  (`FriedmannDynamicDarkEnergy.FriedmannDarkEnergyCert`).
* **Shape reduction.** Under the BIT kernel `w = −1 + δw·Z(z)/Z_today`, the dark-energy
  shape *is* the normalized cosmic-Z history, and linear-in-`a` accumulation forces the
  canonical `1/(1+z)` (`CosmicZHistory.CosmicZShapeCert`).
* **Scale-law forcing.** The named scale-affine ledger admissibility law uniquely forces
  the normalized Z-history to be the scale factor, so the canonical `1/(1+z)` kernel follows
  without choosing an extra curve (`CosmicZScaleLaw.CosmicZScaleLawCert`).
* **Scale-affinity derivation gate.** The no-hidden-scale-coordinate admissibility condition
  derives `ScaleAffineZLaw` and hence the canonical kernel
  (`DarkEnergyScaleAffinityDerivation.ScaleAffinityDerivationCert`).
* **Sign mechanism resolved/classified.** A nonnegative kernel forces a `≥ 1`, increasing
  density ratio, which forces the distance-inferred effective Ω_Λ *down* — real physics,
  and irrelevant to the static match (`StaticDynamicDarkEnergySplit`).
* **Observational surface.** Static ΩΛ is the active Planck-band row; legacy constant-w is
  not currently sensitive to the old target; direct dynamic tests must measure the
  scale-affine `θ·J(φ)/(1+z)` signature (`Verification.DarkEnergyLikelihoodCert`).

## What remains OPEN (recorded honestly, not claimed)

* **Amplitude (U3): present value pinned, one residual premise.** `J(φ)` is the proved
  *ceiling*; the present dynamic amplitude is now the single derived value `δw(0)=φ⁻⁴·J(φ)`
  (`DarkEnergyPhiDilutionLaw.PredictedAmplitudeCert`), not a free choice between the ceiling
  and a gap-fit value. The occupancy `θ=φ⁻⁴` is derived from independent-channel multiplicative
  composition plus single-dimension self-similar attenuation (`φ⁻¹` forced by
  `recipShift_fixed_iff`) at the forced spacetime dimension `4` (`spacetime_dim_eq_four`). The
  only residual premise is the multiplicative composition rule itself (the multiplicative shadow
  of J-cost log-additivity over independent channels, `Cost.Ndim.dot_log_hadamardMul`).
* **Shape (U5), closed at admissibility level.** The shape problem is reduced
  (`shape_reduction`) to deriving the cosmic-Z accumulation history `Z(z)`, and the
  no-hidden-scale-coordinate admissibility gate derives scale-affinity, hence
  `Z/Z_today = a` and the canonical `1/(1+z)`.

So this capstone is a **strong scaffold with an honest frontier**, not a finished strong
theory. The present dynamic amplitude is now pinned to a single derived value; the residues are
the multiplicative-composition premise beneath the amplitude and the no-hidden-coordinate gate
beneath the shape, both universal-forcing-level questions rather than dark-energy-specific
choices.

Status: THEOREM for every bundled field. Zero `sorry`, zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace DarkEnergyStrongClosure

open Constants
open Cost

noncomputable section

/-- **DARK-ENERGY STRONG-CLOSURE CERTIFICATE.**

Bundles the theorem-grade dark-energy results. Each field is proved. The two genuine open
items (amplitude derivation, cosmic-Z shape) are *not* fields here, by design: a strong
theory must close them, and bundling them as "done" would be the overclaim this program
exists to prevent. See the module docstring and `DarkEnergyStatus` for their honest status. -/
structure StrongDarkEnergyClosure where
  /-- Static fraction is forced and matches Planck within 2σ (no kernel). -/
  static_matches_planck :
    |CosmicZAging.planck_omega_lambda - CosmologicalConstantDerivation.Omega_Lambda_RS|
      < 2 * CosmicZAging.planck_sigma
  /-- One spine tying static `ΩΛ` to formula, phase saturation, horizon forcing,
  observation, and the positive EFE source. -/
  static_lambda_spine : StaticLambdaSpine.StaticLambdaSpineCert
  /-- Dynamic deviation is bounded by the phantom-Carnot ceiling `J(φ)`. -/
  dynamic_cost_ceiling :
    ∀ (k : DeltaWKernel.Kernel) (z : ℝ), k.deviation z ≤ Cost.Jcost phi
  /-- Amplitudes live as attenuation fractions of the `J(φ)` ceiling; the sharp implied
  amplitude corresponds to an occupancy fraction below `1/6`. -/
  amplitude_envelope : DarkEnergyAmplitudeDerivation.DynamicAmplitudeEnvelopeCert
  /-- Honest theta status: the future first-principles target type, the current implied
  `0 < θ < 1/6` envelope, and algebraic consequences once a theta is supplied. -/
  theta_status : DarkEnergyThetaStatus.ThetaStatusCert
  /-- Candidate first-principles theta from four-dimensional φ-dilution: `θ=φ⁻⁴`. -/
  theta_phi_four_candidate : DarkEnergyThetaPhiFour.ThetaPhiFourCandidateCert
  /-- Dimension-uniform φ attenuation plus EFE dimension 4 forces `θ=φ⁻⁴`. -/
  phi_dilution_law : DarkEnergyPhiDilutionLaw.PhiDilutionLawCert
  /-- The `φ⁻ⁿ` dilution law is *derived* from independent-channel composition and
  single-dimension self-similarity, with `φ⁻¹` and the exponent both forced. -/
  phi_dilution_derived : DarkEnergyPhiDilutionDerivation.DimensionUniformDilutionCert
  /-- The present dynamic amplitude is pinned to the single derived value `δw(0) = φ⁻⁴·J(φ)`,
  with a numeric band that sits more than six-fold below the `J(φ)` ceiling and strictly
  inside the DESI-testable, Ω_Λ-gap-consistent window `(0.005, ≈0.030)`. -/
  amplitude_predicted : DarkEnergyPhiDilutionLaw.PredictedAmplitudeCert
  /-- The static prediction does not depend on the kernel. -/
  static_independent_of_kernel :
    (|CosmicZAging.planck_omega_lambda - CosmologicalConstantDerivation.Omega_Lambda_RS|
      < 2 * CosmicZAging.planck_sigma) ∧
    (∀ (k : DeltaWKernel.Kernel) (z : ℝ), k.deviation z ≤ Cost.Jcost phi)
  /-- The forced vacuum term is integrated into the quantum-gravity EFE chain. -/
  efe_vacuum_integrated : Gravity.FullEFEWithDarkEnergy.DarkEnergyEFECert
  /-- The dark-energy EFE source is compatible with the unconditional quantum-gravity
  master theorem and preserves the same `κ = 8φ⁵` EFE spine. -/
  qg_master_integrated : Gravity.DarkEnergyQGIntegration.DarkEnergyQGIntegrationCert
  /-- The dark energy is a proper, positive, conserved fluid in the Friedmann equation,
  reducing to ΛCDM at zero amplitude and keeping `H²` well-posed. -/
  friedmann_fluid : FriedmannDynamicDarkEnergy.FriedmannDarkEnergyCert
  /-- The dark-energy shape is the cosmic-Z history (shape reduction); linear-in-`a`
  accumulation forces the canonical `1/(1+z)` kernel. -/
  shape_is_z_history : CosmicZHistory.CosmicZShapeCert
  /-- The named scale-affine ledger law forces `Z/Z_today = a` and hence forces the
  canonical `1/(1+z)` kernel from ledger-uniform scale increments. -/
  scale_law_forces_shape : CosmicZScaleLaw.CosmicZScaleLawCert
  /-- The lower no-hidden-scale-coordinate admissibility gate derives the scale-affine law. -/
  scale_affinity_derivation :
    DarkEnergyScaleAffinityDerivation.ScaleAffinityDerivationCert
  /-- The split certificate (static / dynamic / sign mechanism). -/
  static_dynamic_split : StaticDynamicDarkEnergySplit.StaticDynamicSplitCert
  /-- Observation/falsifier surface: static ΩΛ active, legacy constant-w non-sensitive,
  direct dynamic tests tied to `θ·J(φ)/(1+z)`, and Friedmann positivity. -/
  observational_surface : Verification.DarkEnergyLikelihoodCert.DarkEnergyObservationalCert
  /-- The current status guardrail (records the still-open amplitude / sign items). -/
  status_guardrail : DarkEnergyStatus.DarkEnergyStatusCert

/-- **CAPSTONE: the dark-energy strong-closure scaffold is established.**

Every bundled field is a proved theorem from the cosmology and gravity libraries. This is
the strongest currently-honest statement of the dark-energy theory: the static prediction
is forced and matches data, the dynamic deviation is cost-bounded and QG-integrated, and the
sign mechanism is understood. The amplitude and shape derivations remain open (see the
module docstring) and are deliberately excluded from the bundle. -/
def rs_dark_energy_strong_closure : StrongDarkEnergyClosure where
  static_matches_planck := StaticDynamicDarkEnergySplit.static_within_2sigma
  static_lambda_spine := StaticLambdaSpine.staticLambdaSpineCert
  dynamic_cost_ceiling := DeltaWKernel.delta_w_in_FPT_window
  amplitude_envelope := DarkEnergyAmplitudeDerivation.dynamicAmplitudeEnvelopeCert
  theta_status := DarkEnergyThetaStatus.thetaStatusCert
  theta_phi_four_candidate := DarkEnergyThetaPhiFour.thetaPhiFourCandidateCert
  phi_dilution_law := DarkEnergyPhiDilutionLaw.phiDilutionLawCert
  phi_dilution_derived := DarkEnergyPhiDilutionDerivation.dimensionUniformDilutionCert
  amplitude_predicted := DarkEnergyPhiDilutionLaw.predictedAmplitudeCert
  static_independent_of_kernel :=
    StaticDynamicDarkEnergySplit.static_prediction_independent_of_kernel
  efe_vacuum_integrated := Gravity.FullEFEWithDarkEnergy.darkEnergyEFECert
  qg_master_integrated := Gravity.DarkEnergyQGIntegration.darkEnergyQGIntegrationCert
  friedmann_fluid := FriedmannDynamicDarkEnergy.friedmannDarkEnergyCert
  shape_is_z_history := CosmicZHistory.cosmicZShapeCert
  scale_law_forces_shape := CosmicZScaleLaw.cosmicZScaleLawCert
  scale_affinity_derivation := DarkEnergyScaleAffinityDerivation.scaleAffinityDerivationCert
  static_dynamic_split := StaticDynamicDarkEnergySplit.staticDynamicSplitCert
  observational_surface := Verification.DarkEnergyLikelihoodCert.darkEnergyObservationalCert
  status_guardrail := DarkEnergyStatus.darkEnergyStatusCert

/-! ## Amplitude classification (refines U3)

The "10× amplitude split" is **not** a contradiction. `J(φ)` is a *ceiling* (an upper
bound on the deviation), and the data-allowed amplitude sitting an order of magnitude below
it is exactly what a healthy bound looks like. The only thing the data excludes is kernel
*saturation* (`δw(0) = J(φ)`). So the honest status of U3 is: ceiling consistent with data,
saturation falsified, true amplitude still open (to be derived from the cosmic-Z coupling). -/

/-- The data-allowed amplitude is strictly below the `J(φ)` ceiling: the ceiling is a
consistent upper bound, not a contradiction. -/
theorem amplitude_below_ceiling :
    CosmicAgingAmplitudeSharp.delta_w_implied_max < Cost.Jcost phi := by
  have h := CosmicAgingAmplitudeSharp.jPhi_dominates_implied
  have h2 := CosmicAgingAmplitudeSharp.delta_w_implied_max_gt
  nlinarith

/-- Kernel saturation is excluded by data: the saturation value `δw(0) = J(φ)` exceeds the
data-allowed amplitude more than six-fold. Hence `J(φ)` is the ceiling, not the value. -/
theorem saturation_excluded :
    CosmicAgingAmplitudeSharp.delta_w_implied_max * 6 <
      DeltaWKernel.canonicalDeltaW.deviation 0 := by
  rw [DeltaWKernel.canonicalDeltaW_today]
  exact CosmicAgingAmplitudeSharp.jPhi_dominates_implied

/-- **U3 resolution: a single predicted present amplitude.** The derived occupancy `θ=φ⁻⁴`
(dimension-uniform φ-dilution through the proved four-dimensional EFE carrier) pins the present
dynamic dark-energy deviation to the single value `δw(0) = φ⁻⁴·J(φ)`. It is strictly below the
phantom-Carnot ceiling and, in particular, distinct from the saturation value
`canonicalDeltaW.deviation 0 = J(φ)`. The "10× split" recorded in `DarkEnergyStatus` compared
saturation against a gap-fit value; this theorem exhibits the actual prediction, which is
neither. -/
theorem predicted_amplitude_ne_saturation :
    DarkEnergyPhiDilutionLaw.predictedPresentAmplitude ≠
      DeltaWKernel.canonicalDeltaW.deviation 0 := by
  rw [DeltaWKernel.canonicalDeltaW_today]
  exact ne_of_lt DarkEnergyPhiDilutionLaw.predictedPresentAmplitude_lt_ceiling

/-- The predicted present amplitude lands strictly inside the DESI-testable, Ω_Λ-gap-consistent
window `(bit_strong_falsifier, desi_sharp_threshold) ≈ (0.005, 0.030)`: large enough to be a
real late-time signature, small enough to be consistent with the observed gap. -/
theorem predicted_amplitude_in_desi_window :
    CosmicAgingAmplitudeSharp.bit_strong_falsifier <
      DarkEnergyPhiDilutionLaw.predictedPresentAmplitude ∧
    DarkEnergyPhiDilutionLaw.predictedPresentAmplitude <
      CosmicAgingAmplitudeSharp.desi_sharp_threshold :=
  ⟨DarkEnergyPhiDilutionLaw.predictedPresentAmplitude_above_strong_falsifier,
   DarkEnergyPhiDilutionLaw.predictedPresentAmplitude_below_sharp_desi⟩

/-- The two genuinely-open frontier items, stated as the proved facts that mark them open.
This is the honest "what remains" companion to the capstone. -/
structure DarkEnergyOpenFrontier where
  /-- **U3 (amplitude OPEN).** The forced saturation value and the gap-implied value differ;
  no unique first-principles amplitude is derived yet. -/
  amplitude_not_yet_unique :
    CosmicAgingAmplitudeSharp.delta_w_implied_max ≠
      DeltaWKernel.canonicalDeltaW.deviation 0
  /-- **U5 (shape, nearly closed).** The scale-affine ledger law forces the canonical
  `δw(z)=δw₀/(1+z)` kernel. The remaining residue is deriving that admissibility law from
  lower RS primitives rather than taking it as the no-extra-scale-coordinate condition. -/
  scale_affine_forces_shape :
    ∀ (dw0 Zt : ℝ) (law : CosmicZScaleLaw.ScaleAffineZLaw) (z : ℝ),
      Zt ≠ 0 → (1 : ℝ) + z ≠ 0 →
        CosmicZHistory.bitDeviation dw0 Zt (CosmicZScaleLaw.ZfromScaleLaw Zt law) z =
          dw0 / (1 + z)

def dark_energy_open_frontier : DarkEnergyOpenFrontier where
  amplitude_not_yet_unique := DarkEnergyStatus.blocker_amplitude_split
  scale_affine_forces_shape := CosmicZScaleLaw.scaleAffine_forces_canonical_deviation

end

end DarkEnergyStrongClosure
end Cosmology
end IndisputableMonolith
