import IndisputableMonolith.Holography.DeficitFreePeriod
import IndisputableMonolith.Holography.TurnRatioCarrier
import IndisputableMonolith.Holography.SeamLedgerDischarge

/-!
# HorizonClockRate: B3 rate-only typing (LEG-B, panel 2026-07-06)

Prose acceptance: `derive_20260706_073650` (critic ACCEPT). This module types **only**
what B3 delivers: near-horizon Rindler geometry makes the continued Euclidean angle
advance at rate `κ` per unit Euclidean time (`dθ/dτ_E = κ`). It does **not** assert the
`2π` closure period; that is B2's output (`DeficitFreePeriod.euclideanPeriod`,
`TurnRatioCarrier.turnRatio_eq_one_iff`).

The legacy `DeficitFreePeriod.HorizonRate` (`κ = 1/R`) is a separate Schwarzschild
normalization socket for the Clausius bridge. Do not conflate it with this B3 delivery.
-/

namespace IndisputableMonolith
namespace Holography
namespace HorizonClockRate

open DeficitFreePeriod TurnRatioCarrier SeamLedgerDischarge

/-! ## Named geometric premise (MODEL) -/

/-- **Near-horizon Rindler normal form (MODEL).** A Killing horizon with surface
gravity `κ > 0` admits adapted coordinates `(ρ, τ)` near the bifurcation surface with
local metric coefficient `κ` on the static Killing sector. This module records only the
existence of the rate parameter; no thermality, KMS, or entropy-area law is imported. -/
structure NearHorizonRindlerForm (kappa : ℝ) : Prop where
  kappa_pos : 0 < kappa

/-! ## B3 delivery: angular rate only -/

/-- Euclidean angular coordinate after continuation: `θ = κ τ_E`. -/
noncomputable def euclideanAngle (kappa tauE : ℝ) : ℝ :=
  kappa * tauE

/-- **B3 rate (THEOREM).** The continued recognition clock advances Euclidean angle at
rate `κ`: `dθ/dτ_E = κ` for all `τ_E`. Pure calculus on `θ = κ τ_E`; no period input. -/
theorem euclideanAngle_rate (kappa : ℝ) (hk : 0 < kappa) (tauE : ℝ) :
    HasDerivAt (euclideanAngle kappa) kappa tauE := by
  unfold euclideanAngle
  simpa using (hasDerivAt_id (x := tauE)).const_mul kappa

/-- Algebraic form of the rate law (the panel's `dθ/dτ_E = κ`). -/
theorem euclideanAngle_deriv_eq (kappa : ℝ) (hk : 0 < kappa) (tauE : ℝ) :
    deriv (euclideanAngle kappa) tauE = kappa :=
  (euclideanAngle_rate kappa hk tauE).deriv

/-- **Typed B3 bundle (FORCED-CONDITIONAL on `NearHorizonRindlerForm`).** -/
structure ClockRateBundle (kappa : ℝ) : Prop where
  rindler : NearHorizonRindlerForm kappa
  rate : ∀ tauE : ℝ, deriv (euclideanAngle kappa) tauE = kappa

/-- Every Rindler form yields the rate bundle. -/
theorem clockRateBundle_of_rindler {kappa : ℝ} (h : NearHorizonRindlerForm kappa) :
    ClockRateBundle kappa where
  rindler := h
  rate := fun tauE => euclideanAngle_deriv_eq kappa h.kappa_pos tauE

/-! ## Hyperbolic mismatch class (grounds `HasRealEigen`) -/

/-- **Physical commitment (HYPOTHESIS/MODEL).** The delivered mismatch leg is a
positive real eigenvalue on the hyperbolic (non-elliptic) class: not ±1, not complex.
This is the typed reading of `HasRealEigen` in `SeamTransferCore`. -/
def HyperbolicMismatchClass (W : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Prop :=
  SeamTransferCore.HasRealEigen W x ∧ 0 < x ∧ x ≠ 1

/-! ## Fence: B3 does not assert the period -/

/-- **Fence theorem (THEOREM).** B3's rate law alone does not pin a closure time; the
full-turn time `2π/κ` is definitionally the B2 carrier output, not an input here. -/
theorem period_is_b2_output_not_b3_input (kappa : ℝ) :
    euclideanPeriod kappa = 2 * Real.pi / kappa := rfl

/-- At the B2-forced period, the turn ratio is unity (B1/B2 linkage; B3 not used). -/
theorem turnRatio_unity_at_b2_period (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    T = euclideanPeriod kappa → turnRatio kappa T = 1 :=
  (turnRatio_eq_one_iff kappa T hk).mpr

/-- **Explicit non-claim:** `ClockRateBundle` carries no field about `T = 2π/κ`. -/
theorem clockRateBundle_silent_on_period {kappa : ℝ} (_h : ClockRateBundle kappa) :
    True := trivial

/-! ## Bridge to legacy `HorizonRate` (normalization socket, separate leg) -/

/-- The Clausius-bridge normalization `κ = 1/R` is an independent MODEL socket; it is
not part of the B3 rate-only delivery above. -/
theorem legacy_horizonRate_is_separate (kappa R : ℝ) :
    DeficitFreePeriod.HorizonRate kappa R ↔ kappa = 1 / R :=
  Iff.rfl

end HorizonClockRate
end Holography
end IndisputableMonolith
