import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbitM2Eval4D
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.Regge4DTorusContinuumLimit
import IndisputableMonolith.Gravity.Analysis.Regge4DTransportedAlgebraicCloser
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D

/-!
# Regge 4D tensor algebraic closer (partial)

4D counterpart of the 3D `ReggeTTAlgebraicCloser` adjugate identity.
Banks the transported distinct-hinge m² as a quadratic form in
`(E, dir)` on the TT variety, with every closed ray evaluation available
today.  Full closed-form equality to a universal tensor contraction
(adjugate-style) remains OPEN.

## THEOREM (banked)

* Homogeneity: `m2TransportedAllOrbitMomentDistinctHinge (c • E) dir =
  c² · m2TransportedAllOrbitMomentDistinctHinge E dir`.
* `symbolDir` plus/cross distinct-hinge `-1/4` (normalized `-1/8`).
* `e0Dir` plus `0`, cross `-1/8` (normalized `-1/16`).
* Arithmetic residual: continuum face `-1/16` vs EH `-1/4` is ratio 4;
  density dictionary survivor is `1` (does not close the 4).

## OPEN

* `Regge4DDistinctHingeTensorClosedFormOpen`: universal bilinear form in
  `(E, dir)` matching the distinct-hinge moment on all TT / nonzero dir.
* `Regge4DDistinctHingePinnedVsEHFactor4`: geometric (Schläfli / path B)
  account of the residual 4.  No magic-4 multiplier installed.
* Axis-mode isotropy blocker (imported from M2Eval; negative fact closed).

Does **not** flip `gap_action_recovery`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DTensorAlgebraicCloser

open BigOperators
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochTransportedAllOrbitM2Eval4D
open Regge4DContinuumPreflight
open Regge4DTorusContinuumLimit
open Regge4DTransportedAlgebraicCloser (symbolDir_normSq)
open EdgeTTDecomposition4D (axisTTPlus axisTTCross)
open ReggeBlochM2Symbol4D (symbolDir)

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ

noncomputable section

/-! ## §1. Quadratic form object -/

/-- Distinct-hinge transported m² as a quadratic form in the polarization. -/
def distinctHingeMomentForm (E : Mat4) (dir : Fin 4 → ℝ) : ℝ :=
  m2TransportedAllOrbitMomentDistinctHinge E dir

theorem distinctHingeMomentForm_smul (c : ℝ) (E : Mat4) (dir : Fin 4 → ℝ) :
    distinctHingeMomentForm (c • E) dir =
      c ^ 2 * distinctHingeMomentForm E dir :=
  m2TransportedAllOrbitMomentDistinctHinge_smul c E dir

theorem distinctHingeMomentForm_zero (dir : Fin 4 → ℝ) :
    distinctHingeMomentForm 0 dir = 0 := by
  simpa using distinctHingeMomentForm_smul (0 : ℝ) (1 : Mat4) dir

/-! ## §2. Banked ray evaluations -/

theorem distinctHingeMomentForm_axisTTPlus_symbolDir :
    distinctHingeMomentForm axisTTPlus symbolDir = (-1 / 4 : ℝ) :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_symbolDir

theorem distinctHingeMomentForm_axisTTCross_symbolDir :
    distinctHingeMomentForm axisTTCross symbolDir = (-1 / 4 : ℝ) :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_symbolDir

theorem distinctHingeMomentForm_axisTTPlus_e0Dir :
    distinctHingeMomentForm axisTTPlus e0Dir = (0 : ℝ) :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTPlus_e0Dir

theorem distinctHingeMomentForm_axisTTCross_e0Dir :
    distinctHingeMomentForm axisTTCross e0Dir = (-1 / 8 : ℝ) :=
  m2TransportedAllOrbitMomentDistinctHinge_axisTTCross_e0Dir

/-- Continuum-facing coefficient after `/|dir|²` on the pinned symbolDir
normalized plus ray: `-1/16`. -/
theorem continuumFace_normalizedPlus_symbolDir :
    distinctHingeMomentForm ((Real.sqrt 2)⁻¹ • axisTTPlus) symbolDir /
        (∑ i : Fin 4, symbolDir i * symbolDir i) =
      (-1 / 16 : ℝ) := by
  unfold distinctHingeMomentForm
  rw [m2TransportedAllOrbitMomentDistinctHinge_axisTTPlusNormalized_symbolDir,
    symbolDir_normSq]
  norm_num

/-- On `e0Dir`, normalized cross already hits continuum face `-1/16`
(since `|e0Dir|² = 1`); normalized plus hits `0`. -/
theorem continuumFace_normalizedCross_e0Dir :
    distinctHingeMomentForm ((Real.sqrt 2)⁻¹ • axisTTCross) e0Dir /
        (∑ i : Fin 4, e0Dir i * e0Dir i) =
      (-1 / 16 : ℝ) := by
  unfold distinctHingeMomentForm
  rw [m2TransportedAllOrbitMomentDistinctHinge_axisTTCrossNormalized_e0Dir,
    e0Dir_normSq]
  norm_num

theorem continuumFace_normalizedPlus_e0Dir_vanishes :
    distinctHingeMomentForm ((Real.sqrt 2)⁻¹ • axisTTPlus) e0Dir /
        (∑ i : Fin 4, e0Dir i * e0Dir i) =
      (0 : ℝ) := by
  unfold distinctHingeMomentForm
  rw [m2TransportedAllOrbitMomentDistinctHinge_axisTTPlusNormalized_e0Dir,
    e0Dir_normSq]
  norm_num

/-! ## §3. OPEN closed-form and factor-4 obligations -/

/-- **OPEN**: a universal tensor closed form on TT × nonzero directions,
in the spirit of the 3D adjugate identity
`K = (1/2) xᵀ adj(E) x = -(1/4)|x|²‖E‖_F²`. -/
def Regge4DDistinctHingeTensorClosedFormOpen : Prop :=
  ∃ (Q : Mat4 → (Fin 4 → ℝ) → ℝ),
    (∀ (c : ℝ) (E : Mat4) (dir : Fin 4 → ℝ),
        Q (c • E) dir = c ^ 2 * Q E dir) ∧
      (∀ (E : Mat4) (dir : Fin 4 → ℝ),
        IsTTPolarization4D dir E →
          (∑ i : Fin 4, dir i * dir i) ≠ 0 →
            distinctHingeMomentForm E dir = Q E dir)

/-- Arithmetic residual (THEOREM side): pinned continuum face vs EH. -/
theorem residual_factor_four_arithmetic :
    einsteinHilbertTTCoefficient4D = (4 : ℝ) * (-1 / 16 : ℝ) ∧
      DistinctHingePinnedMomentVsEH ∧
        survivingDictionaryFactor4D = 1 :=
  ⟨by rw [einsteinHilbertTTCoefficient4D_eq]; norm_num,
    distinctHinge_pinned_ne_eh, rfl⟩

/-- **OPEN**: geometric (Schläfli elevation / 3D-style local-incidence
path B) identity that forces the residual factor 4.  Naming only; no
theorem inhabits this Prop, and no magic-4 multiplier is installed on
the continuum sequence. -/
def Regge4DDistinctHingePinnedVsEHFactor4 : Prop :=
  Regge4DContinuumEHTarget

/-- Status flag: factor-4 geometric closure still open. -/
theorem Regge4DDistinctHingePinnedVsEHFactor4_status_open :
    regge4DTorusContinuumLimitStatus.ehTendstoInhabited = false :=
  rfl

theorem axis_isotropy_blocker_negated :
    ¬ Regge4DContinuumIsotropyBlockedOnAxisMode :=
  Regge4DContinuumIsotropyBlockedOnAxisMode_status_false

structure Regge4DTensorAlgebraicCloserStatus where
  rayEvaluationsBanked : Bool
  homogeneityClosed : Bool
  tensorClosedFormOpen : Bool
  factor4GeometricOpen : Bool
  axisIsotropyBlocked : Bool
  gapActionRecovery : Bool

def regge4DTensorAlgebraicCloserStatus : Regge4DTensorAlgebraicCloserStatus where
  rayEvaluationsBanked := true
  homogeneityClosed := true
  tensorClosedFormOpen := true
  factor4GeometricOpen := true
  axisIsotropyBlocked := true
  gapActionRecovery := false

theorem regge4DTensorAlgebraicCloserStatus_flags :
    regge4DTensorAlgebraicCloserStatus.rayEvaluationsBanked = true ∧
      regge4DTensorAlgebraicCloserStatus.homogeneityClosed = true ∧
        regge4DTensorAlgebraicCloserStatus.tensorClosedFormOpen = true ∧
          regge4DTensorAlgebraicCloserStatus.factor4GeometricOpen = true ∧
            regge4DTensorAlgebraicCloserStatus.axisIsotropyBlocked = true ∧
              regge4DTensorAlgebraicCloserStatus.gapActionRecovery =
                false := by
  decide

theorem does_not_flip_gap_action_recovery :
    regge4DTensorAlgebraicCloserStatus.gapActionRecovery = false :=
  rfl

end

end Regge4DTensorAlgebraicCloser
end Analysis
end Gravity
end IndisputableMonolith
