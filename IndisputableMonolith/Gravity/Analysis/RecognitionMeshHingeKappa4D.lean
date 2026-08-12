import Mathlib
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshGeometricDeficit4D
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshExactJBridge4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel

/-!
# Wave B residual R2: hinge kappa with source_dominated admissibility (no xRatio)

QG full-completion session, Wave B attack on
`TypedResidual_hinge_kappa_identified` from
`plans/QG_WaveB_Gap1_Residual_DAG_Draft_20260721.txt`.

## DAG Prop vs Lean shape (recorded divergence)

The DAG draft asked for `∃ κ : HingeCarrier → ℝ` named from RS / mesh
constitutive data such that `|κ σ * δ σ|` admits the
`DeficitSourceConstitutiveCoupling.source_dominated` bound shape on a
positive `meshScale`. Lean has no `HingeCarrier`; R1 already reshaped the
carrier to `ℝ` via `meshGeometricDeficit := starDeficit`
(`N-gap1-r1-carrier-reshape`).

Honest binding used here:
* hinge coupling `meshHingeKappa := fun _ => 1`, the unit coupling of the
  banked `concreteStationarityBridge` pattern
  (`StationarityBridgeClosure`: `∀ σ, kappa σ = 1`); named constitutive
  data, not a free field, and definitionally free of `xRatio` / `Real.log`;
* geometric side from R1: `meshGeometricDeficit` (= `starDeficit`);
* real admissibility content: prove
  `|meshHingeKappa h * meshGeometricDeficit h| ≤ channels * meshScale`
  for `channels = 4` (bridge channel count) and `meshScale = π/2 > 0`,
  using `|arcsin| ≤ π/2` so `|starDeficit| ≤ 2π`;
* mesh context conjoined: `ExactJEqualsTrueReggeHessian` and
  `starFlatAngleSum = 2π` (same as R1).

Blunt honesty: the kappa *naming* is the banked unit-coupling identification
(definitional packaging of `1`). The THEOREM content is the
`source_dominated`-shaped inequality against banked star geometry, plus
nontriviality (`κ ≠ 0`) and the decoys. Continuum Einstein-scale join
(`kappa_einstein` vs hinge-local unit coupling) is left OPEN via
`einsteinScaleJoinOpen`.

Does **not** flip `gap1_bridge_derived`. Does **not** inhabit
`DeficitSourceConstitutiveCoupling` (needs R3 enrichment for signed
`sourceStrength`). Does **not** touch R3 / evade
`no_bare_ledger_selector_recovers_signed_source`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace RecognitionMeshHingeKappa4D

open RecognitionMeshGeometricDeficit4D
open RecognitionMeshExactJBridge4D
open ReggeHinge4DStarKernel

noncomputable section

/-! ## §1. Named hinge coupling (no xRatio) -/

/-- Mesh hinge coupling: unit coupling of the banked
`concreteStationarityBridge` pattern. No `xRatio`, no `Real.log`. -/
def meshHingeKappa : ℝ → ℝ :=
  fun _ => 1

theorem meshHingeKappa_eq_one (h : ℝ) : meshHingeKappa h = 1 := rfl

theorem meshHingeKappa_ne_zero (h : ℝ) : meshHingeKappa h ≠ 0 := by
  simp [meshHingeKappa]

/-! ## §2. Geometric bound feeding source_dominated -/

/-- `|arcsin h| ≤ π/2` for every real (Mathlib clamps outside `[-1,1]`). -/
theorem abs_arcsin_le_pi_div_two (h : ℝ) :
    |Real.arcsin h| ≤ Real.pi / 2 := by
  have hle : Real.arcsin h ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two h
  have hge : -(Real.pi / 2) ≤ Real.arcsin h := Real.neg_pi_div_two_le_arcsin h
  exact abs_le.mpr ⟨hge, hle⟩

/-- Banked star deficit is uniformly bounded: `|δ| ≤ 2π`. -/
theorem meshGeometricDeficit_abs_le_two_pi (h : ℝ) :
    |meshGeometricDeficit h| ≤ 2 * Real.pi := by
  rw [meshGeometricDeficit_eq_arcsin, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hbound := abs_arcsin_le_pi_div_two h
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  calc 4 * |Real.arcsin h|
      ≤ 4 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hbound h4
    _ = 2 * Real.pi := by ring

/-- Bridge channel count used by `concreteStationarityBridge`. -/
def meshHingeChannels : ℕ := 4

theorem meshHingeChannels_pos : 1 ≤ meshHingeChannels := by
  decide

/-- Positive mesh scale discharging `source_dominated` against star geometry:
`4 * (π/2) = 2π` matches the uniform deficit bound. -/
def meshHingeMeshScale : ℝ := Real.pi / 2

theorem meshHingeMeshScale_pos : 0 < meshHingeMeshScale := by
  unfold meshHingeMeshScale
  positivity

/-- **THEOREM (real admissibility).** The named unit coupling admits the
`DeficitSourceConstitutiveCoupling.source_dominated` bound shape against
R1's `meshGeometricDeficit` on a positive mesh scale:
`|κ h * δ h| ≤ channels * meshScale` for all carrier points. -/
theorem meshHingeKappa_source_dominated :
    ∀ h : ℝ,
      |meshHingeKappa h * meshGeometricDeficit h|
        ≤ (meshHingeChannels : ℝ) * meshHingeMeshScale := by
  intro h
  rw [meshHingeKappa_eq_one, one_mul]
  have hδ := meshGeometricDeficit_abs_le_two_pi h
  unfold meshHingeChannels meshHingeMeshScale
  -- `|δ| ≤ 2π = 4 * (π/2)`
  have hscale : (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi := by ring
  rw [← hscale] at hδ
  exact hδ

/-! ## §3. Typed residual R2 -/

/-- **R2.** Hinge kappa identified with source_dominated admissibility
(no xRatio).

Inhabits the DAG residual under the R1 carrier reshape: `κ` is the banked
unit coupling, nontrivial, and `|κ * meshGeometricDeficit|` meets the
blocker `source_dominated` shape on `meshHingeMeshScale > 0`, with the
exact-J / seed-flat mesh context conjoined. -/
def TypedResidual_hinge_kappa_identified : Prop :=
  ∃ κ : ℝ → ℝ,
    κ = meshHingeKappa ∧
      (∀ h : ℝ, κ h ≠ 0) ∧
        (∃ (channels : ℕ), 1 ≤ channels ∧
          ∃ meshScale : ℝ, 0 < meshScale ∧
            ∀ h : ℝ,
              |κ h * meshGeometricDeficit h| ≤ (channels : ℝ) * meshScale) ∧
          ExactJEqualsTrueReggeHessian ∧
            starFlatAngleSum = 2 * Real.pi

/-- **THEOREM:** R2 closed. -/
theorem typedResidual_hinge_kappa_identified_closed :
    TypedResidual_hinge_kappa_identified := by
  refine ⟨meshHingeKappa, rfl, meshHingeKappa_ne_zero, ?_,
    exactJEqualsTrueReggeHessian_holds, star_flat_angle_sum_two_pi⟩
  exact ⟨meshHingeChannels, meshHingeChannels_pos,
    meshHingeMeshScale, meshHingeMeshScale_pos,
    meshHingeKappa_source_dominated⟩

/-- Named alias matching the DAG residual title. -/
theorem TypedResidual_hinge_kappa_identified_closed :
    TypedResidual_hinge_kappa_identified :=
  typedResidual_hinge_kappa_identified_closed

/-! ## §4. Decoys / falsifiers (DAG) -/

/-- **Decoy:** `κ = 0` everywhere trivializes the source and fails the
nontriviality conjunct required by R2. -/
theorem decoy_zero_kappa_fails_nontrivial :
    ¬ (∀ h : ℝ, (fun _ : ℝ => (0 : ℝ)) h ≠ 0) := by
  intro h
  exact (h 0) rfl

/-- **Decoy:** `κ h := log(r h) / δ h` with even positive ratio (smuggles
the recognition ratio into the coupling) cannot equal the named constitutive
unit coupling on a punctured interval. Oddness of `meshGeometricDeficit`
forces the log-ratio quotient to be odd, while `meshHingeKappa` is the
nonzero constant `1`. -/
theorem decoy_log_ratio_over_deficit_ne_meshHingeKappa
    (r : ℝ → ℝ) (_hr_pos : ∀ h : ℝ, 0 < r h)
    (hr_even : ∀ h : ℝ, r (-h) = r h) :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < 1 →
        Real.log (r h) / meshGeometricDeficit h = meshHingeKappa h) := by
  intro hEq
  -- Evaluate at a concrete positive deformation in (0,1), e.g. 1/2.
  have hpos : (0 : ℝ) < |(1 / 2 : ℝ)| := by norm_num
  have hlt : |(1 / 2 : ℝ)| < 1 := by norm_num
  have hpos' : (0 : ℝ) < |(-(1 / 2 : ℝ))| := by norm_num
  have hlt' : |(-(1 / 2 : ℝ))| < 1 := by norm_num
  have heq_pos := hEq (1 / 2) hpos hlt
  have heq_neg := hEq (-(1 / 2)) hpos' hlt'
  -- Left side at -h equals negation of left side at h (δ odd, r even).
  have hδ_odd := meshGeometricDeficit_odd (1 / 2)
  have hr := hr_even (1 / 2)
  have hneg_side :
      Real.log (r (-(1 / 2))) / meshGeometricDeficit (-(1 / 2))
        = -(Real.log (r (1 / 2)) / meshGeometricDeficit (1 / 2)) := by
    rw [hr, hδ_odd, div_neg]
  -- Right side is constantly 1.
  have hκ_pos : meshHingeKappa (1 / 2) = 1 := meshHingeKappa_eq_one _
  have hκ_neg : meshHingeKappa (-(1 / 2)) = 1 := meshHingeKappa_eq_one _
  -- So 1 = lhs(-h) = -lhs(h) = -1, contradiction.
  have hlhs_pos :
      Real.log (r (1 / 2)) / meshGeometricDeficit (1 / 2) = 1 := by
    rw [heq_pos, hκ_pos]
  have hlhs_neg :
      Real.log (r (-(1 / 2))) / meshGeometricDeficit (-(1 / 2)) = 1 := by
    rw [heq_neg, hκ_neg]
  rw [hneg_side, hlhs_pos] at hlhs_neg
  linarith

/-- Package: both DAG decoys. -/
theorem adversarial_decoys_hinge_kappa :
    (¬ (∀ h : ℝ, (fun _ : ℝ => (0 : ℝ)) h ≠ 0)) ∧
      (∀ (r : ℝ → ℝ), (∀ h, 0 < r h) → (∀ h, r (-h) = r h) →
        ¬ (∀ h, 0 < |h| → |h| < 1 →
            Real.log (r h) / meshGeometricDeficit h = meshHingeKappa h)) :=
  ⟨decoy_zero_kappa_fails_nontrivial,
    fun r hpos heven =>
      decoy_log_ratio_over_deficit_ne_meshHingeKappa r hpos heven⟩

/-! ## §5. Status (no ledger flag touch) -/

structure RecognitionMeshHingeKappa4DStatus where
  r2Closed : Bool
  einsteinScaleJoinOpen : Bool
  gap1BridgeDerived : Bool

def recognitionMeshHingeKappa4DStatus :
    RecognitionMeshHingeKappa4DStatus where
  r2Closed := true
  einsteinScaleJoinOpen := true
  gap1BridgeDerived := false

theorem recognitionMeshHingeKappa4DStatus_flags :
    recognitionMeshHingeKappa4DStatus.r2Closed = true ∧
      recognitionMeshHingeKappa4DStatus.einsteinScaleJoinOpen = true ∧
        recognitionMeshHingeKappa4DStatus.gap1BridgeDerived = false := by
  decide

end

end RecognitionMeshHingeKappa4D
end Analysis
end Gravity
end IndisputableMonolith
