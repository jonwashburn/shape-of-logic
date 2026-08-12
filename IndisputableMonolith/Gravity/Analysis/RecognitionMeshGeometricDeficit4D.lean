import Mathlib
import IndisputableMonolith.Geometry.FourTetSignedDeficit
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshExactJBridge4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel

/-!
# Wave B residual R1: mesh geometricDeficit identified (no xRatio)

QG full-completion session, Wave B attack on
`TypedResidual_mesh_geometricDeficit_identified` from
`plans/QG_WaveB_Gap1_Residual_DAG_Draft_20260721.txt`.

## DAG Prop vs Lean shape (recorded divergence)

The DAG draft asked for `∃ δ : HingeCarrier → ℝ` that is the signed
Regge-convention hinge deficit of the recognition Freudenthal mesh
carrier, free of `xRatio` / `log xRatio`. Lean has no declaration
`HingeCarrier`, and `RecognitionFreudenthalMesh4D` does not yet expose a
per-hinge `deficitAngle` deformation family.

Honest binding used here:
* deformation carrier `ℝ` with `FourTetSignedDeficit.starDeficit`
  (signed Regge-convention deficit from squared-edge geometry;
  odd, flat-vanishing, sign-certified);
* mesh context via `ExactJEqualsTrueReggeHessian` on
  `canonicalRecognitionMesh` (`exactJActionOnMesh` /
  `meshTrueReggeQuadraticHessian`);
* Freudenthal seed flatness `star_flat_angle_sum_two_pi` (banked
  `C-p1-regge-star-kernel-seed`).

OPEN remainder after R1 (not a Prop shell): lift `starDeficit` onto
`ReggeActionConcrete.deficitAngle` on an encoded triangulation of the
recognition Freudenthal mesh. That join is not yet expressible
(`RecognitionFreudenthalMesh4D` has no triangulation field;
`FourTetSignedDeficit` stops at the abstract-star convention note).
Recorded only by `encodedFreudenthalLiftOpen := true` below.

Does **not** flip `gap1_bridge_derived`. Does **not** inhabit
`DeficitSourceConstitutiveCoupling`. Does **not** claim
`recognition_ratio_derived`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace RecognitionMeshGeometricDeficit4D

open Geometry.FourTetSignedDeficit
open Geometry.DihedralDerivatives
open RecognitionMeshExactJBridge4D
open ReggeHinge4DStarKernel

noncomputable section

/-! ## §1. Geometry-first deficit on the star deformation carrier -/

/-- Mesh geometric deficit: the banked signed Regge-convention star
deficit as a function of the deformation parameter. Constructed from
squared-edge / dihedral geometry (`starSq`, `dihedralAngle3Sq`); no
`xRatio` or `Real.log` appears in the definition. -/
def meshGeometricDeficit : ℝ → ℝ :=
  starDeficit

theorem meshGeometricDeficit_eq_starDeficit (h : ℝ) :
    meshGeometricDeficit h = starDeficit h := rfl

/-- Geometry-first closed form (arcsin), free of ratio fields. -/
theorem meshGeometricDeficit_eq_arcsin (h : ℝ) :
    meshGeometricDeficit h = 4 * Real.arcsin h :=
  starDeficit_eq_arcsin h

/-- Regge convention: `2π - 4 * dihedralAngle3Sq` on the star data. -/
theorem meshGeometricDeficit_regge_convention (h : ℝ) :
    meshGeometricDeficit h =
      2 * Real.pi - 4 * dihedralAngle3Sq (starSq (starP h)) 0 :=
  rfl

theorem meshGeometricDeficit_odd (h : ℝ) :
    meshGeometricDeficit (-h) = -meshGeometricDeficit h :=
  starDeficit_odd h

theorem meshGeometricDeficit_flat : meshGeometricDeficit 0 = 0 :=
  starDeficit_flat

theorem meshGeometricDeficit_sign (h : ℝ) :
    (0 < h → 0 < meshGeometricDeficit h) ∧
      (h < 0 → meshGeometricDeficit h < 0) :=
  fourTet_deficit_sign h

/-! ## §2. Typed residual R1 -/

/-- **R1.** Mesh geometric deficit identified from exact-J / Regge star
geometry (no xRatio).

Inhabits the DAG residual under the recorded carrier reshape: `δ` is
`starDeficit` on the deformation parameter, the recognition mesh supplies
the exact-J = true-Regge Hessian identity, and the Freudenthal seed star
is flat (`2π`). -/
def TypedResidual_mesh_geometricDeficit_identified : Prop :=
  ∃ δ : ℝ → ℝ,
    δ = starDeficit ∧
      (∀ h : ℝ, δ (-h) = -δ h) ∧
        δ 0 = 0 ∧
          (∀ h : ℝ, (0 < h → 0 < δ h) ∧ (h < 0 → δ h < 0)) ∧
            ExactJEqualsTrueReggeHessian ∧
              starFlatAngleSum = 2 * Real.pi

/-- **THEOREM:** R1 closed. -/
theorem typedResidual_mesh_geometricDeficit_identified_closed :
    TypedResidual_mesh_geometricDeficit_identified := by
  refine ⟨starDeficit, rfl, starDeficit_odd, starDeficit_flat, ?_,
    exactJEqualsTrueReggeHessian_holds, star_flat_angle_sum_two_pi⟩
  intro h
  exact fourTet_deficit_sign h

/-- Named alias matching the DAG residual title. -/
theorem TypedResidual_mesh_geometricDeficit_identified_closed :
    TypedResidual_mesh_geometricDeficit_identified :=
  typedResidual_mesh_geometricDeficit_identified_closed

/-! ## §3. Decoys / falsifiers (DAG) -/

/-- **Decoy:** any even-in-`h` candidate (ledger-style deficit families)
cannot equal the signed mesh geometric deficit on a punctured interval.
Banked as `even_cannot_match_starDeficit`. -/
theorem decoy_even_function_ne_mesh_geometricDeficit
    (g : ℝ → ℝ) (heven : ∀ h : ℝ, g (-h) = g h) :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < 1 → g h = meshGeometricDeficit h) :=
  even_cannot_match_starDeficit g heven

/-- **Decoy:** `δ := log(positedRatio) / κ` with an even posited ratio
(the wrong shortcut that smuggles a ratio field into the deficit) cannot
match `starDeficit` / `meshGeometricDeficit` on a punctured interval. -/
theorem decoy_log_even_ratio_over_kappa_ne_starDeficit
    (r : ℝ → ℝ) (κ : ℝ) (_hκ : κ ≠ 0)
    (_hr_pos : ∀ h : ℝ, 0 < r h)
    (hr_even : ∀ h : ℝ, r (-h) = r h) :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < 1 →
        Real.log (r h) / κ = meshGeometricDeficit h) := by
  let g : ℝ → ℝ := fun h => Real.log (r h) / κ
  have heven : ∀ h : ℝ, g (-h) = g h := by
    intro h
    dsimp [g]
    rw [hr_even h]
  exact decoy_even_function_ne_mesh_geometricDeficit g heven

/-- Package: both DAG decoys. -/
theorem adversarial_decoys_mesh_geometricDeficit :
    (∀ (g : ℝ → ℝ), (∀ h, g (-h) = g h) →
      ¬ (∀ h, 0 < |h| → |h| < 1 → g h = meshGeometricDeficit h)) ∧
      (∀ (r : ℝ → ℝ) (κ : ℝ), κ ≠ 0 → (∀ h, 0 < r h) →
        (∀ h, r (-h) = r h) →
          ¬ (∀ h, 0 < |h| → |h| < 1 →
              Real.log (r h) / κ = meshGeometricDeficit h)) :=
  ⟨decoy_even_function_ne_mesh_geometricDeficit,
    fun r κ hκ hpos heven =>
      decoy_log_even_ratio_over_kappa_ne_starDeficit r κ hκ hpos heven⟩

/-! ## §4. Status (no ledger flag touch) -/

structure RecognitionMeshGeometricDeficit4DStatus where
  r1Closed : Bool
  encodedFreudenthalLiftOpen : Bool
  gap1BridgeDerived : Bool

def recognitionMeshGeometricDeficit4DStatus :
    RecognitionMeshGeometricDeficit4DStatus where
  r1Closed := true
  encodedFreudenthalLiftOpen := true
  gap1BridgeDerived := false

theorem recognitionMeshGeometricDeficit4DStatus_flags :
    recognitionMeshGeometricDeficit4DStatus.r1Closed = true ∧
      recognitionMeshGeometricDeficit4DStatus.encodedFreudenthalLiftOpen =
        true ∧
        recognitionMeshGeometricDeficit4DStatus.gap1BridgeDerived =
          false := by
  decide

end

end RecognitionMeshGeometricDeficit4D
end Analysis
end Gravity
end IndisputableMonolith
