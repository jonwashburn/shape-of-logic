import Mathlib
import IndisputableMonolith.Gravity.Analysis.RecognitionDualEntryEnrichment4D
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshGeometricDeficit4D
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshHingeKappa4D

/-!
# Wave B residual R4: mesh dual-entry DeficitSourceConstitutiveCoupling

QG full-completion session, Wave B attack on
`TypedResidual_DeficitSourceConstitutiveCoupling_from_enrichment` from
`plans/QG_WaveB_Gap1_Residual_DAG_Draft_20260721.txt`.

Assembles banked R1 (`meshGeometricDeficit`), R2 (`meshHingeKappa` +
`source_dominated`), and R3 (`DualEntryStrainState`) into an inhabited
`DeficitSourceConstitutiveCoupling ℝ`, then applies the blocker's conditional
`recognition_ratio_derived_of_deficit_source_coupling`.

## Honesty / scope

* Does **not** flip `gap1_bridge_derived`.
* Does **not** introduce a ledger-named standalone
  `recognition_ratio_derived` Prop binding (that is R5); the theorem here is
  the conditional application on the assembled coupling, named
  `mesh_recognition_ratio_derived`.
* Carrier is the reshaped `H = ℝ` from R1/R2, not an encoded Freudenthal
  triangulation (`encodedFreudenthalLiftOpen` remains true upstream).
* R0a/R0b validation name-bindings remain open.
* Convention: deficit iff debit-leads (`0 < h`), mirror of
  `meshGeometricDeficit_regge_convention` (see `N-gap1-r3-convention-pin`).

Definitions are free of `xRatio` / `Real.log` / `ratio_relation`; the log
appears only in the final derived-ratio theorem statement inherited from
the blocker.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace RecognitionMeshDualEntryCoupling4D

open RecognitionDualEntryEnrichment4D
open RecognitionMeshGeometricDeficit4D
open RecognitionMeshHingeKappa4D
open SevenGaps

noncomputable section

/-! ## §1. Mesh dual-entry enrichment on the deformation carrier -/

/-- Dual-entry state on a single mesh channel (`Fin 1`): debit-leads on
positive deformation, credit-leads on negative, magnitude
`|meshGeometricDeficit h|`. -/
noncomputable def meshDualEntry (h : ℝ) : DualEntryStrainState (Fin 1) where
  debit := fun _ => if 0 < h then (1 : ℤ) else 0
  credit := fun _ => if h < 0 then (1 : ℤ) else 0
  mag := fun _ => |meshGeometricDeficit h|
  mag_nonneg := fun _ => abs_nonneg _
  flux_unit := by
    intro _
    by_cases hpos : 0 < h
    · have hneg : ¬ h < 0 := not_lt.mpr (le_of_lt hpos)
      simp [hpos, hneg]
    · by_cases hneg : h < 0
      · simp [hpos, hneg]
      · simp [hpos, hneg]

/-- Signed source strength extracted from the mesh dual-entry state. -/
noncomputable def meshDualEntrySource (h : ℝ) : ℝ :=
  (meshDualEntry h).extract 0

/-- **THEOREM.** Extracted dual-entry source equals the R2 constitutive
product `κ * δ` (trichotomy on `h`). -/
theorem meshDualEntrySource_eq (h : ℝ) :
    meshDualEntrySource h =
      meshHingeKappa h * meshGeometricDeficit h := by
  unfold meshDualEntrySource DualEntryStrainState.extract
    DualEntryStrainState.strain DualEntryStrainState.phi meshDualEntry
  rw [meshHingeKappa_eq_one, one_mul]
  -- Only cell of Fin 1 is 0.
  simp only
  rcases lt_trichotomy h 0 with hlt | rfl | hgt
  · -- h < 0: debit=0, credit=1, phi=-1, strain = -|δ| = δ
    have hsign := (meshGeometricDeficit_sign h).2 hlt
    have habs : |meshGeometricDeficit h| = -meshGeometricDeficit h :=
      abs_of_neg hsign
    have hpos : ¬ 0 < h := not_lt.mpr (le_of_lt hlt)
    simp [hlt, hpos, habs]
  · -- h = 0: flat
    simp [meshGeometricDeficit_flat, abs_zero]
  · -- 0 < h: debit=1, credit=0, phi=1, strain = |δ| = δ
    have hsign := (meshGeometricDeficit_sign h).1 hgt
    have habs : |meshGeometricDeficit h| = meshGeometricDeficit h :=
      abs_of_pos hsign
    have hneg : ¬ h < 0 := not_lt.mpr (le_of_lt hgt)
    simp [hgt, hneg, habs]

/-! ## §2. Assembled constitutive coupling -/

/-- **R4 assembly.** `DeficitSourceConstitutiveCoupling ℝ` from R1–R3:
channels/kappa/geometricDeficit/meshScale from banked R1/R2, source from
dual-entry extract. Definitionally free of `xRatio` / `Real.log`. -/
noncomputable def meshDualEntryCoupling :
    DeficitSourceConstitutiveCoupling ℝ where
  channels := meshHingeChannels
  channels_pos := meshHingeChannels_pos
  kappa := meshHingeKappa
  geometricDeficit := meshGeometricDeficit
  sourceStrength := meshDualEntrySource
  source_eq := meshDualEntrySource_eq
  meshScale := meshHingeMeshScale
  meshScale_pos := meshHingeMeshScale_pos
  source_dominated := by
    intro σ
    rw [meshDualEntrySource_eq σ]
    exact meshHingeKappa_source_dominated σ

/-- **THEOREM (conditional recognition-ratio on the mesh coupling).**
Applies `recognition_ratio_derived_of_deficit_source_coupling` to the
assembled dual-entry coupling. This is **not** the ledger-named
standalone `recognition_ratio_derived` binding (R5) and does **not** flip
`gap1_bridge_derived` (R6 needs R0a+R0b+R5). -/
theorem mesh_recognition_ratio_derived (σ : ℝ) :
    |Real.log ((ratioBridgeFromDeficitSourceCoupling
          meshDualEntryCoupling).xRatio σ)
        - meshDualEntryCoupling.kappa σ
            * meshDualEntryCoupling.geometricDeficit σ|
      ≤ (meshDualEntryCoupling.channels : ℝ) / 6
          * meshDualEntryCoupling.meshScale ^ 3 :=
  recognition_ratio_derived_of_deficit_source_coupling
    meshDualEntryCoupling σ

/-! ## §3. Typed residual R4 -/

/-- **R4.** Coupling assembled from enrichment + R1/R2 with source_eq and
source_dominated, free of xRatio in the premise fields. -/
def TypedResidual_DeficitSourceConstitutiveCoupling_from_enrichment :
    Prop :=
  ∃ C : DeficitSourceConstitutiveCoupling ℝ,
    C.kappa = meshHingeKappa ∧
      C.geometricDeficit = meshGeometricDeficit ∧
        C.sourceStrength = meshDualEntrySource ∧
          (∀ σ, C.sourceStrength σ = C.kappa σ * C.geometricDeficit σ) ∧
            0 < C.meshScale ∧
              (∀ σ, |C.sourceStrength σ| ≤ (C.channels : ℝ) * C.meshScale) ∧
                1 ≤ C.channels

/-- **THEOREM:** R4 closed. -/
theorem typedResidual_DeficitSourceConstitutiveCoupling_from_enrichment_closed :
    TypedResidual_DeficitSourceConstitutiveCoupling_from_enrichment := by
  refine ⟨meshDualEntryCoupling, rfl, rfl, rfl, ?_,
    meshDualEntryCoupling.meshScale_pos, ?_, meshDualEntryCoupling.channels_pos⟩
  · exact meshDualEntryCoupling.source_eq
  · exact meshDualEntryCoupling.source_dominated

theorem TypedResidual_DeficitSourceConstitutiveCoupling_from_enrichment_closed :
    TypedResidual_DeficitSourceConstitutiveCoupling_from_enrichment :=
  typedResidual_DeficitSourceConstitutiveCoupling_from_enrichment_closed

/-! ## §4. Decoys -/

/-- **Decoy 2.** Columnless magnitude-only extract `|δ|` is even in `h` and
cannot match the signed mesh geometric deficit on a punctured interval
(banked R1 even-function decoy). -/
theorem decoy_magnitude_only_ne_mesh_geometricDeficit :
    ¬ (∀ h : ℝ, 0 < |h| → |h| < 1 →
        |meshGeometricDeficit h| = meshGeometricDeficit h) := by
  have heven : ∀ h : ℝ, |meshGeometricDeficit (-h)| = |meshGeometricDeficit h| := by
    intro h
    rw [meshGeometricDeficit_odd h, abs_neg]
  exact decoy_even_function_ne_mesh_geometricDeficit
    (fun h => |meshGeometricDeficit h|) heven

/-- Package: magnitude-only decoy plus swap-evenness from R3 (decoy 1). -/
theorem adversarial_decoys_mesh_dual_entry :
    (¬ (∀ h : ℝ, 0 < |h| → |h| < 1 →
        |meshGeometricDeficit h| = meshGeometricDeficit h)) ∧
      (∀ (f : DualEntryStrainState (Fin 2) → ℝ)
          (select : RecognitionLedger.RecognitionLedger (Fin 2) → ℝ),
        (∀ E, f E = select E.toBare) →
          ∀ E, f E.swap = f E) :=
  ⟨decoy_magnitude_only_ne_mesh_geometricDeficit,
    fun f select hf E => bare_factorable_is_swap_even f select hf E⟩

/-! ## §5. Status (no ledger flag touch) -/

structure RecognitionMeshDualEntryCoupling4DStatus where
  r4Closed : Bool
  recognitionRatioDerivedLedgerBindingOpen : Bool
  gap1BridgeDerived : Bool

/-- R5 lands the ledger-named binding in
`SevenGaps.RecognitionRatioDerived`; this status field records that the
R4 module itself does not own that binding (binding lives in R5). -/
def recognitionMeshDualEntryCoupling4DStatus :
    RecognitionMeshDualEntryCoupling4DStatus where
  r4Closed := true
  recognitionRatioDerivedLedgerBindingOpen := true
  gap1BridgeDerived := false

theorem recognitionMeshDualEntryCoupling4DStatus_flags :
    recognitionMeshDualEntryCoupling4DStatus.r4Closed = true ∧
      recognitionMeshDualEntryCoupling4DStatus.recognitionRatioDerivedLedgerBindingOpen =
        true ∧
        recognitionMeshDualEntryCoupling4DStatus.gap1BridgeDerived = false := by
  decide

end

end RecognitionMeshDualEntryCoupling4D
end Analysis
end Gravity
end IndisputableMonolith
