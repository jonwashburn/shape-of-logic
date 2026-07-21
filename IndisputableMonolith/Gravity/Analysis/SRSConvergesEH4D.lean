import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.RecognitionMeshExactJBridge4D
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecompositionCloser4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianNormGate4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbolZero4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochM2Rayleigh4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochTorusBridge4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D
import IndisputableMonolith.Gravity.Analysis.Regge4DExactActionSymbol
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D

/-!
# Named closers: `edge_tt_decomposition` and `S_RS_converges_EH_4d`

QG full-theory campaign, ledger-facing export module for weak-field
quadratic action recovery.  The Props are the preflight names; this
module is the sole place that may later inhabit them for the ledger flip.

## Honest scope

* Weak-field quadratic action convergence only.
* Not sourced Einstein equation, continuum Ricci/stress, horizon/coframe,
  arbitrary-curvature GR, or full nonlinear `wick_action_continuation_4d`.
* `gap_action_recovery` flips only when both named theorems are inhabited
  on Elmo with focused axiom audits and adversarial review.
* Banked: `edge_tt_decomposition_closed`; R2 symbolZero; R3 Rayleigh
  faces; R4 discrete torus-family bridge → ContinuumSymbolIs at m²
  Rayleigh; Option-C m² faces; honest `S_RS_converges_EH_4d`.
* `gap_action_recovery` flips with this inhabitant (MEASURED-native_decide
  via m² table certificates). Never ContinuumSymbolIs = Tendsto of a
  j-independent constant face.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace SRSConvergesEH4D

open Regge4DContinuumPreflight
open RecognitionMeshExactJBridge4D
open EdgeTTDecomposition4D
open EdgeTTDecompositionCloser4D
open ReggeEdgeStencil4D
open ReggeExactFlatHessianNormGate4D
open ReggeExactFlatHessianSymbol4D
  (exactHessianM2UnitFrobeniusTTCoeff exactHessianM2GaugeCoeff
    measuredTTNormCoeffN6)
open ReggeExactFlatHessianBlochSymbol4D
open ReggeExactFlatHessianBlochSymbolZero4D
open ReggeExactFlatHessianBlochTorusBridge4D
open ReggeExactMidpointM2TTIdentity4D
  (exactMidpointBlochM2_eq_neg_eighth_frobenius_tt
    exactMidpointBlochM2_gauge_rayleigh_eq_zero)
open Regge4DExactActionSymbol (discreteExactReggeSymbol)
open Filter Topology

noncomputable section

/-- Disambiguate shared aliases after multi-module opens. -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4
abbrev exactFlatCrossTermFold := Regge4DExactActionSymbol.exactFlatCrossTermFold

private theorem frobeniusNormSq_preflight_eq_identity (H : Mat4) :
    Regge4DContinuumPreflight.frobeniusNormSq H =
      ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq H :=
  rfl

private theorem waveNormSq_preflight_eq_identity (k : Wave4) :
    Regge4DContinuumPreflight.waveNormSq k =
      ReggeExactMidpointM2TTIdentity4D.waveNormSq k :=
  rfl

/-! ## §1. Re-export of ledger Prop names -/

abbrev edge_tt_decomposition : Prop :=
  Regge4DContinuumPreflight.edge_tt_decomposition

abbrev S_RS_converges_EH_4d : Prop :=
  Regge4DContinuumPreflight.S_RS_converges_EH_4d

/-! ## §2. Edge closer inhabited; SRS still open -/

theorem edge_tt_decomposition_closed :
    edge_tt_decomposition :=
  EdgeTTDecompositionCloser4D.edge_tt_decomposition

theorem edge_tt_polarization_witnesses :
    IsTTPolarization4D axisWave axisTTPlusNormalized ∧
      IsTTPolarization4D axisWave axisTTCrossNormalized :=
  continuum_target_hypothesis_nonvacuous

theorem edge_tt_gauge_decoy_not_transverse :
    ¬ IsTransverse axisWave decoyGauge :=
  EdgeTTDecompositionCloser4D.decoyGauge_not_transverse

theorem srs_converges_eh_4d_requires_both_gates :
    S_RS_converges_EH_4d =
      (Regge4DContinuumEHTarget ∧ Regge4DContinuumGaugeZeroTarget) := rfl

theorem discrete_bookkeeping_times_unitF_eq_EH :
    discreteBookkeepingFactor * exactHessianM2UnitFrobeniusTTCoeff =
      Regge4DContinuumPreflight.einsteinHilbertTTCoefficient4D :=
  discreteBookkeeping_recovers_frozen_EH

theorem adversarial_decoys_still_hold :
    (finiteTTQuadratic decoyGauge = 32 ∧
      finiteTTQuadratic (axisTTPlus + decoyGauge) ≠
        finiteTTQuadratic axisTTPlus) ∧
      (ReggeBlochM2Symbol4D.m2Symbol axisTTPlus = -3 ∧
        Regge4DContinuumPreflight.einsteinHilbertTTCoefficient4D =
          -(1 / 4 : ℝ) ∧
          (-3 : ℝ) ≠ -(1 / 4 : ℝ)) ∧
        wrongMeshPowerWeight 3 ≠ correctTorusDensityWeight 3 :=
  ⟨decoy_provisional_weight_fails_gauge, decoy_one_orbit_m2_is_not_continuum_target,
    decoy_wrong_mesh_power_side3⟩

/-! ## §3. Status -/

structure SRSConvergesEH4DStatus where
  edgeTTNamed : Bool
  srsNamed : Bool
  edgeTTInhabited : Bool
  srsInhabited : Bool
  gapActionRecovery : Bool

def srsConvergesEH4DStatus : SRSConvergesEH4DStatus where
  edgeTTNamed := true
  srsNamed := true
  edgeTTInhabited := true
  srsInhabited := true
  gapActionRecovery := true

theorem srsConvergesEH4DStatus_flags :
    srsConvergesEH4DStatus.edgeTTNamed = true ∧
      srsConvergesEH4DStatus.srsNamed = true ∧
        srsConvergesEH4DStatus.edgeTTInhabited = true ∧
          srsConvergesEH4DStatus.srsInhabited = true ∧
            srsConvergesEH4DStatus.gapActionRecovery = true := by
  decide

theorem srs_closer_closed :
    srsConvergesEH4DStatus.srsInhabited = true ∧
      srsConvergesEH4DStatus.gapActionRecovery = true := by
  decide

/-! ## §4. Typed residuals (geometric ContinuumSymbolIs Tendsto) -/

def TypedResidual_fold_eq_midpointBloch : Prop :=
  ∀ (H : Mat4) (k : Wave4),
    exactFlatCrossTermFold H k = exactMidpointBlochSymbol H k

def TypedResidual_midpointBloch_symbolZero : Prop :=
  ∀ H : Mat4, exactMidpointBlochSymbolZero H = 0

def TypedResidual_m2_rayleigh_eq_algebraic_face : Prop :=
  (∀ (H : Mat4) (k : Wave4),
      IsTT k H →
        frobeniusNormSq H = 1 →
          waveNormSq k ≠ 0 →
            exactMidpointBlochM2 H k / waveNormSq k =
              exactHessianM2UnitFrobeniusTTCoeff) ∧
    (∀ (m : Wave4) (v : Wave4),
      waveNormSq m ≠ 0 →
        exactMidpointBlochM2 (pureGaugeFamily m v) m / waveNormSq m =
          exactHessianM2GaugeCoeff)

def TypedResidual_discrete_torus_family_bridge : Prop :=
  ∀ (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      Tendsto
        (fun j : ℕ =>
          exactMidpointBlochSymbol E (realMode (torusSide j) m) /
            momentumNormSq (torusSide j) m)
        atTop
        (nhds (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
          waveNormSq (fun i => (m i : ℝ))))

/-- **THEOREM (R2):** midpoint Bloch vanishes at zero momentum. -/
theorem typedResidual_midpointBloch_symbolZero_closed :
    TypedResidual_midpointBloch_symbolZero :=
  ReggeExactFlatHessianBlochSymbolZero4D.typedResidual_midpointBloch_symbolZero

/-- **THEOREM (R3):** cosine two-jet Rayleigh equals algebraic m² faces
(`-1/8` on unit-F TT; `0` on pure gauge). -/
theorem typedResidual_m2_rayleigh_eq_algebraic_face_closed :
    TypedResidual_m2_rayleigh_eq_algebraic_face :=
  ReggeExactFlatHessianBlochM2Rayleigh4D.typedResidual_m2_rayleigh_eq_algebraic_face

/-- **THEOREM (R4):** discrete torus bridge inhabited (uses R2). -/
theorem typedResidual_discrete_torus_family_bridge :
    TypedResidual_discrete_torus_family_bridge :=
  discrete_torus_family_bridge

theorem typedResidual_discrete_torus_family_bridge_closed :
    TypedResidual_discrete_torus_family_bridge :=
  typedResidual_discrete_torus_family_bridge

theorem typedResidual_discrete_torus_family_bridge_of_symbolZero
    (hZ : TypedResidual_midpointBloch_symbolZero) :
    TypedResidual_discrete_torus_family_bridge :=
  discrete_torus_family_bridge_of_symbolZero hZ

/-- Bridge transports ContinuumSymbolIs (mesh midpoint sequence) to the
m² Rayleigh value for every nonzero mode / every polarization. -/
theorem continuumSymbolIs_of_discrete_torus_bridge
    (m : IntMode4) (E : Mat4) (hm : m ≠ 0) :
    Regge4DContinuumSymbolIs m E
      (exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
        waveNormSq (fun i => (m i : ℝ))) :=
  continuumSymbolIs_midpoint_rayleigh m E hm

/-- Option-C face residual (lane 1): Rayleigh equals scale-explicit EH
face on TT and vanishes on pure gauge. -/
def TypedResidual_m2_optionC_faces : Prop :=
  (∀ (m : IntMode4) (E : Mat4),
      m ≠ 0 →
        IsTT (fun i => (m i : ℝ)) E →
          exactMidpointBlochM2 E (fun i => (m i : ℝ)) /
              waveNormSq (fun i => (m i : ℝ)) =
            continuumEHScaleExplicitFace E) ∧
    (∀ (m : IntMode4) (v : Wave4),
      m ≠ 0 →
        exactMidpointBlochM2 (pureGaugeFamily (fun i => (m i : ℝ)) v)
            (fun i => (m i : ℝ)) /
          waveNormSq (fun i => (m i : ℝ)) = 0)

theorem typedResidual_m2_optionC_faces :
    TypedResidual_m2_optionC_faces := by
  refine ⟨?_, ?_⟩
  · intro m E hm hTT
    set k : Wave4 := fun i => (m i : ℝ)
    have hk : waveNormSq k ≠ 0 := waveNormSq_intMode_ne_zero m hm
    have hRay := exactMidpointBlochM2_eq_neg_eighth_frobenius_tt E k hTT
    -- Identity norms are definitionally the preflight norms.
    have hF :
        ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq E =
          frobeniusNormSq E :=
      (frobeniusNormSq_preflight_eq_identity E).symm
    have hw :
        ReggeExactMidpointM2TTIdentity4D.waveNormSq k = waveNormSq k :=
      (waveNormSq_preflight_eq_identity k).symm
    calc
      exactMidpointBlochM2 E k / waveNormSq k
          = ((-(1 / 8) : ℝ) * ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq E *
                ReggeExactMidpointM2TTIdentity4D.waveNormSq k) /
              waveNormSq k := by rw [hRay]
      _ = ((-(1 / 8) : ℝ) * frobeniusNormSq E * waveNormSq k) / waveNormSq k := by
            rw [hF, hw]
      _ = (-(1 / 8) : ℝ) * frobeniusNormSq E := by
            field_simp [hk]
      _ = continuumEHScaleExplicitFace E :=
            (continuumEHScaleExplicitFace_eq E).symm
  · intro m v hm
    set k : Wave4 := fun i => (m i : ℝ)
    have hk : waveNormSq k ≠ 0 := waveNormSq_intMode_ne_zero m hm
    have hk' : ReggeExactMidpointM2TTIdentity4D.waveNormSq k ≠ 0 := by
      simpa [waveNormSq_preflight_eq_identity] using hk
    have hGauge := exactMidpointBlochM2_gauge_rayleigh_eq_zero k v hk'
    simpa [pureGaugeFamily] using hGauge

/-- Compose bridge + Option-C m² faces into EH Tendsto target. -/
theorem continuumEHTarget_of_bridge_and_m2_faces
    (hFaces : TypedResidual_m2_optionC_faces) :
    Regge4DContinuumEHTarget := by
  intro m E hm hTT
  have hRay := continuumSymbolIs_of_discrete_torus_bridge m E hm
  have hEq := hFaces.1 m E hm hTT
  simpa [hEq] using hRay

/-- Compose bridge + Option-C m² faces into gauge-zero Tendsto target. -/
theorem continuumGaugeZeroTarget_of_bridge_and_m2_faces
    (hFaces : TypedResidual_m2_optionC_faces) :
    Regge4DContinuumGaugeZeroTarget := by
  intro m v hm
  have hRay :=
    continuumSymbolIs_of_discrete_torus_bridge m
      (pureGaugeFamily (fun i => (m i : ℝ)) v) hm
  have hEq := hFaces.2 m v hm
  simpa [hEq] using hRay

/-- Packaged: bridge closed; S_RS inhabit reduces to Option-C m² faces. -/
theorem srs_converges_eh_4d_of_m2_optionC_faces
    (hFaces : TypedResidual_m2_optionC_faces) :
    S_RS_converges_EH_4d :=
  ⟨continuumEHTarget_of_bridge_and_m2_faces hFaces,
    continuumGaugeZeroTarget_of_bridge_and_m2_faces hFaces⟩

theorem TypedResidual_m2_optionC_faces_closed :
    TypedResidual_m2_optionC_faces :=
  typedResidual_m2_optionC_faces

theorem S_RS_converges_EH_4d_closed :
    S_RS_converges_EH_4d :=
  srs_converges_eh_4d_of_m2_optionC_faces typedResidual_m2_optionC_faces

/-- **R5.** Legacy discreteExact ×2 sequence binder (not Option-C ledger
`ContinuumSymbolIs`). -/
def TypedResidual_continuum_discreteExact_rebind : Prop :=
  ∀ (m : IntMode4) (E : Mat4) (Λ : ℝ),
    Regge4DDiscreteBookkeepingContinuumSymbolIs m E Λ ↔
      Tendsto
        (fun j : ℕ =>
          discreteExactReggeSymbol j m E /
            momentumNormSq (torusSide j) m)
        atTop (nhds Λ)

def GeometricTendstoResidualOpen : Prop :=
  TypedResidual_fold_eq_midpointBloch ∧
    TypedResidual_midpointBloch_symbolZero ∧
      TypedResidual_m2_rayleigh_eq_algebraic_face ∧
        TypedResidual_discrete_torus_family_bridge ∧
          TypedResidual_continuum_discreteExact_rebind

/-- Bridge lane and Option-C faces are closed, yielding honest S_RS inhabitance. -/
theorem discrete_torus_bridge_closed_srs_closed :
    TypedResidual_discrete_torus_family_bridge ∧
      TypedResidual_midpointBloch_symbolZero ∧
        TypedResidual_m2_optionC_faces ∧
          srsConvergesEH4DStatus.srsInhabited = true ∧
            srsConvergesEH4DStatus.gapActionRecovery = true :=
  ⟨typedResidual_discrete_torus_family_bridge,
    typedResidual_midpointBloch_symbolZero_closed,
    typedResidual_m2_optionC_faces, rfl, rfl⟩

theorem geometric_tendsto_residuals_named_srs_closed :
    srsConvergesEH4DStatus.srsInhabited = true ∧
      srsConvergesEH4DStatus.gapActionRecovery = true :=
  ⟨rfl, rfl⟩

theorem decoy_finiteN_tt_norm_ne_exact_EH_face :
    measuredTTNormCoeffN6 ≠
      Regge4DContinuumPreflight.einsteinHilbertTTCoefficient4D := by
  unfold measuredTTNormCoeffN6
    Regge4DContinuumPreflight.einsteinHilbertTTCoefficient4D
  norm_num

end

end SRSConvergesEH4D
end Analysis
end Gravity
end IndisputableMonolith
