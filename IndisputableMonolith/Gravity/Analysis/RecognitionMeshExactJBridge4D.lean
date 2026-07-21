import Mathlib
import IndisputableMonolith.Gravity.Analysis.Regge4DContinuumPreflight
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.Regge4DTorusContinuumLimit
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochTorusBridge4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactMidpointM2TTIdentity4D

/-!
# Recognition mesh exact-J → Option-C midpoint Bloch bridge (value level)

QG full-theory campaign, Recognition gate of the 4D continuum closure.
Constructs the canonical Recognition mesh carrier for the periodic
Freudenthal 4-torus and attaches a value-level action whose amplitude
Hessian is the geometric Option-C midpoint Bloch symbol on the same
torus family.

## Binding honesty

* **MODEL** (Regge identification): `exactJActionOnMesh` is defined as the
  exact midpoint Bloch symbol on edge classes at amplitude `ε`
  (the geometric Option-C continuum object). Elevating that Hessian to
  the literal nonlinear Regge action via Schläfli remains OPEN;
  star-edge origins for non-`t11` orbits are now landed
  (`ReggeBlochStarEdgeOrigins4D`).
* This module does **not** consume `ExactJRefinementFamilyLimit` as a
  continuum premise (that family is amplitude scaling / response-level).
* Arbitrary `TestVariationPullback` hypotheses are excluded
  (`ArbitraryPullbackExcluded` from the preflight).
* Preferred limit shape: amplitude Hessian at fixed mesh, then `N → ∞`.
* **THEOREM:** amplitude Hessian exists and equals the mesh true-Regge
  Hessian by construction (`ExactJEqualsTrueReggeHessian`).
* **THEOREM:** iterated `N → ∞` Tendsto closes at the scale-explicit
  Option-C face `continuumEHScaleExplicitFace E`
  (`RecognitionExactJConvergesEH`) by composing the discrete torus bridge
  with the exact midpoint m² TT / gauge faces.
* Does **not** flip `gap_action_recovery`.
* Does **not** inhabit `S_RS_converges_EH_4d`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace RecognitionMeshExactJBridge4D

open Regge4DContinuumPreflight
open ReggeFlat4DHessianAssembly
open Regge4DTorusContinuumLimit (intModeDir)
open EdgeTTDecomposition4D (IsTT)
open ReggeBlochAllOrbitSymbol4D (m2AllOrbitMomentPoly)
open ReggeExactFlatHessianBlochSymbol4D
open ReggeExactFlatHessianBlochTorusBridge4D
open ReggeExactMidpointM2TTIdentity4D
  (exactMidpointBlochM2_eq_neg_eighth_frobenius_tt
    exactMidpointBlochM2_gauge_rayleigh_eq_zero)
open Filter Topology

noncomputable section

/-- Local alias: preflight `Mat4` (avoids clash with transported abbrev). -/
abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4

private theorem frobeniusNormSq_preflight_eq_identity (H : Mat4) :
    Regge4DContinuumPreflight.frobeniusNormSq H =
      ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq H :=
  rfl

private theorem waveNormSq_preflight_eq_identity (k : Wave4) :
    Regge4DContinuumPreflight.waveNormSq k =
      ReggeExactMidpointM2TTIdentity4D.waveNormSq k :=
  rfl

/-! ## §1. Canonical Recognition mesh on the Freudenthal torus -/

/-- Recognition-native mesh data for continuum index `j` (side `j+3`).
The exact flat cross-term Hessian on this carrier is the concrete
edge-class geometry; the continuum index records the torus family. -/
structure RecognitionFreudenthalMesh4D where
  continuumIndex : ℕ
  deriving Repr

def RecognitionFreudenthalMesh4D.side (M : RecognitionFreudenthalMesh4D) : ℕ :=
  torusSide M.continuumIndex

def RecognitionFreudenthalMesh4D.toTorus (M : RecognitionFreudenthalMesh4D) :
    CanonicalFreudenthalTorus4D :=
  ⟨M.continuumIndex⟩

theorem RecognitionFreudenthalMesh4D.side_eq_torus
    (M : RecognitionFreudenthalMesh4D) :
    M.side = M.toTorus.side := rfl

/-- Canonical mesh family used by the Recognition gate. -/
def canonicalRecognitionMesh (j : ℕ) : RecognitionFreudenthalMesh4D :=
  ⟨j⟩

theorem canonicalRecognitionMesh_side (j : ℕ) :
    (canonicalRecognitionMesh j).side = j + 3 := rfl

/-! ## §2. True-weight Regge Hessian on the mesh (edge classes) -/

/-- Torus wave covector for the mesh side and integer mode. -/
def meshWave (M : RecognitionFreudenthalMesh4D) (m : IntMode4) : Wave4 :=
  realMode M.side m

/-- Geometry-derived Option-C midpoint Bloch symbol on the Freudenthal
mesh.

MODEL relative to nonlinear Regge: this is the assembled flat
midpoint Hessian, not yet fully Schläfli-elevated for every orbit. -/
def meshTrueReggeQuadraticHessian (M : RecognitionFreudenthalMesh4D)
    (m : IntMode4) (E : Mat4) : ℝ :=
  exactMidpointBlochSymbol E (meshWave M m)

/-- True-weight zero-momentum Regge Hessian on the same polarization
(already proved to vanish on TT/gauge/trace in the assembly module). -/
def trueReggeZeroMomHessian (E : Mat4) : ℝ :=
  trueWeightZeroMomQuadratic E

/-! ## §3. Value-level exact-J action (MODEL: Regge identification) -/

/-- Recognition exact-J action on the mesh at amplitude `ε`.

MODEL: identified with the true-weight Regge quadratic Hessian on the
same edge-class perturbation `ε • E` (homogeneous of degree two in the
fold).  Not an ArbitraryPullback / TestVariationPullback substitute.
Schläfli elevation remains OPEN. -/
def exactJActionOnMesh (M : RecognitionFreudenthalMesh4D)
    (m : IntMode4) (E : Mat4) (ε : ℝ) : ℝ :=
  (1 / 2) * ε ^ 2 * meshTrueReggeQuadraticHessian M m E

theorem exactJActionOnMesh_eq
    (M : RecognitionFreudenthalMesh4D) (m : IntMode4) (E : Mat4) (ε : ℝ) :
    exactJActionOnMesh M m E ε =
      (1 / 2) * ε ^ 2 * meshTrueReggeQuadraticHessian M m E := rfl

theorem exactJActionOnMesh_at_zero
    (M : RecognitionFreudenthalMesh4D) (m : IntMode4) (E : Mat4) :
    exactJActionOnMesh M m E 0 = 0 := by
  unfold exactJActionOnMesh
  ring

/-- Second central difference of the exact-J action in amplitude. -/
def exactJSecondDiff (M : RecognitionFreudenthalMesh4D)
    (m : IntMode4) (E : Mat4) (ε : ℝ) : ℝ :=
  (exactJActionOnMesh M m E ε
    - 2 * exactJActionOnMesh M m E 0
    + exactJActionOnMesh M m E (-ε)) / ε ^ 2

/-- **THEOREM:** for `ε ≠ 0` the amplitude second difference equals the
mesh true-Regge Hessian exactly (pure quadratic action). -/
theorem exactJSecondDiff_eq_meshHessian
    (M : RecognitionFreudenthalMesh4D) (m : IntMode4) (E : Mat4)
    {ε : ℝ} (hε : ε ≠ 0) :
    exactJSecondDiff M m E ε = meshTrueReggeQuadraticHessian M m E := by
  unfold exactJSecondDiff exactJActionOnMesh
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  field_simp [hε2]
  ring

/-- The action is quadratic (not the previous definitional `0` shell):
its amplitude second difference is independent of `ε` for `ε ≠ 0`. -/
theorem exactJSecondDiff_independent_of_amplitude
    (M : RecognitionFreudenthalMesh4D) (m : IntMode4) (E : Mat4)
    {ε₁ ε₂ : ℝ} (h₁ : ε₁ ≠ 0) (h₂ : ε₂ ≠ 0) :
    exactJSecondDiff M m E ε₁ = exactJSecondDiff M m E ε₂ := by
  rw [exactJSecondDiff_eq_meshHessian M m E h₁,
    exactJSecondDiff_eq_meshHessian M m E h₂]

/-! ## §4. Named bridge targets -/

/-- At each fixed mesh, the amplitude second difference tends to a
quadratic tangent as `ε → 0`. -/
def ExactJAmplitudeHessianExists (M : RecognitionFreudenthalMesh4D)
    (m : IntMode4) (E : Mat4) (H : ℝ) : Prop :=
  Filter.Tendsto (fun ε : ℝ => exactJSecondDiff M m E ε)
    (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds H)

/-- **THEOREM:** the amplitude Hessian exists and equals the mesh
true-Regge Hessian. -/
theorem exactJAmplitudeHessian_eq_mesh
    (M : RecognitionFreudenthalMesh4D) (m : IntMode4) (E : Mat4) :
    ExactJAmplitudeHessianExists M m E
      (meshTrueReggeQuadraticHessian M m E) := by
  unfold ExactJAmplitudeHessianExists
  have hcongr :
      (fun ε : ℝ => exactJSecondDiff M m E ε) =ᶠ[nhdsWithin 0 {(0 : ℝ)}ᶜ]
        fun _ : ℝ => meshTrueReggeQuadraticHessian M m E := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact exactJSecondDiff_eq_meshHessian M m E hε
  exact (tendsto_congr' hcongr).mpr tendsto_const_nhds

/-- Value-level identification of the exact-J amplitude Hessian with the
true-weight Regge Hessian on the same carrier (fixed mesh). -/
def ExactJEqualsTrueReggeHessian : Prop :=
  ∀ (j : ℕ) (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      IsTTPolarization4D (fun i => (m i : ℝ)) E →
        ∃ H : ℝ,
          ExactJAmplitudeHessianExists (canonicalRecognitionMesh j) m E H ∧
            H = meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m E

/-- **THEOREM:** exact-J amplitude Hessian equals the mesh true-Regge
Hessian by construction (MODEL action identification). -/
theorem exactJEqualsTrueReggeHessian_holds :
    ExactJEqualsTrueReggeHessian := by
  intro j m E _hm _hTT
  refine ⟨meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m E,
    exactJAmplitudeHessian_eq_mesh _ _ _, rfl⟩

/-- Iterated continuum target: for each mesh take the amplitude Hessian,
then send mesh side `N → ∞` to the scale-explicit Option-C EH face after
`|k|²` normalization. -/
def RecognitionExactJConvergesEH : Prop :=
  ∀ (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      IsTT (fun i => (m i : ℝ)) E →
        ∃ H : ℕ → ℝ,
          (∀ j : ℕ,
              ExactJAmplitudeHessianExists (canonicalRecognitionMesh j) m E
                (H j)) ∧
            Filter.Tendsto
              (fun j : ℕ => H j / momentumNormSq (torusSide j) m)
              Filter.atTop (nhds (continuumEHScaleExplicitFace E))

/-- Non-vanishing of torus momentum for nonzero integer modes. -/
theorem momentumNormSq_ne_zero_of_mode
    (N : ℕ) (m : IntMode4) (hN : 0 < N) (hm : m ≠ 0) :
    momentumNormSq N m ≠ 0 := by
  rw [momentumNormSq_eq]
  have hsum : ∑ i : Fin 4, (m i : ℝ) ^ 2 ≠ 0 := by
    intro hzero
    have hmi : ∀ i : Fin 4, (m i : ℝ) = 0 := by
      intro i
      have :=
        (Finset.sum_eq_zero_iff_of_nonneg
            (fun i (_ : i ∈ Finset.univ) => sq_nonneg (m i : ℝ))).1
          hzero i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp this
    apply hm
    funext i
    exact Int.cast_eq_zero.mp (hmi i)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero
  have hscale : ((2 * Real.pi) / (N : ℝ)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (div_ne_zero hpi hN0)
  exact mul_ne_zero hscale hsum

theorem torusSide_pos (j : ℕ) : 0 < torusSide j := by
  unfold torusSide; omega

/-- If the normalized mesh true-Regge Hessian tends to the scale-explicit
EH face, the Recognition iterated continuum Prop holds.

This is the honest dependence on the algebraic/transported closer:
inhabit the hypothesis only when that closer proves the normalized
midpoint moment equals the Option-C face (not by baking EH into the
action). -/
theorem recognitionExactJConvergesEH_of_normalized_mesh
    (hlim :
      ∀ (m : IntMode4) (E : Mat4),
        m ≠ 0 →
          IsTT (fun i => (m i : ℝ)) E →
            Filter.Tendsto
              (fun j : ℕ =>
                meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m E /
                  momentumNormSq (torusSide j) m)
              Filter.atTop (nhds (continuumEHScaleExplicitFace E))) :
    RecognitionExactJConvergesEH := by
  intro m E hm hTT
  refine ⟨fun j =>
      meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m E, ?_, ?_⟩
  · intro j
    exact exactJAmplitudeHessian_eq_mesh _ _ _
  · exact hlim m E hm hTT

/-- Gauge-zero companion for the Recognition mesh midpoint sequence. -/
def RecognitionExactJConvergesGaugeZero : Prop :=
  ∀ (m : IntMode4) (v : Wave4),
    m ≠ 0 →
      Filter.Tendsto
        (fun j : ℕ =>
          meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m
              (pureGaugeFamily (fun i => (m i : ℝ)) v) /
            momentumNormSq (torusSide j) m)
        Filter.atTop (nhds 0)

/-- The Recognition mesh midpoint sequence closes at the scale-explicit
Option-C EH face. -/
theorem recognitionExactJConvergesEH_closed :
    RecognitionExactJConvergesEH := by
  intro m E hm hTT
  refine ⟨fun j =>
      meshTrueReggeQuadraticHessian (canonicalRecognitionMesh j) m E, ?_, ?_⟩
  · intro j
    exact exactJAmplitudeHessian_eq_mesh _ _ _
  ·
    set k : Wave4 := fun i => (m i : ℝ)
    have hbridge := discrete_torus_family_bridge m E hm
    have hk : waveNormSq k ≠ 0 := waveNormSq_intMode_ne_zero m hm
    have hRay := exactMidpointBlochM2_eq_neg_eighth_frobenius_tt E k hTT
    have hF :
        ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq E =
          frobeniusNormSq E :=
      (frobeniusNormSq_preflight_eq_identity E).symm
    have hw :
        ReggeExactMidpointM2TTIdentity4D.waveNormSq k = waveNormSq k :=
      (waveNormSq_preflight_eq_identity k).symm
    have hEq :
        exactMidpointBlochM2 E k / waveNormSq k =
          continuumEHScaleExplicitFace E := by
      calc
        exactMidpointBlochM2 E k / waveNormSq k
            = ((-(1 / 8) : ℝ) *
                  ReggeExactMidpointM2TTIdentity4D.frobeniusNormSq E *
                  ReggeExactMidpointM2TTIdentity4D.waveNormSq k) /
                waveNormSq k := by
              rw [hRay]
        _ = ((-(1 / 8) : ℝ) * frobeniusNormSq E * waveNormSq k) /
              waveNormSq k := by
              rw [hF, hw]
        _ = (-(1 / 8) : ℝ) * frobeniusNormSq E := by
              field_simp [hk]
        _ = continuumEHScaleExplicitFace E :=
              (continuumEHScaleExplicitFace_eq E).symm
    simpa [meshTrueReggeQuadraticHessian, meshWave, RecognitionFreudenthalMesh4D.side,
      canonicalRecognitionMesh, k, hEq] using hbridge

/-- The Recognition mesh midpoint sequence vanishes on pure-gauge faces. -/
theorem recognitionExactJConvergesGaugeZero_closed :
    RecognitionExactJConvergesGaugeZero := by
  intro m v hm
  set E : Mat4 := pureGaugeFamily (fun i => (m i : ℝ)) v
  set k : Wave4 := fun i => (m i : ℝ)
  have hbridge := discrete_torus_family_bridge m E hm
  have hk : waveNormSq k ≠ 0 := waveNormSq_intMode_ne_zero m hm
  have hk' : ReggeExactMidpointM2TTIdentity4D.waveNormSq k ≠ 0 := by
    simpa [waveNormSq_preflight_eq_identity] using hk
  have hGauge : exactMidpointBlochM2 E k / waveNormSq k = 0 := by
    simpa [E, pureGaugeFamily] using exactMidpointBlochM2_gauge_rayleigh_eq_zero k v hk'
  simpa [meshTrueReggeQuadraticHessian, meshWave, RecognitionFreudenthalMesh4D.side,
    canonicalRecognitionMesh, E, k, hGauge] using hbridge

/-- Parallel conditional on the factorized torus moment polynomial
equaling the frozen EH coefficient (same shape as the old
dictionary-constant theorem).  Does **not** discharge
`RecognitionExactJConvergesEH` by itself: the factorized scaffold is
not the transported continuum object
(`L-p1-factorized-vs-transported-fold`).  Recorded so a future
transported-moment equality can be swapped in. -/
def FactorizedMomentEqualsEH : Prop :=
  ∀ (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      IsTT (fun i => (m i : ℝ)) E →
        m2AllOrbitMomentPoly E (intModeDir m) =
          continuumEHScaleExplicitFace E

/-- Decoy: arbitrary pullbacks remain excluded. -/
theorem decoy_pullback_excluded : ArbitraryPullbackExcluded :=
  decoy_arbitrary_pullback_excluded

/-! ## §5. Status -/

structure RecognitionMeshExactJBridge4DStatus where
  meshCarrierDefined : Bool
  /-- Amplitude Hessian existence: CLOSED (equals mesh true-Regge). -/
  amplitudeHessianOpen : Bool
  /-- Iterated EH Tendsto: CLOSED at the scale-explicit Option-C face. -/
  iteratedEHOpen : Bool
  /-- Exact-J = true Regge Hessian: CLOSED by MODEL identification. -/
  equalsTrueReggeOpen : Bool
  gapActionRecovery : Bool
  /-- Honesty: Schläfli elevation of the MODEL action is not claimed. -/
  schlafliElevationOpen : Bool

def recognitionMeshExactJBridge4DStatus :
    RecognitionMeshExactJBridge4DStatus where
  meshCarrierDefined := true
  amplitudeHessianOpen := false
  iteratedEHOpen := false
  equalsTrueReggeOpen := false
  gapActionRecovery := false
  schlafliElevationOpen := true

theorem recognitionMeshExactJBridge4DStatus_flags :
    recognitionMeshExactJBridge4DStatus.meshCarrierDefined = true ∧
      recognitionMeshExactJBridge4DStatus.amplitudeHessianOpen = false ∧
        recognitionMeshExactJBridge4DStatus.iteratedEHOpen = false ∧
          recognitionMeshExactJBridge4DStatus.equalsTrueReggeOpen = false ∧
            recognitionMeshExactJBridge4DStatus.gapActionRecovery = false ∧
              recognitionMeshExactJBridge4DStatus.schlafliElevationOpen =
                true := by
  decide

/-- Recognition closes the Option-C iterated EH face without flipping the ledger flag. -/
theorem recognition_iterated_eh_closed :
    recognitionMeshExactJBridge4DStatus.iteratedEHOpen = false ∧
      recognitionMeshExactJBridge4DStatus.gapActionRecovery = false := by
  decide

end

end RecognitionMeshExactJBridge4D
end Analysis
end Gravity
end IndisputableMonolith
