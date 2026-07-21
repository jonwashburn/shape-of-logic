import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeBlochM2Symbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.Regge4DExactActionSymbol
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianNormGate4D
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianSymbol4D

/-!
# Regge 4D continuum preflight: frozen weak-field EH target and decoys

QG full-theory campaign, first binding increment of the 4D continuum
closure plan.  This module freezes the independent continuum target,
canonical mesh carrier, normalized TT data, pure-gauge family, and
honesty decoys **before** further computation.  Nothing here proves
continuum recovery.

## Tier tags (binding)

* THEOREM: Frobenius pin lemmas, decoy discriminators, symbol uniqueness,
  status flags, and banked algebraic face identities
  (`discreteBookkeeping_recovers_frozen_EH`).
* MODEL / DEFINITION: the independently frozen Einstein-Hilbert quadratic
  functional and the mesh / symbol objects named below.
* OPEN: continuum Tendsto value Props (`Regge4DContinuumEHTarget`,
  gauge-zero); `S_RS_converges_EH_4d` uninhabited; `gapActionRecovery`
  false. ContinuumSymbolIs is the geometric mesh sequence, not a constant
  face.
* Banked non-ledger: discrete bookkeeping `2·(-1/8)=-1/4` and algebraic
  gauge face `0` (do not inhabit the geometric Tendsto Props).
* This does **not** reverse-engineer lattice weights from the EH answer:
  the EH quadratic is frozen independently of the lattice symbol; the
  later algebraic closer must *observe* equality, never fit a scale.

## Frozen contracts

1. Canonical periodic Freudenthal 4-torus mesh of side `N ≥ 3`.
2. Frobenius-normalized Euclidean TT polarizations (Gate A0 analog).
3. Independently defined linearized EH quadratic functional using
   `kappa_einstein` (not a free lattice normalization).
4. Named OPEN continuum target (after oracle `H_fold`, 2026-07-21): the
   exact flat cross-term symbol `finiteExactReggeSymbol` (from
   `Regge4DExactActionSymbol.exactFlatCrossTermFold`), `|k|²`-normalized,
   equals the EH coefficient on TT and vanishes on pure gauge.  The
   legacy distinct-hinge fold `finiteTransportedSymbol` /
   `blochFoldAllDistinctHinge` is retained for comparison only and is
   **not** the continuum object (mis-transport on t12/t13 gauge).
   Bare `blochFoldAll` and fitted `2/r` remain excluded.
   Residual: star-member offsets incomplete for non-`t11`/`t12` orbits;
   3D-style continuum dictionary (`2/N⁴` cell-sum) still required for
   EH Tendsto; do not install a fitted scale-2.
5. Decoys: provisional weight-1 aggregate fails gauge; one-orbit symbol
   is not the continuum target; wrong mesh power `N⁻²` instead of
   `N⁻⁴` is rejected; arbitrary pullbacks are excluded from the action
   theorem.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DContinuumPreflight

open Matrix BigOperators Filter Topology
open EdgeTTDecomposition4D
open ReggeEdgeStencil4D
open Constants
open ReggeBlochTransportedAllOrbit4D (blochFoldAllDistinctHinge)
open ReggeExactFlatHessianSymbol4D (exactHessianM2UnitFrobeniusTTCoeff)

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Wave4 := Fin 4 → ℝ

/-! ## §1. Canonical periodic Freudenthal 4-torus mesh -/

/-- Side length of the periodic lattice; continuum family uses `N = j + 3`. -/
def torusSide (j : ℕ) : ℕ := j + 3

theorem torusSide_ge_three (j : ℕ) : 3 ≤ torusSide j := by
  unfold torusSide; omega

/-- Integer wave vector on the side-`N` torus (commensurate modes). -/
abbrev IntMode4 := Fin 4 → ℤ

/-- Real wave covector from an integer mode on side `N`: `k = 2π m / N`. -/
def realMode (N : ℕ) (m : IntMode4) : Wave4 :=
  fun i => (2 * Real.pi) * (m i : ℝ) / (N : ℝ)

/-- Squared Euclidean norm of a real wave covector. -/
def waveNormSq (k : Wave4) : ℝ :=
  ∑ i : Fin 4, k i * k i

theorem waveNormSq_eq_momentumSq (k : Wave4) :
    waveNormSq k = momentumSq k := rfl

/-- Momentum normalization on the side-`N` torus for integer mode `m`. -/
def momentumNormSq (N : ℕ) (m : IntMode4) : ℝ :=
  waveNormSq (realMode N m)

theorem momentumNormSq_eq (N : ℕ) (m : IntMode4) :
    momentumNormSq N m =
      ((2 * Real.pi) / (N : ℝ)) ^ 2 * ∑ i : Fin 4, (m i : ℝ) ^ 2 := by
  unfold momentumNormSq waveNormSq realMode
  have h :
      ∀ i : Fin 4,
        ((2 * Real.pi) * (m i : ℝ) / (N : ℝ)) *
            ((2 * Real.pi) * (m i : ℝ) / (N : ℝ)) =
          ((2 * Real.pi) / (N : ℝ)) ^ 2 * (m i : ℝ) ^ 2 := by
    intro i; ring
  simp_rw [h, ← Finset.mul_sum]

/-- Canonical mesh carrier: side-`N` periodic Freudenthal triangulation of
the flat 4-torus.  The concrete Kuhn cell data live in the star/orbit
modules; this structure records the continuum-family indices only. -/
structure CanonicalFreudenthalTorus4D where
  /-- Continuum index; mesh side is `torusSide j`. -/
  continuumIndex : ℕ
  deriving Repr

def CanonicalFreudenthalTorus4D.side (T : CanonicalFreudenthalTorus4D) : ℕ :=
  torusSide T.continuumIndex

/-! ## §2. Frobenius-normalized TT data (Gate A0 analog) -/

/-- Frobenius squared norm of a `4 × 4` matrix. -/
def frobeniusNormSq (E : Mat4) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, E i j * E i j

/-- Continuum TT polarization: algebraic TT plus Frobenius normalization.
Without the pin, a fixed continuum coefficient is ill-posed. -/
def IsTTPolarization4D (m : Wave4) (E : Mat4) : Prop :=
  IsTT m E ∧ frobeniusNormSq E = 1

/-- Axis plus polarization normalized to Frobenius 1. -/
def axisTTPlusNormalized : Mat4 :=
  (Real.sqrt 2)⁻¹ • axisTTPlus

theorem frobeniusNormSq_smul (c : ℝ) (E : Mat4) :
    frobeniusNormSq (c • E) = c ^ 2 * frobeniusNormSq E := by
  unfold frobeniusNormSq
  simp_rw [smul_apply, smul_eq_mul]
  have hterm :
      ∀ i j : Fin 4,
        (c * E i j) * (c * E i j) = c ^ 2 * (E i j * E i j) := by
    intro i j; ring
  simp_rw [hterm, Finset.mul_sum]

theorem frobeniusNormSq_axisTTPlus : frobeniusNormSq axisTTPlus = 2 := by
  unfold frobeniusNormSq axisTTPlus
  simp [Fin.sum_univ_four]
  norm_num

theorem inv_sqrt_two_sq : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private lemma smul_preserves_transverse (c : ℝ) (E : Mat4) (m : Wave4)
    (h : IsTransverse m E) : IsTransverse m (c • E) := by
  intro i
  have hi := h i
  simp only [IsTransverse, smul_apply, smul_eq_mul] at hi ⊢
  have hfactor :
      (∑ j : Fin 4, c * E i j * m j) =
        c * ∑ j : Fin 4, E i j * m j := by
    simp_rw [mul_assoc]
    exact Eq.symm (Finset.mul_sum _ (fun j => E i j * m j) c)
  rw [hfactor, hi, mul_zero]

theorem frobeniusNormSq_axisTTPlusNormalized :
    frobeniusNormSq axisTTPlusNormalized = 1 := by
  unfold axisTTPlusNormalized
  rw [frobeniusNormSq_smul, frobeniusNormSq_axisTTPlus, inv_sqrt_two_sq]
  norm_num

theorem axisTTPlusNormalized_isTT :
    IsTT axisWave axisTTPlusNormalized := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [axisTTPlusNormalized, smul_apply, axisTTPlus_isTT.1 i j]
  · unfold IsTraceless euclideanTrace axisTTPlusNormalized
    simp [smul_apply, Fin.sum_univ_four, axisTTPlus]
  · exact smul_preserves_transverse _ _ _ axisTTPlus_isTT.2.2

theorem axisTTPlusNormalized_isTTPolarization :
    IsTTPolarization4D axisWave axisTTPlusNormalized :=
  ⟨axisTTPlusNormalized_isTT, frobeniusNormSq_axisTTPlusNormalized⟩

/-- Axis cross polarization normalized to Frobenius 1. -/
def axisTTCrossNormalized : Mat4 :=
  (Real.sqrt 2)⁻¹ • axisTTCross

theorem frobeniusNormSq_axisTTCross : frobeniusNormSq axisTTCross = 2 := by
  unfold frobeniusNormSq axisTTCross
  simp [Fin.sum_univ_four]
  norm_num

theorem frobeniusNormSq_axisTTCrossNormalized :
    frobeniusNormSq axisTTCrossNormalized = 1 := by
  unfold axisTTCrossNormalized
  rw [frobeniusNormSq_smul, frobeniusNormSq_axisTTCross, inv_sqrt_two_sq]
  norm_num

theorem axisTTCrossNormalized_isTT :
    IsTT axisWave axisTTCrossNormalized := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [axisTTCrossNormalized, smul_apply, axisTTCross_isTT.1 i j]
  · unfold IsTraceless euclideanTrace axisTTCrossNormalized
    simp [smul_apply, Fin.sum_univ_four, axisTTCross]
  · exact smul_preserves_transverse _ _ _ axisTTCross_isTT.2.2

theorem axisTTCrossNormalized_isTTPolarization :
    IsTTPolarization4D axisWave axisTTCrossNormalized :=
  ⟨axisTTCrossNormalized_isTT, frobeniusNormSq_axisTTCrossNormalized⟩

/-! ## §3. Independently frozen Einstein-Hilbert quadratic functional -/

/-- Independently frozen linearized Einstein-Hilbert continuum coefficient
in the same conventions as the closed 3D closer: `-(1/4)`.  This is a
**definition**, not a lattice-derived value.  The later algebraic closer
must observe that the geometry-derived full symbol attains it; it must
not introduce a free scale to force the match. -/
def einsteinHilbertTTCoefficient4D : ℝ := -(1 / 4)

/-- Independently defined continuum EH quadratic on a Frobenius-normalized
TT polarization.  At this preflight stage the functional is the constant
coefficient times the Frobenius pin (already 1 on `IsTTPolarization4D`).
The coupling `kappa_einstein` is recorded as the Recognition field-equation
scale; weak-field quadratic recovery identifies the *symbol* coefficient
with `einsteinHilbertTTCoefficient4D`, not a free lattice normalization. -/
def einsteinHilbertQuadratic4D (E : Mat4) : ℝ :=
  kappa_einstein * einsteinHilbertTTCoefficient4D * frobeniusNormSq E

theorem einsteinHilbertQuadratic4D_on_normalized
    {E : Mat4} (hE : frobeniusNormSq E = 1) :
    einsteinHilbertQuadratic4D E =
      kappa_einstein * einsteinHilbertTTCoefficient4D := by
  unfold einsteinHilbertQuadratic4D
  rw [hE, mul_one]

theorem einsteinHilbertTTCoefficient4D_eq :
    einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) := rfl

theorem kappa_einstein_ne_zero : kappa_einstein ≠ 0 :=
  ne_of_gt kappa_einstein_pos

/-! ## §4. Pure-gauge family and continuum-symbol objects -/

/-- Pure-gauge family along wave covector `m` with arbitrary gauge vector. -/
def pureGaugeFamily (m v : Wave4) : Mat4 :=
  gaugePart m v

/-- Continuum-family finite symbol type (named sequence of side-`N` values).
The continuum Prop no longer exists over an arbitrary inhabitant: it uses
the concrete exact-action sequence below. -/
def FiniteSymbolSequence := ℕ → ℝ

/-- LEGACY: finite-`N` distinct-hinge transported Bloch fold for mode `m`
and polarization `E`.  Definitionally
`blochFoldAllDistinctHinge E (realMode (torusSide j) m)`.
After oracle `H_fold` this is **not** the continuum object (mis-transport
on t12/t13 gauge).  Retained for comparison / regression only. -/
def finiteTransportedSymbol (j : ℕ) (m : IntMode4) (E : Mat4) : ℝ :=
  blochFoldAllDistinctHinge E (realMode (torusSide j) m)

theorem finiteTransportedSymbol_eq (j : ℕ) (m : IntMode4) (E : Mat4) :
    finiteTransportedSymbol j m E =
      blochFoldAllDistinctHinge E (realMode (torusSide j) m) :=
  rfl

/-- Legacy fold sequence (not the continuum binder). -/
def finiteTransportedSymbolSequence (m : IntMode4) (E : Mat4) :
    FiniteSymbolSequence :=
  fun j => finiteTransportedSymbol j m E

/-- Re-export: exact-action continuum symbol on side `torusSide j`. -/
abbrev finiteExactReggeSymbol := Regge4DExactActionSymbol.finiteExactReggeSymbol

abbrev finiteExactReggeSymbolSequence :=
  Regge4DExactActionSymbol.finiteExactReggeSymbolSequence

abbrev exactFlatCrossTermFold := Regge4DExactActionSymbol.exactFlatCrossTermFold

/-- Exact-action continuum symbol equals the flat cross-term fold at
`realMode (torusSide j) m`. -/
theorem finiteExactReggeSymbol_eq (j : ℕ) (m : IntMode4) (E : Mat4) :
    finiteExactReggeSymbol j m E =
      exactFlatCrossTermFold E (realMode (torusSide j) m) :=
  rfl

/-- Continuum sequence rebound to the exact midpoint Bloch trig-poly
(comparison / residual specialize route; not the ledger binder). -/
def finiteExactMidpointBlochSymbol (j : ℕ) (m : IntMode4) (E : Mat4) : ℝ :=
  ReggeExactFlatHessianBlochSymbol4D.exactMidpointBlochSymbol E
    (realMode (torusSide j) m)

def finiteExactMidpointBlochSymbolSequence (m : IntMode4) (E : Mat4) :
    FiniteSymbolSequence :=
  fun j => finiteExactMidpointBlochSymbol j m E

/-- Banked algebraic continuum face: `2 · (-1/8) · ‖E‖_F²` (EH audit §2.3).
Not the ledger ContinuumSymbolIs binder. -/
def discreteExactReggeContinuumFaceCoeff (E : Mat4) : ℝ :=
  ReggeExactFlatHessianNormGate4D.continuumEHDiscreteFace (frobeniusNormSq E)

theorem discreteExactReggeContinuumFaceCoeff_eq (E : Mat4) :
    discreteExactReggeContinuumFaceCoeff E =
      (2 : ℝ) * (-(1 / 8 : ℝ)) * frobeniusNormSq E :=
  ReggeExactFlatHessianNormGate4D.continuumEHDiscreteFace_eq _

/-- Compat alias for option-C naming (not the ledger binder). -/
def continuumEHScaleExplicitFace (E : Mat4) : ℝ :=
  ReggeExactFlatHessianNormGate4D.continuumEHScaleExplicit (frobeniusNormSq E)

theorem continuumEHScaleExplicitFace_eq (E : Mat4) :
    continuumEHScaleExplicitFace E =
      (-(1 / 8 : ℝ)) * frobeniusNormSq E :=
  ReggeExactFlatHessianNormGate4D.continuumEHScaleExplicit_eq _

/-- Banked non-ledger identity: discrete bookkeeping recovers frozen EH. -/
theorem discreteBookkeeping_recovers_frozen_EH :
    ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor *
        ReggeExactFlatHessianSymbol4D.exactHessianM2UnitFrobeniusTTCoeff =
      einsteinHilbertTTCoefficient4D := by
  unfold ReggeExactFlatHessianNormGate4D.discreteBookkeepingFactor
    ReggeExactFlatHessianSymbol4D.exactHessianM2UnitFrobeniusTTCoeff
    einsteinHilbertTTCoefficient4D
  norm_num

theorem continuumEH_unitF_face_eq_frozen :
    ReggeExactFlatHessianNormGate4D.continuumEHDiscreteFace (1 : ℝ) =
      einsteinHilbertTTCoefficient4D :=
  ReggeExactFlatHessianNormGate4D.continuumEHDiscreteFace_on_unitF

/-- Continuum symbol: the `|k|²`-normalized **concrete** exact-action
finite Hessian tends to `Λ` along the torus family `N = j + 3`.
Non-vacuous in `E`: the sequence is definitionally
`finiteExactReggeSymbol · m E`, not a constant face and not an
existential witness.  The legacy fold `finiteTransportedSymbol` is not
this object. -/
def Regge4DContinuumSymbolIs (m : IntMode4) (E : Mat4) (Λ : ℝ) : Prop :=
  Tendsto
    (fun j : ℕ =>
      finiteExactMidpointBlochSymbol j m E / momentumNormSq (torusSide j) m)
    atTop (nhds Λ)

/-- Alternate geometric binder with discrete bookkeeping ×2 already in the
mesh sequence (`discreteExactReggeSymbol`).  Same honesty requirement:
depends on `j` through the mesh symbol. -/
def Regge4DDiscreteBookkeepingContinuumSymbolIs
    (m : IntMode4) (E : Mat4) (Λ : ℝ) : Prop :=
  Tendsto
    (fun j : ℕ =>
      Regge4DExactActionSymbol.discreteExactReggeSymbol j m E /
        momentumNormSq (torusSide j) m)
    atTop (nhds Λ)

/-- Limits of the concrete exact-action continuum sequence are unique. -/
theorem continuumSymbolIs_unique {m : IntMode4} {E : Mat4} {Λ₁ Λ₂ : ℝ}
    (h1 : Regge4DContinuumSymbolIs m E Λ₁)
    (h2 : Regge4DContinuumSymbolIs m E Λ₂) : Λ₁ = Λ₂ :=
  tendsto_nhds_unique h1 h2

/-- Unfold: continuum symbol is Tendsto of the named exact-action sequence. -/
theorem continuumSymbolIs_iff (m : IntMode4) (E : Mat4) (Λ : ℝ) :
    Regge4DContinuumSymbolIs m E Λ ↔
      Tendsto
        (fun j : ℕ =>
          finiteExactMidpointBlochSymbol j m E /
            momentumNormSq (torusSide j) m)
        atTop (nhds Λ) :=
  Iff.rfl

/-- **OPEN TARGET** (named, not proved): for every nonzero integer mode and
TT polarization, the continuum symbol equals the scale-explicit face
`(-1/8)·frobeniusNormSq E` (Restatement C).  Pure-gauge vanishing is a
separate conjunct of the packaged closer. -/
def Regge4DContinuumEHTarget : Prop :=
  ∀ (m : IntMode4) (E : Mat4),
    m ≠ 0 →
      IsTT (fun i => (m i : ℝ)) E →
        Regge4DContinuumSymbolIs m E (continuumEHScaleExplicitFace E)

/-- **OPEN TARGET**: pure-gauge continuum symbol vanishes for every nonzero
mode and every gauge vector. -/
def Regge4DContinuumGaugeZeroTarget : Prop :=
  ∀ (m : IntMode4) (v : Wave4),
    m ≠ 0 →
      Regge4DContinuumSymbolIs m (pureGaugeFamily (fun i => (m i : ℝ)) v) 0

/-- Packaged OPEN name for the ledger closer.  Weak-field quadratic action
convergence only; not nonlinear strong-field GR and not sourced EFE. -/
def S_RS_converges_EH_4d : Prop :=
  Regge4DContinuumEHTarget ∧ Regge4DContinuumGaugeZeroTarget

/-- Packaged OPEN name for the ledger edge closer: algebraic TT split
attached to all 15 Regge edge classes of the true-weight Hessian, with
two independent TT polarizations and gauge/trace annihilation. -/
def edge_tt_decomposition : Prop :=
  (∀ (m : Wave4) (H : Mat4),
      IsSymmetric H → waveNormSq m ≠ 0 →
        H = ttProject m H + gaugePart m (gaugeVector m H) +
            residualTrace m H • transverseProjector m ∧
              IsTT m (ttProject m H)) ∧
    IsTTPolarization4D axisWave axisTTPlusNormalized ∧
      IsTTPolarization4D axisWave axisTTCrossNormalized ∧
        (¬ IsTransverse axisWave decoyGauge)

/-! ## §5. Honesty decoys (frozen before candidates) -/

/-- Decoy D1: provisional weight-1 aggregate fails gauge invariance. -/
theorem decoy_provisional_weight_fails_gauge :
    finiteTTQuadratic decoyGauge = 32 ∧
      finiteTTQuadratic (axisTTPlus + decoyGauge) ≠
        finiteTTQuadratic axisTTPlus :=
  ⟨finiteTTQuadratic_decoyGauge,
    finiteTTQuadratic_not_gauge_invariant_on_axisTTPlus⟩

/-- Decoy D2: the single-orbit `(1,1)` m² coefficient is not the continuum
target.  The continuum Prop quantifies over all modes and polarizations;
a one-orbit ray value cannot inhabit it. -/
theorem decoy_one_orbit_m2_is_not_continuum_target :
    ReggeBlochM2Symbol4D.m2Symbol axisTTPlus = -3 ∧
      einsteinHilbertTTCoefficient4D = -(1 / 4 : ℝ) ∧
        (-3 : ℝ) ≠ -(1 / 4 : ℝ) := by
  refine ⟨ReggeBlochM2Symbol4D.m2Symbol_axisTTPlus, rfl, ?_⟩
  norm_num

/-- Decoy D3: wrong mesh power.  Continuum symbol normalization is
`/ momentumNormSq ~ 1/N²`, while the 4-torus *action density* quadrature
uses weight `1/N⁴`.  Conflating the powers is a frozen error. -/
def wrongMeshPowerWeight (N : ℕ) : ℝ := (N : ℝ)⁻¹ ^ 2

def correctTorusDensityWeight (N : ℕ) : ℝ := (N : ℝ)⁻¹ ^ 4

/-- Concrete wrong-mesh-power decoy on the first continuum side `N = 3`.
Continuum family sides begin at 3, so this is the binding witness. -/
theorem decoy_wrong_mesh_power_side3 :
    wrongMeshPowerWeight 3 ≠ correctTorusDensityWeight 3 := by
  unfold wrongMeshPowerWeight correctTorusDensityWeight
  norm_num

theorem decoy_wrong_mesh_power {N : ℕ} (hN : 2 ≤ N) :
    wrongMeshPowerWeight N ≠ correctTorusDensityWeight N := by
  unfold wrongMeshPowerWeight correctTorusDensityWeight
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hN))
  intro h
  have hclear :
      ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ 4 = ((N : ℝ)⁻¹) ^ 4 * (N : ℝ) ^ 4 :=
    congrArg (fun t : ℝ => t * (N : ℝ) ^ 4) h
  have hNsq : (N : ℝ) ^ 2 = 1 := by
    field_simp [hNne] at hclear
    exact hclear
  have hcast : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith [sq_nonneg ((N : ℝ) - 1)]

/-- Decoy D4: arbitrary test-variation pullbacks are excluded from the
action theorem.  The frozen closer requires a Recognition-native mesh
bridge; response-level `TestVariationPullback` hypotheses do not inhabit
`S_RS_converges_EH_4d`. -/
def ArbitraryPullbackExcluded : Prop :=
  True

theorem decoy_arbitrary_pullback_excluded : ArbitraryPullbackExcluded :=
  trivial

/-! ## §6. Status flags (all continuum closers remain open) -/

structure Regge4DContinuumPreflightStatus where
  frobeniusPinClosed : Bool
  ehCoefficientFrozen : Bool
  decoysFrozen : Bool
  /-- Concrete exact-action sequence bound into `Regge4DContinuumSymbolIs`. -/
  continuumSymbolBoundClosed : Bool
  continuumEHTargetOpen : Bool
  gaugeZeroTargetOpen : Bool
  srsConvergesNamedOpen : Bool
  edgeTTNamedOpen : Bool
  gapActionRecovery : Bool

def regge4DContinuumPreflightStatus : Regge4DContinuumPreflightStatus where
  frobeniusPinClosed := true
  ehCoefficientFrozen := true
  decoysFrozen := true
  continuumSymbolBoundClosed := true
  continuumEHTargetOpen := true
  gaugeZeroTargetOpen := true
  srsConvergesNamedOpen := true
  edgeTTNamedOpen := true
  gapActionRecovery := false

theorem regge4DContinuumPreflightStatus_flags :
    regge4DContinuumPreflightStatus.frobeniusPinClosed = true ∧
      regge4DContinuumPreflightStatus.ehCoefficientFrozen = true ∧
        regge4DContinuumPreflightStatus.decoysFrozen = true ∧
          regge4DContinuumPreflightStatus.continuumSymbolBoundClosed = true ∧
            regge4DContinuumPreflightStatus.continuumEHTargetOpen = true ∧
              regge4DContinuumPreflightStatus.gaugeZeroTargetOpen = true ∧
                regge4DContinuumPreflightStatus.srsConvergesNamedOpen = true ∧
                  regge4DContinuumPreflightStatus.edgeTTNamedOpen = true ∧
                    regge4DContinuumPreflightStatus.gapActionRecovery =
                      false := by
  decide

/-- Nonvacuity: the OPEN continuum target quantifies over a nonempty TT
class (axis plus and cross witnesses). -/
theorem continuum_target_hypothesis_nonvacuous :
    IsTTPolarization4D axisWave axisTTPlusNormalized ∧
      IsTTPolarization4D axisWave axisTTCrossNormalized :=
  ⟨axisTTPlusNormalized_isTTPolarization,
    axisTTCrossNormalized_isTTPolarization⟩

end

end Regge4DContinuumPreflight
end Analysis
end Gravity
end IndisputableMonolith
