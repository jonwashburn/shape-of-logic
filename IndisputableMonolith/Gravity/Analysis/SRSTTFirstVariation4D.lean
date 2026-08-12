import Mathlib
import IndisputableMonolith.Gravity.Analysis.SRSConvergesEH4D

/-!
# TT directional first variation of the closed 4D midpoint Bloch symbol

Derives the genuine cross-term / directional first variation of
`exactMidpointBlochSymbol` in the Euclidean weak-field TT sector, then
transports its torus-normalized continuum face via the banked
`S_RS_converges_EH_4d_closed` Tendsto on `H+K` and `H-K` plus polarization.

## Honesty (binding)

* **THEOREM** only in the Euclidean weak-field TT sector of the closed
  midpoint Bloch continuum face.
* Explicitly **NOT** a source equation, **NOT** Ricci / null focusing,
  and **NOT** GAP1 closure.
* The exact missing future object is a concrete Recognition-derived
  Freudenthal exact-J metric refinement / pullback identifying the sourced
  response with this midpoint variation, followed by Lorentzian null-dyad
  Ricci / stress transport.
* Do not cite `PixelAreaModel`, `LocalNullPatch`,
  `ObeysRSNullFieldEquation`, or the MODEL `exactJActionOnMesh` of
  `RecognitionMeshExactJBridge4D` as an argument.  (Transitively imported
  modules may exist; they are not used here.)
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace SRSTTFirstVariation4D

open Regge4DContinuumPreflight
open ReggeExactFlatHessianBlochData4D
open ReggeExactFlatHessianBlochSymbol4D
open ReggeExactFlatHessianBlochTorusBridge4D
open EdgeTTDecomposition4D
open SRSConvergesEH4D
open BigOperators Filter Topology

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section

abbrev Mat4 := Regge4DContinuumPreflight.Mat4
abbrev Wave4 := Regge4DContinuumPreflight.Wave4
abbrev CouplingIdx := ReggeExactFlatHessianBlochSymbol4D.CouplingIdx

/-! ## §1. Frobenius pairing and edge-strain linearity -/

/-- Euclidean Frobenius pairing on `4×4` matrices. -/
def frobeniusPairing4D (H K : Mat4) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, H i j * K i j

theorem frobeniusNormSq_eq_pairing_self (H : Mat4) :
    frobeniusNormSq H = frobeniusPairing4D H H := rfl

theorem edgeStrain_add (H K : Mat4) (D : Fin 4 → ℤ) :
    edgeStrain (H + K) D = edgeStrain H D + edgeStrain K D := by
  unfold edgeStrain
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, (H + K) i j * (D i : ℝ) * (D j : ℝ)
        = ∑ i : Fin 4, ∑ j : Fin 4,
            (H i j * (D i : ℝ) * (D j : ℝ) +
              K i j * (D i : ℝ) * (D j : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          simp only [Matrix.add_apply]
          ring
    _ = ∑ i : Fin 4,
          ((∑ j : Fin 4, H i j * (D i : ℝ) * (D j : ℝ)) +
            ∑ j : Fin 4, K i j * (D i : ℝ) * (D j : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    _ = (∑ i : Fin 4, ∑ j : Fin 4, H i j * (D i : ℝ) * (D j : ℝ)) +
          (∑ i : Fin 4, ∑ j : Fin 4, K i j * (D i : ℝ) * (D j : ℝ)) :=
        Finset.sum_add_distrib

theorem edgeStrain_smul (c : ℝ) (H : Mat4) (D : Fin 4 → ℤ) :
    edgeStrain (c • H) D = c * edgeStrain H D := by
  unfold edgeStrain
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, (c • H) i j * (D i : ℝ) * (D j : ℝ)
        = ∑ i : Fin 4, ∑ j : Fin 4,
            c * (H i j * (D i : ℝ) * (D j : ℝ)) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          simp only [Matrix.smul_apply, smul_eq_mul]
          ring
    _ = c * ∑ i : Fin 4, ∑ j : Fin 4, H i j * (D i : ℝ) * (D j : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ c).symm

theorem edgeStrain_neg (H : Mat4) (D : Fin 4 → ℤ) :
    edgeStrain (-H) D = -edgeStrain H D := by
  simpa [neg_one_smul] using edgeStrain_smul (-1) H D

theorem edgeStrain_sub (H K : Mat4) (D : Fin 4 → ℤ) :
    edgeStrain (H - K) D = edgeStrain H D - edgeStrain K D := by
  rw [sub_eq_add_neg, edgeStrain_add, edgeStrain_neg, ← sub_eq_add_neg]

/-! ## §2. Cross-term first variation (genuine bilinearization) -/

/-- Coupling weight cross term: polarization of the product of edge strains. -/
def couplingWeightCross (H K : Mat4) (c : Coupling) : ℝ :=
  (1 / 2 : ℝ) * (c.s : ℝ) *
    (edgeStrain H c.De * edgeStrain K c.Dep +
      edgeStrain K c.De * edgeStrain H c.Dep)

def couplingWeightCrossIdx (H K : Mat4) (i : CouplingIdx) : ℝ :=
  couplingWeightCross H K couplingTable[i]

/-- Opaque cross-weight wrapper (Fin-1208 hygiene). -/
irreducible_def crossWeightFn (H K : Mat4) : CouplingIdx → ℝ :=
  couplingWeightCrossIdx H K

/-- Directional first variation of `exactMidpointBlochSymbol` at `H` in
direction `K` (finite coupling sum with cross edge-strain factors). -/
def exactMidpointBlochFirstVariation (H K : Mat4) (k : Wave4) : ℝ :=
  ∑ i : CouplingIdx,
    couplingWeightCrossIdx H K i * Real.cos (couplingPhaseIdx k i)

theorem exactMidpointBlochSymbol_eq_irred (H : Mat4) (k : Wave4) :
    exactMidpointBlochSymbol H k =
      ∑ i ∈ couplingUniv, weightFn H i * Real.cos (phaseFn k i) := by
  rw [weightFn_def, phaseFn_def, couplingUniv_def]
  rfl

theorem exactMidpointBlochFirstVariation_eq_irred
    (H K : Mat4) (k : Wave4) :
    exactMidpointBlochFirstVariation H K k =
      ∑ i ∈ couplingUniv,
        crossWeightFn H K i * Real.cos (phaseFn k i) := by
  rw [crossWeightFn_def, phaseFn_def, couplingUniv_def]
  rfl

theorem couplingWeight_line (H K : Mat4) (c : Coupling) (t : ℝ) :
    couplingWeight (H + t • K) c =
      couplingWeight H c +
        t * couplingWeightCross H K c +
          t ^ 2 * couplingWeight K c := by
  unfold couplingWeight couplingWeightCross
  have hDe :
      edgeStrain (H + t • K) c.De =
        edgeStrain H c.De + t * edgeStrain K c.De := by
    rw [edgeStrain_add, edgeStrain_smul]
  have hDep :
      edgeStrain (H + t • K) c.Dep =
        edgeStrain H c.Dep + t * edgeStrain K c.Dep := by
    rw [edgeStrain_add, edgeStrain_smul]
  rw [hDe, hDep]
  ring

theorem couplingWeightIdx_line (H K : Mat4) (i : CouplingIdx) (t : ℝ) :
    couplingWeightIdx (H + t • K) i =
      couplingWeightIdx H i +
        t * couplingWeightCrossIdx H K i +
          t ^ 2 * couplingWeightIdx K i := by
  unfold couplingWeightIdx couplingWeightCrossIdx
  exact couplingWeight_line H K couplingTable[i] t

theorem weightFn_line (H K : Mat4) (t : ℝ) (i : CouplingIdx) :
    weightFn (H + t • K) i =
      weightFn H i + t * crossWeightFn H K i + t ^ 2 * weightFn K i := by
  rw [weightFn_def, weightFn_def, weightFn_def, crossWeightFn_def]
  exact couplingWeightIdx_line H K i t

/-- Line expansion: `Q(H+tK) = Q(H) + t·FV(H,K) + t²·Q(K)`. -/
theorem exactMidpointBlochSymbol_line (H K : Mat4) (k : Wave4) (t : ℝ) :
    exactMidpointBlochSymbol (H + t • K) k =
      exactMidpointBlochSymbol H k +
        t * exactMidpointBlochFirstVariation H K k +
          t ^ 2 * exactMidpointBlochSymbol K k := by
  rw [exactMidpointBlochSymbol_eq_irred,
    exactMidpointBlochSymbol_eq_irred H,
    exactMidpointBlochSymbol_eq_irred K,
    exactMidpointBlochFirstVariation_eq_irred]
  have hsplit (i : CouplingIdx) (_ : i ∈ couplingUniv) :
      weightFn (H + t • K) i * Real.cos (phaseFn k i) =
        weightFn H i * Real.cos (phaseFn k i) +
          t * (crossWeightFn H K i * Real.cos (phaseFn k i)) +
            t ^ 2 * (weightFn K i * Real.cos (phaseFn k i)) := by
    rw [weightFn_line]
    ring
  calc
    ∑ i ∈ couplingUniv, weightFn (H + t • K) i * Real.cos (phaseFn k i)
        = ∑ i ∈ couplingUniv,
            (weightFn H i * Real.cos (phaseFn k i) +
              t * (crossWeightFn H K i * Real.cos (phaseFn k i)) +
                t ^ 2 * (weightFn K i * Real.cos (phaseFn k i))) :=
          Finset.sum_congr rfl hsplit
    _ = (∑ i ∈ couplingUniv, weightFn H i * Real.cos (phaseFn k i)) +
          (∑ i ∈ couplingUniv,
              t * (crossWeightFn H K i * Real.cos (phaseFn k i))) +
            ∑ i ∈ couplingUniv,
              t ^ 2 * (weightFn K i * Real.cos (phaseFn k i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ i ∈ couplingUniv, weightFn H i * Real.cos (phaseFn k i)) +
          t * ∑ i ∈ couplingUniv,
              crossWeightFn H K i * Real.cos (phaseFn k i) +
            t ^ 2 *
              ∑ i ∈ couplingUniv, weightFn K i * Real.cos (phaseFn k i) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem hasDerivAt_affine_quad (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + b * t + c * t ^ 2) b 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => c * t ^ 2) 0 0 := by
    simpa using h1.const_mul c
  have h3 : HasDerivAt (fun t : ℝ => b * t) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul b
  have h4 := (h2.add h3).add_const a
  have hfun :
      (fun t : ℝ => a + b * t + c * t ^ 2) =
        fun x : ℝ =>
          ((fun t : ℝ => c * t ^ 2) + (fun t : ℝ => b * t)) x + a := by
    funext t
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  simpa using h4

/-- Finite-line directional derivative of the midpoint symbol at `t = 0`. -/
theorem hasDerivAt_exactMidpointBlochSymbol_line
    (H K : Mat4) (k : Wave4) :
    HasDerivAt (fun t : ℝ => exactMidpointBlochSymbol (H + t • K) k)
      (exactMidpointBlochFirstVariation H K k) 0 := by
  have hfun :
      (fun t : ℝ => exactMidpointBlochSymbol (H + t • K) k) =
        fun t : ℝ =>
          exactMidpointBlochSymbol H k +
            exactMidpointBlochFirstVariation H K k * t +
              exactMidpointBlochSymbol K k * t ^ 2 := by
    funext t
    simpa [mul_comm, add_assoc, add_left_comm, add_comm] using
      exactMidpointBlochSymbol_line H K k t
  rw [hfun]
  exact hasDerivAt_affine_quad (exactMidpointBlochSymbol H k)
    (exactMidpointBlochFirstVariation H K k) (exactMidpointBlochSymbol K k)

/-- Polarization identity for the midpoint first variation. -/
theorem exactMidpointBlochFirstVariation_polarization
    (H K : Mat4) (k : Wave4) :
    exactMidpointBlochFirstVariation H K k =
      (exactMidpointBlochSymbol (H + K) k -
        exactMidpointBlochSymbol (H - K) k) / 2 := by
  have hPlus :
      exactMidpointBlochSymbol (H + K) k =
        exactMidpointBlochSymbol H k +
          exactMidpointBlochFirstVariation H K k +
            exactMidpointBlochSymbol K k := by
    simpa [one_smul] using exactMidpointBlochSymbol_line H K k 1
  have hMinus :
      exactMidpointBlochSymbol (H - K) k =
        exactMidpointBlochSymbol H k -
          exactMidpointBlochFirstVariation H K k +
            exactMidpointBlochSymbol K k := by
    have h := exactMidpointBlochSymbol_line H K k (-1)
    have hsmul : H + (-1 : ℝ) • K = H - K := by
      rw [neg_one_smul, sub_eq_add_neg]
    rw [hsmul] at h
    -- Q(H-K) = Q(H) + (-1)·FV + ((-1)²)·Q(K)
    linarith
  linarith

/-! ## §3. IsTT closed under add / sub -/

theorem IsSymmetric_add {H K : Mat4}
    (hH : IsSymmetric H) (hK : IsSymmetric K) : IsSymmetric (H + K) := by
  intro i j
  simp only [Matrix.add_apply, hH i j, hK i j]

theorem IsSymmetric_sub {H K : Mat4}
    (hH : IsSymmetric H) (hK : IsSymmetric K) : IsSymmetric (H - K) := by
  intro i j
  simp only [Matrix.sub_apply, hH i j, hK i j]

theorem IsTraceless_add {H K : Mat4}
    (hH : IsTraceless H) (hK : IsTraceless K) : IsTraceless (H + K) := by
  unfold IsTraceless euclideanTrace at hH hK ⊢
  simp only [Matrix.add_apply]
  rw [Finset.sum_add_distrib, hH, hK, add_zero]

theorem IsTraceless_sub {H K : Mat4}
    (hH : IsTraceless H) (hK : IsTraceless K) : IsTraceless (H - K) := by
  unfold IsTraceless euclideanTrace at hH hK ⊢
  simp only [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, hH, hK, sub_zero]

theorem IsTransverse_add {m : Wave4} {H K : Mat4}
    (hH : IsTransverse m H) (hK : IsTransverse m K) :
    IsTransverse m (H + K) := by
  intro i
  simp only [Matrix.add_apply, add_mul]
  rw [Finset.sum_add_distrib, hH i, hK i, add_zero]

theorem IsTransverse_sub {m : Wave4} {H K : Mat4}
    (hH : IsTransverse m H) (hK : IsTransverse m K) :
    IsTransverse m (H - K) := by
  intro i
  simp only [Matrix.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib, hH i, hK i, sub_zero]

theorem IsTT_add {m : Wave4} {H K : Mat4}
    (hH : IsTT m H) (hK : IsTT m K) : IsTT m (H + K) :=
  ⟨IsSymmetric_add hH.1 hK.1, IsTraceless_add hH.2.1 hK.2.1,
    IsTransverse_add hH.2.2 hK.2.2⟩

theorem IsTT_sub {m : Wave4} {H K : Mat4}
    (hH : IsTT m H) (hK : IsTT m K) : IsTT m (H - K) :=
  ⟨IsSymmetric_sub hH.1 hK.1, IsTraceless_sub hH.2.1 hK.2.1,
    IsTransverse_sub hH.2.2 hK.2.2⟩

/-! ## §4. Continuum face polarization and TT first-variation Tendsto -/

theorem frobeniusPairing4D_polarization (H K : Mat4) :
    frobeniusNormSq (H + K) - frobeniusNormSq (H - K) =
      4 * frobeniusPairing4D H K := by
  unfold frobeniusNormSq frobeniusPairing4D
  calc
    (∑ i : Fin 4, ∑ j : Fin 4, (H + K) i j * (H + K) i j) -
          ∑ i : Fin 4, ∑ j : Fin 4, (H - K) i j * (H - K) i j
        = ∑ i : Fin 4,
            (∑ j : Fin 4, (H + K) i j * (H + K) i j -
              ∑ j : Fin 4, (H - K) i j * (H - K) i j) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin 4, ∑ j : Fin 4,
          ((H + K) i j * (H + K) i j - (H - K) i j * (H - K) i j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin 4, ∑ j : Fin 4, 4 * (H i j * K i j) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => ?_
          simp only [Matrix.add_apply, Matrix.sub_apply]
          ring
    _ = 4 * ∑ i : Fin 4, ∑ j : Fin 4, H i j * K i j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum Finset.univ (fun j => H i j * K i j) 4).symm

/-- Algebraic continuum-face polarization equals `-(1/4)` Frobenius pairing. -/
theorem continuumFace_polarization_eq_neg_quarter_frobenius
    (H K : Mat4) :
    (continuumEHScaleExplicitFace (H + K) -
        continuumEHScaleExplicitFace (H - K)) / 2 =
      -(1 / 4 : ℝ) * frobeniusPairing4D H K := by
  rw [continuumEHScaleExplicitFace_eq, continuumEHScaleExplicitFace_eq]
  have h := frobeniusPairing4D_polarization H K
  linarith

theorem momentumNormSq_torus_ne_zero (j : ℕ) (m : IntMode4) (hm : m ≠ 0) :
    momentumNormSq (torusSide j) m ≠ 0 := by
  rw [momentumNormSq_eq_scale_sq]
  have hscale : torusScale j ≠ 0 := by
    unfold torusScale torusSide
    have hN : ((j + 3 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    exact div_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hN
  exact mul_ne_zero (pow_ne_zero 2 hscale) (waveNormSq_intMode_ne_zero m hm)

/-- Normalized finite-mesh directional derivative (no continuum interchange). -/
theorem hasDerivAt_finiteExactMidpointBlochSymbol_normalized
    (j : ℕ) (m : IntMode4) (H K : Mat4) (hm : m ≠ 0) :
    HasDerivAt
      (fun t : ℝ =>
        finiteExactMidpointBlochSymbol j m (H + t • K) /
          momentumNormSq (torusSide j) m)
      (exactMidpointBlochFirstVariation H K (realMode (torusSide j) m) /
        momentumNormSq (torusSide j) m)
      0 := by
  have hn := momentumNormSq_torus_ne_zero j m hm
  have h :=
    hasDerivAt_exactMidpointBlochSymbol_line H K (realMode (torusSide j) m)
  simpa [finiteExactMidpointBlochSymbol] using h.div_const _

/-- **Headline THEOREM (Euclidean weak-field TT sector):** the torus-normalized
midpoint first variation tends to `-(1/4)` Frobenius pairing. -/
theorem continuumTTFirstVariation_closed :
    ∀ (m : IntMode4) (H K : Mat4),
      m ≠ 0 →
        IsTT (fun i => (m i : ℝ)) H →
          IsTT (fun i => (m i : ℝ)) K →
            Tendsto
              (fun j : ℕ =>
                exactMidpointBlochFirstVariation H K
                    (realMode (torusSide j) m) /
                  momentumNormSq (torusSide j) m)
              atTop
              (nhds (-(1 / 4 : ℝ) * frobeniusPairing4D H K)) := by
  intro m H K hm hH hK
  have hTT_add : IsTT (fun i => (m i : ℝ)) (H + K) := IsTT_add hH hK
  have hTT_sub : IsTT (fun i => (m i : ℝ)) (H - K) := IsTT_sub hH hK
  have hPlus := S_RS_converges_EH_4d_closed.1 m (H + K) hm hTT_add
  have hMinus := S_RS_converges_EH_4d_closed.1 m (H - K) hm hTT_sub
  have hDiff := hPlus.sub hMinus
  have hFace := continuumFace_polarization_eq_neg_quarter_frobenius H K
  have hSeq :
      (fun j : ℕ =>
          (finiteExactMidpointBlochSymbol j m (H + K) /
                momentumNormSq (torusSide j) m -
              finiteExactMidpointBlochSymbol j m (H - K) /
                momentumNormSq (torusSide j) m) /
            2) =
        fun j : ℕ =>
          exactMidpointBlochFirstVariation H K (realMode (torusSide j) m) /
            momentumNormSq (torusSide j) m := by
    funext j
    have hn := momentumNormSq_torus_ne_zero j m hm
    have hpol :=
      exactMidpointBlochFirstVariation_polarization H K
        (realMode (torusSide j) m)
    change
      ((exactMidpointBlochSymbol (H + K) (realMode (torusSide j) m) /
              momentumNormSq (torusSide j) m -
            exactMidpointBlochSymbol (H - K) (realMode (torusSide j) m) /
              momentumNormSq (torusSide j) m) /
          2) =
        exactMidpointBlochFirstVariation H K (realMode (torusSide j) m) /
          momentumNormSq (torusSide j) m
    field_simp [hn]
    linarith [hpol]
  have hTend :
      Tendsto
        (fun j : ℕ =>
          (finiteExactMidpointBlochSymbol j m (H + K) /
                momentumNormSq (torusSide j) m -
              finiteExactMidpointBlochSymbol j m (H - K) /
                momentumNormSq (torusSide j) m) /
            2)
        atTop
        (nhds
          ((continuumEHScaleExplicitFace (H + K) -
              continuumEHScaleExplicitFace (H - K)) / 2)) :=
    hDiff.div_const 2
  have hTend' :
      Tendsto
        (fun j : ℕ =>
          exactMidpointBlochFirstVariation H K (realMode (torusSide j) m) /
            momentumNormSq (torusSide j) m)
        atTop
        (nhds
          ((continuumEHScaleExplicitFace (H + K) -
              continuumEHScaleExplicitFace (H - K)) / 2)) := by
    rwa [hSeq] at hTend
  simpa [hFace] using hTend'

/-! ## §5. Packaged certificate -/

/-- Bundle: line derivative, polarization identity, continuum TT theorem. -/
def SRSTTFirstVariation4DCert : Prop :=
  (∀ (H K : Mat4) (k : Wave4),
      HasDerivAt (fun t : ℝ => exactMidpointBlochSymbol (H + t • K) k)
        (exactMidpointBlochFirstVariation H K k) 0) ∧
    (∀ (H K : Mat4) (k : Wave4),
      exactMidpointBlochFirstVariation H K k =
        (exactMidpointBlochSymbol (H + K) k -
          exactMidpointBlochSymbol (H - K) k) / 2) ∧
      (∀ (m : IntMode4) (H K : Mat4),
        m ≠ 0 →
          IsTT (fun i => (m i : ℝ)) H →
            IsTT (fun i => (m i : ℝ)) K →
              Tendsto
                (fun j : ℕ =>
                  exactMidpointBlochFirstVariation H K
                      (realMode (torusSide j) m) /
                    momentumNormSq (torusSide j) m)
                atTop
                (nhds (-(1 / 4 : ℝ) * frobeniusPairing4D H K)))

theorem srsTTFirstVariation4D_cert : SRSTTFirstVariation4DCert :=
  ⟨hasDerivAt_exactMidpointBlochSymbol_line,
    exactMidpointBlochFirstVariation_polarization,
    continuumTTFirstVariation_closed⟩

end

end SRSTTFirstVariation4D
end Analysis
end Gravity
end IndisputableMonolith
