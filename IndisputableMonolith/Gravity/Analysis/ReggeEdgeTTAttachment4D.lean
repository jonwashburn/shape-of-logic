import Mathlib
import IndisputableMonolith.Gravity.Analysis.EdgeTTDecomposition4D

/-!
# Regge edge TT attachment (4D), plane-wave layer

QG full-theory campaign, Wave 4 / lane W4-1 (`edge_tt_decomposition`),
next kernel-checked increment after the algebraic `EdgeTTDecomposition4D`
layer: attach the Euclidean `4 × 4` TT / gauge / transverse-trace split to
**plane-wave EDGE loadings** on axis edges of the 4-torus, using the same
quadratic-form convention as the 3D chain
(`polEdgeCoeff E d = Σᵢⱼ Eᵢⱼ Dⁱ Dʲ` in `ReggeTTSymbolPreflight`).

## Tier tags (binding)

* THEOREM: every named result in this file (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* This does **not** prove the ledger name `edge_tt_decomposition` in full
  (no 4D Regge action, no continuum Einstein-Hilbert recovery, no full
  Freudenthal edge-class stencil in 4D).
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.

## What is proved (honest scope)

1. **4D plane-wave edge map.** For a matrix `H` and wave covector `m`, the
   axis-edge squared-length loading is `edgeLoad H (axisDisp a) = H a a`,
   and the midpoint plane-wave perturbation is that load times
   `cos(m·x + mₐ/2)`, mirroring the 3D midpoint convention.
2. **Linearity + decomposition transport.** The edge load (hence the
   plane-wave edge perturbation) of `H` equals the sum of the loads of
   `ttProject`, `gaugePart`, and the residual transverse-trace part, by
   linearity of `edgeLoad` plus `exists_edgeTTDecomposition`.
3. **Gauge ↔ discrete Lie (exact finite-difference identity).** For
   `gaugePart m v` on the axis edge `a`,
   `edgeLoad (gaugePart m v) (axisDisp a) = 2 mₐ vₐ`.
   The plane-wave vertex field `ξ_b(x) = v_b sin(m·x)` has discrete
   Lie loading
   `2 (ξ_a(x+eₐ) - ξ_a(x)) = 4 vₐ sin(mₐ/2) cos(m·x + mₐ/2)`.
   Therefore the matrix-gauge plane-wave edge perturbation equals
   `(mₐ / (2 sin(mₐ/2)))` times that discrete Lie loading whenever
   `sin(mₐ/2) ≠ 0`.  This is the exact lattice identity; it is **not**
   the continuum claim `δℓ² = 2 ∂_a ξ_a`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeEdgeTTAttachment4D

open Matrix BigOperators
open EdgeTTDecomposition4D

noncomputable section

/-! ## §1. 4D axis edges and edge loadings (3D `polEdgeCoeff` convention) -/

/-- Unit axis displacement in direction `a` on `Fin 4`. -/
def axisDisp (a : Fin 4) : Fin 4 → ℝ :=
  fun i => if i = a then (1 : ℝ) else 0

/-- Quadratic edge loading `Dᵀ H D = Σᵢⱼ Hᵢⱼ Dⁱ Dʲ` (same convention as
3D `polEdgeCoeff`). -/
def edgeLoad (H : Mat4) (d : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, H i j * d i * d j

/-- Midpoint phase of an axis edge based at covering-space coordinate `x`
with wave covector `m`: `m · (x + eₐ/2)`. -/
def axisMidpointPhase (m x : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  (∑ i : Fin 4, m i * x i) + m a / 2

/-- Plane-wave squared-length perturbation amplitude on the axis edge
from `x` to `x+eₐ` induced by matrix `H` (the `t`-linear coefficient in
the 3D family `ℓ² = ℓ²_flat + t · c_d · cos(mid)`). -/
def planeWaveAxisEdgePert (H : Mat4) (m x : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  edgeLoad H (axisDisp a) * Real.cos (axisMidpointPhase m x a)

/-! ## §2. Elementary edge-load algebra -/

theorem axisDisp_apply (a i : Fin 4) :
    axisDisp a i = if i = a then (1 : ℝ) else 0 := rfl

theorem edgeLoad_axis (H : Mat4) (a : Fin 4) :
    edgeLoad H (axisDisp a) = H a a := by
  unfold edgeLoad axisDisp
  simp [Finset.sum_ite_eq']

theorem edgeLoad_add (A B : Mat4) (d : Fin 4 → ℝ) :
    edgeLoad (A + B) d = edgeLoad A d + edgeLoad B d := by
  unfold edgeLoad
  simp [add_apply, add_mul, Finset.sum_add_distrib]

theorem edgeLoad_smul (c : ℝ) (H : Mat4) (d : Fin 4 → ℝ) :
    edgeLoad (c • H) d = c * edgeLoad H d := by
  unfold edgeLoad
  simp only [smul_apply, smul_eq_mul]
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, c * H i j * d i * d j
        = ∑ i : Fin 4, ∑ j : Fin 4, c * (H i j * d i * d j) := by
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    _ = c * ∑ i : Fin 4, ∑ j : Fin 4, H i j * d i * d j := by
      simp [Finset.mul_sum]

theorem edgeLoad_neg (H : Mat4) (d : Fin 4 → ℝ) :
    edgeLoad (-H) d = -edgeLoad H d := by
  simpa [neg_one_smul] using edgeLoad_smul (-1) H d

theorem edgeLoad_sub (A B : Mat4) (d : Fin 4 → ℝ) :
    edgeLoad (A - B) d = edgeLoad A d - edgeLoad B d := by
  rw [sub_eq_add_neg, edgeLoad_add, edgeLoad_neg]
  ring

theorem planeWaveAxisEdgePert_add (A B : Mat4) (m x : Fin 4 → ℝ) (a : Fin 4) :
    planeWaveAxisEdgePert (A + B) m x a =
      planeWaveAxisEdgePert A m x a + planeWaveAxisEdgePert B m x a := by
  unfold planeWaveAxisEdgePert
  rw [edgeLoad_add, add_mul]

theorem planeWaveAxisEdgePert_smul (c : ℝ) (H : Mat4) (m x : Fin 4 → ℝ)
    (a : Fin 4) :
    planeWaveAxisEdgePert (c • H) m x a =
      c * planeWaveAxisEdgePert H m x a := by
  unfold planeWaveAxisEdgePert
  rw [edgeLoad_smul, mul_assoc]

/-! ## §3. Gauge matrix → edge load (algebraic Lie symbol) -/

theorem edgeLoad_gaugePart (m v d : Fin 4 → ℝ) :
    edgeLoad (gaugePart m v) d =
      2 * (∑ i : Fin 4, m i * d i) * (∑ j : Fin 4, v j * d j) := by
  -- Direct: Dᵀ (m⊗v+v⊗m) D = 2 (m·D)(v·D).  Expand on axis basis later;
  -- here prove by rewriting each summand.
  have hαβ :
      (∑ i : Fin 4, ∑ j : Fin 4, m i * v j * d i * d j) =
        (∑ i : Fin 4, m i * d i) * (∑ j : Fin 4, v j * d j) := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, m i * v j * d i * d j
          = ∑ i : Fin 4, ∑ j : Fin 4, (m i * d i) * (v j * d j) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin 4, (m i * d i) * ∑ j : Fin 4, v j * d j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
      _ = (∑ i : Fin 4, m i * d i) * (∑ j : Fin 4, v j * d j) := by
        rw [← Finset.sum_mul]
  have hβα :
      (∑ i : Fin 4, ∑ j : Fin 4, v i * m j * d i * d j) =
        (∑ i : Fin 4, v i * d i) * (∑ j : Fin 4, m j * d j) := by
    calc
      ∑ i : Fin 4, ∑ j : Fin 4, v i * m j * d i * d j
          = ∑ i : Fin 4, ∑ j : Fin 4, (v i * d i) * (m j * d j) := by
        refine Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin 4, (v i * d i) * ∑ j : Fin 4, m j * d j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
      _ = (∑ i : Fin 4, v i * d i) * (∑ j : Fin 4, m j * d j) := by
        rw [← Finset.sum_mul]
  unfold edgeLoad gaugePart
  calc
    ∑ i : Fin 4, ∑ j : Fin 4, (m i * v j + v i * m j) * d i * d j
        = ∑ i : Fin 4, ∑ j : Fin 4,
            (m i * v j * d i * d j + v i * m j * d i * d j) := by
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ i : Fin 4, ∑ j : Fin 4, m i * v j * d i * d j) +
          (∑ i : Fin 4, ∑ j : Fin 4, v i * m j * d i * d j) := by
      simp [Finset.sum_add_distrib]
    _ = (∑ i : Fin 4, m i * d i) * (∑ j : Fin 4, v j * d j) +
          (∑ i : Fin 4, v i * d i) * (∑ j : Fin 4, m j * d j) := by
      rw [hαβ, hβα]
    _ = 2 * (∑ i : Fin 4, m i * d i) * (∑ j : Fin 4, v j * d j) := by
      set α := ∑ i : Fin 4, m i * d i
      set β := ∑ i : Fin 4, v i * d i
      ring

/-- Axis specialization: `edgeLoad (gaugePart m v) eₐ = 2 mₐ vₐ`. -/
theorem edgeLoad_gaugePart_axis (m v : Fin 4 → ℝ) (a : Fin 4) :
    edgeLoad (gaugePart m v) (axisDisp a) = 2 * m a * v a := by
  rw [edgeLoad_gaugePart]
  have hm : (∑ i : Fin 4, m i * axisDisp a i) = m a := by
    unfold axisDisp; simp [Finset.sum_ite_eq']
  have hv : (∑ j : Fin 4, v j * axisDisp a j) = v a := by
    unfold axisDisp; simp [Finset.sum_ite_eq']
  rw [hm, hv]

/-! ## §4. Discrete Lie form of a plane-wave vertex shift -/

/-- Plane-wave vertex displacement field `ξ_b(x) = v_b sin(m·x)`. -/
def gaugeVertexField (v m x : Fin 4 → ℝ) (b : Fin 4) : ℝ :=
  v b * Real.sin (∑ i : Fin 4, m i * x i)

/-- Covering-space shift of the basepoint by one lattice step along axis `a`. -/
def shiftAxis (x : Fin 4 → ℝ) (a : Fin 4) : Fin 4 → ℝ :=
  fun i => if i = a then x i + 1 else x i

/-- Discrete Lie loading of squared axis-edge length from the vertex field:
`2 (ξ_a(x+eₐ) - ξ_a(x))` (first-order change of `|eₐ + Δξ|²`). -/
def discreteLieAxis (v m x : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  2 * (gaugeVertexField v m (shiftAxis x a) a - gaugeVertexField v m x a)

/-- Lattice derivative symbol along axis `a`: `2 sin(mₐ/2)`. -/
def latticeDerivSymbol (m : Fin 4 → ℝ) (a : Fin 4) : ℝ :=
  2 * Real.sin (m a / 2)

theorem shiftAxis_dot (m x : Fin 4 → ℝ) (a : Fin 4) :
    (∑ i : Fin 4, m i * shiftAxis x a i) =
      (∑ i : Fin 4, m i * x i) + m a := by
  unfold shiftAxis
  have h (i : Fin 4) :
      m i * (if i = a then x i + 1 else x i) =
        m i * x i + m i * (if i = a then (1 : ℝ) else 0) := by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

theorem sin_add_sub_sin (θ φ : ℝ) :
    Real.sin (θ + φ) - Real.sin θ =
      2 * Real.sin (φ / 2) * Real.cos (θ + φ / 2) := by
  have h := Real.sin_sub_sin (θ + φ) θ
  -- sin(A)-sin(B) = 2 sin((A-B)/2) cos((A+B)/2)
  have hAB : ((θ + φ) - θ) / 2 = φ / 2 := by ring
  have hsum : ((θ + φ) + θ) / 2 = θ + φ / 2 := by ring
  rw [h, hAB, hsum]

/-- Exact trig expansion of the discrete Lie loading on an axis edge. -/
theorem discreteLieAxis_eq (v m x : Fin 4 → ℝ) (a : Fin 4) :
    discreteLieAxis v m x a =
      2 * v a * latticeDerivSymbol m a *
        Real.cos (axisMidpointPhase m x a) := by
  unfold discreteLieAxis gaugeVertexField axisMidpointPhase latticeDerivSymbol
  set θ : ℝ := ∑ i : Fin 4, m i * x i
  have hθ' : (∑ i : Fin 4, m i * shiftAxis x a i) = θ + m a :=
    shiftAxis_dot m x a
  simp only [hθ']
  have htrig := sin_add_sub_sin θ (m a)
  calc
    2 * (v a * Real.sin (θ + m a) - v a * Real.sin θ)
        = 2 * v a * (Real.sin (θ + m a) - Real.sin θ) := by ring
    _ = 2 * v a * (2 * Real.sin (m a / 2) * Real.cos (θ + m a / 2)) := by
      rw [htrig]
    _ = 2 * v a * (2 * Real.sin (m a / 2)) * Real.cos (θ + m a / 2) := by
      ring

/-- Plane-wave edge perturbation of a gauge matrix on an axis edge. -/
theorem planeWaveAxisEdgePert_gaugePart (m v x : Fin 4 → ℝ) (a : Fin 4) :
    planeWaveAxisEdgePert (gaugePart m v) m x a =
      2 * m a * v a * Real.cos (axisMidpointPhase m x a) := by
  unfold planeWaveAxisEdgePert
  rw [edgeLoad_gaugePart_axis]

/-- **THEOREM (exact finite-difference gauge identity).**
Whenever `sin(mₐ/2) ≠ 0`, the matrix-gauge plane-wave edge perturbation
equals `(mₐ / (2 sin(mₐ/2)))` times the discrete Lie loading of the
plane-wave vertex field.  Continuum `∂ ↦ multiply by m` is the small-`mₐ`
limit of this factor and is **not** claimed here. -/
theorem planeWaveAxisEdgePert_gaugePart_eq_discreteLie
    (m v x : Fin 4 → ℝ) (a : Fin 4)
    (hsin : Real.sin (m a / 2) ≠ 0) :
    planeWaveAxisEdgePert (gaugePart m v) m x a =
      (m a / latticeDerivSymbol m a) * discreteLieAxis v m x a := by
  have hden : latticeDerivSymbol m a ≠ 0 := by
    unfold latticeDerivSymbol
    exact mul_ne_zero two_ne_zero hsin
  rw [planeWaveAxisEdgePert_gaugePart, discreteLieAxis_eq]
  -- 2 mₐ vₐ cos = (mₐ / (2 sin(mₐ/2))) * (2 vₐ * (2 sin(mₐ/2)) * cos)
  unfold latticeDerivSymbol
  field_simp [hsin, hden]

/-! ## §5. Decomposition transports to edge loads -/

theorem edgeLoad_decomposition (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : momentumSq m ≠ 0) (d : Fin 4 → ℝ) :
    edgeLoad H d =
      edgeLoad (ttProject m H) d +
        edgeLoad (gaugePart m (gaugeVector m H)) d +
        edgeLoad (residualTrace m H • transverseProjector m) d := by
  have h := (exists_edgeTTDecomposition m H hH hm).1
  -- Rewrite only the left-hand `H`, not the occurrences inside `ttProject m H`.
  conv_lhs => rw [h]
  rw [edgeLoad_add, edgeLoad_add]

theorem planeWaveAxisEdgePert_decomposition (m : Fin 4 → ℝ) (H : Mat4)
    (hH : IsSymmetric H) (hm : momentumSq m ≠ 0) (x : Fin 4 → ℝ)
    (a : Fin 4) :
    planeWaveAxisEdgePert H m x a =
      planeWaveAxisEdgePert (ttProject m H) m x a +
        planeWaveAxisEdgePert (gaugePart m (gaugeVector m H)) m x a +
        planeWaveAxisEdgePert (residualTrace m H • transverseProjector m)
          m x a := by
  unfold planeWaveAxisEdgePert
  rw [edgeLoad_decomposition m H hH hm]
  ring

/-! ## §6. TT matrices are fixed by the projector -/

theorem load_eq_zero_of_isTT (m : Fin 4 → ℝ) (H : Mat4) (h : IsTT m H)
    (i : Fin 4) : load H m i = 0 :=
  h.2.2 i

theorem gaugeVector_eq_zero_of_isTT (m : Fin 4 → ℝ) (H : Mat4)
    (hTT : IsTT m H) (_hm : momentumSq m ≠ 0) :
    gaugeVector m H = fun _ => 0 := by
  funext i
  unfold gaugeVector
  have hw : load H m = fun _ => 0 := by
    funext j; exact load_eq_zero_of_isTT m H hTT j
  have hdot : dot (fun _ : Fin 4 => (0 : ℝ)) m = 0 := by
    unfold dot; simp
  simp [hw, hdot]

theorem gaugePart_zero (m : Fin 4 → ℝ) :
    gaugePart m (fun _ => (0 : ℝ)) = 0 := by
  funext i j
  simp [gaugePart]

theorem gaugeCorrected_eq_of_isTT (m : Fin 4 → ℝ) (H : Mat4)
    (hTT : IsTT m H) (hm : momentumSq m ≠ 0) :
    gaugeCorrected m H = H := by
  unfold gaugeCorrected
  rw [gaugeVector_eq_zero_of_isTT m H hTT hm, gaugePart_zero]
  simp

theorem residualTrace_eq_zero_of_isTT (m : Fin 4 → ℝ) (H : Mat4)
    (hTT : IsTT m H) (hm : momentumSq m ≠ 0) :
    residualTrace m H = 0 := by
  unfold residualTrace
  rw [gaugeCorrected_eq_of_isTT m H hTT hm]
  have := hTT.2.1
  simp [IsTraceless] at this
  simp [this]

theorem ttProject_eq_of_isTT (m : Fin 4 → ℝ) (H : Mat4)
    (hTT : IsTT m H) (hm : momentumSq m ≠ 0) :
    ttProject m H = H := by
  unfold ttProject
  rw [gaugeCorrected_eq_of_isTT m H hTT hm,
    residualTrace_eq_zero_of_isTT m H hTT hm]
  simp

/-! ## §7. Decoy: a non-gauge matrix is not a discrete Lie shift -/

/-- Decoy witness matrix: the algebraic plus TT polarization
`diag(0,0,1,−1)` against `axisWave`. -/
def decoyTT : Mat4 := axisTTPlus

/-- A plane-wave edge perturbation equals some gauge discrete-Lie form on
axis `a` when there exists `v` with matching axis load `2 mₐ vₐ`. -/
def IsGaugeDiscreteLieOnAxis (m : Fin 4 → ℝ) (H : Mat4) (a : Fin 4) :
    Prop :=
  ∃ v : Fin 4 → ℝ, edgeLoad H (axisDisp a) = 2 * m a * v a

theorem decoyTT_edgeLoad_axis2 :
    edgeLoad decoyTT (axisDisp 2) = 1 := by
  simp [decoyTT, edgeLoad_axis, axisTTPlus]

theorem decoyTT_not_gaugeDiscreteLie_axis2 :
    ¬ IsGaugeDiscreteLieOnAxis axisWave decoyTT 2 := by
  rintro ⟨v, hv⟩
  have hm : axisWave 2 = 0 := by simp [axisWave]
  rw [decoyTT_edgeLoad_axis2, hm] at hv
  norm_num at hv

theorem decoyTT_isTT : IsTT axisWave decoyTT :=
  axisTTPlus_isTT

/-! ## §8. Nonvacuity: a concrete nonzero TT edge perturbation -/

def witnessWave : Fin 4 → ℝ := axisWave
def witnessH : Mat4 := axisTTPlus
def witnessBase : Fin 4 → ℝ := fun _ => 0

theorem witness_isTT : IsTT witnessWave witnessH :=
  axisTTPlus_isTT

theorem witness_momentumSq : momentumSq witnessWave ≠ 0 := by
  simp [witnessWave, axisWave_momentumSq]

theorem witness_ttProject_eq : ttProject witnessWave witnessH = witnessH :=
  ttProject_eq_of_isTT witnessWave witnessH witness_isTT witness_momentumSq

theorem witness_edgeLoad_tt_ne_zero :
    edgeLoad (ttProject witnessWave witnessH) (axisDisp 2) ≠ 0 := by
  rw [witness_ttProject_eq, edgeLoad_axis]
  simp [witnessH, axisTTPlus]

theorem witness_tt_edge_ne_zero :
    planeWaveAxisEdgePert (ttProject witnessWave witnessH) witnessWave
        witnessBase 2 ≠ 0 := by
  unfold planeWaveAxisEdgePert
  rw [witness_ttProject_eq, edgeLoad_axis]
  simp [witnessH, witnessWave, witnessBase, axisTTPlus, axisMidpointPhase,
    axisWave, Real.cos_zero]

end

end ReggeEdgeTTAttachment4D
end Analysis
end Gravity
end IndisputableMonolith
