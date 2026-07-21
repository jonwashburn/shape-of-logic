import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeTTAttachment4D

/-!
# Regge edge stencil (4D): Freudenthal 4-cube classes + provisional finite quadratic

QG full-theory campaign, next kernel-checked increment after
`ReggeEdgeTTAttachment4D`: the 4D analogue of the 3D chain's finite TT
edge-class packaging (`polEdgeCoeff` / hinge-diagonal block ingredients in
`ReggeTTSymbolPreflight` and `ReggeTTHingeAwareZeroMode`).

## Tier tags (binding)

* THEOREM: every named result in this file (kernel-checked; no `sorry`,
  no `admit`, no new axioms, no `native_decide`, no `: True` shells).
* OPEN: the class weights of the true 4D Regge Hessian at flat.  The
  provisional aggregate below uses weight `1` on every nonzero 0/1
  displacement class.  Deriving the correct 4D Regge weights (the 4D
  lift of the 3D hinge factor `-1/(4 ℓ² √ℓ²)` contracted with deficit
  incidence) is **not** done here and must not be reverse-engineered
  from the Einstein-Hilbert answer.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** prove the ledger name `edge_tt_decomposition` in full.
* This does **not** flip `gap_action_recovery`.

## What is proved (honest scope)

1. **15 Freudenthal-style edge classes.** Nonzero displacement vectors in
   `{0,1}⁴`, indexed by `Fin 15` via bit masks `d.val + 1`.
2. **Plane-wave midpoint loading.** Per class, squared-length coefficient
   `classCoeff H d = Dᵀ H D` (same convention as 3D `polEdgeCoeff` /
   4D `edgeLoad`) times `cos(m·x + m·D/2)`.
3. **Provisional finite quadratic aggregate.**
   `finiteTTQuadratic H = Σ_d (classCoeff H d)²` with all-ones weights
   (OPEN for true Regge weights).  Exact polarization identity in `H`.
4. **Gauge entry (exact, non-fake).** Pure gauge loads by
   `classCoeff (gaugePart m v) d = 2 (m·D)(v·D)`, so the provisional
   aggregate on pure gauge is `Σ_d 4 (m·D)² (v·D)²`, which is **not**
   identically zero.  Exact gauge invariance of this provisional
   aggregate therefore fails; the identity that holds is recorded, and
   an explicit TT + gauge counterexample is given.
5. **Nonvacuity + decoys.** The aggregate is `8` on `axisTTPlus`;
   pure-gauge and pure-trace inputs evaluate to the distinct predicted
   values `32` and `80`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeEdgeStencil4D

open Matrix BigOperators
open EdgeTTDecomposition4D
open ReggeEdgeTTAttachment4D

noncomputable section

/-! ## §1. Fifteen nonzero 0/1 displacement classes of the 4-cube -/

/-- Bit-mask of class `d`: the integer `d.val + 1 ∈ {1,…,15}`. -/
def maskOf (d : Fin 15) : ℕ := d.val + 1

/-- Whether coordinate `i` is set in the 0/1 displacement of class `d`. -/
def classBit (d : Fin 15) (i : Fin 4) : Bool :=
  Nat.testBit (maskOf d) i.val

/-- Displacement vector of class `d` (entries in `{0,1}`). -/
def classDisp (d : Fin 15) : Fin 4 → ℝ :=
  fun i => if classBit d i then (1 : ℝ) else 0

/-- Flat squared length of class `d` (Hamming weight of the mask). -/
def classDispSq (d : Fin 15) : ℝ :=
  ∑ i : Fin 4, classDisp d i * classDisp d i

/-- Nat Hamming weight of the class mask (bits 0..3). -/
def classWeightNat (d : Fin 15) : ℕ :=
  (if classBit d 0 then 1 else 0) +
    (if classBit d 1 then 1 else 0) +
    (if classBit d 2 then 1 else 0) +
    (if classBit d 3 then 1 else 0)

theorem classWeightNat_pos (d : Fin 15) : 0 < classWeightNat d := by
  fin_cases d <;> decide

theorem classDisp_ne_zero (d : Fin 15) : classDisp d ≠ 0 := by
  intro h
  have hw := classWeightNat_pos d
  have hbits :
      classWeightNat d =
        (if classBit d 0 then 1 else 0) +
          (if classBit d 1 then 1 else 0) +
          (if classBit d 2 then 1 else 0) +
          (if classBit d 3 then 1 else 0) := rfl
  have hz : ∀ i : Fin 4, classDisp d i = 0 := by
    intro i; simp [h]
  have hb0 : classBit d 0 = false := by
    have := hz 0; simp [classDisp] at this; exact this
  have hb1 : classBit d 1 = false := by
    have := hz 1; simp [classDisp] at this; exact this
  have hb2 : classBit d 2 = false := by
    have := hz 2; simp [classDisp] at this; exact this
  have hb3 : classBit d 3 = false := by
    have := hz 3; simp [classDisp] at this; exact this
  simp [hbits, hb0, hb1, hb2, hb3] at hw

theorem classDispSq_eq_weight (d : Fin 15) :
    classDispSq d = (classWeightNat d : ℝ) := by
  unfold classDispSq classDisp classWeightNat
  simp [Fin.sum_univ_four]
  cases classBit d 0 <;> cases classBit d 1 <;>
    cases classBit d 2 <;> cases classBit d 3 <;> norm_num

/-! ## §2. Class coefficients and midpoint plane-wave perturbations -/

/-- Edge-class coefficient: `c_d(H) = Dᵀ H D` (3D `polEdgeCoeff` convention). -/
def classCoeff (H : Mat4) (d : Fin 15) : ℝ :=
  edgeLoad H (classDisp d)

/-- Midpoint Bloch phase of class `d` based at covering coordinate `x`:
`m · (x + D/2)`. -/
def classMidpointPhase (m x : Fin 4 → ℝ) (d : Fin 15) : ℝ :=
  (∑ i : Fin 4, m i * x i) + (∑ i : Fin 4, m i * classDisp d i) / 2

/-- Plane-wave squared-length perturbation of class `d`:
`c_d(H) · cos(m·x + m·D/2)`. -/
def planeWaveClassPert (H : Mat4) (m x : Fin 4 → ℝ) (d : Fin 15) : ℝ :=
  classCoeff H d * Real.cos (classMidpointPhase m x d)

theorem classCoeff_add (A B : Mat4) (d : Fin 15) :
    classCoeff (A + B) d = classCoeff A d + classCoeff B d := by
  unfold classCoeff; exact edgeLoad_add A B _

theorem classCoeff_smul (c : ℝ) (H : Mat4) (d : Fin 15) :
    classCoeff (c • H) d = c * classCoeff H d := by
  unfold classCoeff; exact edgeLoad_smul c H _

theorem classCoeff_neg (H : Mat4) (d : Fin 15) :
    classCoeff (-H) d = -classCoeff H d := by
  unfold classCoeff; exact edgeLoad_neg H _

theorem classCoeff_sub (A B : Mat4) (d : Fin 15) :
    classCoeff (A - B) d = classCoeff A d - classCoeff B d := by
  unfold classCoeff; exact edgeLoad_sub A B _

theorem planeWaveClassPert_add (A B : Mat4) (m x : Fin 4 → ℝ) (d : Fin 15) :
    planeWaveClassPert (A + B) m x d =
      planeWaveClassPert A m x d + planeWaveClassPert B m x d := by
  unfold planeWaveClassPert
  rw [classCoeff_add, add_mul]

theorem planeWaveClassPert_smul (c : ℝ) (H : Mat4) (m x : Fin 4 → ℝ)
    (d : Fin 15) :
    planeWaveClassPert (c • H) m x d = c * planeWaveClassPert H m x d := by
  unfold planeWaveClassPert
  rw [classCoeff_smul, mul_assoc]

/-! ## §3. Provisional finite quadratic aggregate (weight 1; OPEN) -/

/-- Symmetric bilinear polarization of the provisional aggregate. -/
def finiteTTBilinear (A B : Mat4) : ℝ :=
  ∑ d : Fin 15, classCoeff A d * classCoeff B d

/-- Provisional finite TT quadratic form on edge classes:
`Q(H) = Σ_d w_d c_d(H)²` with provisional weights `w_d = 1` for every
nonzero 0/1 class.  **OPEN:** replace `w_d` by the true 4D Regge
flat-Hessian class weights when derived; do not fit them to EH. -/
def finiteTTQuadratic (H : Mat4) : ℝ :=
  ∑ d : Fin 15, classCoeff H d ^ 2

theorem finiteTTQuadratic_eq_bilinear (H : Mat4) :
    finiteTTQuadratic H = finiteTTBilinear H H := by
  unfold finiteTTQuadratic finiteTTBilinear
  refine Finset.sum_congr rfl fun d _ => by ring

theorem finiteTTBilinear_symm (A B : Mat4) :
    finiteTTBilinear A B = finiteTTBilinear B A := by
  unfold finiteTTBilinear
  refine Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem finiteTTBilinear_add_left (A₁ A₂ B : Mat4) :
    finiteTTBilinear (A₁ + A₂) B =
      finiteTTBilinear A₁ B + finiteTTBilinear A₂ B := by
  unfold finiteTTBilinear
  simp_rw [classCoeff_add, add_mul, Finset.sum_add_distrib]

theorem finiteTTBilinear_smul_left (c : ℝ) (A B : Mat4) :
    finiteTTBilinear (c • A) B = c * finiteTTBilinear A B := by
  unfold finiteTTBilinear
  simp_rw [classCoeff_smul, mul_assoc, ← Finset.mul_sum]

/-- Exact quadratic expansion / polarization identity. -/
theorem finiteTTQuadratic_add (A B : Mat4) :
    finiteTTQuadratic (A + B) =
      finiteTTQuadratic A + finiteTTQuadratic B + 2 * finiteTTBilinear A B := by
  unfold finiteTTQuadratic finiteTTBilinear
  have h :
      ∀ d : Fin 15,
        classCoeff (A + B) d ^ 2 =
          classCoeff A d ^ 2 + classCoeff B d ^ 2 +
            2 * (classCoeff A d * classCoeff B d) := by
    intro d
    rw [classCoeff_add]
    ring
  simp_rw [h, Finset.sum_add_distrib, Finset.mul_sum]

theorem finiteTTQuadratic_smul (c : ℝ) (H : Mat4) :
    finiteTTQuadratic (c • H) = c ^ 2 * finiteTTQuadratic H := by
  unfold finiteTTQuadratic
  simp_rw [classCoeff_smul]
  -- (c * a)^2 = c^2 * a^2
  have h : ∀ d : Fin 15, (c * classCoeff H d) ^ 2 = c ^ 2 * classCoeff H d ^ 2 := by
    intro d; ring
  simp_rw [h, ← Finset.mul_sum]

theorem finiteTTQuadratic_neg (H : Mat4) :
    finiteTTQuadratic (-H) = finiteTTQuadratic H := by
  have h := finiteTTQuadratic_smul (-1) H
  simpa [neg_one_smul] using h

/-! ## §4. Gauge entry at the exact finite-difference level -/

theorem classCoeff_gaugePart (m v : Fin 4 → ℝ) (d : Fin 15) :
    classCoeff (gaugePart m v) d =
      2 * (∑ i : Fin 4, m i * classDisp d i) *
        (∑ j : Fin 4, v j * classDisp d j) := by
  unfold classCoeff
  exact edgeLoad_gaugePart m v _

/-- Exact pure-gauge evaluation of the provisional aggregate.
This is **not** identically zero, so the provisional weight-1 aggregate
is **not** gauge-invariant. -/
theorem finiteTTQuadratic_gaugePart (m v : Fin 4 → ℝ) :
    finiteTTQuadratic (gaugePart m v) =
      ∑ d : Fin 15,
        4 * (∑ i : Fin 4, m i * classDisp d i) ^ 2 *
          (∑ j : Fin 4, v j * classDisp d j) ^ 2 := by
  unfold finiteTTQuadratic
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [classCoeff_gaugePart]
  ring

/-- Explicit pure-gauge witness vector along axis 0. -/
def axisGaugeVector : Fin 4 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0

theorem classCoeff_gaugePart_axis (d : Fin 15) :
    classCoeff (gaugePart axisWave axisGaugeVector) d =
      2 * (if classBit d 0 then (1 : ℝ) else 0) := by
  rw [classCoeff_gaugePart]
  have hm :
      (∑ i : Fin 4, axisWave i * classDisp d i) =
        if classBit d 0 then (1 : ℝ) else 0 := by
    simp [axisWave, classDisp, Fin.sum_univ_four]
  have hv :
      (∑ j : Fin 4, axisGaugeVector j * classDisp d j) =
        if classBit d 0 then (1 : ℝ) else 0 := by
    simp [axisGaugeVector, classDisp, Fin.sum_univ_four]
  rw [hm, hv]
  cases classBit d 0 <;> norm_num

/-- Nat indicator: class has bit 0 set. -/
def hasBit0 (d : Fin 15) : ℕ := if classBit d 0 then 1 else 0

theorem sum_hasBit0 : (∑ d : Fin 15, hasBit0 d) = 8 := by
  unfold hasBit0 classBit maskOf
  decide

theorem finiteTTQuadratic_gaugePart_axisWave :
    finiteTTQuadratic (gaugePart axisWave axisGaugeVector) = 32 := by
  unfold finiteTTQuadratic
  have hterm :
      ∀ d : Fin 15,
        classCoeff (gaugePart axisWave axisGaugeVector) d ^ 2 =
          (4 : ℝ) * (hasBit0 d : ℝ) := by
    intro d
    rw [classCoeff_gaugePart_axis]
    unfold hasBit0
    cases classBit d 0 <;> norm_num
  simp_rw [hterm, ← Finset.mul_sum, ← Nat.cast_sum, sum_hasBit0]
  norm_num

theorem finiteTTQuadratic_gaugePart_axisWave_ne_zero :
    finiteTTQuadratic (gaugePart axisWave axisGaugeVector) ≠ 0 := by
  rw [finiteTTQuadratic_gaugePart_axisWave]
  norm_num

/-! ## §5. Axis-TTPlus coefficients and nonvacuity -/

theorem classCoeff_axisTTPlus (d : Fin 15) :
    classCoeff axisTTPlus d =
      (if classBit d 2 then (1 : ℝ) else 0) -
        if classBit d 3 then (1 : ℝ) else 0 := by
  unfold classCoeff edgeLoad axisTTPlus classDisp
  simp [Fin.sum_univ_four]
  split_ifs <;> ring

/-- Cross polarization class coefficient: `Dᵀ H_× D = 2 D₂ D₃`. -/
theorem classCoeff_axisTTCross (d : Fin 15) :
    classCoeff axisTTCross d =
      2 * (if classBit d 2 then (1 : ℝ) else 0) *
        (if classBit d 3 then (1 : ℝ) else 0) := by
  unfold classCoeff edgeLoad axisTTCross classDisp
  simp [Fin.sum_univ_four]
  split_ifs <;> ring

/-- Nat square of the plus-class coefficient (0 or 1). -/
def axisTTPlusSqNat (d : Fin 15) : ℕ :=
  if classBit d 2 ≠ classBit d 3 then 1 else 0

theorem classCoeff_axisTTPlus_sq (d : Fin 15) :
    classCoeff axisTTPlus d ^ 2 = (axisTTPlusSqNat d : ℝ) := by
  rw [classCoeff_axisTTPlus]
  unfold axisTTPlusSqNat
  cases classBit d 2 <;> cases classBit d 3 <;> norm_num

theorem sum_axisTTPlusSqNat : (∑ d : Fin 15, axisTTPlusSqNat d) = 8 := by
  unfold axisTTPlusSqNat classBit maskOf
  decide

theorem finiteTTQuadratic_axisTTPlus : finiteTTQuadratic axisTTPlus = 8 := by
  unfold finiteTTQuadratic
  simp_rw [classCoeff_axisTTPlus_sq, ← Nat.cast_sum, sum_axisTTPlusSqNat]
  norm_num

theorem finiteTTQuadratic_axisTTPlus_ne_zero :
    finiteTTQuadratic axisTTPlus ≠ 0 := by
  rw [finiteTTQuadratic_axisTTPlus]
  norm_num

theorem finiteTTQuadratic_axisTTPlus_isTT_seed :
    IsTT axisWave axisTTPlus ∧ finiteTTQuadratic axisTTPlus ≠ 0 :=
  ⟨axisTTPlus_isTT, finiteTTQuadratic_axisTTPlus_ne_zero⟩

/-! ## §6. Gauge non-invariance on a TT seed -/

/-- Cross-term Nat contribution `c₊(d) · (c_g(d)/2)` equals 0 in the sum
(the signed products cancel). -/
def crossNat (d : Fin 15) : ℤ :=
  let cPlus : ℤ :=
    (if classBit d 2 then (1 : ℤ) else 0) - if classBit d 3 then 1 else 0
  let cG : ℤ := if classBit d 0 then 1 else 0
  cPlus * cG

theorem sum_crossNat : (∑ d : Fin 15, crossNat d) = 0 := by
  unfold crossNat classBit maskOf
  decide

theorem finiteTTBilinear_axisTTPlus_gauge :
    finiteTTBilinear axisTTPlus (gaugePart axisWave axisGaugeVector) = 0 := by
  unfold finiteTTBilinear
  have hterm :
      ∀ d : Fin 15,
        classCoeff axisTTPlus d *
            classCoeff (gaugePart axisWave axisGaugeVector) d =
          (2 : ℝ) * (crossNat d : ℝ) := by
    intro d
    rw [classCoeff_axisTTPlus, classCoeff_gaugePart_axis]
    unfold crossNat
    cases classBit d 0 <;> cases classBit d 2 <;>
      cases classBit d 3 <;> norm_num
  simp_rw [hterm, ← Finset.mul_sum, ← Int.cast_sum, sum_crossNat]
  norm_num

/-- THEOREM: provisional aggregate fails exact gauge invariance on a TT seed.
`axisTTPlus` is TT for `axisWave`, yet adding the pure axis gauge changes `Q`. -/
theorem finiteTTQuadratic_not_gauge_invariant_on_axisTTPlus :
    finiteTTQuadratic (axisTTPlus + gaugePart axisWave axisGaugeVector) ≠
      finiteTTQuadratic axisTTPlus := by
  rw [finiteTTQuadratic_add, finiteTTBilinear_axisTTPlus_gauge,
    finiteTTQuadratic_gaugePart_axisWave]
  rw [finiteTTQuadratic_axisTTPlus]
  norm_num

/-! ## §7. Decoys: pure gauge and pure trace -/

/-- Pure-gauge decoy. -/
def decoyGauge : Mat4 := gaugePart axisWave axisGaugeVector

theorem finiteTTQuadratic_decoyGauge : finiteTTQuadratic decoyGauge = 32 := by
  unfold decoyGauge
  exact finiteTTQuadratic_gaugePart_axisWave

/-- Pure-trace decoy: the Euclidean identity (not TT). -/
def decoyTrace : Mat4 := 1

theorem classCoeff_decoyTrace (d : Fin 15) :
    classCoeff decoyTrace d = classDispSq d := by
  unfold classCoeff decoyTrace classDispSq edgeLoad
  -- Dᵀ I D = |D|²
  simp [one_apply, Fin.sum_univ_four, classDisp]

theorem classCoeff_decoyTrace_sq (d : Fin 15) :
    classCoeff decoyTrace d ^ 2 = (classWeightNat d : ℝ) ^ 2 := by
  rw [classCoeff_decoyTrace, classDispSq_eq_weight]

theorem sum_weightSqNat : (∑ d : Fin 15, classWeightNat d ^ 2) = 80 := by
  unfold classWeightNat classBit maskOf
  decide

theorem finiteTTQuadratic_decoyTrace : finiteTTQuadratic decoyTrace = 80 := by
  unfold finiteTTQuadratic
  simp_rw [classCoeff_decoyTrace_sq]
  -- Σ (n : ℝ)^2 = Σ (n^2 : ℝ)
  have h : ∀ d : Fin 15, ((classWeightNat d : ℝ) ^ 2) = ((classWeightNat d ^ 2 : ℕ) : ℝ) := by
    intro d; norm_cast
  simp_rw [h, ← Nat.cast_sum, sum_weightSqNat]
  norm_num

theorem decoy_values_distinct :
    finiteTTQuadratic decoyGauge ≠ finiteTTQuadratic decoyTrace ∧
      finiteTTQuadratic decoyGauge ≠ finiteTTQuadratic axisTTPlus ∧
      finiteTTQuadratic decoyTrace ≠ finiteTTQuadratic axisTTPlus := by
  rw [finiteTTQuadratic_decoyGauge, finiteTTQuadratic_decoyTrace,
    finiteTTQuadratic_axisTTPlus]
  norm_num

/-! ## §8. Axis class recovers the attachment layer -/

theorem classDisp_axis0 : classDisp (0 : Fin 15) = axisDisp 0 := by
  funext i
  fin_cases i <;> simp [classDisp, classBit, maskOf, axisDisp, Nat.testBit]

theorem classCoeff_axis0 (H : Mat4) :
    classCoeff H (0 : Fin 15) = edgeLoad H (axisDisp 0) := by
  unfold classCoeff
  rw [classDisp_axis0]

theorem planeWaveClassPert_axis0 (H : Mat4) (m x : Fin 4 → ℝ) :
    planeWaveClassPert H m x (0 : Fin 15) =
      planeWaveAxisEdgePert H m x 0 := by
  unfold planeWaveClassPert planeWaveAxisEdgePert classCoeff classMidpointPhase
    axisMidpointPhase
  rw [classDisp_axis0]
  have hdot : (∑ i : Fin 4, m i * axisDisp 0 i) = m 0 := by
    unfold axisDisp; simp [Finset.sum_ite_eq']
  rw [hdot]

end

end ReggeEdgeStencil4D
end Analysis
end Gravity
end IndisputableMonolith
