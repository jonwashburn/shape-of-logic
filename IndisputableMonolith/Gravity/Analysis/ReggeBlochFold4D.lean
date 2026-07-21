import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DStarKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D finite-momentum Bloch fold ((1,1) orbit)

QG full-theory campaign: exact phase-decorated fold of the committed
true-weight flat Hessian for type-`(1,1)` triangle hinges in one Kuhn
cell, using the midpoint plane-wave convention of `ReggeEdgeStencil4D`.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: **(1,1) orbit only** (72 oriented slots per cell).
* This does **not** evaluate the `m²` Taylor coefficient against the
  Einstein–Hilbert / TT continuum symbol (next lane).
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.

## What is proved

1. **Factorized phased fold** at `m = 0` equals committed
   `orbitZeroMomQuadratic .t11` (consistency gate
   `factorizedBlochFold11_zeroMomentum`).
2. **Transported phased fold** `blochFold11` over all 72 slots with
   bilinearity and zero-momentum phase drop.
3. **Structural vanishing:** difference masks `(1,2)` and `(2,1)` give
   identically zero `axisTTPlus` contributions for every wave vector
   (area supports miss axis-TT class loads).
4. **Certificate algebra** at `m⋆ = (π/2, π/2, π/2, 0)`: the Nat-kind
   axis table sums to `-3` and the gauge table to `-4 + 4√2`.
5. **Integer Bloch symbol** at `m⋆`: every midpoint phase is a natural
   multiple of `π/4` (`classMidpointPhase_waveStar`), so each slot term
   equals `(N₁ + N₂·√2)/8` with decidable integers
   (`transportedSlotTerm_waveStar_eval`).
6. **Geometric ↔ certificate match, CLOSED:** on all 240 oriented slots
   the integer certificates match the Nat-kind tables (`slotN_axis_match`,
   `slotN_gauge_match` by `decide`), hence
   `transportedSlotTerm_axis_waveStar` / `transportedSlotTerm_gauge_waveStar`.
7. **Closing values:** `blochFold11 axisTTPlus waveStar = -3` (nonzero:
   nonvacuity) and `blochFold11 decoyGauge waveStar = -4 + 4√2` (nonzero:
   discrete gauge invariance at finite momentum holds only up to the
   finite-difference identity).

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochFold4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeHinge4DOrbitClassification
open ReggeHinge4DFlatKernel
open ReggeFlat4DHessianAssembly
open EdgeTTDecomposition4D

noncomputable section

/-! ## §1. Phased class dots -/

def maskCoord (mask : ℕ) : Fin 4 → ℝ :=
  fun i => if Nat.testBit mask i.val then (1 : ℝ) else 0

def hingeBase (s : Fin 24) (t : Fin 10) : Fin 4 → ℝ :=
  maskCoord (triangleVertexMasks s t).1

def phasedClassDot (v : Fin 15 → ℝ) (H : Mat4) (m x : Fin 4 → ℝ) : ℝ :=
  ∑ d : Fin 15, v d * planeWaveClassPert H m x d

theorem phasedClassDot_add (v : Fin 15 → ℝ) (A B : Mat4)
    (m x : Fin 4 → ℝ) :
    phasedClassDot v (A + B) m x =
      phasedClassDot v A m x + phasedClassDot v B m x := by
  unfold phasedClassDot
  simp_rw [planeWaveClassPert_add, mul_add, Finset.sum_add_distrib]

theorem phasedClassDot_smul (v : Fin 15 → ℝ) (c : ℝ) (A : Mat4)
    (m x : Fin 4 → ℝ) :
    phasedClassDot v (c • A) m x = c * phasedClassDot v A m x := by
  unfold phasedClassDot
  simp_rw [planeWaveClassPert_smul]
  refine Eq.trans ?_ (Finset.mul_sum _ _ c).symm
  exact Finset.sum_congr rfl fun d _ => by ring

theorem phasedClassDot_zeroMomentum (v : Fin 15 → ℝ) (H : Mat4)
    (x : Fin 4 → ℝ) :
    phasedClassDot v H (fun _ => (0 : ℝ)) x = classDot v H := by
  unfold phasedClassDot classDot coeffDot planeWaveClassPert classMidpointPhase
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [Real.cos_zero]

/-! ## §2. Factorized fold and consistency gate -/

def isT11 (s : Fin 24) (t : Fin 10) : Prop :=
  hingeOrbitType s t = .t11

instance (s : Fin 24) (t : Fin 10) : Decidable (isT11 s t) :=
  inferInstanceAs (Decidable (hingeOrbitType s t = .t11))

theorem isT11_iff_pop (s : Fin 24) (t : Fin 10) :
    isT11 s t ↔ hingeTypePop s t = (1, 1) := by
  constructor
  · intro h
    have hpop := hingeOrbitType_toPop s t
    simp only [isT11] at h
    rw [h, HingeOrbitType.toPop] at hpop
    exact hpop.symm
  · intro h
    simp [isT11, hingeOrbitType, h, popToOrbitType, Option.getD]

def factorizedSlotTerm (H : Mat4) (m : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isT11 s t then
    phasedClassDot areaCov11 H m (hingeBase s t) *
      phasedClassDot ReggeHinge4DStarKernel.fullStarClassKernel H m
        (hingeBase s t)
  else 0

def factorizedBlochFold11 (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, factorizedSlotTerm H m s t

private lemma t11_count_nat :
    (∑ s : Fin 24, ∑ t : Fin 10, (if isT11 s t then (1 : ℕ) else 0)) =
      72 := by
  have h : (∑ s : Fin 24, ∑ t : Fin 10,
      (if hingeTypePop s t = (1, 1) then (1 : ℕ) else 0)) = 72 := by
    simpa [cellTriangleCount, triangleTypeNat] using cellTriangleCount_t11
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h' : isT11 s t
  · have hp : hingeTypePop s t = (1, 1) := (isT11_iff_pop s t).mp h'
    simp [h', hp]
  · have : hingeTypePop s t ≠ (1, 1) := fun happ =>
      h' ((isT11_iff_pop s t).mpr happ)
    simp [h', this]

private lemma t11_count_real :
    (∑ s : Fin 24, ∑ t : Fin 10, (if isT11 s t then (1 : ℝ) else 0)) =
      (72 : ℝ) := by
  have := congrArg (fun n : ℕ => (n : ℝ)) t11_count_nat
  refine Eq.trans ?_ this
  simp_rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isT11 s t <;> simp [h]

/-- Consistency gate: factorized fold at zero momentum recovers the
committed `(1,1)` orbit quadratic. -/
theorem factorizedBlochFold11_zeroMomentum (H : Mat4) :
    factorizedBlochFold11 H (fun _ => (0 : ℝ)) =
      orbitZeroMomQuadratic .t11 H := by
  unfold factorizedBlochFold11 orbitZeroMomQuadratic orbitCellCount
    orbitAreaCov orbitDeficitKernel
  have hterm : ∀ s t,
      factorizedSlotTerm H (fun _ => (0 : ℝ)) s t =
        (if isT11 s t then (1 : ℝ) else 0) *
          (classDot areaCov11 H *
            classDot ReggeHinge4DStarKernel.fullStarClassKernel H) := by
    intro s t
    unfold factorizedSlotTerm
    by_cases h : isT11 s t <;> simp [h, phasedClassDot_zeroMomentum]
  simp_rw [hterm]
  -- Pull the constant product out of the double sum.
  rw [show
      (∑ s : Fin 24, ∑ t : Fin 10,
          (if isT11 s t then (1 : ℝ) else 0) *
            (classDot areaCov11 H *
              classDot ReggeHinge4DStarKernel.fullStarClassKernel H)) =
        (∑ s : Fin 24, ∑ t : Fin 10, (if isT11 s t then (1 : ℝ) else 0)) *
          (classDot areaCov11 H *
            classDot ReggeHinge4DStarKernel.fullStarClassKernel H) by
    simp_rw [Finset.sum_mul]]
  rw [t11_count_real]
  ring

/-! ## §3. Transported fold -/

def transportPermOfDiff (a b : ℕ) : Fin 24 :=
  match a, b with
  | 1, 2 => 0
  | 1, 4 => 2
  | 1, 8 => 4
  | 2, 1 => 6
  | 2, 4 => 8
  | 2, 8 => 10
  | 4, 1 => 12
  | 4, 2 => 14
  | 4, 8 => 16
  | 8, 1 => 18
  | 8, 2 => 20
  | 8, 4 => 22
  | _, _ => 0

def permClass (p : Fin 24) (d : Fin 15) : Fin 15 :=
  ⟨permMask (coordPermOf p) (maskOf d) - 1, by
    have : 0 < permMask (coordPermOf p) (maskOf d) ∧
        permMask (coordPermOf p) (maskOf d) ≤ 15 := by
      fin_cases p <;> fin_cases d <;> decide
    omega⟩

def transportedDeficit (p : Fin 24) : Fin 15 → ℝ :=
  fun d =>
    ∑ d0 : Fin 15,
      if permClass p d0 = d then
        ReggeHinge4DStarKernel.fullStarClassKernel d0 else 0

def slotTransportPerm (s : Fin 24) (t : Fin 10) : Fin 24 :=
  transportPermOfDiff (diffMaskA s t) (diffMaskB s t)

def slotAreaCov (s : Fin 24) (t : Fin 10) : Fin 15 → ℝ :=
  fun d =>
    if maskOf d = diffMaskA s t then (1 / 4 : ℝ)
    else if maskOf d = diffMaskB s t then (1 / 4 : ℝ)
    else 0

def slotDeficitKer (s : Fin 24) (t : Fin 10) : Fin 15 → ℝ :=
  transportedDeficit (slotTransportPerm s t)

def transportedSlotTerm (H : Mat4) (m : Fin 4 → ℝ)
    (s : Fin 24) (t : Fin 10) : ℝ :=
  if isT11 s t then
    phasedClassDot (slotAreaCov s t) H m (hingeBase s t) *
      phasedClassDot (slotDeficitKer s t) H m (hingeBase s t)
  else 0

/-- Honest transported finite-momentum `(1,1)` Bloch fold (72 instances). -/
def blochFold11 (H : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, transportedSlotTerm H m s t

def blochFold11Bilinear (A B : Mat4) (m : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (∑ s : Fin 24, ∑ t : Fin 10,
      if isT11 s t then
        phasedClassDot (slotAreaCov s t) A m (hingeBase s t) *
            phasedClassDot (slotDeficitKer s t) B m (hingeBase s t) +
          phasedClassDot (slotAreaCov s t) B m (hingeBase s t) *
            phasedClassDot (slotDeficitKer s t) A m (hingeBase s t)
      else (0 : ℝ))

theorem blochFold11_eq_bilinear (H : Mat4) (m : Fin 4 → ℝ) :
    blochFold11 H m = blochFold11Bilinear H H m := by
  unfold blochFold11 blochFold11Bilinear transportedSlotTerm
  have h : ∀ s t,
      (if isT11 s t then
        phasedClassDot (slotAreaCov s t) H m (hingeBase s t) *
          phasedClassDot (slotDeficitKer s t) H m (hingeBase s t)
       else (0 : ℝ)) =
        (1 / 2 : ℝ) *
          (if isT11 s t then
            phasedClassDot (slotAreaCov s t) H m (hingeBase s t) *
                phasedClassDot (slotDeficitKer s t) H m (hingeBase s t) +
              phasedClassDot (slotAreaCov s t) H m (hingeBase s t) *
                phasedClassDot (slotDeficitKer s t) H m (hingeBase s t)
           else 0) := by
    intro s t
    by_cases ht : isT11 s t
    · simp only [ht, ite_true]; ring
    · simp only [ht, ite_false]; ring
  simp_rw [h]
  -- ∑∑ (1/2) * f = (1/2) * ∑∑ f
  simp_rw [← Finset.mul_sum]

theorem blochFold11Bilinear_symm (A B : Mat4) (m : Fin 4 → ℝ) :
    blochFold11Bilinear A B m = blochFold11Bilinear B A m := by
  unfold blochFold11Bilinear
  refine congr_arg (fun z : ℝ => (1 / 2 : ℝ) * z) ?_
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isT11 s t
  · simp only [h, ite_true]; ring
  · simp only [h, ite_false]

theorem blochFold11Bilinear_add_left (A₁ A₂ B : Mat4) (m : Fin 4 → ℝ) :
    blochFold11Bilinear (A₁ + A₂) B m =
      blochFold11Bilinear A₁ B m + blochFold11Bilinear A₂ B m := by
  unfold blochFold11Bilinear
  simp_rw [phasedClassDot_add]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : isT11 s t
  · simp [h]; ring
  · simp [h]

theorem blochFold11Bilinear_smul_left (c : ℝ) (A B : Mat4)
    (m : Fin 4 → ℝ) :
    blochFold11Bilinear (c • A) B m = c * blochFold11Bilinear A B m := by
  unfold blochFold11Bilinear
  simp_rw [phasedClassDot_smul]
  have h : ∀ s t,
      (if isT11 s t then
        c * phasedClassDot (slotAreaCov s t) A m (hingeBase s t) *
            phasedClassDot (slotDeficitKer s t) B m (hingeBase s t) +
          phasedClassDot (slotAreaCov s t) B m (hingeBase s t) *
            (c * phasedClassDot (slotDeficitKer s t) A m (hingeBase s t))
      else (0 : ℝ)) =
        c *
          (if isT11 s t then
            phasedClassDot (slotAreaCov s t) A m (hingeBase s t) *
                phasedClassDot (slotDeficitKer s t) B m (hingeBase s t) +
              phasedClassDot (slotAreaCov s t) B m (hingeBase s t) *
                phasedClassDot (slotDeficitKer s t) A m (hingeBase s t)
          else 0) := by
    intro s t
    by_cases h : isT11 s t
    · simp [h]; ring
    · simp [h]
  simp_rw [h, ← Finset.mul_sum]
  ring

theorem transportedSlotTerm_zeroMomentum (H : Mat4)
    (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm H (fun _ => (0 : ℝ)) s t =
      if isT11 s t then
        classDot (slotAreaCov s t) H * classDot (slotDeficitKer s t) H
      else 0 := by
  unfold transportedSlotTerm
  by_cases h : isT11 s t <;> simp [h, phasedClassDot_zeroMomentum]

/-! ## §4. Structural vanishing on seed-mask orientations -/

theorem classCoeff_axisTTPlus_mask_1 :
    classCoeff axisTTPlus (0 : Fin 15) = 0 := by
  have h2 : Nat.testBit 1 2 = false := by decide
  have h3 : Nat.testBit 1 3 = false := by decide
  simp [classCoeff_axisTTPlus, classBit, maskOf, h2, h3]

theorem classCoeff_axisTTPlus_mask_2 :
    classCoeff axisTTPlus (1 : Fin 15) = 0 := by
  have h2 : Nat.testBit 2 2 = false := by decide
  have h3 : Nat.testBit 2 3 = false := by decide
  simp [classCoeff_axisTTPlus, classBit, maskOf, h2, h3]

theorem classCoeff_axisTTPlus_mask_3 :
    classCoeff axisTTPlus (2 : Fin 15) = 0 := by
  have h2 : Nat.testBit 3 2 = false := by decide
  have h3 : Nat.testBit 3 3 = false := by decide
  simp [classCoeff_axisTTPlus, classBit, maskOf, h2, h3]

theorem slotAreaCov_support (s : Fin 24) (t : Fin 10) (d : Fin 15)
    (h : slotAreaCov s t d ≠ 0) :
    maskOf d = diffMaskA s t ∨ maskOf d = diffMaskB s t := by
  unfold slotAreaCov at h
  split_ifs at h with hA hB
  · exact Or.inl hA
  · exact Or.inr hB
  · exact (h rfl).elim

theorem phasedClassDot_area_axis_of_masks_1_2
    (s : Fin 24) (t : Fin 10) (m x : Fin 4 → ℝ)
    (ha : diffMaskA s t = 1) (hb : diffMaskB s t = 2) :
    phasedClassDot (slotAreaCov s t) axisTTPlus m x = 0 := by
  unfold phasedClassDot planeWaveClassPert
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hv : slotAreaCov s t d = 0
  · simp [hv]
  · have hmask := slotAreaCov_support s t d hv
    have hc : classCoeff axisTTPlus d = 0 := by
      rcases hmask with h | h
      · have h1 : maskOf d = 1 := by simpa [ha] using h
        have : d.val = 0 := by
          have := congrArg (· - 1) h1
          simpa [maskOf] using this
        have hd : d = ⟨0, by decide⟩ := Fin.ext this
        simpa [hd] using classCoeff_axisTTPlus_mask_1
      · have h2 : maskOf d = 2 := by simpa [hb] using h
        have : d.val = 1 := by
          have := congrArg (· - 1) h2
          simpa [maskOf] using this
        have hd : d = ⟨1, by decide⟩ := Fin.ext this
        simpa [hd] using classCoeff_axisTTPlus_mask_2
    simp [hc]

theorem phasedClassDot_area_axis_of_masks_2_1
    (s : Fin 24) (t : Fin 10) (m x : Fin 4 → ℝ)
    (ha : diffMaskA s t = 2) (hb : diffMaskB s t = 1) :
    phasedClassDot (slotAreaCov s t) axisTTPlus m x = 0 := by
  unfold phasedClassDot planeWaveClassPert
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hv : slotAreaCov s t d = 0
  · simp [hv]
  · have hmask := slotAreaCov_support s t d hv
    have hc : classCoeff axisTTPlus d = 0 := by
      rcases hmask with h | h
      · have h2 : maskOf d = 2 := by simpa [ha] using h
        have : d.val = 1 := by
          have := congrArg (· - 1) h2
          simpa [maskOf] using this
        have hd : d = ⟨1, by decide⟩ := Fin.ext this
        simpa [hd] using classCoeff_axisTTPlus_mask_2
      · have h1 : maskOf d = 1 := by simpa [hb] using h
        have : d.val = 0 := by
          have := congrArg (· - 1) h1
          simpa [maskOf] using this
        have hd : d = ⟨0, by decide⟩ := Fin.ext this
        simpa [hd] using classCoeff_axisTTPlus_mask_1
    simp [hc]

theorem transportedSlotTerm_axis_seedMasks
    (s : Fin 24) (t : Fin 10) (m : Fin 4 → ℝ)
    (h : (diffMaskA s t = 1 ∧ diffMaskB s t = 2) ∨
      (diffMaskA s t = 2 ∧ diffMaskB s t = 1)) :
    transportedSlotTerm axisTTPlus m s t = 0 := by
  unfold transportedSlotTerm
  by_cases ht : isT11 s t
  · simp only [ht, ite_true]
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [phasedClassDot_area_axis_of_masks_1_2 s t m (hingeBase s t) ha hb]
      ring
    · rw [phasedClassDot_area_axis_of_masks_2_1 s t m (hingeBase s t) ha hb]
      ring
  · simp [ht]

/-! ## §5. Wave vector and certificate algebra -/

/-- `m⋆ = (π/2, π/2, π/2, 0)`. -/
def waveStar : Fin 4 → ℝ
  | 0 => Real.pi / 2
  | 1 => Real.pi / 2
  | 2 => Real.pi / 2
  | 3 => 0

def axisStarKind (s : Fin 24) (t : Fin 10) : ℕ :=
  if (s.val, t.val) ∈
      [(0, 6), (2, 6), (4, 9), (5, 9), (6, 6), (8, 6), (10, 9), (11, 9),
        (18, 9), (19, 9), (20, 9), (21, 9)] then 1
  else if (s.val, t.val) ∈
      [(2, 0), (3, 0), (8, 0), (9, 0), (12, 0), (13, 0), (14, 0), (15, 0),
        (19, 6), (21, 6), (22, 6), (23, 6)] then 2
  else 0

def axisStarContrib (s : Fin 24) (t : Fin 10) : ℝ :=
  if axisStarKind s t = 1 then -Real.sqrt 2 / 8
  else if axisStarKind s t = 2 then -1 / 4 + Real.sqrt 2 / 8
  else 0

def gaugeStarKind (s : Fin 24) (t : Fin 10) : ℕ :=
  if (s.val, t.val) ∈ [(7, 6), (10, 6), (13, 6), (16, 6)] then 1 else 0

def gaugeStarContrib (s : Fin 24) (t : Fin 10) : ℝ :=
  if gaugeStarKind s t = 1 then -1 + Real.sqrt 2 else 0

theorem axisStarKind_count1 :
    (∑ s : Fin 24, ∑ t : Fin 10,
        if axisStarKind s t = 1 then (1 : ℕ) else 0) = 12 := by
  decide

theorem axisStarKind_count2 :
    (∑ s : Fin 24, ∑ t : Fin 10,
        if axisStarKind s t = 2 then (1 : ℕ) else 0) = 12 := by
  decide

theorem gaugeStarKind_count1 :
    (∑ s : Fin 24, ∑ t : Fin 10,
        if gaugeStarKind s t = 1 then (1 : ℕ) else 0) = 4 := by
  decide

/-- Certificate sum for axis TT at `m⋆`: `-3`. -/
theorem sum_axisStarContrib :
    (∑ s : Fin 24, ∑ t : Fin 10, axisStarContrib s t) = (-3 : ℝ) := by
  unfold axisStarContrib
  set a : ℝ := -Real.sqrt 2 / 8
  set b : ℝ := -1 / 4 + Real.sqrt 2 / 8
  have hterm : ∀ s t,
      (if axisStarKind s t = 1 then a
        else if axisStarKind s t = 2 then b else (0 : ℝ)) =
        a * (if axisStarKind s t = 1 then (1 : ℝ) else 0) +
          b * (if axisStarKind s t = 2 then (1 : ℝ) else 0) := by
    intro s t
    have hk : axisStarKind s t ≤ 2 := by
      unfold axisStarKind; split_ifs <;> simp
    match h : axisStarKind s t with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | n + 3 => omega
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc1 :
      (∑ s : Fin 24, ∑ t : Fin 10,
          if axisStarKind s t = 1 then (1 : ℝ) else 0) = 12 := by
    simpa [Nat.cast_sum] using
      congrArg (fun n : ℕ => (n : ℝ)) axisStarKind_count1
  have hc2 :
      (∑ s : Fin 24, ∑ t : Fin 10,
          if axisStarKind s t = 2 then (1 : ℝ) else 0) = 12 := by
    simpa [Nat.cast_sum] using
      congrArg (fun n : ℕ => (n : ℝ)) axisStarKind_count2
  rw [hc1, hc2]
  -- a*12 + b*12 = -3
  unfold a b
  ring

/-- Certificate sum for decoy gauge at `m⋆`: `-4 + 4√2`. -/
theorem sum_gaugeStarContrib :
    (∑ s : Fin 24, ∑ t : Fin 10, gaugeStarContrib s t) =
      -4 + 4 * Real.sqrt 2 := by
  unfold gaugeStarContrib
  set c : ℝ := -1 + Real.sqrt 2
  have hterm : ∀ s t,
      (if gaugeStarKind s t = 1 then c else (0 : ℝ)) =
        c * (if gaugeStarKind s t = 1 then (1 : ℝ) else 0) := by
    intro s t; by_cases h : gaugeStarKind s t = 1 <;> simp [h]
  simp_rw [hterm, ← Finset.mul_sum]
  have hc :
      (∑ s : Fin 24, ∑ t : Fin 10,
          if gaugeStarKind s t = 1 then (1 : ℝ) else 0) = 4 := by
    simpa [Nat.cast_sum] using
      congrArg (fun n : ℕ => (n : ℝ)) gaugeStarKind_count1
  rw [hc]
  unfold c
  ring

/-! ## §6. Integer Bloch symbol at `waveStar`

Every midpoint phase at `waveStar` is a natural multiple of `π/4`, so
each phased class dot is `a + b·(√2/2)` with decidable integers `a, b`.
This turns the geometric slot terms into integer certificates.
-/

/-- Base-vertex quarter-turn half-count (bits 0,1,2 of the base mask). -/
def baseTurns (s : Fin 24) (t : Fin 10) : ℕ :=
  (if Nat.testBit (triangleVertexMasks s t).1 0 then 1 else 0) +
    (if Nat.testBit (triangleVertexMasks s t).1 1 then 1 else 0) +
      (if Nat.testBit (triangleVertexMasks s t).1 2 then 1 else 0)

/-- Midpoint quarter-turn count of class `d` (bits 0,1,2 of its mask). -/
def dispTurns (d : Fin 15) : ℕ :=
  (if classBit d 0 then 1 else 0) +
    (if classBit d 1 then 1 else 0) +
      (if classBit d 2 then 1 else 0)

/-- Total quarter turns of the midpoint phase at `waveStar`. -/
def quarterTurns (s : Fin 24) (t : Fin 10) (d : Fin 15) : ℕ :=
  2 * baseTurns s t + dispTurns d

/-- Integer part of `cos(k·π/4)` (period-8 table). -/
def cosC1 : ℕ → ℤ
  | 0 => 1
  | 4 => -1
  | _ => 0

/-- `√2/2`-coefficient of `cos(k·π/4)` (period-8 table). -/
def cosC2 : ℕ → ℤ
  | 1 => 1
  | 3 => -1
  | 5 => -1
  | 7 => 1
  | _ => 0

private lemma waveStar_dot_maskCoord (M : ℕ) :
    (∑ i : Fin 4, waveStar i * maskCoord M i) =
      (((if Nat.testBit M 0 then 1 else 0) +
          (if Nat.testBit M 1 then 1 else 0) +
            (if Nat.testBit M 2 then 1 else 0) : ℕ) : ℝ) *
        (Real.pi / 2) := by
  rw [Fin.sum_univ_four]
  by_cases h0 : Nat.testBit M 0 <;> by_cases h1 : Nat.testBit M 1 <;>
    by_cases h2 : Nat.testBit M 2 <;> by_cases h3 : Nat.testBit M 3 <;>
    simp [waveStar, maskCoord, h0, h1, h2, h3] <;> ring

private lemma waveStar_dot_classDisp (d : Fin 15) :
    (∑ i : Fin 4, waveStar i * classDisp d i) =
      ((dispTurns d : ℕ) : ℝ) * (Real.pi / 2) := by
  rw [Fin.sum_univ_four]
  unfold dispTurns
  by_cases h0 : classBit d 0 <;> by_cases h1 : classBit d 1 <;>
    by_cases h2 : classBit d 2 <;> by_cases h3 : classBit d 3 <;>
    simp [waveStar, classDisp, h0, h1, h2, h3] <;> ring

/-- The midpoint phase at `waveStar` is `quarterTurns · π/4` exactly. -/
theorem classMidpointPhase_waveStar (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    classMidpointPhase waveStar (hingeBase s t) d =
      (quarterTurns s t d : ℝ) * (Real.pi / 4) := by
  unfold classMidpointPhase hingeBase quarterTurns baseTurns
  rw [waveStar_dot_maskCoord, waveStar_dot_classDisp]
  push_cast
  ring

/-- Exact table for `cos(k·π/4)`, valid for every natural `k`. -/
theorem cos_quarterTurns (k : ℕ) :
    Real.cos ((k : ℝ) * (Real.pi / 4)) =
      (cosC1 (k % 8) : ℝ) + (cosC2 (k % 8) : ℝ) * (Real.sqrt 2 / 2) := by
  have hmod : ((k % 8 : ℕ) : ℝ) + 8 * ((k / 8 : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div k 8)
  have hsplit : (k : ℝ) * (Real.pi / 4) =
      ((k % 8 : ℕ) : ℝ) * (Real.pi / 4) +
        ((k / 8 : ℕ) : ℝ) * (2 * Real.pi) := by
    rw [← hmod]; ring
  rw [hsplit,
    (Real.cos_periodic.nat_mul (k / 8)) (((k % 8 : ℕ) : ℝ) * (Real.pi / 4))]
  have h8 : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨
      k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;> rw [h]
  · norm_num [cosC1, cosC2, Real.cos_zero]
  · norm_num [cosC1, cosC2, Real.cos_pi_div_four]
  · rw [show ((2 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi / 2 by push_cast; ring]
    norm_num [cosC1, cosC2, Real.cos_pi_div_two]
  · rw [show ((3 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi - Real.pi / 4 by
      push_cast; ring]
    rw [Real.cos_pi_sub]
    norm_num [cosC1, cosC2, Real.cos_pi_div_four]
  · rw [show ((4 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi by push_cast; ring]
    norm_num [cosC1, cosC2, Real.cos_pi]
  · rw [show ((5 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi + Real.pi / 4 by
      push_cast; ring]
    rw [Real.cos_add]
    norm_num [cosC1, cosC2, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  · rw [show ((6 : ℕ) : ℝ) * (Real.pi / 4) = Real.pi + Real.pi / 2 by
      push_cast; ring]
    rw [Real.cos_add]
    norm_num [cosC1, cosC2, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  · rw [show ((7 : ℕ) : ℝ) * (Real.pi / 4) = 2 * Real.pi - Real.pi / 4 by
      push_cast; ring]
    rw [Real.cos_sub]
    norm_num [cosC1, cosC2, Real.cos_two_pi, Real.sin_two_pi,
      Real.cos_pi_div_four]

/-- Integer (×4) slot area table. -/
def slotAreaCovZ4 (s : Fin 24) (t : Fin 10) (d : Fin 15) : ℤ :=
  if maskOf d = diffMaskA s t then 1
  else if maskOf d = diffMaskB s t then 1
  else 0

private lemma slotAreaCov_eq_cast (s : Fin 24) (t : Fin 10) (d : Fin 15) :
    slotAreaCov s t d = ((slotAreaCovZ4 s t d : ℤ) : ℝ) / 4 := by
  unfold slotAreaCov slotAreaCovZ4
  split_ifs <;> norm_num

/-- Integer symbol of the phased area dot (×4, integer part). -/
def slotA1 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d : Fin 15,
    slotAreaCovZ4 s t d * cz d * cosC1 (quarterTurns s t d % 8)

/-- Integer symbol of the phased area dot (×4, `√2/2` part). -/
def slotA2 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d : Fin 15,
    slotAreaCovZ4 s t d * cz d * cosC2 (quarterTurns s t d % 8)

/-- Integer symbol of the phased transported-kernel dot (integer part). -/
def slotK1 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    kernel11Sign d0 * cz (permClass (slotTransportPerm s t) d0) *
      cosC1 (quarterTurns s t (permClass (slotTransportPerm s t) d0) % 8)

/-- Integer symbol of the phased transported-kernel dot (`√2/2` part). -/
def slotK2 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  ∑ d0 : Fin 15,
    kernel11Sign d0 * cz (permClass (slotTransportPerm s t) d0) *
      cosC2 (quarterTurns s t (permClass (slotTransportPerm s t) d0) % 8)

/-- Integer certificate of a slot term (×8, integer part). -/
def slotN1 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isT11 s t then
    2 * slotA1 cz s t * slotK1 cz s t + slotA2 cz s t * slotK2 cz s t
  else 0

/-- Integer certificate of a slot term (×8, `√2` part). -/
def slotN2 (cz : Fin 15 → ℤ) (s : Fin 24) (t : Fin 10) : ℤ :=
  if isT11 s t then
    slotA1 cz s t * slotK2 cz s t + slotA2 cz s t * slotK1 cz s t
  else 0

/-- Reindexing: a phased dot against the transported kernel is the seed
kernel folded through the class permutation. -/
theorem phasedClassDot_transportedDeficit (p : Fin 24) (H : Mat4)
    (m x : Fin 4 → ℝ) :
    phasedClassDot (transportedDeficit p) H m x =
      ∑ d0 : Fin 15,
        ReggeHinge4DStarKernel.fullStarClassKernel d0 *
          planeWaveClassPert H m x (permClass p d0) := by
  unfold phasedClassDot transportedDeficit
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  have h : ∀ d : Fin 15,
      (if permClass p d0 = d then
        ReggeHinge4DStarKernel.fullStarClassKernel d0 else 0) *
          planeWaveClassPert H m x d =
        (if permClass p d0 = d then
          ReggeHinge4DStarKernel.fullStarClassKernel d0 *
            planeWaveClassPert H m x d else 0) := by
    intro d; split_ifs <;> simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp

/-- Master area evaluation at `waveStar`. -/
theorem phasedA_waveStar (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    phasedClassDot (slotAreaCov s t) H waveStar (hingeBase s t) =
      ((slotA1 cz s t : ℝ) + (slotA2 cz s t : ℝ) * (Real.sqrt 2 / 2)) / 4 := by
  unfold phasedClassDot slotA1 slotA2
  rw [Int.cast_sum, Int.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold planeWaveClassPert
  rw [slotAreaCov_eq_cast, hH d, classMidpointPhase_waveStar,
    cos_quarterTurns]
  push_cast
  ring

/-- Master transported-kernel evaluation at `waveStar`. -/
theorem phasedK_waveStar (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    phasedClassDot (slotDeficitKer s t) H waveStar (hingeBase s t) =
      (slotK1 cz s t : ℝ) + (slotK2 cz s t : ℝ) * (Real.sqrt 2 / 2) := by
  unfold slotDeficitKer
  rw [phasedClassDot_transportedDeficit]
  unfold slotK1 slotK2
  rw [Int.cast_sum, Int.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d0 _ => ?_
  unfold planeWaveClassPert
  rw [kernel11_eq_sign, hH, classMidpointPhase_waveStar, cos_quarterTurns]
  push_cast
  ring

/-- MASTER SLOT EVALUATION: every transported slot term at `waveStar`
equals its integer certificate `(N1 + N2·√2)/8`. -/
theorem transportedSlotTerm_waveStar_eval (H : Mat4) (cz : Fin 15 → ℤ)
    (hH : ∀ d, classCoeff H d = (cz d : ℝ)) (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm H waveStar s t =
      ((slotN1 cz s t : ℝ) + (slotN2 cz s t : ℝ) * Real.sqrt 2) / 8 := by
  unfold transportedSlotTerm slotN1 slotN2
  by_cases ht : isT11 s t
  · simp only [ht, ite_true]
    rw [phasedA_waveStar H cz hH s t, phasedK_waveStar H cz hH s t]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num)
    push_cast
    linear_combination
      (((slotA2 cz s t : ℤ) : ℝ) * ((slotK2 cz s t : ℤ) : ℝ) / 16) * h2
  · simp [ht]

/-! ## §7. Closing the geometric ↔ certificate match at `waveStar` -/

/-- Integer certificate of the axis table by kind:
kind 1 ↦ `(0,-1)` (value `-√2/8`), kind 2 ↦ `(-2,1)` (value `-1/4+√2/8`). -/
def axisCertN1 : ℕ → ℤ
  | 2 => -2
  | _ => 0

def axisCertN2 : ℕ → ℤ
  | 1 => -1
  | 2 => 1
  | _ => 0

def gaugeCertN1 : ℕ → ℤ
  | 1 => -8
  | _ => 0

def gaugeCertN2 : ℕ → ℤ
  | 1 => 8
  | _ => 0

set_option maxRecDepth 8000 in
/-- DECIDABLE GATE: the integer slot certificates on `axisTTPlus` match
the Nat-kind table on every one of the 240 oriented slots. -/
theorem slotN_axis_match :
    ∀ s : Fin 24, ∀ t : Fin 10,
      slotN1 axisTTPlusCoeffZ s t = axisCertN1 (axisStarKind s t) ∧
        slotN2 axisTTPlusCoeffZ s t = axisCertN2 (axisStarKind s t) := by
  decide

/-- Integer coefficient table for the pure-gauge probe. -/
def decoyGaugeCoeffZ (d : Fin 15) : ℤ := 2 * (gaugeBit0 d : ℤ)

theorem classCoeff_decoyGauge_int (d : Fin 15) :
    classCoeff decoyGauge d = (decoyGaugeCoeffZ d : ℝ) := by
  rw [classCoeff_decoyGauge_bit]
  unfold decoyGaugeCoeffZ
  push_cast
  ring

set_option maxRecDepth 8000 in
/-- DECIDABLE GATE: the integer slot certificates on `decoyGauge` match
the Nat-kind table on every slot. -/
theorem slotN_gauge_match :
    ∀ s : Fin 24, ∀ t : Fin 10,
      slotN1 decoyGaugeCoeffZ s t = gaugeCertN1 (gaugeStarKind s t) ∧
        slotN2 decoyGaugeCoeffZ s t = gaugeCertN2 (gaugeStarKind s t) := by
  decide

/-- GEOMETRIC ↔ CERTIFICATE MATCH (axis): every transported slot term on
`axisTTPlus` at `waveStar` equals its certificate entry. -/
theorem transportedSlotTerm_axis_waveStar (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm axisTTPlus waveStar s t = axisStarContrib s t := by
  rw [transportedSlotTerm_waveStar_eval axisTTPlus axisTTPlusCoeffZ
    classCoeff_axisTTPlus_int s t,
    (slotN_axis_match s t).1, (slotN_axis_match s t).2]
  unfold axisStarContrib
  have hk : axisStarKind s t = 0 ∨ axisStarKind s t = 1 ∨
      axisStarKind s t = 2 := by
    unfold axisStarKind; split_ifs <;> simp
  rcases hk with h | h | h <;> rw [h]
  all_goals norm_num [axisCertN1, axisCertN2]
  all_goals ring

/-- GEOMETRIC ↔ CERTIFICATE MATCH (gauge). -/
theorem transportedSlotTerm_gauge_waveStar (s : Fin 24) (t : Fin 10) :
    transportedSlotTerm decoyGauge waveStar s t = gaugeStarContrib s t := by
  rw [transportedSlotTerm_waveStar_eval decoyGauge decoyGaugeCoeffZ
    classCoeff_decoyGauge_int s t,
    (slotN_gauge_match s t).1, (slotN_gauge_match s t).2]
  unfold gaugeStarContrib
  have hk : gaugeStarKind s t = 0 ∨ gaugeStarKind s t = 1 := by
    unfold gaugeStarKind; split_ifs <;> simp
  rcases hk with h | h <;> rw [h]
  all_goals norm_num [gaugeCertN1, gaugeCertN2]
  all_goals ring

/-- CLOSING THEOREM: the honest transported `(1,1)` Bloch fold on the
axis TT polarization at `m⋆ = (π/2, π/2, π/2, 0)` equals `-3`. -/
theorem blochFold11_axisTTPlus_waveStar :
    blochFold11 axisTTPlus waveStar = -3 := by
  unfold blochFold11
  simp_rw [transportedSlotTerm_axis_waveStar]
  exact sum_axisStarContrib

/-- Nonvacuity of the finite-momentum fold on axis TT. -/
theorem blochFold11_axisTTPlus_waveStar_ne_zero :
    blochFold11 axisTTPlus waveStar ≠ 0 := by
  rw [blochFold11_axisTTPlus_waveStar]; norm_num

/-- CLOSING THEOREM (gauge verdict): the fold on the pure-gauge probe at
`m⋆` equals `-4 + 4√2` (nonzero; discrete gauge invariance at finite
momentum holds only up to the finite-difference identity). -/
theorem blochFold11_decoyGauge_waveStar :
    blochFold11 decoyGauge waveStar = -4 + 4 * Real.sqrt 2 := by
  unfold blochFold11
  simp_rw [transportedSlotTerm_gauge_waveStar]
  exact sum_gaugeStarContrib

theorem blochFold11_decoyGauge_waveStar_ne_zero :
    blochFold11 decoyGauge waveStar ≠ 0 := by
  rw [blochFold11_decoyGauge_waveStar]
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    have := Real.lt_sqrt (x := 1) (y := 2) (by norm_num)
    norm_num at this
    exact this
  nlinarith

/-! ## §8. Status -/

structure BlochFold4DStatus where
  factorizedZeroMomentumClosed : Bool
  transportedBilinearClosed : Bool
  seedMaskAxisVanishClosed : Bool
  certificateAlgebraClosed : Bool
  geometricCertificateMatchClosed : Bool
  m2EhComparisonOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def blochFold4DStatus : BlochFold4DStatus where
  factorizedZeroMomentumClosed := true
  transportedBilinearClosed := true
  seedMaskAxisVanishClosed := true
  certificateAlgebraClosed := true
  geometricCertificateMatchClosed := true
  m2EhComparisonOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem blochFold4DStatus_flags :
    blochFold4DStatus.factorizedZeroMomentumClosed = true ∧
      blochFold4DStatus.transportedBilinearClosed = true ∧
        blochFold4DStatus.seedMaskAxisVanishClosed = true ∧
          blochFold4DStatus.certificateAlgebraClosed = true ∧
            blochFold4DStatus.geometricCertificateMatchClosed = true ∧
              blochFold4DStatus.m2EhComparisonOpen = true ∧
                blochFold4DStatus.convergesEH4d = false ∧
                  blochFold4DStatus.gapActionRecovery = false := by
  decide

end

end ReggeBlochFold4D
end Analysis
end Gravity
end IndisputableMonolith
