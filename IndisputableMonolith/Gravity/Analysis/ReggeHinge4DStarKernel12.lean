import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DDihedralKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D full periodic-lattice star deficit class kernel, type (1,2)

QG full-theory campaign, next kernel-checked increment after
`ReggeHinge4DStarKernel` (type `(1,1)` seed orbit).  Imports the
Freudenthal incidence layer, the 15-class stencil, and the committed
Gram-projection / cleared-denominator cosine calculus; never redefines
their API.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: the type `(1,2)` triangle hinge `{0, e₀, e₀+e₁+e₂}` (masks
  `0,1,7`; difference masks `(1,6)`) and its **full** periodic
  Freudenthal star in the integer lattice (two containing unit cubes,
  four incident 4-simplices).  The complement-related type `(2,1)` is
  **OPEN** (not transported in this module).  Other hinge orbits remain
  OPEN.
* This does **not** complete the flat Hessian assembly over all hinges.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (deliverable A)

1. **Star enumeration.** Exactly four `(cube translate, Kuhn simplex)`
   pairs contain the `(1,2)` representative hinge.
2. **Flat cosine multiset.** All four simplices have flat cosine `0`
   (two local squared-length orbits), recomputed from each orbit's own
   Gram vector via the committed `cosDihedral` pattern.
3. **Flatness gate.** Star angle sum equals exactly `2π`
   (`4 · arccos 0 = 4 · π/2`).
4. **Full-star deficit class kernel** on all 15 stencil classes with
   values `±√2/2`.
5. **Gates:** nonvacuity, swap-`1↔2` hinge-fixing symmetry,
   uniform-scaling decoy `√2/2`, homothety stationarity `0`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DStarKernel12

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeHinge4DDihedralKernel
open ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Cube translates and star enumeration -/

inductive CubeTranslate
  | origin
  | minusE3
  deriving DecidableEq, Repr, Fintype

def localHingeMasks : CubeTranslate → Finset ℕ
  | .origin => {0, 1, 7}
  | .minusE3 => {8, 9, 15}

def containsHinge (c : CubeTranslate) (s : Fin 24) : Bool :=
  decide (∀ m ∈ localHingeMasks c, ∃ i : Fin 5, vertexMask s i = m)

structure StarMember where
  cube : CubeTranslate
  simplex : Fin 24
  deriving DecidableEq, Repr

def starMembers : List StarMember :=
  [ ⟨.origin, 0⟩, ⟨.origin, 2⟩
  , ⟨.minusE3, 18⟩, ⟨.minusE3, 19⟩ ]

theorem starMembers_length : starMembers.length = 4 := rfl

theorem starMembers_complete (c : CubeTranslate) (s : Fin 24) :
    containsHinge c s = true ↔ ⟨c, s⟩ ∈ starMembers := by
  cases c <;> fin_cases s <;> decide

theorem star_cardinality :
    (Finset.univ.filter (fun p : CubeTranslate × Fin 24 =>
      containsHinge p.1 p.2 = true)).card = 4 := by
  decide

/-! ## §2. Flat squared-length orbit representatives -/

def nearFlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 2
  | 5 => 1 | 6 => 3 | 7 => 1 | 8 => 1 | 9 => 2
def farFlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 2
  | 5 => 2 | 6 => 1 | 7 => 4 | 8 => 1 | 9 => 3

theorem hingeGramDet_near : hingeGramDet nearFlatSqEdges = 8 := by
  norm_num [hingeGramDet, nearFlatSqEdges]
theorem apexDotNum_near : apexDotNum nearFlatSqEdges = 0 := by
  norm_num [apexDotNum, hingeGramDet, nearFlatSqEdges]
theorem apex3NormSqNum_near : apex3NormSqNum nearFlatSqEdges = 4 := by
  norm_num [apex3NormSqNum, hingeGramDet, nearFlatSqEdges]
theorem apex4NormSqNum_near : apex4NormSqNum nearFlatSqEdges = 8 := by
  norm_num [apex4NormSqNum, hingeGramDet, nearFlatSqEdges]

theorem hingeGramDet_far : hingeGramDet farFlatSqEdges = 8 := by
  norm_num [hingeGramDet, farFlatSqEdges]
theorem apexDotNum_far : apexDotNum farFlatSqEdges = 0 := by
  norm_num [apexDotNum, hingeGramDet, farFlatSqEdges]
theorem apex3NormSqNum_far : apex3NormSqNum farFlatSqEdges = 8 := by
  norm_num [apex3NormSqNum, hingeGramDet, farFlatSqEdges]
theorem apex4NormSqNum_far : apex4NormSqNum farFlatSqEdges = 4 := by
  norm_num [apex4NormSqNum, hingeGramDet, farFlatSqEdges]

theorem cosDihedral_near_flat : cosDihedral nearFlatSqEdges = 0 := by
  rw [cos_numForm _ (by rw [hingeGramDet_near]; norm_num),
    apexDotNum_near, apex3NormSqNum_near, apex4NormSqNum_near]
  norm_num

theorem cosDihedral_far_flat : cosDihedral farFlatSqEdges = 0 := by
  rw [cos_numForm _ (by rw [hingeGramDet_far]; norm_num),
    apexDotNum_far, apex3NormSqNum_far, apex4NormSqNum_far]
  norm_num

/-! ## §3. Flatness gate -/

def flatAngleRight : ℝ := Real.arccos 0
theorem flatAngleRight_eq : flatAngleRight = Real.pi / 2 := Real.arccos_zero
def starFlatAngleSum : ℝ := 4 * flatAngleRight
theorem star_flat_angle_sum_two_pi : starFlatAngleSum = 2 * Real.pi := by
  simp only [starFlatAngleSum, flatAngleRight_eq]; ring

def starFlatCosines : Fin 4 → ℝ
  | _ => 0

theorem starFlatCosines_match_orbits :
    starFlatCosines 0 = cosDihedral nearFlatSqEdges ∧
      starFlatCosines 2 = cosDihedral farFlatSqEdges :=
  ⟨cosDihedral_near_flat.symm, cosDihedral_far_flat.symm⟩

/-! ## §4. Coordinate paths and cosine kernels -/

def nearCoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else nearFlatSqEdges j

def farCoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else farFlatSqEdges j

def nearCosKernel : Fin 10 → ℝ
  | ⟨4, _⟩ => (-4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨6, _⟩ => (4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨7, _⟩ => (8 : ℝ) / (8 * Real.sqrt 2)
  | ⟨8, _⟩ => (4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨9, _⟩ => (-8 : ℝ) / (8 * Real.sqrt 2)
  | _ => 0
def farCosKernel : Fin 10 → ℝ
  | ⟨0, _⟩ => (-4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨1, _⟩ => (-4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨3, _⟩ => (8 : ℝ) / (8 * Real.sqrt 2)
  | ⟨5, _⟩ => (4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨7, _⟩ => (4 : ℝ) / (8 * Real.sqrt 2)
  | ⟨9, _⟩ => (-8 : ℝ) / (8 * Real.sqrt 2)
  | _ => 0

private lemma hasDerivAt_quadPoly (a b c t0 : ℝ) :
    HasDerivAt (fun t : ℝ => a * t ^ 2 + b * t + c) (2 * a * t0 + b) t0 := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t0) t0 := by
    simpa using hasDerivAt_pow 2 t0
  have h2 : HasDerivAt (fun t : ℝ => a * t ^ 2) (a * (2 * t0)) t0 :=
    h1.const_mul a
  have h3 : HasDerivAt (fun t : ℝ => b * t) b t0 := by
    simpa using (hasDerivAt_id t0).const_mul b
  have h4 := (h2.add h3).add_const c
  convert h4 using 1
  ring

private lemma hasDerivAt_numForm_zeroDot {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 0) (hPQ0 : P t0 * Q t0 = 32) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      (N' / (8 * Real.sqrt 2)) t0 := by
  have hPQ : HasDerivAt (fun t => P t * Q t)
      (P' * Q t0 + P t0 * Q') t0 := hP.mul hQ
  have hPQne : P t0 * Q t0 ≠ 0 := by rw [hPQ0]; norm_num
  have hsqrt : HasDerivAt (fun t => Real.sqrt (P t * Q t))
      ((P' * Q t0 + P t0 * Q') / (2 * Real.sqrt (P t0 * Q t0))) t0 :=
    hPQ.sqrt hPQne
  have hden : HasDerivAt (fun t => 2 * Real.sqrt (P t * Q t))
      (2 * ((P' * Q t0 + P t0 * Q') / (2 * Real.sqrt (P t0 * Q t0)))) t0 :=
    hsqrt.const_mul 2
  have hdenne : 2 * Real.sqrt (P t0 * Q t0) ≠ 0 := by
    rw [hPQ0]; positivity
  have hdiv := hN.div hden hdenne
  have h32 : Real.sqrt (P t0 * Q t0) = 4 * Real.sqrt 2 := by
    rw [hPQ0, show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2) 2,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  -- Match the quotient-rule derivative at N=0, PQ=32 to N'/(8√2).
  convert hdiv using 1
  simp [h32, hN0]
  field_simp [hs]
  ring

private lemma hasDerivAt_near_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (nearCoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (nearCoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (nearCoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (nearCoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 0)
    (hPQ0 : (aP * t0 ^ 2 + bP * t0 + cP) * (aQ * t0 ^ 2 + bQ * t0 + cQ) = 32)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath k t))
      ((2 * aN * t0 + bN) / (8 * Real.sqrt 2)) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain :=
    hasDerivAt_numForm_zeroDot hN hP hQ hN0 (by simpa using hPQ0)
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (nearCoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma hasDerivAt_far_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (farCoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (farCoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (farCoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (farCoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 0)
    (hPQ0 : (aP * t0 ^ 2 + bP * t0 + cP) * (aQ * t0 ^ 2 + bQ * t0 + cQ) = 32)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath k t))
      ((2 * aN * t0 + bN) / (8 * Real.sqrt 2)) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain :=
    hasDerivAt_numForm_zeroDot hN hP hQ hN0 (by simpa using hPQ0)
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (farCoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma near_path0_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 0 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (nearCoordPath 0 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ apex4NormSqNum (nearCoordPath 0 t) = (-1) * t ^ 2 + (10) * t + (-1)
    ∧ hingeGramDet (nearCoordPath 0 t) = (-1) * t ^ 2 + (10) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 0 t))
      (0) 1 := by
  have h := hasDerivAt_near_slot 0 1 (0) (0) (0) (-1) (6) (-1)
    (-1) (10) (-1) (-1) (10) (-1) near_path0_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path1_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 1 t) = (-2) * t ^ 2 + (12) * t + (-18)
    ∧ apex3NormSqNum (nearCoordPath 1 t) = (-1) * t ^ 2 + (6) * t + (-5)
    ∧ apex4NormSqNum (nearCoordPath 1 t) = (-3) * t ^ 2 + (18) * t + (-19)
    ∧ hingeGramDet (nearCoordPath 1 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 1 t))
      (0) 3 := by
  have h := hasDerivAt_near_slot 1 3 (-2) (12) (-18) (-1) (6) (-5)
    (-3) (18) (-19) (-1) (6) (-1) near_path1_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path2_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (nearCoordPath 2 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (nearCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (nearCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 2 t))
      (0) 2 := by
  have h := hasDerivAt_near_slot 2 2 (0) (0) (0) (-2) (8) (-4)
    (0) (0) (8) (0) (0) (8) near_path2_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path3_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (nearCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (nearCoordPath 3 t) = (-2) * t ^ 2 + (16) * t + (-24)
    ∧ hingeGramDet (nearCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 3 t))
      (0) 4 := by
  have h := hasDerivAt_near_slot 3 4 (0) (0) (0) (0) (0) (4)
    (-2) (16) (-24) (0) (0) (8) near_path3_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path4_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 4 t) = (-4) * t ^ 2 + (12) * t + (-8)
    ∧ apex3NormSqNum (nearCoordPath 4 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (nearCoordPath 4 t) = (-4) * t ^ 2 + (20) * t + (-16)
    ∧ hingeGramDet (nearCoordPath 4 t) = (-1) * t ^ 2 + (8) * t + (-4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 4 t))
      ((-4 : ℝ) / (8 * Real.sqrt 2)) 2 := by
  have h := hasDerivAt_near_slot 4 2 (-4) (12) (-8) (-2) (8) (-4)
    (-4) (20) (-16) (-1) (8) (-4) near_path4_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path5_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (nearCoordPath 5 t) = (-3) * t ^ 2 + (10) * t + (-3)
    ∧ apex4NormSqNum (nearCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (nearCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 5 t))
      (0) 1 := by
  have h := hasDerivAt_near_slot 5 1 (0) (0) (0) (-3) (10) (-3)
    (0) (0) (8) (0) (0) (8) near_path5_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path6_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 6 t) = (0) * t ^ 2 + (4) * t + (-12)
    ∧ apex3NormSqNum (nearCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (nearCoordPath 6 t) = (-3) * t ^ 2 + (18) * t + (-19)
    ∧ hingeGramDet (nearCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 6 t))
      ((4 : ℝ) / (8 * Real.sqrt 2)) 3 := by
  have h := hasDerivAt_near_slot 6 3 (0) (4) (-12) (0) (0) (4)
    (-3) (18) (-19) (0) (0) (8) near_path6_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path7_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 7 t) = (0) * t ^ 2 + (8) * t + (-8)
    ∧ apex3NormSqNum (nearCoordPath 7 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ apex4NormSqNum (nearCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (nearCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 7 t))
      ((8 : ℝ) / (8 * Real.sqrt 2)) 1 := by
  have h := hasDerivAt_near_slot 7 1 (0) (8) (-8) (-1) (6) (-1)
    (0) (0) (8) (0) (0) (8) near_path7_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path8_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 8 t) = (0) * t ^ 2 + (4) * t + (-4)
    ∧ apex3NormSqNum (nearCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (nearCoordPath 8 t) = (-1) * t ^ 2 + (10) * t + (-1)
    ∧ hingeGramDet (nearCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 8 t))
      ((4 : ℝ) / (8 * Real.sqrt 2)) 1 := by
  have h := hasDerivAt_near_slot 8 1 (0) (4) (-4) (0) (0) (4)
    (-1) (10) (-1) (0) (0) (8) near_path8_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma near_path9_polys : ∀ t : ℝ,
    apexDotNum (nearCoordPath 9 t) = (0) * t ^ 2 + (-8) * t + (16)
    ∧ apex3NormSqNum (nearCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (nearCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (nearCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      nearCoordPath, nearFlatSqEdges] <;> ring

theorem hasDerivAt_near_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath 9 t))
      ((-8 : ℝ) / (8 * Real.sqrt 2)) 2 := by
  have h := hasDerivAt_near_slot 9 2 (0) (-8) (16) (0) (0) (4)
    (0) (0) (8) (0) (0) (8) near_path9_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

theorem hasDerivAt_near_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (nearCoordPath k t))
      (nearCosKernel k) (nearFlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_near_slot0
  · exact hasDerivAt_near_slot1
  · exact hasDerivAt_near_slot2
  · exact hasDerivAt_near_slot3
  · exact hasDerivAt_near_slot4
  · exact hasDerivAt_near_slot5
  · exact hasDerivAt_near_slot6
  · exact hasDerivAt_near_slot7
  · exact hasDerivAt_near_slot8
  · exact hasDerivAt_near_slot9

private lemma far_path0_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 0 t) = (-2) * t ^ 2 + (0) * t + (2)
    ∧ apex3NormSqNum (farCoordPath 0 t) = (-4) * t ^ 2 + (16) * t + (-4)
    ∧ apex4NormSqNum (farCoordPath 0 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (farCoordPath 0 t) = (-1) * t ^ 2 + (10) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 0 t))
      ((-4 : ℝ) / (8 * Real.sqrt 2)) 1 := by
  have h := hasDerivAt_far_slot 0 1 (-2) (0) (2) (-4) (16) (-4)
    (-1) (6) (-1) (-1) (10) (-1) far_path0_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path1_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 1 t) = (0) * t ^ 2 + (-4) * t + (12)
    ∧ apex3NormSqNum (farCoordPath 1 t) = (-2) * t ^ 2 + (12) * t + (-10)
    ∧ apex4NormSqNum (farCoordPath 1 t) = (-1) * t ^ 2 + (6) * t + (-5)
    ∧ hingeGramDet (farCoordPath 1 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 1 t))
      ((-4 : ℝ) / (8 * Real.sqrt 2)) 3 := by
  have h := hasDerivAt_far_slot 1 3 (0) (-4) (12) (-2) (12) (-10)
    (-1) (6) (-5) (-1) (6) (-1) far_path1_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path2_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (farCoordPath 2 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex4NormSqNum (farCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (farCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 2 t))
      (0) 1 := by
  have h := hasDerivAt_far_slot 2 1 (0) (0) (0) (-2) (12) (-2)
    (0) (0) (4) (0) (0) (8) far_path2_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path3_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 3 t) = (0) * t ^ 2 + (8) * t + (-16)
    ∧ apex3NormSqNum (farCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (farCoordPath 3 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (farCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 3 t))
      ((8 : ℝ) / (8 * Real.sqrt 2)) 2 := by
  have h := hasDerivAt_far_slot 3 2 (0) (8) (-16) (0) (0) (8)
    (-2) (8) (-4) (0) (0) (8) far_path3_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path4_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 4 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (farCoordPath 4 t) = (-1) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (farCoordPath 4 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (farCoordPath 4 t) = (-1) * t ^ 2 + (8) * t + (-4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 4 t))
      (0) 2 := by
  have h := hasDerivAt_far_slot 4 2 (0) (0) (0) (-1) (8) (-4)
    (-2) (8) (-4) (-1) (8) (-4) far_path4_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path5_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 5 t) = (0) * t ^ 2 + (4) * t + (-8)
    ∧ apex3NormSqNum (farCoordPath 5 t) = (-3) * t ^ 2 + (12) * t + (-4)
    ∧ apex4NormSqNum (farCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (farCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 5 t))
      ((4 : ℝ) / (8 * Real.sqrt 2)) 2 := by
  have h := hasDerivAt_far_slot 5 2 (0) (4) (-8) (-3) (12) (-4)
    (0) (0) (4) (0) (0) (8) far_path5_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path6_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (farCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (farCoordPath 6 t) = (-3) * t ^ 2 + (10) * t + (-3)
    ∧ hingeGramDet (farCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 6 t))
      (0) 1 := by
  have h := hasDerivAt_far_slot 6 1 (0) (0) (0) (0) (0) (8)
    (-3) (10) (-3) (0) (0) (8) far_path6_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path7_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 7 t) = (0) * t ^ 2 + (4) * t + (-16)
    ∧ apex3NormSqNum (farCoordPath 7 t) = (-1) * t ^ 2 + (8) * t + (-8)
    ∧ apex4NormSqNum (farCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (farCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 7 t))
      ((4 : ℝ) / (8 * Real.sqrt 2)) 4 := by
  have h := hasDerivAt_far_slot 7 4 (0) (4) (-16) (-1) (8) (-8)
    (0) (0) (4) (0) (0) (8) far_path7_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path8_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (farCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (farCoordPath 8 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (farCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 8 t))
      (0) 1 := by
  have h := hasDerivAt_far_slot 8 1 (0) (0) (0) (0) (0) (8)
    (-1) (6) (-1) (0) (0) (8) far_path8_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

private lemma far_path9_polys : ∀ t : ℝ,
    apexDotNum (farCoordPath 9 t) = (0) * t ^ 2 + (-8) * t + (24)
    ∧ apex3NormSqNum (farCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (farCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (farCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      farCoordPath, farFlatSqEdges] <;> ring

theorem hasDerivAt_far_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath 9 t))
      ((-8 : ℝ) / (8 * Real.sqrt 2)) 3 := by
  have h := hasDerivAt_far_slot 9 3 (0) (-8) (24) (0) (0) (8)
    (0) (0) (4) (0) (0) (8) far_path9_polys
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  norm_num

theorem hasDerivAt_far_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (farCoordPath k t))
      (farCosKernel k) (farFlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_far_slot0
  · exact hasDerivAt_far_slot1
  · exact hasDerivAt_far_slot2
  · exact hasDerivAt_far_slot3
  · exact hasDerivAt_far_slot4
  · exact hasDerivAt_far_slot5
  · exact hasDerivAt_far_slot6
  · exact hasDerivAt_far_slot7
  · exact hasDerivAt_far_slot8
  · exact hasDerivAt_far_slot9

/-! ## §5. Full-star deficit class kernel -/

def chainRight : ℝ := (-1 : ℝ)
def nearDeficitKernel : Fin 10 → ℝ := nearCosKernel
def farDeficitKernel : Fin 10 → ℝ := farCosKernel

theorem nearDeficitKernel_eq_chain (k : Fin 10) :
    nearDeficitKernel k = -chainRight * nearCosKernel k := by
  simp [nearDeficitKernel, chainRight]

theorem farDeficitKernel_eq_chain (k : Fin 10) :
    farDeficitKernel k = -chainRight * farCosKernel k := by
  simp [farDeficitKernel, chainRight]

def starSlotClass : Fin 4 → Fin 10 → Fin 15
  | 0, 0 => 0
  | 0, 1 => 6
  | 0, 2 => 2
  | 0, 3 => 14
  | 0, 4 => 5
  | 0, 5 => 1
  | 0, 6 => 13
  | 0, 7 => 3
  | 0, 8 => 7
  | 0, 9 => 11
  | 1, 0 => 0
  | 1, 1 => 6
  | 1, 2 => 4
  | 1, 3 => 14
  | 1, 4 => 5
  | 1, 5 => 3
  | 1, 6 => 13
  | 1, 7 => 1
  | 1, 8 => 7
  | 1, 9 => 9
  | 2, 0 => 0
  | 2, 1 => 6
  | 2, 2 => 7
  | 2, 3 => 2
  | 2, 4 => 5
  | 2, 5 => 8
  | 2, 6 => 1
  | 2, 7 => 14
  | 2, 8 => 3
  | 2, 9 => 10
  | 3, 0 => 0
  | 3, 1 => 6
  | 3, 2 => 7
  | 3, 3 => 4
  | 3, 4 => 5
  | 3, 5 => 8
  | 3, 6 => 3
  | 3, 7 => 14
  | 3, 8 => 1
  | 3, 9 => 12

def starLocalDeficitKernel : Fin 4 → Fin 10 → ℝ
  | 0 | 1 => nearDeficitKernel
  | 2 | 3 => farDeficitKernel

def assembleStarMember (m : Fin 4) : Fin 15 → ℝ :=
  fun d => ∑ e : Fin 10,
    if starSlotClass m e = d then starLocalDeficitKernel m e else 0

def fullStarClassKernelAssembled : Fin 15 → ℝ :=
  fun d => ∑ m : Fin 4, assembleStarMember m d

def fullStarClassKernel : Fin 15 → ℝ
  | ⟨0, _⟩ => -(Real.sqrt 2) / 2
  | ⟨1, _⟩ => Real.sqrt 2 / 2
  | ⟨2, _⟩ => Real.sqrt 2 / 2
  | ⟨3, _⟩ => Real.sqrt 2 / 2
  | ⟨4, _⟩ => Real.sqrt 2 / 2
  | ⟨5, _⟩ => -(Real.sqrt 2) / 2
  | ⟨6, _⟩ => -(Real.sqrt 2) / 2
  | ⟨7, _⟩ => Real.sqrt 2 / 2
  | ⟨8, _⟩ => Real.sqrt 2 / 2
  | ⟨9, _⟩ => -(Real.sqrt 2) / 2
  | ⟨10, _⟩ => -(Real.sqrt 2) / 2
  | ⟨11, _⟩ => -(Real.sqrt 2) / 2
  | ⟨12, _⟩ => -(Real.sqrt 2) / 2
  | ⟨13, _⟩ => Real.sqrt 2 / 2
  | ⟨14, _⟩ => Real.sqrt 2 / 2

private lemma sum4 (f : Fin 4 → ℝ) :
    (∑ m : Fin 4, f m) = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) =
        insert (0 : Fin 4) (insert (1 : Fin 4) (insert (2 : Fin 4)
          (insert (3 : Fin 4) (∅ : Finset (Fin 4))))) from by decide]
  simp [Finset.sum_insert]
  ring

private lemma sum_support_near (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e ≠ 4 → e ≠ 6 → e ≠ 7 → e ≠ 8 → e ≠ 9 → f e = 0) :
    (∑ e : Fin 10, f e) = f 4 + f 6 + f 7 + f 8 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (4 : Fin 10) (insert (6 : Fin 10) (insert (7 : Fin 10)
          (insert (8 : Fin 10) (insert (9 : Fin 10)
            ({0, 1, 2, 3, 5} : Finset (Fin 10)))))) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => by
      fin_cases e <;> simp at he ⊢ <;>
        exact hz _ (by decide) (by decide) (by decide) (by decide) (by decide))]
  abel

private lemma sum_support_far (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e ≠ 0 → e ≠ 1 → e ≠ 3 → e ≠ 5 → e ≠ 7 → e ≠ 9 →
      f e = 0) :
    (∑ e : Fin 10, f e) = f 0 + f 1 + f 3 + f 5 + f 7 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (0 : Fin 10) (insert (1 : Fin 10) (insert (3 : Fin 10)
          (insert (5 : Fin 10) (insert (7 : Fin 10) (insert (9 : Fin 10)
            ({2, 4, 6, 8} : Finset (Fin 10))))))) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => by
      fin_cases e <;> simp at he ⊢ <;>
        exact hz _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))]
  abel

private lemma near_kernel_zero_off (e : Fin 10)
    (h4 : e ≠ 4) (h6 : e ≠ 6) (h7 : e ≠ 7) (h8 : e ≠ 8) (h9 : e ≠ 9) :
    nearDeficitKernel e = 0 := by
  fin_cases e <;> first | rfl | contradiction

private lemma far_kernel_zero_off (e : Fin 10)
    (h0 : e ≠ 0) (h1 : e ≠ 1) (h3 : e ≠ 3) (h5 : e ≠ 5) (h7 : e ≠ 7)
    (h9 : e ≠ 9) :
    farDeficitKernel e = 0 := by
  fin_cases e <;> first | rfl | contradiction

private lemma member0_eval (d : Fin 15) :
    assembleStarMember 0 d =
      (if d = 5 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 13 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 3 then (8 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 7 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 11 then (-8 : ℝ) / (8 * Real.sqrt 2) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support_near (fun e =>
      if starSlotClass 0 e = d then nearDeficitKernel e else 0)
    (fun e h4 h6 h7 h8 h9 => by simp [near_kernel_zero_off e h4 h6 h7 h8 h9])]
  simp only [starSlotClass, nearDeficitKernel, nearCosKernel]
  aesop

private lemma member1_eval (d : Fin 15) :
    assembleStarMember 1 d =
      (if d = 5 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 13 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 1 then (8 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 7 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 9 then (-8 : ℝ) / (8 * Real.sqrt 2) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support_near (fun e =>
      if starSlotClass 1 e = d then nearDeficitKernel e else 0)
    (fun e h4 h6 h7 h8 h9 => by simp [near_kernel_zero_off e h4 h6 h7 h8 h9])]
  simp only [starSlotClass, nearDeficitKernel, nearCosKernel]
  aesop

private lemma member2_eval (d : Fin 15) :
    assembleStarMember 2 d =
      (if d = 0 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 6 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 2 then (8 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 8 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 14 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 10 then (-8 : ℝ) / (8 * Real.sqrt 2) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support_far (fun e =>
      if starSlotClass 2 e = d then farDeficitKernel e else 0)
    (fun e h0 h1 h3 h5 h7 h9 => by
      simp [far_kernel_zero_off e h0 h1 h3 h5 h7 h9])]
  simp only [starSlotClass, farDeficitKernel, farCosKernel]
  aesop

private lemma member3_eval (d : Fin 15) :
    assembleStarMember 3 d =
      (if d = 0 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 6 then (-4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 4 then (8 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 8 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 14 then (4 : ℝ) / (8 * Real.sqrt 2) else 0) +
        (if d = 12 then (-8 : ℝ) / (8 * Real.sqrt 2) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support_far (fun e =>
      if starSlotClass 3 e = d then farDeficitKernel e else 0)
    (fun e h0 h1 h3 h5 h7 h9 => by
      simp [far_kernel_zero_off e h0 h1 h3 h5 h7 h9])]
  simp only [starSlotClass, farDeficitKernel, farCosKernel]
  aesop


theorem fullStarClassKernel_eq (d : Fin 15) :
    fullStarClassKernelAssembled d = fullStarClassKernel d := by
  simp only [fullStarClassKernelAssembled]
  rw [sum4, member0_eval, member1_eval, member2_eval, member3_eval]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  fin_cases d <;> simp [fullStarClassKernel] <;> field_simp <;>
    ring_nf <;> simp only [hs2, pow_two] <;> try ring

theorem fullStarClassKernel_values :
    fullStarClassKernel 0 = -(Real.sqrt 2) / 2 ∧
      fullStarClassKernel 1 = Real.sqrt 2 / 2 ∧
        fullStarClassKernel 5 = -(Real.sqrt 2) / 2 ∧
          fullStarClassKernel 14 = Real.sqrt 2 / 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §6. Gates -/

theorem fullStarClassKernel_nonvacuous : fullStarClassKernel 0 ≠ 0 := by
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp [fullStarClassKernel, hs]

def swap12Mask (m : ℕ) : ℕ :=
  (if Nat.testBit m 0 then 1 else 0) +
    (if Nat.testBit m 1 then 4 else 0) +
      (if Nat.testBit m 2 then 2 else 0) +
        (if Nat.testBit m 3 then 8 else 0)

theorem swap12Mask_bounds (d : Fin 15) :
    0 < swap12Mask (maskOf d) ∧ swap12Mask (maskOf d) ≤ 15 := by
  fin_cases d <;> decide

def swap12Class (d : Fin 15) : Fin 15 :=
  ⟨swap12Mask (maskOf d) - 1, by
    have h := swap12Mask_bounds d
    omega⟩

theorem fullStarClassKernel_swap12 (d : Fin 15) :
    fullStarClassKernel (swap12Class d) = fullStarClassKernel d := by
  fin_cases d <;> rfl

def fullStarDirectional (v : Fin 15 → ℝ) : ℝ :=
  ∑ d : Fin 15, v d * fullStarClassKernel d

private lemma sum15_all (f : Fin 15 → ℝ) :
    (∑ d : Fin 15, f d) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 +
        f 10 + f 11 + f 12 + f 13 + f 14 := by
  rw [show (Finset.univ : Finset (Fin 15)) =
        insert (0 : Fin 15) (insert (1 : Fin 15) (insert (2 : Fin 15)
          (insert (3 : Fin 15) (insert (4 : Fin 15) (insert (5 : Fin 15)
            (insert (6 : Fin 15) (insert (7 : Fin 15) (insert (8 : Fin 15)
              (insert (9 : Fin 15) (insert (10 : Fin 15) (insert (11 : Fin 15)
                (insert (12 : Fin 15) (insert (13 : Fin 15) (insert (14 : Fin 15)
                  (∅ : Finset (Fin 15)))))))))))))))) from by decide]
  simp [Finset.sum_insert]
  ring

theorem fullStar_uniformScale_decoy :
    fullStarDirectional (fun _ => (1 : ℝ)) = Real.sqrt 2 / 2 := by
  simp only [fullStarDirectional]
  rw [sum15_all]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp [fullStarClassKernel]
  field_simp
  ring

theorem fullStar_homothety_stationary :
    fullStarDirectional (fun d => (classWeightNat d : ℝ)) = 0 := by
  simp only [fullStarDirectional]
  rw [sum15_all]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have w0 : classWeightNat 0 = 1 := by decide
  have w1 : classWeightNat 1 = 1 := by decide
  have w2 : classWeightNat 2 = 2 := by decide
  have w3 : classWeightNat 3 = 1 := by decide
  have w4 : classWeightNat 4 = 2 := by decide
  have w5 : classWeightNat 5 = 2 := by decide
  have w6 : classWeightNat 6 = 3 := by decide
  have w7 : classWeightNat 7 = 1 := by decide
  have w8 : classWeightNat 8 = 2 := by decide
  have w9 : classWeightNat 9 = 2 := by decide
  have w10 : classWeightNat 10 = 3 := by decide
  have w11 : classWeightNat 11 = 2 := by decide
  have w12 : classWeightNat 12 = 3 := by decide
  have w13 : classWeightNat 13 = 3 := by decide
  have w14 : classWeightNat 14 = 4 := by decide
  simp [fullStarClassKernel, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9,
    w10, w11, w12, w13, w14]
  field_simp
  ring

/-! ## §7. Status -/

structure Hinge4DStarKernel12Status where
  starEnumerationClosed : Bool
  flatnessGateClosed : Bool
  fullStarClassKernelClosed : Bool
  type21ComplementOrbitOpen : Bool
  otherHingeOrbitsOpen : Bool
  flatHessianAssemblyOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DStarKernel12Status : Hinge4DStarKernel12Status where
  starEnumerationClosed := true
  flatnessGateClosed := true
  fullStarClassKernelClosed := true
  type21ComplementOrbitOpen := true
  otherHingeOrbitsOpen := true
  flatHessianAssemblyOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DStarKernel12Status_flags :
    hinge4DStarKernel12Status.starEnumerationClosed = true ∧
      hinge4DStarKernel12Status.flatnessGateClosed = true ∧
        hinge4DStarKernel12Status.fullStarClassKernelClosed = true ∧
          hinge4DStarKernel12Status.type21ComplementOrbitOpen = true ∧
            hinge4DStarKernel12Status.otherHingeOrbitsOpen = true ∧
              hinge4DStarKernel12Status.flatHessianAssemblyOpen = true ∧
                hinge4DStarKernel12Status.convergesEH4d = false ∧
                  hinge4DStarKernel12Status.gapActionRecovery = false := by
  decide

end

end ReggeHinge4DStarKernel12
end Analysis
end Gravity
end IndisputableMonolith
