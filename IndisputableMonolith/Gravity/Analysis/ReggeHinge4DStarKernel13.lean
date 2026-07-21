import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DDihedralKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D type-(1,3) periodic-lattice star deficit class kernel

QG full-theory campaign, next kernel-checked increment after
`ReggeHinge4DStarKernel` (type `(1,1)` seed orbit) and
`ReggeHinge4DOrbitClassification`.  Imports the Freudenthal incidence
layer, the 15-class stencil, and the Gram-projection cosine calculus;
never redefines their API.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: the type-`(1,3)` triangle hinge with absolute masks
  `{0, e₀, e₀+e₁+e₂+e₃}` = `{0,1,15}` (difference masks `(1,14)`,
  local flat squared lengths `(1,3,4)`) and its **full** periodic
  Freudenthal star.  The complementary type `(3,1)` is related by
  mask complement in the classification layer; transport of this
  kernel to `(3,1)` is **OPEN**.
* This does **not** complete the flat Hessian assembly over all hinges.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (deliverable A)

1. **Star enumeration.** Exactly six Kuhn simplices in the origin unit
   cube contain the hinge; among cube translates in `{-1,0,1}⁴` only
   the origin contains it (decidable search).
2. **Flat cosine multiset.** All six simplices have flat cosine `1/2`,
   from the shared Gram vector of local squared lengths.
3. **Flatness gate.** Star angle sum equals exactly `2π`
   (`6 · arccos(1/2) = 6 · (π/3)`).
4. **All ten coordinate derivatives** via the cleared-denominator
   master lemma at flat values `(N,P,Q) = (8,8,8)`.
5. **Full-star deficit class kernel** on classes
   `(1,3,5,7,9,11,13)` with values
   `(-√3,-√3,+√3,-√3,+√3,+√3,-√3)`.
6. **Gates:** nonvacuity, hinge-fixing transposition `1↔2` of axes
   `{1,2,3}`, uniform-scaling decoy, homothety stationarity exactly `0`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DStarKernel13

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeHinge4DDihedralKernel
open ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Cube translates and star enumeration -/

/-- Candidate unit-cube origins with each coordinate in `{-1,0,1}`,
encoded as `Fin 3` values `0,1,2`.  A vertex with absolute coordinate
`v ∈ {0,1}` lies in the cube of origin-index `o` iff
`o ≤ v+1 ≤ o+1` (equivalently the shifted interval test). -/
abbrev CubeOffset := Fin 3 × Fin 3 × Fin 3 × Fin 3

def offsetAxis : CubeOffset → Fin 4 → Fin 3
  | c, 0 => c.1
  | c, 1 => c.2.1
  | c, 2 => c.2.2.1
  | c, 3 => c.2.2.2

/-- Absolute hinge vertex coordinates in `{0,1}⁴`. -/
def absHingeCoord : Fin 3 → Fin 4 → Fin 2
  | 0, _ => 0
  | 1, 0 => 1
  | 1, _ => 0
  | 2, _ => 1

def axisFits (o : Fin 3) (v : Fin 2) : Bool :=
  decide (o.val ≤ v.val + 1 ∧ v.val + 1 ≤ o.val + 1)

def vertexInCube (c : CubeOffset) (k : Fin 3) : Bool :=
  decide (∀ i : Fin 4, axisFits (offsetAxis c i) (absHingeCoord k i) = true)

def cubeContainsHinge (c : CubeOffset) : Bool :=
  decide (∀ k : Fin 3, vertexInCube c k = true)

def originOffset : CubeOffset :=
  (⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)

theorem cubeContainsHinge_origin : cubeContainsHinge originOffset = true := by
  decide

theorem star_cube_cardinality :
    (Finset.univ.filter (fun c : CubeOffset =>
      cubeContainsHinge c = true)).card = 1 := by
  decide

theorem only_origin_contains_hinge :
    (Finset.univ.filter (fun c : CubeOffset =>
      cubeContainsHinge c = true)) = {originOffset} := by
  decide

/-- Local masks of the type-`(1,3)` hinge in the origin cube. -/
def localHingeMasks : Finset ℕ := {0, 1, 15}


def containsHinge (s : Fin 24) : Bool :=
  decide (∀ m ∈ localHingeMasks, ∃ i : Fin 5, vertexMask s i = m)

def starMembers : List (Fin 24) := [0, 1, 2, 3, 4, 5]

theorem starMembers_length : starMembers.length = 6 := rfl

theorem starMembers_complete (s : Fin 24) :
    containsHinge s = true ↔ s ∈ starMembers := by
  fin_cases s <;> decide

theorem star_cardinality :
    (Finset.univ.filter (fun s : Fin 24 => containsHinge s = true)).card =
      6 := by
  decide

/-! ## §2. Flat squared-length representative (hinge ordered `0,1,15`) -/

/-- Flat local squared edges for every star member after reordering the
five vertices so the hinge occupies slots `(0,1,2)` and the two apexes
follow Freudenthal chain order. -/
def t13FlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 3
  | 5 => 1 | 6 => 2 | 7 => 2 | 8 => 1 | 9 => 1

theorem hingeGramDet_t13 : hingeGramDet t13FlatSqEdges = 12 := by
  norm_num [hingeGramDet, t13FlatSqEdges]
theorem apexDotNum_t13 : apexDotNum t13FlatSqEdges = 8 := by
  norm_num [apexDotNum, hingeGramDet, t13FlatSqEdges]
theorem apex3NormSqNum_t13 : apex3NormSqNum t13FlatSqEdges = 8 := by
  norm_num [apex3NormSqNum, hingeGramDet, t13FlatSqEdges]
theorem apex4NormSqNum_t13 : apex4NormSqNum t13FlatSqEdges = 8 := by
  norm_num [apex4NormSqNum, hingeGramDet, t13FlatSqEdges]

theorem cosDihedral_t13_flat :
    cosDihedral t13FlatSqEdges = (1 / 2 : ℝ) := by
  rw [cos_numForm _ (by rw [hingeGramDet_t13]; norm_num),
    apexDotNum_t13, apex3NormSqNum_t13, apex4NormSqNum_t13]
  rw [show (8 : ℝ) * 8 = 64 by norm_num,
    show Real.sqrt (64 : ℝ) = 8 by
      rw [show (64 : ℝ) = (8 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]]
  norm_num

/-! ## §3. Flatness gate -/

theorem arccos_one_half : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
  have hcos : Real.cos (Real.pi / 3) = (1 / 2 : ℝ) := Real.cos_pi_div_three
  rw [← hcos, Real.arccos_cos (by positivity) (by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith [show Real.pi / 3 ≤ Real.pi from by linarith])]

def flatAngleT13 : ℝ := Real.arccos (1 / 2 : ℝ)

theorem flatAngleT13_eq : flatAngleT13 = Real.pi / 3 := arccos_one_half

def starFlatAngleSum : ℝ := 6 * flatAngleT13

theorem star_flat_angle_sum_two_pi : starFlatAngleSum = 2 * Real.pi := by
  simp only [starFlatAngleSum, flatAngleT13_eq]
  ring

def starFlatCosines : Fin 6 → ℝ := fun _ => (1 / 2 : ℝ)

theorem starFlatCosines_match :
    ∀ m : Fin 6, starFlatCosines m = cosDihedral t13FlatSqEdges := by
  intro m
  simp [starFlatCosines, cosDihedral_t13_flat]

/-! ## §4. Coordinate derivatives (master lemma at `(N,P,Q)=(8,8,8)`) -/

def t13CoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else t13FlatSqEdges j

def t13CosKernel : Fin 10 → ℝ
  | ⟨4, _⟩ => (-1 / 4 : ℝ)
  | ⟨6, _⟩ => (3 / 8 : ℝ)
  | ⟨7, _⟩ => (3 / 8 : ℝ)
  | ⟨9, _⟩ => (-3 / 4 : ℝ)
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

/-- Cleared-denominator master derivative at flat `(N,P,Q)=(8,8,8)`. -/
private lemma hasDerivAt_numForm_t13 {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 8) (hP0 : P t0 = 8) (hQ0 : Q t0 = 8) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      ((2 * N' - P' - Q') / 32) t0 := by
  have hPQ : HasDerivAt (fun t => P t * Q t)
      (P' * Q t0 + P t0 * Q') t0 := hP.mul hQ
  have hPQ0 : P t0 * Q t0 = 64 := by rw [hP0, hQ0]; norm_num
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
  convert hdiv using 1
  have h8 : Real.sqrt (P t0 * Q t0) = 8 := by
    rw [hPQ0, show (64 : ℝ) = (8 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  rw [h8, hN0, hP0, hQ0]
  ring

private lemma hasDerivAt_t13_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (t13CoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (t13CoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (t13CoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (t13CoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 8)
    (hP0 : aP * t0 ^ 2 + bP * t0 + cP = 8)
    (hQ0 : aQ * t0 ^ 2 + bQ * t0 + cQ = 8)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath k t))
      ((2 * (2 * aN * t0 + bN) - (2 * aP * t0 + bP)
        - (2 * aQ * t0 + bQ)) / 32) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain := hasDerivAt_numForm_t13 hN hP hQ hN0 hP0 hQ0
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (t13CoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma t13_path0_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 0 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex3NormSqNum (t13CoordPath 0 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex4NormSqNum (t13CoordPath 0 t) = (-1) * t ^ 2 + (10) * t + (-1)
    ∧ hingeGramDet (t13CoordPath 0 t) = (-1) * t ^ 2 + (14) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path1_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 1 t) = (-2) * t ^ 2 + (16) * t + (-24)
    ∧ apex3NormSqNum (t13CoordPath 1 t) = (-1) * t ^ 2 + (8) * t + (-8)
    ∧ apex4NormSqNum (t13CoordPath 1 t) = (-2) * t ^ 2 + (16) * t + (-24)
    ∧ hingeGramDet (t13CoordPath 1 t) = (-1) * t ^ 2 + (8) * t + (-4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path2_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (t13CoordPath 2 t) = (-3) * t ^ 2 + (12) * t + (-4)
    ∧ apex4NormSqNum (t13CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t13CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path3_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (t13CoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t13CoordPath 3 t) = (-3) * t ^ 2 + (18) * t + (-19)
    ∧ hingeGramDet (t13CoordPath 3 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path4_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 4 t) = (-4) * t ^ 2 + (20) * t + (-16)
    ∧ apex3NormSqNum (t13CoordPath 4 t) = (-2) * t ^ 2 + (12) * t + (-10)
    ∧ apex4NormSqNum (t13CoordPath 4 t) = (-3) * t ^ 2 + (18) * t + (-19)
    ∧ hingeGramDet (t13CoordPath 4 t) = (-1) * t ^ 2 + (10) * t + (-9) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path5_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 5 t) = (0) * t ^ 2 + (4) * t + (4)
    ∧ apex3NormSqNum (t13CoordPath 5 t) = (-4) * t ^ 2 + (16) * t + (-4)
    ∧ apex4NormSqNum (t13CoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t13CoordPath 5 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path6_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 6 t) = (0) * t ^ 2 + (8) * t + (-8)
    ∧ apex3NormSqNum (t13CoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t13CoordPath 6 t) = (-4) * t ^ 2 + (20) * t + (-16)
    ∧ hingeGramDet (t13CoordPath 6 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path7_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 7 t) = (0) * t ^ 2 + (8) * t + (-8)
    ∧ apex3NormSqNum (t13CoordPath 7 t) = (-1) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (t13CoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t13CoordPath 7 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path8_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 8 t) = (0) * t ^ 2 + (4) * t + (4)
    ∧ apex3NormSqNum (t13CoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t13CoordPath 8 t) = (-1) * t ^ 2 + (10) * t + (-1)
    ∧ hingeGramDet (t13CoordPath 8 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

private lemma t13_path9_polys : ∀ t : ℝ,
    apexDotNum (t13CoordPath 9 t) = (0) * t ^ 2 + (-12) * t + (20)
    ∧ apex3NormSqNum (t13CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t13CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t13CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (12) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t13CoordPath, t13FlatSqEdges] <;> ring

theorem hasDerivAt_t13_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 0 t)) 0 1 := by
  have h := hasDerivAt_t13_slot 0 1 (-2) (12) (-2) (-2) (12) (-2)
    (-1) (10) (-1) (-1) (14) (-1) t13_path0_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 1 t)) 0 4 := by
  have h := hasDerivAt_t13_slot 1 4 (-2) (16) (-24) (-1) (8) (-8)
    (-2) (16) (-24) (-1) (8) (-4) t13_path1_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 2 t)) 0 2 := by
  have h := hasDerivAt_t13_slot 2 2 (0) (0) (8) (-3) (12) (-4)
    (0) (0) (8) (0) (0) (12) t13_path2_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 3 t)) 0 3 := by
  have h := hasDerivAt_t13_slot 3 3 (0) (0) (8) (0) (0) (8)
    (-3) (18) (-19) (0) (0) (12) t13_path3_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 4 t))
      ((-1 / 4 : ℝ)) 3 := by
  have h := hasDerivAt_t13_slot 4 3 (-4) (20) (-16) (-2) (12) (-10)
    (-3) (18) (-19) (-1) (10) (-9) t13_path4_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 5 t)) 0 1 := by
  have h := hasDerivAt_t13_slot 5 1 (0) (4) (4) (-4) (16) (-4)
    (0) (0) (8) (0) (0) (12) t13_path5_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 6 t))
      ((3 / 8 : ℝ)) 2 := by
  have h := hasDerivAt_t13_slot 6 2 (0) (8) (-8) (0) (0) (8)
    (-4) (20) (-16) (0) (0) (12) t13_path6_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 7 t))
      ((3 / 8 : ℝ)) 2 := by
  have h := hasDerivAt_t13_slot 7 2 (0) (8) (-8) (-1) (8) (-4)
    (0) (0) (8) (0) (0) (12) t13_path7_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 8 t)) 0 1 := by
  have h := hasDerivAt_t13_slot 8 1 (0) (4) (4) (0) (0) (8)
    (-1) (10) (-1) (0) (0) (12) t13_path8_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath 9 t))
      ((-3 / 4 : ℝ)) 1 := by
  have h := hasDerivAt_t13_slot 9 1 (0) (-12) (20) (0) (0) (8)
    (0) (0) (8) (0) (0) (12) t13_path9_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t13_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (t13CoordPath k t))
      (t13CosKernel k) (t13FlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_t13_slot0
  · exact hasDerivAt_t13_slot1
  · exact hasDerivAt_t13_slot2
  · exact hasDerivAt_t13_slot3
  · exact hasDerivAt_t13_slot4
  · exact hasDerivAt_t13_slot5
  · exact hasDerivAt_t13_slot6
  · exact hasDerivAt_t13_slot7
  · exact hasDerivAt_t13_slot8
  · exact hasDerivAt_t13_slot9

/-! ## §5. Deficit kernels and class assembly -/

/-- Chain factor `-1/sin` at flat cosine `1/2` (`sin = √3/2`). -/
def chainT13 : ℝ := - (2 / Real.sqrt 3)

theorem chainT13_eq : chainT13 = - (2 * Real.sqrt 3 / 3) := by
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  simp only [chainT13]
  field_simp [hs]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

def t13DeficitKernel : Fin 10 → ℝ
  | ⟨4, _⟩ => - (Real.sqrt 3) / 6
  | ⟨6, _⟩ => Real.sqrt 3 / 4
  | ⟨7, _⟩ => Real.sqrt 3 / 4
  | ⟨9, _⟩ => - (Real.sqrt 3) / 2
  | _ => 0

theorem t13DeficitKernel_eq_chain (k : Fin 10) :
    t13DeficitKernel k = -chainT13 * t13CosKernel k := by
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs3 : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases k <;>
    (simp only [t13DeficitKernel, chainT13, t13CosKernel]
     try field_simp [hs]
     try simp [hs3]
     try ring)

/-- Local-slot → 15-class map for each of the six star members, after
reordering vertices so the hinge is `(0,1,15)` and apexes follow the
Freudenthal chain. -/
def starSlotClass : Fin 6 → Fin 10 → Fin 15
  | 0, 0 => 0 | 0, 1 => 14 | 0, 2 => 2 | 0, 3 => 6 | 0, 4 => 13
  | 0, 5 => 1 | 0, 6 => 5 | 0, 7 => 11 | 0, 8 => 7 | 0, 9 => 3
  | 1, 0 => 0 | 1, 1 => 14 | 1, 2 => 2 | 1, 3 => 10 | 1, 4 => 13
  | 1, 5 => 1 | 1, 6 => 9 | 1, 7 => 11 | 1, 8 => 3 | 1, 9 => 7
  | 2, 0 => 0 | 2, 1 => 14 | 2, 2 => 4 | 2, 3 => 6 | 2, 4 => 13
  | 2, 5 => 3 | 2, 6 => 5 | 2, 7 => 9 | 2, 8 => 7 | 2, 9 => 1
  | 3, 0 => 0 | 3, 1 => 14 | 3, 2 => 4 | 3, 3 => 12 | 3, 4 => 13
  | 3, 5 => 3 | 3, 6 => 11 | 3, 7 => 9 | 3, 8 => 1 | 3, 9 => 7
  | 4, 0 => 0 | 4, 1 => 14 | 4, 2 => 8 | 4, 3 => 10 | 4, 4 => 13
  | 4, 5 => 7 | 4, 6 => 9 | 4, 7 => 5 | 4, 8 => 3 | 4, 9 => 1
  | 5, 0 => 0 | 5, 1 => 14 | 5, 2 => 8 | 5, 3 => 12 | 5, 4 => 13
  | 5, 5 => 7 | 5, 6 => 11 | 5, 7 => 5 | 5, 8 => 1 | 5, 9 => 3

def assembleStarMember (m : Fin 6) : Fin 15 → ℝ :=
  fun d => ∑ e : Fin 10,
    if starSlotClass m e = d then t13DeficitKernel e else 0

def fullStarClassKernelAssembled : Fin 15 → ℝ :=
  fun d => ∑ m : Fin 6, assembleStarMember m d

def fullStarClassKernel : Fin 15 → ℝ
  | ⟨1, _⟩ => - Real.sqrt 3
  | ⟨3, _⟩ => - Real.sqrt 3
  | ⟨5, _⟩ => Real.sqrt 3
  | ⟨7, _⟩ => - Real.sqrt 3
  | ⟨9, _⟩ => Real.sqrt 3
  | ⟨11, _⟩ => Real.sqrt 3
  | ⟨13, _⟩ => - Real.sqrt 3
  | _ => 0

private lemma sum_support4_4679 (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e ≠ 4 → e ≠ 6 → e ≠ 7 → e ≠ 9 → f e = 0) :
    (∑ e : Fin 10, f e) = f 4 + f 6 + f 7 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (4 : Fin 10) (insert (6 : Fin 10)
          (insert (7 : Fin 10) (insert (9 : Fin 10)
            ({0, 1, 2, 3, 5, 8} : Finset (Fin 10))))) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => by
      fin_cases e <;> simp at he ⊢ <;>
        exact hz _ (by decide) (by decide) (by decide) (by decide))]
  abel

private lemma deficit_zero_off (e : Fin 10)
    (h4 : e ≠ 4) (h6 : e ≠ 6) (h7 : e ≠ 7) (h9 : e ≠ 9) :
    t13DeficitKernel e = 0 := by
  fin_cases e <;> first | rfl | contradiction

private lemma member_eval (m : Fin 6) (d : Fin 15) :
    assembleStarMember m d =
      (if starSlotClass m 4 = d then t13DeficitKernel 4 else 0) +
        (if starSlotClass m 6 = d then t13DeficitKernel 6 else 0) +
          (if starSlotClass m 7 = d then t13DeficitKernel 7 else 0) +
            (if starSlotClass m 9 = d then t13DeficitKernel 9 else 0) := by
  simp only [assembleStarMember]
  exact sum_support4_4679 (fun e =>
      if starSlotClass m e = d then t13DeficitKernel e else 0)
    (fun e h4 h6 h7 h9 => by simp [deficit_zero_off e h4 h6 h7 h9])

private lemma sum6 (f : Fin 6 → ℝ) :
    (∑ m : Fin 6, f m) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [show (Finset.univ : Finset (Fin 6)) =
        insert (0 : Fin 6) (insert (1 : Fin 6) (insert (2 : Fin 6)
          (insert (3 : Fin 6) (insert (4 : Fin 6) (insert (5 : Fin 6)
            (∅ : Finset (Fin 6))))))) from by decide]
  simp [Finset.sum_insert]
  ring

private lemma member0_closed (d : Fin 15) :
    assembleStarMember 0 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 5 then Real.sqrt 3 / 4 else 0) +
          (if d = 11 then Real.sqrt 3 / 4 else 0) +
            (if d = 3 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

private lemma member1_closed (d : Fin 15) :
    assembleStarMember 1 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 9 then Real.sqrt 3 / 4 else 0) +
          (if d = 11 then Real.sqrt 3 / 4 else 0) +
            (if d = 7 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

private lemma member2_closed (d : Fin 15) :
    assembleStarMember 2 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 5 then Real.sqrt 3 / 4 else 0) +
          (if d = 9 then Real.sqrt 3 / 4 else 0) +
            (if d = 1 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

private lemma member3_closed (d : Fin 15) :
    assembleStarMember 3 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 11 then Real.sqrt 3 / 4 else 0) +
          (if d = 9 then Real.sqrt 3 / 4 else 0) +
            (if d = 7 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

private lemma member4_closed (d : Fin 15) :
    assembleStarMember 4 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 9 then Real.sqrt 3 / 4 else 0) +
          (if d = 5 then Real.sqrt 3 / 4 else 0) +
            (if d = 1 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

private lemma member5_closed (d : Fin 15) :
    assembleStarMember 5 d =
      (if d = 13 then - (Real.sqrt 3) / 6 else 0) +
        (if d = 11 then Real.sqrt 3 / 4 else 0) +
          (if d = 5 then Real.sqrt 3 / 4 else 0) +
            (if d = 3 then - (Real.sqrt 3) / 2 else 0) := by
  rw [member_eval]
  simp only [starSlotClass, t13DeficitKernel]
  aesop

theorem fullStarClassKernel_eq (d : Fin 15) :
    fullStarClassKernelAssembled d = fullStarClassKernel d := by
  simp only [fullStarClassKernelAssembled]
  rw [sum6, member0_closed, member1_closed, member2_closed,
    member3_closed, member4_closed, member5_closed]
  fin_cases d <;> simp [fullStarClassKernel] <;> ring


theorem fullStarClassKernel_values :
    fullStarClassKernel 1 = - Real.sqrt 3 ∧
      fullStarClassKernel 3 = - Real.sqrt 3 ∧
        fullStarClassKernel 5 = Real.sqrt 3 ∧
          fullStarClassKernel 7 = - Real.sqrt 3 ∧
            fullStarClassKernel 9 = Real.sqrt 3 ∧
              fullStarClassKernel 11 = Real.sqrt 3 ∧
                fullStarClassKernel 13 = - Real.sqrt 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fullStarClassKernel_zero_off (d : Fin 15)
    (h1 : d ≠ 1) (h3 : d ≠ 3) (h5 : d ≠ 5) (h7 : d ≠ 7)
    (h9 : d ≠ 9) (h11 : d ≠ 11) (h13 : d ≠ 13) :
    fullStarClassKernel d = 0 := by
  fin_cases d <;> first | rfl | contradiction

/-! ## §6. Gates -/

theorem fullStarClassKernel_nonvacuous : fullStarClassKernel 5 ≠ 0 := by
  change Real.sqrt 3 ≠ 0
  exact Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)

/-- Axis swap `1 ↔ 2` (bits 1 and 2); an S₃ generator fixing the hinge
vertex set `{0,1,15}`. -/
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

/-- Explicit table for `swap12Class` (kernel-decidable). -/
def swap12ClassTable : Fin 15 → Fin 15
  | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2
  | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 11
  | 10 => 12 | 11 => 9 | 12 => 10 | 13 => 13 | 14 => 14

theorem swap12Class_eq_table (d : Fin 15) :
    swap12Class d = swap12ClassTable d := by
  fin_cases d <;> decide

theorem fullStarClassKernel_swap12 (d : Fin 15) :
    fullStarClassKernel (swap12Class d) = fullStarClassKernel d := by
  rw [swap12Class_eq_table]
  fin_cases d <;> simp [fullStarClassKernel, swap12ClassTable]

def fullStarDirectional (v : Fin 15 → ℝ) : ℝ :=
  ∑ d : Fin 15, v d * fullStarClassKernel d

private lemma sum15_support (f : Fin 15 → ℝ)
    (hz : ∀ d : Fin 15, d ≠ 1 → d ≠ 3 → d ≠ 5 → d ≠ 7 → d ≠ 9 → d ≠ 11 →
      d ≠ 13 → f d = 0) :
    (∑ d : Fin 15, f d) =
      f 1 + f 3 + f 5 + f 7 + f 9 + f 11 + f 13 := by
  classical
  have hrest :
      ∑ d ∈ ({0, 2, 4, 6, 8, 10, 12, 14} : Finset (Fin 15)), f d = 0 := by
    refine Finset.sum_eq_zero ?_
    intro d hd
    have : d = 0 ∨ d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8 ∨ d = 10 ∨ d = 12 ∨
        d = 14 := by
      fin_cases d <;> simp at hd ⊢
    rcases this with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact hz _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  rw [show (Finset.univ : Finset (Fin 15)) =
        insert (1 : Fin 15) (insert (3 : Fin 15) (insert (5 : Fin 15)
          (insert (7 : Fin 15) (insert (9 : Fin 15) (insert (11 : Fin 15)
            (insert (13 : Fin 15)
              ({0, 2, 4, 6, 8, 10, 12, 14} : Finset (Fin 15))))))))
        from by decide]
  simp [Finset.sum_insert, hrest]
  ring

theorem fullStar_uniformScale_decoy :
    fullStarDirectional (fun _ => (1 : ℝ)) = - Real.sqrt 3 := by
  simp only [fullStarDirectional]
  rw [sum15_support _ (fun d h1 h3 h5 h7 h9 h11 h13 => by
    rw [fullStarClassKernel_zero_off d h1 h3 h5 h7 h9 h11 h13, mul_zero])]
  simp [fullStarClassKernel]

theorem fullStar_homothety_stationary :
    fullStarDirectional (fun d => (classWeightNat d : ℝ)) = 0 := by
  simp only [fullStarDirectional]
  rw [sum15_support _ (fun d h1 h3 h5 h7 h9 h11 h13 => by
    rw [fullStarClassKernel_zero_off d h1 h3 h5 h7 h9 h11 h13, mul_zero])]
  have w1 : classWeightNat 1 = 1 := by decide
  have w3 : classWeightNat 3 = 1 := by decide
  have w5 : classWeightNat 5 = 2 := by decide
  have w7 : classWeightNat 7 = 1 := by decide
  have w9 : classWeightNat 9 = 2 := by decide
  have w11 : classWeightNat 11 = 2 := by decide
  have w13 : classWeightNat 13 = 3 := by decide
  simp [fullStarClassKernel, w1, w3, w5, w7, w9, w11, w13]
  ring

/-! ## §7. Status -/

structure Hinge4DStarKernel13Status where
  starEnumerationClosed : Bool
  flatnessGateClosed : Bool
  fullStarClassKernelClosed : Bool
  type31TransportOpen : Bool
  flatHessianAssemblyOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DStarKernel13Status : Hinge4DStarKernel13Status where
  starEnumerationClosed := true
  flatnessGateClosed := true
  fullStarClassKernelClosed := true
  type31TransportOpen := true
  flatHessianAssemblyOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DStarKernel13Status_flags :
    hinge4DStarKernel13Status.starEnumerationClosed = true ∧
      hinge4DStarKernel13Status.flatnessGateClosed = true ∧
        hinge4DStarKernel13Status.fullStarClassKernelClosed = true ∧
          hinge4DStarKernel13Status.type31TransportOpen = true ∧
            hinge4DStarKernel13Status.flatHessianAssemblyOpen = true ∧
              hinge4DStarKernel13Status.convergesEH4d = false ∧
                hinge4DStarKernel13Status.gapActionRecovery = false := by
  decide

/-! ## §8. Axiom audit (embedded; shared `.lake` symlink emits no olean) -/

#print axioms cubeContainsHinge_origin
#print axioms star_cube_cardinality
#print axioms only_origin_contains_hinge
#print axioms starMembers_length
#print axioms starMembers_complete
#print axioms star_cardinality
#print axioms cosDihedral_t13_flat
#print axioms arccos_one_half
#print axioms star_flat_angle_sum_two_pi
#print axioms starFlatCosines_match
#print axioms hasDerivAt_t13_coord
#print axioms chainT13_eq
#print axioms t13DeficitKernel_eq_chain
#print axioms swap12Class_eq_table
#print axioms fullStarClassKernel_eq
#print axioms fullStarClassKernel_values
#print axioms fullStarClassKernel_zero_off
#print axioms fullStarClassKernel_nonvacuous
#print axioms fullStarClassKernel_swap12
#print axioms fullStar_uniformScale_decoy
#print axioms fullStar_homothety_stationary
#print axioms hinge4DStarKernel13Status_flags

end

end ReggeHinge4DStarKernel13
end Analysis
end Gravity
end IndisputableMonolith
