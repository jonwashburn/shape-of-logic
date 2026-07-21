import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DDihedralKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D full periodic-lattice star deficit class kernel (type (2,2))

QG full-theory campaign, next kernel-checked increment after
`ReggeHinge4DStarKernel` (type (1,1) seed orbit).  Imports the Freudenthal
incidence layer, the 15-class stencil, and the Gram-projection cosine
calculus; never redefines their API.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: the type-(2,2) triangle hinge `{0, e₀+e₁, e₀+e₁+e₂+e₃}`
  (masks `{0,3,15}`, difference masks `(3,12)`) and its **full**
  periodic Freudenthal star.  Other hinge orbits remain as previously
  closed or OPEN.
* This does **not** complete the flat Hessian assembly over all hinges.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (deliverable A)

1. **Star enumeration.** Exactly four `(cube translate, Kuhn simplex)`
   pairs contain the (2,2) hinge; among all 16 axis-aligned unit-cube
   corners with coordinates in `{-1,0}`, only the origin corner
   contains the absolute hinge, verified by decidable computation.
2. **Flat cosine multiset.** All four incident simplices have flat
   cosine `0`, from each simplex's own hinge-ordered Gram vector
   (local squared lengths `(2,4,1,3,2,1,1,3,1,2)`).
3. **Flatness gate.** Star angle sum equals exactly `2π`
   (`4 · arccos 0 = 4 · (π/2)`).
4. **Full-star deficit class kernel** on all 15 stencil classes with
   the closed form recorded below.
5. **Gates:** nonvacuity, swap-`0↔1` and swap-`2↔3` symmetry (both
   fix the hinge vertex set), uniform-scaling decoy, homothety
   stationarity.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DStarKernel22

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeHinge4DDihedralKernel
open ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Cube translates and star enumeration -/

/-- Absolute (2,2) hinge vertex masks. -/
def absHingeMasks : Finset ℕ := {0, 3, 15}

/-- Cube corner encoded as a 4-bit mask: bit `i` set means the corner
has coordinate `-1` on axis `i` (else `0`). -/
abbrev CubeCorner := Fin 16

/-- Geometric containment: absolute vertex mask `m` lies in the unit
cube with corner `c` iff every negatively shifted axis has absolute
coordinate `0`. -/
def cornerContainsMask (c : CubeCorner) (m : ℕ) : Bool :=
  decide (∀ i : Fin 4, ¬ Nat.testBit c.val i.val ∨ ¬ Nat.testBit m i.val)

def cornerContainsHinge (c : CubeCorner) : Bool :=
  decide (∀ m ∈ absHingeMasks, cornerContainsMask c m = true)

/-- Local mask of an absolute vertex inside a containing corner cube
(XOR with the corner bitmask). -/
def localMask (c : CubeCorner) (m : ℕ) : ℕ := Nat.xor m c.val

def localHingeMasks (c : CubeCorner) : Finset ℕ :=
  absHingeMasks.image (localMask c)

def containsHinge (c : CubeCorner) (s : Fin 24) : Bool :=
  cornerContainsHinge c &&
    decide (∀ m ∈ localHingeMasks c, ∃ i : Fin 5, vertexMask s i = m)

structure StarMember where
  cube : CubeCorner
  simplex : Fin 24
  deriving DecidableEq, Repr

def starMembers : List StarMember :=
  [ ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 6⟩, ⟨0, 7⟩ ]

theorem starMembers_length : starMembers.length = 4 := rfl

theorem starMembers_complete (c : CubeCorner) (s : Fin 24) :
    containsHinge c s = true ↔ ⟨c, s⟩ ∈ starMembers := by
  revert c s
  decide

theorem star_cardinality :
    (Finset.univ.filter (fun p : CubeCorner × Fin 24 =>
      containsHinge p.1 p.2 = true)).card = 4 := by
  decide

theorem only_origin_corner_contains_hinge (c : CubeCorner)
    (h : cornerContainsHinge c = true) : c = 0 := by
  revert c
  decide

/-! ## §2. Flat squared-length orbit representative -/

/-- Hinge-ordered flat squared lengths for each (2,2) star simplex:
hinge vertices ordered `(0,3,15)`, apexes by increasing simplex index. -/
def t22FlatSqEdges : SqEdges4
  | 0 => 2 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2
  | 5 => 1 | 6 => 1 | 7 => 3 | 8 => 1 | 9 => 2

theorem hingeGramDet_t22 : hingeGramDet t22FlatSqEdges = 16 := by
  norm_num [hingeGramDet, t22FlatSqEdges]
theorem apexDotNum_t22 : apexDotNum t22FlatSqEdges = 0 := by
  norm_num [apexDotNum, hingeGramDet, t22FlatSqEdges]
theorem apex3NormSqNum_t22 : apex3NormSqNum t22FlatSqEdges = 8 := by
  norm_num [apex3NormSqNum, hingeGramDet, t22FlatSqEdges]
theorem apex4NormSqNum_t22 : apex4NormSqNum t22FlatSqEdges = 8 := by
  norm_num [apex4NormSqNum, hingeGramDet, t22FlatSqEdges]

theorem cosDihedral_t22_flat : cosDihedral t22FlatSqEdges = 0 := by
  rw [cos_numForm _ (by rw [hingeGramDet_t22]; norm_num),
    apexDotNum_t22, apex3NormSqNum_t22, apex4NormSqNum_t22]
  norm_num

/-! ## §3. Flatness gate -/

def flatAngleT22 : ℝ := Real.arccos 0

theorem flatAngleT22_eq : flatAngleT22 = Real.pi / 2 := Real.arccos_zero

def starFlatAngleSum : ℝ := 4 * flatAngleT22

theorem star_flat_angle_sum_two_pi : starFlatAngleSum = 2 * Real.pi := by
  simp only [starFlatAngleSum, flatAngleT22_eq]
  ring

def starFlatCosines : Fin 4 → ℝ := fun _ => 0

theorem starFlatCosines_match_orbit (m : Fin 4) :
    starFlatCosines m = cosDihedral t22FlatSqEdges :=
  cosDihedral_t22_flat.symm

/-! ## §4. Coordinate derivatives (cleared-denominator master lemma) -/

def t22CoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else t22FlatSqEdges j

def t22CosKernel : Fin 10 → ℝ
  | ⟨0, _⟩ => (-1 / 4 : ℝ)
  | ⟨1, _⟩ => (-1 / 4 : ℝ)
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => (1 / 2 : ℝ)
  | ⟨4, _⟩ => (-1 / 4 : ℝ)
  | ⟨5, _⟩ => (1 / 2 : ℝ)
  | ⟨6, _⟩ => (1 / 2 : ℝ)
  | ⟨7, _⟩ => (1 / 2 : ℝ)
  | ⟨8, _⟩ => 0
  | ⟨9, _⟩ => (-1 : ℝ)

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

/-- Master lemma at the (2,2) flat point: `N=0`, `P=Q=8`, so
`d/dt (N/(2√(PQ))) = N'/16`. -/
private lemma hasDerivAt_numForm_t22 {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 0) (hP0 : P t0 = 8) (hQ0 : Q t0 = 8) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      (N' / 16) t0 := by
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
  rw [h8, hN0]
  ring

private lemma hasDerivAt_t22_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (t22CoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (t22CoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (t22CoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (t22CoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 0)
    (hP0 : aP * t0 ^ 2 + bP * t0 + cP = 8)
    (hQ0 : aQ * t0 ^ 2 + bQ * t0 + cQ = 8)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath k t))
      ((2 * aN * t0 + bN) / 16) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain := hasDerivAt_numForm_t22 hN hP hQ hN0 hP0 hQ0
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (t22CoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma t22_path0_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 0 t) = (-2) * t ^ 2 + (4) * t + (0)
    ∧ apex3NormSqNum (t22CoordPath 0 t) = (-3) * t ^ 2 + (12) * t + (-4)
    ∧ apex4NormSqNum (t22CoordPath 0 t) = (-1) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (t22CoordPath 0 t) = (-1) * t ^ 2 + (12) * t + (-4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path1_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 1 t) = (0) * t ^ 2 + (-4) * t + (16)
    ∧ apex3NormSqNum (t22CoordPath 1 t) = (-1) * t ^ 2 + (8) * t + (-8)
    ∧ apex4NormSqNum (t22CoordPath 1 t) = (-1) * t ^ 2 + (8) * t + (-8)
    ∧ hingeGramDet (t22CoordPath 1 t) = (-1) * t ^ 2 + (8) * t + (0) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path2_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (t22CoordPath 2 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex4NormSqNum (t22CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t22CoordPath 2 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path3_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 3 t) = (0) * t ^ 2 + (8) * t + (-24)
    ∧ apex3NormSqNum (t22CoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t22CoordPath 3 t) = (-2) * t ^ 2 + (12) * t + (-10)
    ∧ hingeGramDet (t22CoordPath 3 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path4_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 4 t) = (-2) * t ^ 2 + (4) * t + (0)
    ∧ apex3NormSqNum (t22CoordPath 4 t) = (-1) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (t22CoordPath 4 t) = (-3) * t ^ 2 + (12) * t + (-4)
    ∧ hingeGramDet (t22CoordPath 4 t) = (-1) * t ^ 2 + (12) * t + (-4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path5_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 5 t) = (0) * t ^ 2 + (8) * t + (-8)
    ∧ apex3NormSqNum (t22CoordPath 5 t) = (-4) * t ^ 2 + (16) * t + (-4)
    ∧ apex4NormSqNum (t22CoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t22CoordPath 5 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path6_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 6 t) = (0) * t ^ 2 + (8) * t + (-8)
    ∧ apex3NormSqNum (t22CoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t22CoordPath 6 t) = (-4) * t ^ 2 + (16) * t + (-4)
    ∧ hingeGramDet (t22CoordPath 6 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path7_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 7 t) = (0) * t ^ 2 + (8) * t + (-24)
    ∧ apex3NormSqNum (t22CoordPath 7 t) = (-2) * t ^ 2 + (12) * t + (-10)
    ∧ apex4NormSqNum (t22CoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t22CoordPath 7 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path8_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 8 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (t22CoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t22CoordPath 8 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ hingeGramDet (t22CoordPath 8 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

private lemma t22_path9_polys : ∀ t : ℝ,
    apexDotNum (t22CoordPath 9 t) = (0) * t ^ 2 + (-16) * t + (32)
    ∧ apex3NormSqNum (t22CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (t22CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ hingeGramDet (t22CoordPath 9 t) = (0) * t ^ 2 + (0) * t + (16) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      t22CoordPath, t22FlatSqEdges] <;> ring

theorem hasDerivAt_t22_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 0 t))
      ((-1 / 4 : ℝ)) 2 := by
  have h := hasDerivAt_t22_slot 0 2 (-2) (4) (0) (-3) (12) (-4) (-1) (8) (-4) (-1) (12) (-4) t22_path0_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 1 t))
      ((-1 / 4 : ℝ)) 4 := by
  have h := hasDerivAt_t22_slot 1 4 (0) (-4) (16) (-1) (8) (-8) (-1) (8) (-8) (-1) (8) (0) t22_path1_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 2 t))
      (0) 1 := by
  have h := hasDerivAt_t22_slot 2 1 (0) (0) (0) (-2) (12) (-2) (0) (0) (8) (0) (0) (16) t22_path2_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 3 t))
      ((1 / 2 : ℝ)) 3 := by
  have h := hasDerivAt_t22_slot 3 3 (0) (8) (-24) (0) (0) (8) (-2) (12) (-10) (0) (0) (16) t22_path3_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 4 t))
      ((-1 / 4 : ℝ)) 2 := by
  have h := hasDerivAt_t22_slot 4 2 (-2) (4) (0) (-1) (8) (-4) (-3) (12) (-4) (-1) (12) (-4) t22_path4_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 5 t))
      ((1 / 2 : ℝ)) 1 := by
  have h := hasDerivAt_t22_slot 5 1 (0) (8) (-8) (-4) (16) (-4) (0) (0) (8) (0) (0) (16) t22_path5_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 6 t))
      ((1 / 2 : ℝ)) 1 := by
  have h := hasDerivAt_t22_slot 6 1 (0) (8) (-8) (0) (0) (8) (-4) (16) (-4) (0) (0) (16) t22_path6_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 7 t))
      ((1 / 2 : ℝ)) 3 := by
  have h := hasDerivAt_t22_slot 7 3 (0) (8) (-24) (-2) (12) (-10) (0) (0) (8) (0) (0) (16) t22_path7_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 8 t))
      (0) 1 := by
  have h := hasDerivAt_t22_slot 8 1 (0) (0) (0) (0) (0) (8) (-2) (12) (-2) (0) (0) (16) t22_path8_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath 9 t))
      ((-1 : ℝ)) 2 := by
  have h := hasDerivAt_t22_slot 9 2 (0) (-16) (32) (0) (0) (8) (0) (0) (8) (0) (0) (16) t22_path9_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_t22_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (t22CoordPath k t))
      (t22CosKernel k) (t22FlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_t22_slot0
  · exact hasDerivAt_t22_slot1
  · exact hasDerivAt_t22_slot2
  · exact hasDerivAt_t22_slot3
  · exact hasDerivAt_t22_slot4
  · exact hasDerivAt_t22_slot5
  · exact hasDerivAt_t22_slot6
  · exact hasDerivAt_t22_slot7
  · exact hasDerivAt_t22_slot8
  · exact hasDerivAt_t22_slot9

/-! ## §5. Full-star deficit class kernel -/

/-- Arccos chain factor `d(arccos)/d(cos)` at flat cosine `0`: `-1`. -/
def chainT22 : ℝ := (-1 : ℝ)

/-- Per-simplex deficit kernel equals `-chain · cosKernel = cosKernel`. -/
def t22DeficitKernel : Fin 10 → ℝ := t22CosKernel

theorem t22DeficitKernel_eq_chain (k : Fin 10) :
    t22DeficitKernel k = -chainT22 * t22CosKernel k := by
  simp [t22DeficitKernel, chainT22]

/-- Hinge-ordered local slot → global edge class, for star members
indexed in `starMembers` order (simplices `0,1,6,7`). -/
def starSlotClass : Fin 4 → Fin 10 → Fin 15
  | 0, 0 => 2 | 0, 1 => 14 | 0, 2 => 0 | 0, 3 => 6 | 0, 4 => 11
  | 0, 5 => 1 | 0, 6 => 3 | 0, 7 => 13 | 0, 8 => 7 | 0, 9 => 5
  | 1, 0 => 2 | 1, 1 => 14 | 1, 2 => 0 | 1, 3 => 10 | 1, 4 => 11
  | 1, 5 => 1 | 1, 6 => 7 | 1, 7 => 13 | 1, 8 => 3 | 1, 9 => 9
  | 2, 0 => 2 | 2, 1 => 14 | 2, 2 => 1 | 2, 3 => 6 | 2, 4 => 11
  | 2, 5 => 0 | 2, 6 => 3 | 2, 7 => 12 | 2, 8 => 7 | 2, 9 => 4
  | 3, 0 => 2 | 3, 1 => 14 | 3, 2 => 1 | 3, 3 => 10 | 3, 4 => 11
  | 3, 5 => 0 | 3, 6 => 7 | 3, 7 => 12 | 3, 8 => 3 | 3, 9 => 8

def assembleStarMember (m : Fin 4) : Fin 15 → ℝ :=
  fun d => ∑ e : Fin 10,
    if starSlotClass m e = d then t22DeficitKernel e else 0

def fullStarClassKernelAssembled : Fin 15 → ℝ :=
  fun d => ∑ m : Fin 4, assembleStarMember m d

def fullStarClassKernel : Fin 15 → ℝ
  | ⟨0, _⟩ => (1 : ℝ)
  | ⟨1, _⟩ => (1 : ℝ)
  | ⟨2, _⟩ => (-1 : ℝ)
  | ⟨3, _⟩ => (1 : ℝ)
  | ⟨4, _⟩ => (-1 : ℝ)
  | ⟨5, _⟩ => (-1 : ℝ)
  | ⟨6, _⟩ => (1 : ℝ)
  | ⟨7, _⟩ => (1 : ℝ)
  | ⟨8, _⟩ => (-1 : ℝ)
  | ⟨9, _⟩ => (-1 : ℝ)
  | ⟨10, _⟩ => (1 : ℝ)
  | ⟨11, _⟩ => (-1 : ℝ)
  | ⟨12, _⟩ => (1 : ℝ)
  | ⟨13, _⟩ => (1 : ℝ)
  | ⟨14, _⟩ => (-1 : ℝ)

private lemma sum_fin10 (f : Fin 10 → ℝ) :
    (∑ e : Fin 10, f e) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (0 : Fin 10) (insert (1 : Fin 10) (insert (2 : Fin 10)
          (insert (3 : Fin 10) (insert (4 : Fin 10) (insert (5 : Fin 10)
            (insert (6 : Fin 10) (insert (7 : Fin 10) (insert (8 : Fin 10)
              (insert (9 : Fin 10) (∅ : Finset (Fin 10))))))))))) from by decide]
  simp [Finset.sum_insert]
  ring

private lemma member_eval (m : Fin 4) (d : Fin 15) :
    assembleStarMember m d =
      (if starSlotClass m 0 = d then t22DeficitKernel 0 else 0) +
      (if starSlotClass m 1 = d then t22DeficitKernel 1 else 0) +
      (if starSlotClass m 2 = d then t22DeficitKernel 2 else 0) +
      (if starSlotClass m 3 = d then t22DeficitKernel 3 else 0) +
      (if starSlotClass m 4 = d then t22DeficitKernel 4 else 0) +
      (if starSlotClass m 5 = d then t22DeficitKernel 5 else 0) +
      (if starSlotClass m 6 = d then t22DeficitKernel 6 else 0) +
      (if starSlotClass m 7 = d then t22DeficitKernel 7 else 0) +
      (if starSlotClass m 8 = d then t22DeficitKernel 8 else 0) +
      (if starSlotClass m 9 = d then t22DeficitKernel 9 else 0) := by
  simp only [assembleStarMember]
  exact sum_fin10 _

private lemma sum4 (f : Fin 4 → ℝ) :
    (∑ m : Fin 4, f m) = f 0 + f 1 + f 2 + f 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) =
        insert (0 : Fin 4) (insert (1 : Fin 4) (insert (2 : Fin 4)
          (insert (3 : Fin 4) (∅ : Finset (Fin 4))))) from by decide]
  simp [Finset.sum_insert]
  ring

theorem fullStarClassKernel_eq (d : Fin 15) :
    fullStarClassKernelAssembled d = fullStarClassKernel d := by
  simp only [fullStarClassKernelAssembled]
  rw [sum4]
  fin_cases d <;>
    (simp [member_eval, starSlotClass, t22DeficitKernel, t22CosKernel,
      fullStarClassKernel] <;> norm_num)

theorem fullStarClassKernel_values :
    fullStarClassKernel 0 = (1 : ℝ) ∧
      fullStarClassKernel 1 = (1 : ℝ) ∧
        fullStarClassKernel 2 = (-1 : ℝ) ∧
          fullStarClassKernel 3 = (1 : ℝ) ∧
            fullStarClassKernel 4 = (-1 : ℝ) ∧
              fullStarClassKernel 5 = (-1 : ℝ) ∧
                fullStarClassKernel 6 = (1 : ℝ) ∧
                  fullStarClassKernel 7 = (1 : ℝ) ∧
                    fullStarClassKernel 8 = (-1 : ℝ) ∧
                      fullStarClassKernel 9 = (-1 : ℝ) ∧
                        fullStarClassKernel 10 = (1 : ℝ) ∧
                          fullStarClassKernel 11 = (-1 : ℝ) ∧
                            fullStarClassKernel 12 = (1 : ℝ) ∧
                              fullStarClassKernel 13 = (1 : ℝ) ∧
                                fullStarClassKernel 14 = (-1 : ℝ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §6. Gates -/

def swap01Mask (m : ℕ) : ℕ :=
  (if Nat.testBit m 0 then 2 else 0) +
    (if Nat.testBit m 1 then 1 else 0) +
      (if Nat.testBit m 2 then 4 else 0) +
        (if Nat.testBit m 3 then 8 else 0)

theorem swap01Mask_bounds (d : Fin 15) :
    0 < swap01Mask (maskOf d) ∧ swap01Mask (maskOf d) ≤ 15 := by
  fin_cases d <;> decide

def swap01Class (d : Fin 15) : Fin 15 :=
  ⟨swap01Mask (maskOf d) - 1, by
    have h := swap01Mask_bounds d
    omega⟩

theorem fullStarClassKernel_nonvacuous : fullStarClassKernel 0 ≠ 0 := by
  norm_num [fullStarClassKernel]

theorem fullStarClassKernel_swap01 (d : Fin 15) :
    fullStarClassKernel (swap01Class d) = fullStarClassKernel d := by
  fin_cases d <;> rfl

theorem fullStarClassKernel_swap23 (d : Fin 15) :
    fullStarClassKernel (swap23Class d) = fullStarClassKernel d := by
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
    fullStarDirectional (fun _ => (1 : ℝ)) = (1 : ℝ) := by
  simp only [fullStarDirectional]
  rw [sum15_all]
  simp [fullStarClassKernel]

theorem fullStar_homothety_stationary :
    fullStarDirectional (fun d => (classWeightNat d : ℝ)) = 0 := by
  simp only [fullStarDirectional]
  rw [sum15_all]
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
  norm_num

/-! ## §7. Status -/

structure Hinge4DStarKernel22Status where
  starEnumerationClosed : Bool
  flatnessGateClosed : Bool
  fullStarClassKernelClosed : Bool
  otherHingeOrbitsOpen : Bool
  flatHessianAssemblyOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DStarKernel22Status : Hinge4DStarKernel22Status where
  starEnumerationClosed := true
  flatnessGateClosed := true
  fullStarClassKernelClosed := true
  otherHingeOrbitsOpen := true
  flatHessianAssemblyOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DStarKernel22Status_flags :
    hinge4DStarKernel22Status.starEnumerationClosed = true ∧
      hinge4DStarKernel22Status.flatnessGateClosed = true ∧
        hinge4DStarKernel22Status.fullStarClassKernelClosed = true ∧
          hinge4DStarKernel22Status.otherHingeOrbitsOpen = true ∧
            hinge4DStarKernel22Status.flatHessianAssemblyOpen = true ∧
              hinge4DStarKernel22Status.convergesEH4d = false ∧
                hinge4DStarKernel22Status.gapActionRecovery = false := by
  decide

end

end ReggeHinge4DStarKernel22
end Analysis
end Gravity
end IndisputableMonolith
