import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DDihedralKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D full periodic-lattice star deficit class kernel

QG full-theory campaign, next kernel-checked increment after
`ReggeHinge4DDihedralKernel`.  Imports the Freudenthal incidence layer,
the 15-class stencil, and the seed two-simplex dihedral cosine calculus;
never redefines their API.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: the seed triangle hinge `{0, e₀, e₀+e₁}` and its **full**
  periodic Freudenthal star in the integer lattice (four containing
  unit cubes, six incident 4-simplices).  Other hinge orbits of the
  lattice are OPEN.
* This does **not** complete the flat Hessian assembly over all hinges.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (deliverable A)

1. **Star enumeration.** Exactly six `(cube translate, Kuhn simplex)`
   pairs contain the seed hinge.
2. **Flat cosine multiset.** Four simplices have flat cosine `1/√2`
   and two have flat cosine `0`, from each orbit's own Gram vector.
3. **Flatness gate.** Star angle sum equals exactly `2π`.
4. **Full-star deficit class kernel** on classes
   `(2,3,6,7,10,11,14)` with values `(-1,-1,+1,-1,+1,+1,-1)`.
5. **Gates:** nonvacuity, swap-`2↔3` symmetry, uniform-scaling decoy,
   homothety stationarity.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DStarKernel

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeHinge4DDihedralKernel
open ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Cube translates and star enumeration -/

inductive CubeTranslate
  | origin
  | minusE2
  | minusE3
  | minusE2E3
  deriving DecidableEq, Repr, Fintype

def localHingeMasks : CubeTranslate → Finset ℕ
  | .origin => {0, 1, 3}
  | .minusE2 => {4, 5, 7}
  | .minusE3 => {8, 9, 11}
  | .minusE2E3 => {12, 13, 15}

def containsHinge (c : CubeTranslate) (s : Fin 24) : Bool :=
  decide (∀ m ∈ localHingeMasks c, ∃ i : Fin 5, vertexMask s i = m)

structure StarMember where
  cube : CubeTranslate
  simplex : Fin 24
  deriving DecidableEq, Repr

def starMembers : List StarMember :=
  [ ⟨.origin, 0⟩, ⟨.origin, 1⟩
  , ⟨.minusE2, 12⟩, ⟨.minusE3, 18⟩
  , ⟨.minusE2E3, 16⟩, ⟨.minusE2E3, 22⟩ ]

theorem starMembers_length : starMembers.length = 6 := rfl

theorem starMembers_complete (c : CubeTranslate) (s : Fin 24) :
    containsHinge c s = true ↔ ⟨c, s⟩ ∈ starMembers := by
  cases c <;> fin_cases s <;> decide

theorem star_cardinality :
    (Finset.univ.filter (fun p : CubeTranslate × Fin 24 =>
      containsHinge p.1 p.2 = true)).card = 6 := by
  decide

/-! ## §2. Flat squared-length orbit representatives -/

def oppFlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 1 | 4 => 1
  | 5 => 3 | 6 => 2 | 7 => 4 | 8 => 3 | 9 => 1

def orthFlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 1
  | 5 => 2 | 6 => 2 | 7 => 3 | 8 => 1 | 9 => 4

theorem hingeGramDet_opp : hingeGramDet oppFlatSqEdges = 4 := by
  norm_num [hingeGramDet, oppFlatSqEdges]
theorem apexDotNum_opp : apexDotNum oppFlatSqEdges = 8 := by
  norm_num [apexDotNum, hingeGramDet, oppFlatSqEdges]
theorem apex3NormSqNum_opp : apex3NormSqNum oppFlatSqEdges = 8 := by
  norm_num [apex3NormSqNum, hingeGramDet, oppFlatSqEdges]
theorem apex4NormSqNum_opp : apex4NormSqNum oppFlatSqEdges = 4 := by
  norm_num [apex4NormSqNum, hingeGramDet, oppFlatSqEdges]

theorem hingeGramDet_orth : hingeGramDet orthFlatSqEdges = 4 := by
  norm_num [hingeGramDet, orthFlatSqEdges]
theorem apexDotNum_orth : apexDotNum orthFlatSqEdges = 0 := by
  norm_num [apexDotNum, hingeGramDet, orthFlatSqEdges]
theorem apex3NormSqNum_orth : apex3NormSqNum orthFlatSqEdges = 4 := by
  norm_num [apex3NormSqNum, hingeGramDet, orthFlatSqEdges]
theorem apex4NormSqNum_orth : apex4NormSqNum orthFlatSqEdges = 4 := by
  norm_num [apex4NormSqNum, hingeGramDet, orthFlatSqEdges]

theorem cosDihedral_opp_flat :
    cosDihedral oppFlatSqEdges = 1 / Real.sqrt 2 := by
  rw [cos_numForm _ (by rw [hingeGramDet_opp]; norm_num),
    apexDotNum_opp, apex3NormSqNum_opp, apex4NormSqNum_opp]
  rw [show (8 : ℝ) * 4 = 32 by norm_num,
    show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2) 2,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [div_eq_div_iff (by positivity)
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))]
  ring

theorem cosDihedral_orth_flat : cosDihedral orthFlatSqEdges = 0 := by
  rw [cos_numForm _ (by rw [hingeGramDet_orth]; norm_num),
    apexDotNum_orth, apex3NormSqNum_orth, apex4NormSqNum_orth]
  norm_num

/-! ## §3. Flatness gate -/

theorem arccos_one_div_sqrt_two :
    Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
  have hcos : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have heq : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    rw [div_eq_div_iff hs (by norm_num : (2 : ℝ) ≠ 0), one_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq, ← hcos, Real.arccos_cos (by positivity) (by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith)]

def flatAngleSeedOpp : ℝ := Real.arccos (1 / Real.sqrt 2)
def flatAngleOrth : ℝ := Real.arccos 0

theorem flatAngleSeedOpp_eq : flatAngleSeedOpp = Real.pi / 4 :=
  arccos_one_div_sqrt_two
theorem flatAngleOrth_eq : flatAngleOrth = Real.pi / 2 := Real.arccos_zero

def starFlatAngleSum : ℝ := 4 * flatAngleSeedOpp + 2 * flatAngleOrth

theorem star_flat_angle_sum_two_pi : starFlatAngleSum = 2 * Real.pi := by
  simp only [starFlatAngleSum, flatAngleSeedOpp_eq, flatAngleOrth_eq]
  ring

def starFlatCosines : Fin 6 → ℝ
  | ⟨0, _⟩ | ⟨1, _⟩ => 1 / Real.sqrt 2
  | ⟨2, _⟩ | ⟨3, _⟩ => 0
  | ⟨4, _⟩ | ⟨5, _⟩ => 1 / Real.sqrt 2

theorem starFlatCosines_match_orbits :
    starFlatCosines 0 = cosDihedral seedFlatSqEdges ∧
      starFlatCosines 2 = cosDihedral orthFlatSqEdges ∧
        starFlatCosines 4 = cosDihedral oppFlatSqEdges :=
  ⟨cosDihedral_flat.symm, cosDihedral_orth_flat.symm, cosDihedral_opp_flat.symm⟩


/-! ## §4. Opposite-orbit cosine derivatives -/

def oppCoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else oppFlatSqEdges j

def oppCosKernel : Fin 10 → ℝ
  | ⟨2, _⟩ => Real.sqrt 2 / 8
  | ⟨9, _⟩ => -(Real.sqrt 2) / 4
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

private lemma hasDerivAt_numForm_opp {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 8) (hP0 : P t0 = 8) (hQ0 : Q t0 = 4) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      (Real.sqrt 2 * (2 * N' - P' - 2 * Q') / 32) t0 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hPQ : HasDerivAt (fun t => P t * Q t)
      (P' * Q t0 + P t0 * Q') t0 := hP.mul hQ
  have hPQ0 : P t0 * Q t0 = 32 := by rw [hP0, hQ0]; norm_num
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
  have h32 : Real.sqrt (P t0 * Q t0) = 4 * Real.sqrt 2 := by
    rw [hPQ0, show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2) 2,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  -- Quotient-rule value at these constants:
  -- (N'*den - N*den')/den^2 with den = 8√2, N=8, den' = (4P'+8Q')/(4√2) = (P'+2Q')/√2
  -- = (8√2 N' - 8(P'+2Q')/√2) / 128
  -- = (√2 N' - (P'+2Q')/√2) / 16
  -- = (2N' - P' - 2Q')/(16√2)
  -- = √2 (2N' - P' - 2Q') / 32
  rw [h32, hN0, hP0, hQ0]
  have hpow : (2 * (4 * Real.sqrt 2)) ^ 2 = 128 := by
    rw [show (2 * (4 * Real.sqrt 2)) ^ 2
        = 64 * (Real.sqrt 2 * Real.sqrt 2) from by ring, hs2]
    norm_num
  rw [hpow]
  have hden' :
      2 * ((P' * (4 : ℝ) + (8 : ℝ) * Q') / (2 * (4 * Real.sqrt 2))) =
        (P' + 2 * Q') / Real.sqrt 2 := by
    field_simp [hs2]
    ring
  -- After convert, goal is equality of the two derivative expressions.
  -- Rewrite the den' factor appearing in the quotient rule.
  simp only [hden']
  -- Clear denominators, then replace √2 ^ 2 by 2.
  field_simp
  simp only [pow_two, hs2]
  ring

private lemma hasDerivAt_opp_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (oppCoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (oppCoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (oppCoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (oppCoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 8)
    (hP0 : aP * t0 ^ 2 + bP * t0 + cP = 8)
    (hQ0 : aQ * t0 ^ 2 + bQ * t0 + cQ = 4)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath k t))
      (Real.sqrt 2 * (2 * (2 * aN * t0 + bN) - (2 * aP * t0 + bP)
        - 2 * (2 * aQ * t0 + bQ)) / 32) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain := hasDerivAt_numForm_opp hN hP hQ hN0 hP0 hQ0
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (oppCoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma opp_path0_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 0 t) = (-6) * t ^ 2 + (20) * t + (-6)
    ∧ apex3NormSqNum (oppCoordPath 0 t) = (-4) * t ^ 2 + (16) * t + (-4)
    ∧ apex4NormSqNum (oppCoordPath 0 t) = (-3) * t ^ 2 + (10) * t + (-3)
    ∧ hingeGramDet (oppCoordPath 0 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path1_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 1 t) = (-4) * t ^ 2 + (16) * t + (-8)
    ∧ apex3NormSqNum (oppCoordPath 1 t) = (-3) * t ^ 2 + (12) * t + (-4)
    ∧ apex4NormSqNum (oppCoordPath 1 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (oppCoordPath 1 t) = (-1) * t ^ 2 + (4) * t + (0) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path2_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 2 t) = (0) * t ^ 2 + (4) * t + (0)
    ∧ apex3NormSqNum (oppCoordPath 2 t) = (-1) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (oppCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (oppCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path3_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 3 t) = (0) * t ^ 2 + (4) * t + (4)
    ∧ apex3NormSqNum (oppCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (oppCoordPath 3 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (oppCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path4_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 4 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex3NormSqNum (oppCoordPath 4 t) = (-2) * t ^ 2 + (12) * t + (-2)
    ∧ apex4NormSqNum (oppCoordPath 4 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (oppCoordPath 4 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path5_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (oppCoordPath 5 t) = (-2) * t ^ 2 + (12) * t + (-10)
    ∧ apex4NormSqNum (oppCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (oppCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path6_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (oppCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (oppCoordPath 6 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (oppCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path7_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (oppCoordPath 7 t) = (-1) * t ^ 2 + (8) * t + (-8)
    ∧ apex4NormSqNum (oppCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (oppCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path8_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex3NormSqNum (oppCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (oppCoordPath 8 t) = (-1) * t ^ 2 + (6) * t + (-5)
    ∧ hingeGramDet (oppCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

private lemma opp_path9_polys : ∀ t : ℝ,
    apexDotNum (oppCoordPath 9 t) = (0) * t ^ 2 + (-4) * t + (12)
    ∧ apex3NormSqNum (oppCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (8)
    ∧ apex4NormSqNum (oppCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (oppCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      oppCoordPath, oppFlatSqEdges] <;> ring

theorem hasDerivAt_opp_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 0 t))
      (0) 1 := by
  have h := hasDerivAt_opp_slot 0 1 (-6) (20) (-6) (-4) (16) (-4)
    (-3) (10) (-3) (-1) (6) (-1) opp_path0_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 1 t))
      (0) 2 := by
  have h := hasDerivAt_opp_slot 1 2 (-4) (16) (-8) (-3) (12) (-4)
    (-2) (8) (-4) (-1) (4) (0) opp_path1_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 2 t))
      (Real.sqrt 2 / 8) 2 := by
  have h := hasDerivAt_opp_slot 2 2 (0) (4) (0) (-1) (8) (-4)
    (0) (0) (4) (0) (0) (4) opp_path2_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 3 t))
      (0) 1 := by
  have h := hasDerivAt_opp_slot 3 1 (0) (4) (4) (0) (0) (8)
    (-1) (6) (-1) (0) (0) (4) opp_path3_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 4 t))
      (0) 1 := by
  have h := hasDerivAt_opp_slot 4 1 (-2) (12) (-2) (-2) (12) (-2)
    (-1) (6) (-1) (-1) (6) (-1) opp_path4_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 5 t))
      (0) 3 := by
  have h := hasDerivAt_opp_slot 5 3 (0) (0) (8) (-2) (12) (-10)
    (0) (0) (4) (0) (0) (4) opp_path5_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 6 t))
      (0) 2 := by
  have h := hasDerivAt_opp_slot 6 2 (0) (0) (8) (0) (0) (8)
    (-2) (8) (-4) (0) (0) (4) opp_path6_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 7 t))
      (0) 4 := by
  have h := hasDerivAt_opp_slot 7 4 (0) (0) (8) (-1) (8) (-8)
    (0) (0) (4) (0) (0) (4) opp_path7_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 8 t))
      (0) 3 := by
  have h := hasDerivAt_opp_slot 8 3 (0) (0) (8) (0) (0) (8)
    (-1) (6) (-5) (0) (0) (4) opp_path8_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_opp_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath 9 t))
      (-(Real.sqrt 2) / 4) 1 := by
  have h := hasDerivAt_opp_slot 9 1 (0) (-4) (12) (0) (0) (8)
    (0) (0) (4) (0) (0) (4) opp_path9_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring


theorem hasDerivAt_opp_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (oppCoordPath k t))
      (oppCosKernel k) (oppFlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_opp_slot0
  · exact hasDerivAt_opp_slot1
  · exact hasDerivAt_opp_slot2
  · exact hasDerivAt_opp_slot3
  · exact hasDerivAt_opp_slot4
  · exact hasDerivAt_opp_slot5
  · exact hasDerivAt_opp_slot6
  · exact hasDerivAt_opp_slot7
  · exact hasDerivAt_opp_slot8
  · exact hasDerivAt_opp_slot9

/-! ## §5. Orthogonal-orbit cosine derivatives -/

def orthCoordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else orthFlatSqEdges j

def orthCosKernel : Fin 10 → ℝ
  | ⟨1, _⟩ => (-1 / 2 : ℝ)
  | ⟨3, _⟩ => (1 / 2 : ℝ)
  | ⟨7, _⟩ => (1 / 2 : ℝ)
  | ⟨9, _⟩ => (-1 / 2 : ℝ)
  | _ => 0

private lemma hasDerivAt_numForm_orth {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 0) (hP0 : P t0 = 4) (hQ0 : Q t0 = 4) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      (N' / 8) t0 := by
  have hPQ : HasDerivAt (fun t => P t * Q t)
      (P' * Q t0 + P t0 * Q') t0 := hP.mul hQ
  have hPQ0 : P t0 * Q t0 = 16 := by rw [hP0, hQ0]; norm_num
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
  have h4 : Real.sqrt (P t0 * Q t0) = 4 := by
    rw [hPQ0, show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [h4, hN0]
  ring

private lemma hasDerivAt_orth_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (orthCoordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (orthCoordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (orthCoordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (orthCoordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 0)
    (hP0 : aP * t0 ^ 2 + bP * t0 + cP = 4)
    (hQ0 : aQ * t0 ^ 2 + bQ * t0 + cQ = 4)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath k t))
      ((2 * aN * t0 + bN) / 8) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain := hasDerivAt_numForm_orth hN hP hQ hN0 hP0 hQ0
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (orthCoordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

private lemma orth_path0_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 0 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 0 t) = (-3) * t ^ 2 + (10) * t + (-3)
    ∧ apex4NormSqNum (orthCoordPath 0 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (orthCoordPath 0 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path1_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 1 t) = (0) * t ^ 2 + (-4) * t + (8)
    ∧ apex3NormSqNum (orthCoordPath 1 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (orthCoordPath 1 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (orthCoordPath 1 t) = (-1) * t ^ 2 + (4) * t + (0) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path2_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 2 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ apex4NormSqNum (orthCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (orthCoordPath 2 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path3_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 3 t) = (0) * t ^ 2 + (4) * t + (-12)
    ∧ apex3NormSqNum (orthCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (orthCoordPath 3 t) = (-1) * t ^ 2 + (6) * t + (-5)
    ∧ hingeGramDet (orthCoordPath 3 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path4_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 4 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 4 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ apex4NormSqNum (orthCoordPath 4 t) = (-3) * t ^ 2 + (10) * t + (-3)
    ∧ hingeGramDet (orthCoordPath 4 t) = (-1) * t ^ 2 + (6) * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path5_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 5 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ apex4NormSqNum (orthCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (orthCoordPath 5 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path6_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (orthCoordPath 6 t) = (-2) * t ^ 2 + (8) * t + (-4)
    ∧ hingeGramDet (orthCoordPath 6 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path7_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 7 t) = (0) * t ^ 2 + (4) * t + (-12)
    ∧ apex3NormSqNum (orthCoordPath 7 t) = (-1) * t ^ 2 + (6) * t + (-5)
    ∧ apex4NormSqNum (orthCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (orthCoordPath 7 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path8_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (0)
    ∧ apex3NormSqNum (orthCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (orthCoordPath 8 t) = (-1) * t ^ 2 + (6) * t + (-1)
    ∧ hingeGramDet (orthCoordPath 8 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

private lemma orth_path9_polys : ∀ t : ℝ,
    apexDotNum (orthCoordPath 9 t) = (0) * t ^ 2 + (-4) * t + (16)
    ∧ apex3NormSqNum (orthCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ apex4NormSqNum (orthCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4)
    ∧ hingeGramDet (orthCoordPath 9 t) = (0) * t ^ 2 + (0) * t + (4) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      orthCoordPath, orthFlatSqEdges] <;> ring

theorem hasDerivAt_orth_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 0 t))
      (0) 1 := by
  have h := hasDerivAt_orth_slot 0 1 (0) (0) (0) (-3) (10) (-3)
    (-1) (6) (-1) (-1) (6) (-1) orth_path0_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 1 t))
      ((-1 / 2 : ℝ)) 2 := by
  have h := hasDerivAt_orth_slot 1 2 (0) (-4) (8) (-2) (8) (-4)
    (-2) (8) (-4) (-1) (4) (0) orth_path1_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 2 t))
      (0) 1 := by
  have h := hasDerivAt_orth_slot 2 1 (0) (0) (0) (-1) (6) (-1)
    (0) (0) (4) (0) (0) (4) orth_path2_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 3 t))
      ((1 / 2 : ℝ)) 3 := by
  have h := hasDerivAt_orth_slot 3 3 (0) (4) (-12) (0) (0) (4)
    (-1) (6) (-5) (0) (0) (4) orth_path3_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 4 t))
      (0) 1 := by
  have h := hasDerivAt_orth_slot 4 1 (0) (0) (0) (-1) (6) (-1)
    (-3) (10) (-3) (-1) (6) (-1) orth_path4_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 5 t))
      (0) 2 := by
  have h := hasDerivAt_orth_slot 5 2 (0) (0) (0) (-2) (8) (-4)
    (0) (0) (4) (0) (0) (4) orth_path5_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 6 t))
      (0) 2 := by
  have h := hasDerivAt_orth_slot 6 2 (0) (0) (0) (0) (0) (4)
    (-2) (8) (-4) (0) (0) (4) orth_path6_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 7 t))
      ((1 / 2 : ℝ)) 3 := by
  have h := hasDerivAt_orth_slot 7 3 (0) (4) (-12) (-1) (6) (-5)
    (0) (0) (4) (0) (0) (4) orth_path7_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 8 t))
      (0) 1 := by
  have h := hasDerivAt_orth_slot 8 1 (0) (0) (0) (0) (0) (4)
    (-1) (6) (-1) (0) (0) (4) orth_path8_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_orth_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath 9 t))
      ((-1 / 2 : ℝ)) 4 := by
  have h := hasDerivAt_orth_slot 9 4 (0) (-4) (16) (0) (0) (4)
    (0) (0) (4) (0) (0) (4) orth_path9_polys
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring


theorem hasDerivAt_orth_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (orthCoordPath k t))
      (orthCosKernel k) (orthFlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_orth_slot0
  · exact hasDerivAt_orth_slot1
  · exact hasDerivAt_orth_slot2
  · exact hasDerivAt_orth_slot3
  · exact hasDerivAt_orth_slot4
  · exact hasDerivAt_orth_slot5
  · exact hasDerivAt_orth_slot6
  · exact hasDerivAt_orth_slot7
  · exact hasDerivAt_orth_slot8
  · exact hasDerivAt_orth_slot9

/-! ## §6. Full-star deficit class kernel -/

def chainSeedOpp : ℝ := -(Real.sqrt 2)
def chainOrth : ℝ := (-1 : ℝ)

def oppDeficitKernel : Fin 10 → ℝ
  | ⟨2, _⟩ => (1 / 4 : ℝ)
  | ⟨9, _⟩ => (-1 / 2 : ℝ)
  | _ => 0

def orthDeficitKernel : Fin 10 → ℝ
  | ⟨1, _⟩ => (-1 / 2 : ℝ)
  | ⟨3, _⟩ => (1 / 2 : ℝ)
  | ⟨7, _⟩ => (1 / 2 : ℝ)
  | ⟨9, _⟩ => (-1 / 2 : ℝ)
  | _ => 0

theorem oppDeficitKernel_eq_chain :
    oppDeficitKernel 2 = -chainSeedOpp * oppCosKernel 2 ∧
      oppDeficitKernel 9 = -chainSeedOpp * oppCosKernel 9 := by
  constructor
  · simp only [oppDeficitKernel, chainSeedOpp, oppCosKernel]
    rw [show -(-(Real.sqrt 2)) * (Real.sqrt 2 / 8)
        = (Real.sqrt 2 * Real.sqrt 2) / 8 from by ring,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  · simp only [oppDeficitKernel, chainSeedOpp, oppCosKernel]
    rw [show -(-(Real.sqrt 2)) * (-(Real.sqrt 2) / 4)
        = -(Real.sqrt 2 * Real.sqrt 2) / 4 from by ring,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

theorem orthDeficitKernel_eq_chain (k : Fin 10) :
    orthDeficitKernel k = -chainOrth * orthCosKernel k := by
  fin_cases k <;> simp [orthDeficitKernel, chainOrth, orthCosKernel]

def starSlotClass : Fin 6 → Fin 10 → Fin 15
  | 0, e => localEdgeClass 0 e
  | 1, e => localEdgeClass 1 e
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 3 | 2, 3 => 10 | 2, 4 => 1
  | 2, 5 => 4 | 2, 6 => 9 | 2, 7 => 6 | 2, 8 => 7 | 2, 9 => 14
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 7 | 3, 3 => 6 | 3, 4 => 1
  | 3, 5 => 8 | 3, 6 => 5 | 3, 7 => 10 | 3, 8 => 3 | 3, 9 => 14
  | 4, 0 => 0 | 4, 1 => 2 | 4, 2 => 11 | 4, 3 => 7 | 4, 4 => 1
  | 4, 5 => 12 | 4, 6 => 8 | 4, 7 => 14 | 4, 8 => 10 | 4, 9 => 3
  | 5, 0 => 0 | 5, 1 => 2 | 5, 2 => 11 | 5, 3 => 3 | 5, 4 => 1
  | 5, 5 => 12 | 5, 6 => 4 | 5, 7 => 14 | 5, 8 => 6 | 5, 9 => 7

def starLocalDeficitKernel : Fin 6 → Fin 10 → ℝ
  | 0 | 1 => singleSimplexDeficitKernel
  | 2 | 3 => orthDeficitKernel
  | 4 | 5 => oppDeficitKernel

def assembleStarMember (m : Fin 6) : Fin 15 → ℝ :=
  fun d => ∑ e : Fin 10,
    if starSlotClass m e = d then starLocalDeficitKernel m e else 0

def fullStarClassKernelAssembled : Fin 15 → ℝ :=
  fun d => ∑ m : Fin 6, assembleStarMember m d

def fullStarClassKernel : Fin 15 → ℝ
  | ⟨2, _⟩ => (-1 : ℝ)
  | ⟨3, _⟩ => (-1 : ℝ)
  | ⟨6, _⟩ => (1 : ℝ)
  | ⟨7, _⟩ => (-1 : ℝ)
  | ⟨10, _⟩ => (1 : ℝ)
  | ⟨11, _⟩ => (1 : ℝ)
  | ⟨14, _⟩ => (-1 : ℝ)
  | _ => 0

private lemma member0_eval (d : Fin 15) :
    assembleStarMember 0 d =
      (if d = 11 then (1 / 4 : ℝ) else 0) +
        (if d = 7 then (-1 / 2 : ℝ) else 0) := by
  change assembleClassKernel 0 singleSimplexDeficitKernel d = _
  rw [assembleClassKernel_eval]
  rw [show localEdgeClass 0 8 = (11 : Fin 15) from by decide,
    show localEdgeClass 0 9 = (7 : Fin 15) from by decide,
    singleSimplexDeficitKernel_eight, singleSimplexDeficitKernel_nine]
  aesop

private lemma member1_eval (d : Fin 15) :
    assembleStarMember 1 d =
      (if d = 11 then (1 / 4 : ℝ) else 0) +
        (if d = 3 then (-1 / 2 : ℝ) else 0) := by
  change assembleClassKernel 1 singleSimplexDeficitKernel d = _
  rw [assembleClassKernel_eval]
  rw [show localEdgeClass 1 8 = (11 : Fin 15) from by decide,
    show localEdgeClass 1 9 = (3 : Fin 15) from by decide,
    singleSimplexDeficitKernel_eight, singleSimplexDeficitKernel_nine]
  aesop

private lemma sum_support4 (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e ≠ 1 → e ≠ 3 → e ≠ 7 → e ≠ 9 → f e = 0) :
    (∑ e : Fin 10, f e) = f 1 + f 3 + f 7 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (1 : Fin 10) (insert (3 : Fin 10)
          (insert (7 : Fin 10) (insert (9 : Fin 10)
            ({0, 2, 4, 5, 6, 8} : Finset (Fin 10))))) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => by
      fin_cases e <;> simp at he ⊢ <;>
        exact hz _ (by decide) (by decide) (by decide) (by decide))]
  abel

private lemma sum_support2_29 (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e ≠ 2 → e ≠ 9 → f e = 0) :
    (∑ e : Fin 10, f e) = f 2 + f 9 := by
  rw [show (Finset.univ : Finset (Fin 10)) =
        insert (2 : Fin 10) (insert (9 : Fin 10)
          ({0, 1, 3, 4, 5, 6, 7, 8} : Finset (Fin 10))) from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => by
      fin_cases e <;> simp at he ⊢ <;>
        exact hz _ (by decide) (by decide))]
  abel

private lemma orth_kernel_zero_off (e : Fin 10)
    (h1 : e ≠ 1) (h3 : e ≠ 3) (h7 : e ≠ 7) (h9 : e ≠ 9) :
    orthDeficitKernel e = 0 := by
  fin_cases e <;> first | rfl | contradiction

private lemma opp_kernel_zero_off (e : Fin 10) (h2 : e ≠ 2) (h9 : e ≠ 9) :
    oppDeficitKernel e = 0 := by
  fin_cases e <;> first | rfl | contradiction

private lemma member2_eval (d : Fin 15) :
    assembleStarMember 2 d =
      (if d = 2 then (-1 / 2 : ℝ) else 0) +
        (if d = 10 then (1 / 2 : ℝ) else 0) +
          (if d = 6 then (1 / 2 : ℝ) else 0) +
            (if d = 14 then (-1 / 2 : ℝ) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support4 (fun e =>
      if starSlotClass 2 e = d then orthDeficitKernel e else 0)
    (fun e h1 h3 h7 h9 => by simp [orth_kernel_zero_off e h1 h3 h7 h9])]
  simp only [starSlotClass, orthDeficitKernel]
  aesop

private lemma member3_eval (d : Fin 15) :
    assembleStarMember 3 d =
      (if d = 2 then (-1 / 2 : ℝ) else 0) +
        (if d = 6 then (1 / 2 : ℝ) else 0) +
          (if d = 10 then (1 / 2 : ℝ) else 0) +
            (if d = 14 then (-1 / 2 : ℝ) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support4 (fun e =>
      if starSlotClass 3 e = d then orthDeficitKernel e else 0)
    (fun e h1 h3 h7 h9 => by simp [orth_kernel_zero_off e h1 h3 h7 h9])]
  simp only [starSlotClass, orthDeficitKernel]
  aesop

private lemma member4_eval (d : Fin 15) :
    assembleStarMember 4 d =
      (if d = 11 then (1 / 4 : ℝ) else 0) +
        (if d = 3 then (-1 / 2 : ℝ) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support2_29 (fun e =>
      if starSlotClass 4 e = d then oppDeficitKernel e else 0)
    (fun e h2 h9 => by simp [opp_kernel_zero_off e h2 h9])]
  simp only [starSlotClass, oppDeficitKernel]
  aesop

private lemma member5_eval (d : Fin 15) :
    assembleStarMember 5 d =
      (if d = 11 then (1 / 4 : ℝ) else 0) +
        (if d = 7 then (-1 / 2 : ℝ) else 0) := by
  simp only [assembleStarMember, starLocalDeficitKernel]
  rw [sum_support2_29 (fun e =>
      if starSlotClass 5 e = d then oppDeficitKernel e else 0)
    (fun e h2 h9 => by simp [opp_kernel_zero_off e h2 h9])]
  simp only [starSlotClass, oppDeficitKernel]
  aesop

private lemma sum6 (f : Fin 6 → ℝ) :
    (∑ m : Fin 6, f m) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [show (Finset.univ : Finset (Fin 6)) =
        insert (0 : Fin 6) (insert (1 : Fin 6) (insert (2 : Fin 6)
          (insert (3 : Fin 6) (insert (4 : Fin 6) (insert (5 : Fin 6)
            (∅ : Finset (Fin 6))))))) from by decide]
  simp [Finset.sum_insert]
  ring

theorem fullStarClassKernel_eq (d : Fin 15) :
    fullStarClassKernelAssembled d = fullStarClassKernel d := by
  simp only [fullStarClassKernelAssembled]
  rw [sum6]
  rw [member0_eval, member1_eval, member2_eval, member3_eval,
    member4_eval, member5_eval]
  fin_cases d <;> simp [fullStarClassKernel] <;> norm_num

theorem fullStarClassKernel_values :
    fullStarClassKernel 2 = (-1 : ℝ) ∧
      fullStarClassKernel 3 = (-1 : ℝ) ∧
        fullStarClassKernel 6 = (1 : ℝ) ∧
          fullStarClassKernel 7 = (-1 : ℝ) ∧
            fullStarClassKernel 10 = (1 : ℝ) ∧
              fullStarClassKernel 11 = (1 : ℝ) ∧
                fullStarClassKernel 14 = (-1 : ℝ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem fullStarClassKernel_zero_off (d : Fin 15)
    (h2 : d ≠ 2) (h3 : d ≠ 3) (h6 : d ≠ 6) (h7 : d ≠ 7)
    (h10 : d ≠ 10) (h11 : d ≠ 11) (h14 : d ≠ 14) :
    fullStarClassKernel d = 0 := by
  fin_cases d <;> first | rfl | contradiction

/-! ## §7. Gates -/

theorem fullStarClassKernel_nonvacuous : fullStarClassKernel 11 ≠ 0 := by
  norm_num [fullStarClassKernel]

theorem fullStarClassKernel_swap23 (d : Fin 15) :
    fullStarClassKernel (swap23Class d) = fullStarClassKernel d := by
  have hinv : ∀ x : Fin 15, swap23Class (swap23Class x) = x := by decide
  have hs2 : swap23Class (2 : Fin 15) = 2 := by decide
  have hs3 : swap23Class (3 : Fin 15) = 7 := by decide
  have hs6 : swap23Class (6 : Fin 15) = 10 := by decide
  have hs7 : swap23Class (7 : Fin 15) = 3 := by decide
  have hs10 : swap23Class (10 : Fin 15) = 6 := by decide
  have hs11 : swap23Class (11 : Fin 15) = 11 := by decide
  have hs14 : swap23Class (14 : Fin 15) = 14 := by decide
  by_cases h2 : d = 2
  · subst h2; rw [hs2]
  by_cases h3 : d = 3
  · subst h3; rw [hs3]; rfl
  by_cases h6 : d = 6
  · subst h6; rw [hs6]; rfl
  by_cases h7 : d = 7
  · subst h7; rw [hs7]; rfl
  by_cases h10 : d = 10
  · subst h10; rw [hs10]; rfl
  by_cases h11 : d = 11
  · subst h11; rw [hs11]
  by_cases h14 : d = 14
  · subst h14; rw [hs14]
  have g2 : swap23Class d ≠ 2 := fun h => h2 (by rw [← hinv d, h, hs2])
  have g3 : swap23Class d ≠ 3 := fun h => h7 (by rw [← hinv d, h, hs3])
  have g6 : swap23Class d ≠ 6 := fun h => h10 (by rw [← hinv d, h, hs6])
  have g7 : swap23Class d ≠ 7 := fun h => h3 (by rw [← hinv d, h, hs7])
  have g10 : swap23Class d ≠ 10 := fun h => h6 (by rw [← hinv d, h, hs10])
  have g11 : swap23Class d ≠ 11 := fun h => h11 (by rw [← hinv d, h, hs11])
  have g14 : swap23Class d ≠ 14 := fun h => h14 (by rw [← hinv d, h, hs14])
  rw [fullStarClassKernel_zero_off _ g2 g3 g6 g7 g10 g11 g14,
    fullStarClassKernel_zero_off _ h2 h3 h6 h7 h10 h11 h14]

def fullStarDirectional (v : Fin 15 → ℝ) : ℝ :=
  ∑ d : Fin 15, v d * fullStarClassKernel d

private lemma sum15_support (f : Fin 15 → ℝ)
    (hz : ∀ d : Fin 15, d ≠ 2 → d ≠ 3 → d ≠ 6 → d ≠ 7 → d ≠ 10 → d ≠ 11 →
      d ≠ 14 → f d = 0) :
    (∑ d : Fin 15, f d) =
      f 2 + f 3 + f 6 + f 7 + f 10 + f 11 + f 14 := by
  classical
  have hrest :
      ∑ d ∈ ({0, 1, 4, 5, 8, 9, 12, 13} : Finset (Fin 15)), f d = 0 := by
    refine Finset.sum_eq_zero ?_
    intro d hd
    have : d = 0 ∨ d = 1 ∨ d = 4 ∨ d = 5 ∨ d = 8 ∨ d = 9 ∨ d = 12 ∨ d = 13 := by
      fin_cases d <;> simp at hd ⊢
    rcases this with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact hz _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  rw [show (Finset.univ : Finset (Fin 15)) =
        insert (2 : Fin 15) (insert (3 : Fin 15) (insert (6 : Fin 15)
          (insert (7 : Fin 15) (insert (10 : Fin 15) (insert (11 : Fin 15)
            (insert (14 : Fin 15)
              ({0, 1, 4, 5, 8, 9, 12, 13} : Finset (Fin 15)))))))) from by decide]
  simp [Finset.sum_insert, hrest]
  ring

theorem fullStar_uniformScale_decoy :
    fullStarDirectional (fun _ => (1 : ℝ)) = (-1 : ℝ) := by
  simp only [fullStarDirectional]
  rw [sum15_support _ (fun d h2 h3 h6 h7 h10 h11 h14 => by
    rw [fullStarClassKernel_zero_off d h2 h3 h6 h7 h10 h11 h14, mul_zero])]
  simp [fullStarClassKernel]

theorem fullStar_homothety_stationary :
    fullStarDirectional (fun d => (classWeightNat d : ℝ)) = 0 := by
  simp only [fullStarDirectional]
  rw [sum15_support _ (fun d h2 h3 h6 h7 h10 h11 h14 => by
    rw [fullStarClassKernel_zero_off d h2 h3 h6 h7 h10 h11 h14, mul_zero])]
  have w2 : classWeightNat 2 = 2 := by decide
  have w3 : classWeightNat 3 = 1 := by decide
  have w6 : classWeightNat 6 = 3 := by decide
  have w7 : classWeightNat 7 = 1 := by decide
  have w10 : classWeightNat 10 = 3 := by decide
  have w11 : classWeightNat 11 = 2 := by decide
  have w14 : classWeightNat 14 = 4 := by decide
  simp [fullStarClassKernel, w2, w3, w6, w7, w10, w11, w14]
  norm_num

/-! ## §8. Status -/

structure Hinge4DStarKernelStatus where
  starEnumerationClosed : Bool
  flatnessGateClosed : Bool
  fullStarClassKernelClosed : Bool
  otherHingeOrbitsOpen : Bool
  flatHessianAssemblyOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DStarKernelStatus : Hinge4DStarKernelStatus where
  starEnumerationClosed := true
  flatnessGateClosed := true
  fullStarClassKernelClosed := true
  otherHingeOrbitsOpen := true
  flatHessianAssemblyOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DStarKernelStatus_flags :
    hinge4DStarKernelStatus.starEnumerationClosed = true ∧
      hinge4DStarKernelStatus.flatnessGateClosed = true ∧
        hinge4DStarKernelStatus.fullStarClassKernelClosed = true ∧
          hinge4DStarKernelStatus.otherHingeOrbitsOpen = true ∧
            hinge4DStarKernelStatus.flatHessianAssemblyOpen = true ∧
              hinge4DStarKernelStatus.convergesEH4d = false ∧
                hinge4DStarKernelStatus.gapActionRecovery = false := by
  decide

end

end ReggeHinge4DStarKernel
end Analysis
end Gravity
end IndisputableMonolith
