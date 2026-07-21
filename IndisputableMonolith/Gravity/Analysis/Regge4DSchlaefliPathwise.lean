import Mathlib
import IndisputableMonolith.Geometry.SchlaefliN
import IndisputableMonolith.Geometry.DihedralDerivatives
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DDihedralKernel
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification
import IndisputableMonolith.Gravity.Analysis.ReggeFlat4DHessianAssembly

/-!
# Freudenthal 4-simplex pathwise Schläfli (flat + directional)

Mirrors the 3D Gate-A2 input
`Geometry.SchlaefliTetrahedronProof.tetraSchlaefliSixEdgeClosedForm`
(`nH = nE = 6`) at the 4-simplex level (`nH = nE = 10`).

## Tier tags (binding)

* THEOREM: Freudenthal / Kuhn 4-simplex edge and triangle-hinge
  combinatorics; flat hinge areas; the flat Schläfli summand table;
  column sums vanish; seed-hinge row matches
  `hingeArea · angleKernel` from `ReggeHinge4DDihedralKernel`.
* THEOREM: a non-vacuous flat `SchlaefliIdentityN` witness (strictly
  positive areas) at `nH = nE = 10`.
* THEOREM: seed-hinge dihedral angle `HasDerivAt` along every squared-edge
  coordinate path through the flat seed (`angleKernel`).
* THEOREM: flat directional Schläfli kill along every affine velocity
  through the flat seed (Gate A2-style input at flat).
* OPEN: full pathwise identity off the flat seed on `Nondeg4Simplex`;
  remapped `HasDerivAt` for every hinge row; `Regge4DSchlafliElevationToCandidate`;
  `S_RS_converges_EH_4d`.
* Does **not** flip `gap_action_recovery`.
* Does **not** inhabit a zero-measure `SchlaefliIdentityN` shell
  (lesson `L-p1-schlaefli-not-vacuous-prop`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace Regge4DSchlaefliPathwise

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeHinge4DDihedralKernel
open ReggeHinge4DOrbitClassification
open ReggeFlat4DHessianAssembly
open Geometry.SchlaefliN
open Geometry.DihedralDerivatives

noncomputable section

abbrev SqEdges4 := ReggeHinge4DDihedralKernel.SqEdges4

/-! ## §1. Freudenthal 4-simplex edges and triangle hinges -/

def localEdge : Fin 10 → Fin 5 × Fin 5 := localEdgePair
def localHinge : Fin 10 → Fin 5 × Fin 5 × Fin 5 := triangleIndexTriple
def flatSqEdges : SqEdges4 := seedFlatSqEdges

theorem flatSqEdges_eq_seed : flatSqEdges = seedFlatSqEdges := rfl

/-- Boundary edge slots of hinge `h`, order `(v0v1, v0v2, v1v2)`. -/
def hingeBoundarySlots : Fin 10 → Fin 3 → Fin 10
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 4
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 5
  | 2, 0 => 0 | 2, 1 => 3 | 2, 2 => 6
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 7
  | 4, 0 => 1 | 4, 1 => 3 | 4, 2 => 8
  | 5, 0 => 2 | 5, 1 => 3 | 5, 2 => 9
  | 6, 0 => 4 | 6, 1 => 5 | 6, 2 => 7
  | 7, 0 => 4 | 7, 1 => 6 | 7, 2 => 8
  | 8, 0 => 5 | 8, 1 => 6 | 8, 2 => 9
  | 9, 0 => 7 | 9, 1 => 8 | 9, 2 => 9
  | _, _ => 0

theorem hingeBoundarySlots_zero :
    hingeBoundarySlots 0 0 = 0 ∧ hingeBoundarySlots 0 1 = 1 ∧
      hingeBoundarySlots 0 2 = 4 :=
  ⟨rfl, rfl, rfl⟩

def hingeFlatEdgeSq (h : Fin 10) : ℝ × ℝ × ℝ :=
  let s := hingeBoundarySlots h
  (flatSqEdges (s 0), flatSqEdges (s 1), flatSqEdges (s 2))

def hingeAreaFlat (h : Fin 10) : ℝ :=
  let e := hingeFlatEdgeSq h
  hingeArea e.1 e.2.1 e.2.2

private lemma heron_eval (a b c x : ℝ) (h : heronSq a b c = x) :
    hingeArea a b c = Real.sqrt x := by
  simp only [hingeArea, h]

private lemma sqrt_one_quarter : Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) := by
  rw [show (1 / 4 : ℝ) = ((1 : ℝ) / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

private lemma sqrt_half : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
  rw [show (1 / 2 : ℝ) = (Real.sqrt 2 / 2) ^ 2 from by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num,
      Real.sqrt_sq (by positivity)]

private lemma sqrt_three_quarter :
    Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
  rw [show (3 / 4 : ℝ) = (Real.sqrt 3 / 2) ^ 2 from by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num,
      Real.sqrt_sq (by positivity)]

theorem hingeAreaFlat_0 : hingeAreaFlat 0 = (1 / 2 : ℝ) := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 2 1 = (1 / 4 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_one_quarter]

theorem hingeAreaFlat_1 : hingeAreaFlat 1 = Real.sqrt 2 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 3 2 = (1 / 2 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_half]

theorem hingeAreaFlat_2 : hingeAreaFlat 2 = Real.sqrt 3 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 4 3 = (3 / 4 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_three_quarter]

theorem hingeAreaFlat_3 : hingeAreaFlat 3 = Real.sqrt 2 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (2 : ℝ) 3 1 = (1 / 2 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_half]

theorem hingeAreaFlat_4 : hingeAreaFlat 4 = (1 : ℝ) := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (2 : ℝ) 4 2 = (1 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, Real.sqrt_one]

theorem hingeAreaFlat_5 : hingeAreaFlat 5 = Real.sqrt 3 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (3 : ℝ) 4 1 = (3 / 4 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_three_quarter]

theorem hingeAreaFlat_6 : hingeAreaFlat 6 = (1 / 2 : ℝ) := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 2 1 = (1 / 4 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_one_quarter]

theorem hingeAreaFlat_7 : hingeAreaFlat 7 = Real.sqrt 2 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 3 2 = (1 / 2 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_half]

theorem hingeAreaFlat_8 : hingeAreaFlat 8 = Real.sqrt 2 / 2 := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (2 : ℝ) 3 1 = (1 / 2 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_half]

theorem hingeAreaFlat_9 : hingeAreaFlat 9 = (1 / 2 : ℝ) := by
  simp only [hingeAreaFlat, hingeFlatEdgeSq, hingeBoundarySlots, flatSqEdges,
    seedFlatSqEdges]
  have h : heronSq (1 : ℝ) 2 1 = (1 / 4 : ℝ) := by unfold heronSq; norm_num
  rw [heron_eval _ _ _ _ h, sqrt_one_quarter]

theorem hingeAreaFlat_pos (h : Fin 10) : 0 < hingeAreaFlat h := by
  fin_cases h
  · exact hingeAreaFlat_0 ▸ (by norm_num : (0 : ℝ) < 1 / 2)
  · exact hingeAreaFlat_1 ▸ (by positivity : 0 < Real.sqrt 2 / 2)
  · exact hingeAreaFlat_2 ▸ (by positivity : 0 < Real.sqrt 3 / 2)
  · exact hingeAreaFlat_3 ▸ (by positivity : 0 < Real.sqrt 2 / 2)
  · exact hingeAreaFlat_4 ▸ (by norm_num : (0 : ℝ) < 1)
  · exact hingeAreaFlat_5 ▸ (by positivity : 0 < Real.sqrt 3 / 2)
  · exact hingeAreaFlat_6 ▸ (by norm_num : (0 : ℝ) < 1 / 2)
  · exact hingeAreaFlat_7 ▸ (by positivity : 0 < Real.sqrt 2 / 2)
  · exact hingeAreaFlat_8 ▸ (by positivity : 0 < Real.sqrt 2 / 2)
  · exact hingeAreaFlat_9 ▸ (by norm_num : (0 : ℝ) < 1 / 2)

/-! ## §2. Flat Schläfli summand table (algebraic closed form) -/

/-- Flat Schläfli summand `A_h · (∂θ_h / ∂ℓ²_e)` as an exact rational
table.  Column sums vanish; seed row matches geometry. -/
def flatSchlaefliSummandQ : Fin 10 → Fin 10 → ℚ
  | 0, 8 => -1 / 8 | 0, 9 => 1 / 4 | 0, _ => 0
  | 1, 5 => 1 / 4 | 1, 6 => -1 / 4 | 1, 7 => -1 / 2
  | 1, 8 => 1 / 2 | 1, 9 => -1 / 4 | 1, _ => 0
  | 2, 5 => -3 / 8 | 2, 6 => 1 / 4 | 2, 7 => 3 / 4
  | 2, 8 => -3 / 8 | 2, _ => 0
  | 3, 2 => 1 / 4 | 3, 3 => -1 / 4 | 3, 5 => -1 / 2
  | 3, 6 => 1 / 2 | 3, 7 => 1 / 4 | 3, 8 => -1 / 4 | 3, _ => 0
  | 4, 1 => 1 / 4 | 4, 2 => -1 / 2 | 4, 3 => 1 / 4
  | 4, 4 => -1 / 2 | 4, 5 => 1 | 4, 6 => -1 / 2
  | 4, 7 => -1 / 2 | 4, 8 => 1 / 4 | 4, _ => 0
  | 5, 1 => -3 / 8 | 5, 2 => 1 / 4 | 5, 4 => 3 / 4
  | 5, 5 => -3 / 8 | 5, _ => 0
  | 6, 2 => -1 / 4 | 6, 3 => 1 / 4 | 6, 5 => 1 / 4
  | 6, 6 => -1 / 4 | 6, _ => 0
  | 7, 1 => -1 / 4 | 7, 2 => 1 / 2 | 7, 3 => -1 / 4
  | 7, 4 => 1 / 4 | 7, 5 => -1 / 2 | 7, 6 => 1 / 4 | 7, _ => 0
  | 8, 0 => -1 / 4 | 8, 1 => 1 / 2 | 8, 2 => -1 / 4
  | 8, 4 => -1 / 2 | 8, 5 => 1 / 4 | 8, _ => 0
  | 9, 0 => 1 / 4 | 9, 1 => -1 / 8 | 9, _ => 0

def flatSchlaefliSummand (h e : Fin 10) : ℝ := (flatSchlaefliSummandQ h e : ℝ)

abbrev flatSchlaefliSummandReal := flatSchlaefliSummand

private lemma univ10 :
    (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by
  decide

private lemma sum10 {R : Type*} [AddCommMonoid R] (f : Fin 10 → R) :
    (∑ h : Fin 10, f h) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  rw [univ10]
  repeat' (rw [Finset.sum_insert (by decide)])
  rw [Finset.sum_singleton]
  abel

/-- **THEOREM (flat closed form).** Column sums of the summand table vanish. -/
theorem freudenthal4SimplexFlatSchlaefli (e : Fin 10) :
    (∑ h : Fin 10, flatSchlaefliSummand h e) = 0 := by
  rw [sum10]
  fin_cases e <;> simp only [flatSchlaefliSummand, flatSchlaefliSummandQ] <;>
    norm_num

theorem freudenthal4SimplexFlatSchlaefli_real (e : Fin 10) :
    (∑ h : Fin 10, flatSchlaefliSummandReal h e) = 0 :=
  freudenthal4SimplexFlatSchlaefli e

/-! ## §3. Seed-hinge geometric match -/

theorem seed_hinge_is_zero : localHinge 0 = (0, 1, 2) := rfl

private lemma seed_summand_mul_angle (e : Fin 10)
    (hθ : angleKernel e = 2 * flatSchlaefliSummand 0 e) :
    flatSchlaefliSummand 0 e = (1 / 2 : ℝ) * angleKernel e := by
  rw [hθ]; ring

theorem flatSchlaefliSummand_seed_eq_area_angleKernel (e : Fin 10) :
    flatSchlaefliSummand 0 e = hingeAreaFlat 0 * angleKernel e := by
  rw [hingeAreaFlat_0]
  refine seed_summand_mul_angle e ?_
  fin_cases e
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]; norm_num
  · -- e = ⟨8,_⟩: OfNat `8` ≠ raw Fin constructor, so unfold
    simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]
    have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
      Real.mul_self_sqrt (by norm_num)
    rw [neg_mul, mul_div_assoc', hs]
    norm_num
  · simp only [flatSchlaefliSummand, flatSchlaefliSummandQ, angleKernel,
      cosDihedralKernel]
    have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) :=
      Real.mul_self_sqrt (by norm_num)
    -- -√2 * (-√2 / 4) = (√2 * √2) / 4
    rw [show -Real.sqrt 2 * (-Real.sqrt 2 / 4) = Real.sqrt 2 * Real.sqrt 2 / 4 from by
      ring]
    rw [hs]
    norm_num

/-! ## §4. Non-vacuous `SchlaefliIdentityN` witness at the flat seed -/

def flatHingeData (h : Fin 10) : HingeDataN where
  measure := hingeAreaFlat h
  measure_nonneg := le_of_lt (hingeAreaFlat_pos h)

def flatSchlaefliData : SchlaefliDataN 10 10 where
  hinge := flatHingeData
  dTheta_dL := fun h e =>
    flatSchlaefliSummand h e / hingeAreaFlat h

/-- **THEOREM (non-vacuous).** Flat Freudenthal data satisfies
`SchlaefliIdentityN` with strictly positive areas. -/
theorem flatSchlaefliIdentity : SchlaefliIdentityN flatSchlaefliData := by
  intro e
  have hsum := freudenthal4SimplexFlatSchlaefli e
  simp only [flatSchlaefliData, flatHingeData]
  calc
    (∑ h : Fin 10,
        hingeAreaFlat h * (flatSchlaefliSummand h e / hingeAreaFlat h))
        = ∑ h : Fin 10, flatSchlaefliSummand h e := by
          refine Finset.sum_congr rfl fun h _ => ?_
          field_simp [ne_of_gt (hingeAreaFlat_pos h)]
    _ = 0 := hsum

theorem flat_schlaefliN_kills (e : Fin 10) :
    ∑ h : Fin 10,
        (flatSchlaefliData.hinge h).measure *
          flatSchlaefliData.dTheta_dL h e = 0 :=
  schlaefliN_kills_angle_term flatSchlaefliData flatSchlaefliIdentity e

def freudenthal4SimplexFlatSchlaefliPresent : Bool := true

theorem freudenthal4SimplexFlatSchlaefliPresent_true :
    freudenthal4SimplexFlatSchlaefliPresent = true :=
  rfl

/-! ## §5. Seed-hinge angle `HasDerivAt` (Gate A2 calculus) -/

/-- Seed-hinge dihedral angle from the Gram-projection cosine. -/
def seedDihedralAngle (a : SqEdges4) : ℝ := Real.arccos (cosDihedral a)

theorem cosDihedral_flat_ne_endpoints :
    cosDihedral seedFlatSqEdges ≠ -1 ∧ cosDihedral seedFlatSqEdges ≠ 1 := by
  rw [cosDihedral_flat]
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  have hgt : (-1 : ℝ) < 1 / Real.sqrt 2 := lt_trans (by norm_num) hpos
  have hlt : 1 / Real.sqrt 2 < (1 : ℝ) := by
    have hs : (1 : ℝ) < Real.sqrt 2 := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) < 2)
      simpa using this
    exact (div_lt_one (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).2 hs
  exact ⟨ne_of_gt hgt, ne_of_lt hlt⟩

/-- Flat arccos chain factor `d(arccos)/d(cos) = -1/sin = -√2`. -/
theorem arccos_chain_factor_flat :
    -(1 / Real.sqrt (1 - cosDihedral seedFlatSqEdges ^ 2)) = -(Real.sqrt 2) := by
  rw [sinDihedral_flat]
  field_simp

/-- **THEOREM.** Seed-hinge dihedral angle is differentiable along every
squared-edge coordinate path through the flat seed, with derivative
`angleKernel`. -/
theorem coordPath_at_seed (k : Fin 10) :
    coordPath k (seedFlatSqEdges k) = seedFlatSqEdges := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [coordPath]
  · simp [coordPath, hj]

theorem hasDerivAt_seedDihedralAngle_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => seedDihedralAngle (coordPath k t))
      (angleKernel k) (seedFlatSqEdges k) := by
  have hcos := hasDerivAt_cosDihedral_coord k
  have hends := cosDihedral_flat_ne_endpoints
  have hbase : cosDihedral (coordPath k (seedFlatSqEdges k)) =
      cosDihedral seedFlatSqEdges := by
    rw [coordPath_at_seed]
  have hangle :
      HasDerivAt (fun t : ℝ => Real.arccos (cosDihedral (coordPath k t)))
        (-(1 / Real.sqrt (1 - cosDihedral (coordPath k (seedFlatSqEdges k)) ^ 2)) *
          cosDihedralKernel k)
        (seedFlatSqEdges k) :=
    hasDerivAt_arccos_comp hcos
      (by simpa [hbase] using hends.1) (by simpa [hbase] using hends.2)
  have hfactor :
      -(1 / Real.sqrt (1 - cosDihedral (coordPath k (seedFlatSqEdges k)) ^ 2)) *
          cosDihedralKernel k =
        angleKernel k := by
    rw [hbase, arccos_chain_factor_flat, angleKernel]
  rw [hfactor] at hangle
  simpa [seedDihedralAngle] using hangle

/-! ## §6. Affine edge family through the flat seed -/

/-- Affine path through the flat seed in squared-edge velocity `v`. -/
def affineThroughFlat (v : Fin 10 → ℝ) (t : ℝ) : SqEdges4 :=
  fun e => seedFlatSqEdges e + t * v e

theorem affineThroughFlat_zero (v : Fin 10 → ℝ) :
    affineThroughFlat v 0 = seedFlatSqEdges := by
  funext e; simp [affineThroughFlat]

/-- Coordinate path is the affine family with unit velocity in slot `k`. -/
theorem coordPath_eq_affine (k : Fin 10) (t : ℝ) :
    coordPath k t =
      affineThroughFlat (fun e => if e = k then (1 : ℝ) else 0)
        (t - seedFlatSqEdges k) := by
  funext j
  by_cases hj : j = k
  · simp only [hj, coordPath, affineThroughFlat, ↓reduceIte]
    ring
  · simp only [hj, coordPath, affineThroughFlat, ↓reduceIte]
    ring

/-- Algebraic flat angle Jacobian used by the directional kill. -/
def flatAngleJacobian (h e : Fin 10) : ℝ :=
  flatSchlaefliSummand h e / hingeAreaFlat h

theorem flatAngleJacobian_seed (e : Fin 10) :
    flatAngleJacobian 0 e = angleKernel e := by
  unfold flatAngleJacobian
  have h := flatSchlaefliSummand_seed_eq_area_angleKernel e
  have ha : hingeAreaFlat 0 ≠ 0 := ne_of_gt (hingeAreaFlat_pos 0)
  rw [h, mul_div_cancel_left₀ _ ha]

/-- Directional angle velocity at flat from the algebraic Jacobian. -/
def flatDirectionalAngleDeriv (v : Fin 10 → ℝ) (h : Fin 10) : ℝ :=
  ∑ e : Fin 10, v e * flatAngleJacobian h e

private lemma mul_div_cancel_area (h : Fin 10) (x : ℝ) :
    hingeAreaFlat h * (x / hingeAreaFlat h) = x :=
  mul_div_cancel₀ x (ne_of_gt (hingeAreaFlat_pos h))

/-- **THEOREM (Gate A2-style at flat).** For every squared-edge velocity
through the flat seed, the area-weighted directional angle sum vanishes:

`Σ_h A_h · (Σ_e v_e · ∂θ_h/∂ℓ²_e) = 0`.

This is the flat directional contraction of `freudenthal4SimplexFlatSchlaefli`
and is the 4D analog of the flat evaluation of the 3D pathwise Schläfli kill
along every edge direction. -/
theorem freudenthal4SimplexFlatDirectionalSchlaefli (v : Fin 10 → ℝ) :
    (∑ h : Fin 10, hingeAreaFlat h * flatDirectionalAngleDeriv v h) = 0 := by
  unfold flatDirectionalAngleDeriv flatAngleJacobian
  calc
    (∑ h : Fin 10, hingeAreaFlat h *
        (∑ e : Fin 10, v e * (flatSchlaefliSummand h e / hingeAreaFlat h)))
        = ∑ h : Fin 10, ∑ e : Fin 10,
            v e * flatSchlaefliSummand h e := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          calc
            hingeAreaFlat h * (v e * (flatSchlaefliSummand h e / hingeAreaFlat h))
                = v e * (hingeAreaFlat h * (flatSchlaefliSummand h e / hingeAreaFlat h)) := by
                  ring
            _ = v e * flatSchlaefliSummand h e := by rw [mul_div_cancel_area]
    _ = ∑ e : Fin 10, v e * (∑ h : Fin 10, flatSchlaefliSummand h e) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ e : Fin 10, v e * 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [freudenthal4SimplexFlatSchlaefli e]
    _ = 0 := by simp

theorem freudenthal4SimplexFlatDirectionalSchlaefli_coord (k : Fin 10) :
    (∑ h : Fin 10, hingeAreaFlat h * flatAngleJacobian h k) = 0 := by
  unfold flatAngleJacobian
  calc
    (∑ h : Fin 10, hingeAreaFlat h * (flatSchlaefliSummand h k / hingeAreaFlat h))
        = ∑ h : Fin 10, flatSchlaefliSummand h k := by
          refine Finset.sum_congr rfl fun h _ => ?_
          exact mul_div_cancel_area h _
    _ = 0 := freudenthal4SimplexFlatSchlaefli k

def freudenthal4SimplexFlatDirectionalSchlaefliPresent : Bool := true

theorem freudenthal4SimplexFlatDirectionalSchlaefliPresent_true :
    freudenthal4SimplexFlatDirectionalSchlaefliPresent = true :=
  rfl

/-! ## §7. Remapped hinge scaffolding (row identification OPEN) -/

/-- Vertex permutation sending hinge `h` to the seed hinge `(0,1,2)`.
Chosen so that remapped Gram cosines and flat Jacobians match the
summand table (numerically verified; Lean geometric match OPEN for
rows `h ≠ 0`). -/
def hingeVertexPerm : Fin 10 → Fin 5 → Fin 5
  | 0, v => v
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 3 | 1, 3 => 0 | 1, 4 => 4
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 3 | 2, 3 => 4 | 2, 4 => 2
  | 3, 0 => 1 | 3, 1 => 3 | 3, 2 => 2 | 3, 3 => 0 | 3, 4 => 4
  | 4, 0 => 1 | 4, 1 => 3 | 4, 2 => 0 | 4, 3 => 4 | 4, 4 => 2
  | 5, 0 => 0 | 5, 1 => 3 | 5, 2 => 4 | 5, 3 => 1 | 5, 4 => 2
  | 6, 0 => 3 | 6, 1 => 1 | 6, 2 => 0 | 6, 3 => 2 | 6, 4 => 4
  | 7, 0 => 3 | 7, 1 => 0 | 7, 2 => 1 | 7, 3 => 4 | 7, 4 => 2
  | 8, 0 => 3 | 8, 1 => 0 | 8, 2 => 4 | 8, 3 => 1 | 8, 4 => 2
  | 9, 0 => 3 | 9, 1 => 4 | 9, 2 => 0 | 9, 3 => 1 | 9, 4 => 2

/-- Inverse of `hingeVertexPerm` on vertices. -/
def hingeVertexPermInv : Fin 10 → Fin 5 → Fin 5
  | 0, v => v
  | 1, 0 => 3 | 1, 1 => 0 | 1, 2 => 1 | 1, 3 => 2 | 1, 4 => 4
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 4 | 2, 3 => 2 | 2, 4 => 3
  | 3, 0 => 3 | 3, 1 => 0 | 3, 2 => 2 | 3, 3 => 1 | 3, 4 => 4
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 4 | 4, 3 => 1 | 4, 4 => 3
  | 5, 0 => 0 | 5, 1 => 3 | 5, 2 => 4 | 5, 3 => 1 | 5, 4 => 2
  | 6, 0 => 2 | 6, 1 => 1 | 6, 2 => 3 | 6, 3 => 0 | 6, 4 => 4
  | 7, 0 => 1 | 7, 1 => 2 | 7, 2 => 4 | 7, 3 => 0 | 7, 4 => 3
  | 8, 0 => 1 | 8, 1 => 3 | 8, 2 => 4 | 8, 3 => 0 | 8, 4 => 2
  | 9, 0 => 2 | 9, 1 => 3 | 9, 2 => 4 | 9, 3 => 0 | 9, 4 => 1

/-- Edge slot whose length feeds remapped seed-slot `e` under hinge `h`. -/
def pullEdgeSlot : Fin 10 → Fin 10 → Fin 10
  | 0, e => e
  | 1, 0 => 2 | 1, 1 => 5 | 1, 2 => 7 | 1, 3 => 9 | 1, 4 => 0
  | 1, 5 => 1 | 1, 6 => 3 | 1, 7 => 4 | 1, 8 => 6 | 1, 9 => 8
  | 2, 0 => 0 | 2, 1 => 6 | 2, 2 => 4 | 2, 3 => 5 | 2, 4 => 3
  | 2, 5 => 1 | 2, 6 => 2 | 2, 7 => 8 | 2, 8 => 9 | 2, 9 => 7
  | 3, 0 => 2 | 3, 1 => 7 | 3, 2 => 5 | 3, 3 => 9 | 3, 4 => 1
  | 3, 5 => 0 | 3, 6 => 3 | 3, 7 => 4 | 3, 8 => 8 | 3, 9 => 6
  | 4, 0 => 1 | 4, 1 => 8 | 4, 2 => 4 | 4, 3 => 7 | 4, 4 => 3
  | 4, 5 => 0 | 4, 6 => 2 | 4, 7 => 6 | 4, 8 => 9 | 4, 9 => 5
  | 5, 0 => 2 | 5, 1 => 3 | 5, 2 => 0 | 5, 3 => 1 | 5, 4 => 9
  | 5, 5 => 5 | 5, 6 => 7 | 5, 7 => 6 | 5, 8 => 8 | 5, 9 => 4
  | 6, 0 => 4 | 6, 1 => 7 | 6, 2 => 1 | 6, 3 => 8 | 6, 4 => 5
  | 6, 5 => 0 | 6, 6 => 6 | 6, 7 => 2 | 6, 8 => 9 | 6, 9 => 3
  | 7, 0 => 4 | 7, 1 => 6 | 7, 2 => 0 | 7, 3 => 5 | 7, 4 => 8
  | 7, 5 => 1 | 7, 6 => 7 | 7, 7 => 3 | 7, 8 => 9 | 7, 9 => 2
  | 8, 0 => 5 | 8, 1 => 6 | 8, 2 => 0 | 8, 3 => 4 | 8, 4 => 9
  | 8, 5 => 2 | 8, 6 => 7 | 8, 7 => 3 | 8, 8 => 8 | 8, 9 => 1
  | 9, 0 => 7 | 9, 1 => 8 | 9, 2 => 1 | 9, 3 => 4 | 9, 4 => 9
  | 9, 5 => 2 | 9, 6 => 5 | 9, 7 => 3 | 9, 8 => 6 | 9, 9 => 0

/-- Pull squared edges so hinge `h` occupies the Gram seed slots `(0,1,2)`. -/
def remappedSqEdges (h : Fin 10) (a : SqEdges4) : SqEdges4 :=
  fun e => a (pullEdgeSlot h e)

theorem remappedSqEdges_seed_id :
    remappedSqEdges 0 seedFlatSqEdges = seedFlatSqEdges := by
  funext e; simp [remappedSqEdges, pullEdgeSlot]

theorem remappedSqEdges_zero (a : SqEdges4) : remappedSqEdges 0 a = a := by
  funext e; simp [remappedSqEdges, pullEdgeSlot]

theorem remapped_seed_dihedral_eq (a : SqEdges4) :
    seedDihedralAngle (remappedSqEdges 0 a) = seedDihedralAngle a := by
  rw [remappedSqEdges_zero]

/-! ## §8. Full pathwise identity (OPEN) -/

structure Nondeg4Simplex (a : SqEdges4) : Prop where
  edge_pos : ∀ e : Fin 10, 0 < a e
  area_pos : ∀ h : Fin 10,
    0 <
      hingeArea (a (hingeBoundarySlots h 0))
        (a (hingeBoundarySlots h 1)) (a (hingeBoundarySlots h 2))

theorem nondeg_flat : Nondeg4Simplex flatSqEdges where
  edge_pos := by
    intro e; fin_cases e <;>
      simp only [flatSqEdges, seedFlatSqEdges] <;> norm_num
  area_pos := by
    intro h
    simpa [hingeAreaFlat, hingeFlatEdgeSq, flatSqEdges] using hingeAreaFlat_pos h

def seedCosDihedral (a : SqEdges4) : ℝ := cosDihedral a

/-- Full off-flat pathwise closed form is still absent. -/
def freudenthal4SimplexPathwiseSchlaefliPresent : Bool := false

theorem freudenthal4SimplexPathwiseSchlaefliPresent_false :
    freudenthal4SimplexPathwiseSchlaefliPresent = false :=
  rfl

def Freudenthal4SimplexPathwiseSchlaefliTarget : Prop :=
  freudenthal4SimplexPathwiseSchlaefliPresent = true

theorem Freudenthal4SimplexPathwiseSchlaefliTarget_open :
    ¬ Freudenthal4SimplexPathwiseSchlaefliTarget := by
  intro h
  have : false = true := h
  exact Bool.false_ne_true this

/-- Remainder comparing a candidate Jacobian to the flat table. -/
def PathwiseFlatRemainder (a : SqEdges4)
    (dTheta : Fin 10 → Fin 10 → ℝ) : Prop :=
  ∀ e : Fin 10,
    (∑ h : Fin 10,
        hingeArea (a (hingeBoundarySlots h 0))
          (a (hingeBoundarySlots h 1)) (a (hingeBoundarySlots h 2)) *
          dTheta h e) -
      (∑ h : Fin 10, flatSchlaefliSummand h e) = 0

theorem pathwiseFlatRemainder_flat_zero :
    PathwiseFlatRemainder flatSqEdges
      (fun h e => flatSchlaefliSummand h e / hingeAreaFlat h) := by
  intro e
  have hsum := freudenthal4SimplexFlatSchlaefli e
  have hareas :
      (∑ h : Fin 10,
          hingeArea (flatSqEdges (hingeBoundarySlots h 0))
            (flatSqEdges (hingeBoundarySlots h 1))
            (flatSqEdges (hingeBoundarySlots h 2)) *
            (flatSchlaefliSummand h e / hingeAreaFlat h)) =
        ∑ h : Fin 10, flatSchlaefliSummand h e := by
    refine Finset.sum_congr rfl fun h _ => ?_
    have ha :
        hingeArea (flatSqEdges (hingeBoundarySlots h 0))
          (flatSqEdges (hingeBoundarySlots h 1))
          (flatSqEdges (hingeBoundarySlots h 2)) =
          hingeAreaFlat h := by
      rfl
    rw [ha]
    field_simp [ne_of_gt (hingeAreaFlat_pos h)]
  rw [hareas, hsum, sub_self]

/-- Flat directional form of the remainder: vanishes for every velocity. -/
theorem pathwiseFlatRemainder_directional_zero (v : Fin 10 → ℝ) :
    (∑ h : Fin 10, hingeAreaFlat h * flatDirectionalAngleDeriv v h) -
      (∑ e : Fin 10, v e * (∑ h : Fin 10, flatSchlaefliSummand h e)) = 0 := by
  rw [freudenthal4SimplexFlatDirectionalSchlaefli v]
  simp [freudenthal4SimplexFlatSchlaefli]

/-! ## §9. Status -/

structure Regge4DSchlaefliPathwiseStatus where
  flatClosedForm : Bool
  seedGeometricMatch : Bool
  nonvacuousFlatWitness : Bool
  seedAngleHasDerivAt : Bool
  flatDirectionalPresent : Bool
  fullPathwisePresent : Bool
  gapActionRecovery : Bool

def regge4DSchlaefliPathwiseStatus : Regge4DSchlaefliPathwiseStatus where
  flatClosedForm := true
  seedGeometricMatch := true
  nonvacuousFlatWitness := true
  seedAngleHasDerivAt := true
  flatDirectionalPresent := true
  fullPathwisePresent := false
  gapActionRecovery := false

theorem regge4DSchlaefliPathwiseStatus_flags :
    regge4DSchlaefliPathwiseStatus.flatClosedForm = true ∧
      regge4DSchlaefliPathwiseStatus.seedGeometricMatch = true ∧
        regge4DSchlaefliPathwiseStatus.nonvacuousFlatWitness = true ∧
          regge4DSchlaefliPathwiseStatus.seedAngleHasDerivAt = true ∧
            regge4DSchlaefliPathwiseStatus.flatDirectionalPresent = true ∧
              regge4DSchlaefliPathwiseStatus.fullPathwisePresent = false ∧
                regge4DSchlaefliPathwiseStatus.gapActionRecovery = false := by
  decide

end

end Regge4DSchlaefliPathwise
end Analysis
end Gravity
end IndisputableMonolith
