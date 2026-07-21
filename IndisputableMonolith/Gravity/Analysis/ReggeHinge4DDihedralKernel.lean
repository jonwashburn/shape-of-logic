import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D seed-hinge dihedral cosine kernel at flat

QG full-theory campaign, next kernel-checked increment after
`ReggeHinge4DFlatKernel`.  Imports the Freudenthal incidence layer and
the 15-class stencil; never redefines their API.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: the seed triangle hinge `{0, e₀, e₀+e₁}` inside its **two**
  seed-cell Freudenthal 4-simplices only (the permutations beginning
  `(0,1,…)`; both share the same local squared-edge vector, proved
  against the incidence layer's `localEdgeMask`).  The full lattice
  orbit sum over all hinges is OPEN.
* This does **not** complete the flat Hessian of the 4D Regge action.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (deliverable A)

1. **Gram-projection cosine.** `cosDihedral` of the seed-hinge dihedral
   angle as an explicit function of the ten local squared edge lengths
   (inner product / norms of the two apex vectors projected orthogonal
   to the hinge plane, in cleared-denominator Gram form).
2. **Flat value.** `cosDihedral = 1/√2` at the flat Freudenthal point
   (equivalently `cos² = 1/2`, `sin = 1/√2`); transcendental-free
   arithmetic throughout (`sin² = 1 − cos²`).
3. **All ten coordinate derivatives** (`HasDerivAt`, deliverable A):
   slot 8 ↦ `√2/8`, slot 9 ↦ `-√2/4`, slots 0–7 ↦ `0`, packaged as
   `cosDihedralKernel` with the master theorem
   `hasDerivAt_cosDihedral_coord`.
4. **Angle and two-simplex partial deficit kernels.** Via the arccos
   chain factor `-1/sin = -√2` at flat: local angle kernel
   `(slot 8, slot 9) ↦ (-1/4, 1/2)`; assembled on the 15 edge classes
   through each seed simplex's `localEdgeClass` table, the two-simplex
   partial deficit gradient `∂(2π - θ₀ - θ₁)/∂ℓ²` is supported on
   classes `(3, 7, 11)` with values `(-1/2, -1/2, +1/2)`.
5. **Nonvacuity, symmetry, decoy.** Slot-9 kernel nonzero; the class
   kernel is invariant under the hinge-fixing axis swap `2 ↔ 3`;
   uniform squared-length scaling gives `-√2/8 ≠ 0` (computed, not
   assumed), while the true homothety direction gives `0` exactly as
   scale invariance demands.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DDihedralKernel

open BigOperators
open ReggeHinge4DFlatKernel
open ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Local squared edges of the seed simplices -/

abbrev SqEdges4 := Fin 10 → ℝ

/-- Flat Freudenthal squared lengths shared by both seed simplices,
in the local slot order `localEdgePair` of the incidence layer. -/
def seedFlatSqEdges : SqEdges4
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1
  | 5 => 2 | 6 => 3 | 7 => 1 | 8 => 2 | 9 => 1

@[simp] lemma seedFlat_0 : seedFlatSqEdges 0 = 1 := rfl
@[simp] lemma seedFlat_1 : seedFlatSqEdges 1 = 2 := rfl
@[simp] lemma seedFlat_2 : seedFlatSqEdges 2 = 3 := rfl
@[simp] lemma seedFlat_3 : seedFlatSqEdges 3 = 4 := rfl
@[simp] lemma seedFlat_4 : seedFlatSqEdges 4 = 1 := rfl
@[simp] lemma seedFlat_5 : seedFlatSqEdges 5 = 2 := rfl
@[simp] lemma seedFlat_6 : seedFlatSqEdges 6 = 3 := rfl
@[simp] lemma seedFlat_7 : seedFlatSqEdges 7 = 1 := rfl
@[simp] lemma seedFlat_8 : seedFlatSqEdges 8 = 2 := rfl
@[simp] lemma seedFlat_9 : seedFlatSqEdges 9 = 1 := rfl

/-- ℕ mirror of the flat squared lengths (for kernel-decidable
comparison with the incidence layer's masks). -/
def seedFlatMaskNat : Fin 10 → ℕ
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1
  | 5 => 2 | 6 => 3 | 7 => 1 | 8 => 2 | 9 => 1

lemma seedFlat_eq_cast (e : Fin 10) :
    seedFlatSqEdges e = (seedFlatMaskNat e : ℝ) := by
  fin_cases e <;> norm_num [seedFlatSqEdges, seedFlatMaskNat]

/-- Bit weight of a 4-axis mask: unit Freudenthal steps flip one axis
each, so the flat squared edge length is the number of set bits of the
incidence layer's XOR mask. -/
def maskWeight (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0)
    + (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0)

/-- THEOREM: the flat local squared lengths agree with the bit weights
of the incidence layer's edge masks for seed simplex `0`. -/
theorem seedFlatSqEdges_simplex0 (e : Fin 10) :
    seedFlatSqEdges e = (maskWeight (localEdgeMask 0 e) : ℝ) := by
  have h : ∀ e : Fin 10,
      seedFlatMaskNat e = maskWeight (localEdgeMask 0 e) := by decide
  rw [seedFlat_eq_cast, h e]

/-- THEOREM: same agreement for seed simplex `1`. -/
theorem seedFlatSqEdges_simplex1 (e : Fin 10) :
    seedFlatSqEdges e = (maskWeight (localEdgeMask 1 e) : ℝ) := by
  have h : ∀ e : Fin 10,
      seedFlatMaskNat e = maskWeight (localEdgeMask 1 e) := by decide
  rw [seedFlat_eq_cast, h e]

/-! ## §2. Gram-projection cosine -/

/-- `4⟨a,a⟩⟨b,b⟩ − (2⟨a,b⟩)²` for the hinge edge-vectors from vertex 0
(`4·` the squared hinge area factor). -/
def hingeGramDet (a : SqEdges4) : ℝ :=
  4 * a 0 * a 1 - (a 0 + a 1 - a 4) ^ 2

/-- Numerator of `⟨c',d'⟩ · hingeGramDet` (apex projections orthogonal
to the hinge plane). -/
def apexDotNum (a : SqEdges4) : ℝ :=
  let den := hingeGramDet a
  (-2) * a 0 * (a 1 + a 2 - a 7) * (a 1 + a 3 - a 8)
    + (-2) * a 1 * (a 0 + a 2 - a 5) * (a 0 + a 3 - a 6)
    + den * (a 2 + a 3 - a 9)
    + (a 0 + a 1 - a 4) * (a 0 + a 2 - a 5) * (a 1 + a 3 - a 8)
    + (a 0 + a 1 - a 4) * (a 0 + a 3 - a 6) * (a 1 + a 2 - a 7)

/-- Numerator of `|c'|² · hingeGramDet`. -/
def apex3NormSqNum (a : SqEdges4) : ℝ :=
  let den := hingeGramDet a
  (-a 0) * (a 1 + a 2 - a 7) ^ 2 + (-a 1) * (a 0 + a 2 - a 5) ^ 2
    + a 2 * den
    + (a 0 + a 1 - a 4) * (a 0 + a 2 - a 5) * (a 1 + a 2 - a 7)

/-- Numerator of `|d'|² · hingeGramDet`. -/
def apex4NormSqNum (a : SqEdges4) : ℝ :=
  let den := hingeGramDet a
  (-a 0) * (a 1 + a 3 - a 8) ^ 2 + (-a 1) * (a 0 + a 3 - a 6) ^ 2
    + a 3 * den
    + (a 0 + a 1 - a 4) * (a 0 + a 3 - a 6) * (a 1 + a 3 - a 8)

def apexDot (a : SqEdges4) : ℝ := apexDotNum a / (2 * hingeGramDet a)
def apex3NormSq (a : SqEdges4) : ℝ := apex3NormSqNum a / hingeGramDet a
def apex4NormSq (a : SqEdges4) : ℝ := apex4NormSqNum a / hingeGramDet a

/-- Cosine of the seed-hinge dihedral angle inside one 4-simplex. -/
def cosDihedral (a : SqEdges4) : ℝ :=
  apexDot a / Real.sqrt (apex3NormSq a * apex4NormSq a)

/-- THEOREM: cleared-denominator form of the cosine wherever the hinge
Gram determinant is positive. -/
theorem cos_numForm (a : SqEdges4) (hden : 0 < hingeGramDet a) :
    cosDihedral a =
      apexDotNum a /
        (2 * Real.sqrt (apex3NormSqNum a * apex4NormSqNum a)) := by
  have hden' : hingeGramDet a ≠ 0 := ne_of_gt hden
  simp only [cosDihedral, apexDot, apex3NormSq, apex4NormSq]
  rw [show apex3NormSqNum a / hingeGramDet a *
        (apex4NormSqNum a / hingeGramDet a)
      = apex3NormSqNum a * apex4NormSqNum a / (hingeGramDet a) ^ 2 from by
    rw [div_mul_div_comm, pow_two]]
  rw [Real.sqrt_div' (apex3NormSqNum a * apex4NormSqNum a)
    (sq_nonneg (hingeGramDet a))]
  rw [Real.sqrt_sq hden.le]
  by_cases hPQ : Real.sqrt (apex3NormSqNum a * apex4NormSqNum a) = 0
  · rw [hPQ]
    simp
  · field_simp

/-! ## §3. Flat evaluation -/

theorem hingeGramDet_flat : hingeGramDet seedFlatSqEdges = 4 := by
  norm_num [hingeGramDet]

theorem apexDotNum_flat : apexDotNum seedFlatSqEdges = 8 := by
  norm_num [apexDotNum, hingeGramDet]

theorem apex3NormSqNum_flat : apex3NormSqNum seedFlatSqEdges = 4 := by
  norm_num [apex3NormSqNum, hingeGramDet]

theorem apex4NormSqNum_flat : apex4NormSqNum seedFlatSqEdges = 8 := by
  norm_num [apex4NormSqNum, hingeGramDet]

/-- THEOREM: flat cosine equals `1/√2`. -/
theorem cosDihedral_flat :
    cosDihedral seedFlatSqEdges = 1 / Real.sqrt 2 := by
  rw [cos_numForm _ (by rw [hingeGramDet_flat]; norm_num),
    apexDotNum_flat, apex3NormSqNum_flat, apex4NormSqNum_flat]
  rw [show (4 : ℝ) * 8 = 32 by norm_num,
    show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2) 2,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [div_eq_div_iff (by positivity)
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))]
  ring

/-- THEOREM: flat cosine squared is `1/2` (transcendental-free form). -/
theorem cosDihedral_flat_sq :
    cosDihedral seedFlatSqEdges ^ 2 = (1 / 2 : ℝ) := by
  rw [cosDihedral_flat, div_pow, one_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem cosDihedral_flat_pos : 0 < cosDihedral seedFlatSqEdges := by
  rw [cosDihedral_flat]; positivity

/-- THEOREM: flat sine from `sin² = 1 − cos²`, positive branch. -/
theorem sinDihedral_flat :
    Real.sqrt (1 - cosDihedral seedFlatSqEdges ^ 2) = 1 / Real.sqrt 2 := by
  rw [cosDihedral_flat_sq, show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) 2, Real.sqrt_one]

/-! ## §4. Kernel table -/

/-- Flat cosine derivatives with respect to the ten local squared
lengths (all THEOREM via `hasDerivAt_cosDihedral_coord`). -/
def cosDihedralKernel : Fin 10 → ℝ
  | ⟨8, _⟩ => Real.sqrt 2 / 8
  | ⟨9, _⟩ => -(Real.sqrt 2) / 4
  | _ => 0

lemma cosDihedralKernel_eight : cosDihedralKernel 8 = Real.sqrt 2 / 8 := rfl
lemma cosDihedralKernel_nine : cosDihedralKernel 9 = -(Real.sqrt 2) / 4 := rfl

lemma cosDihedralKernel_le_seven (k : Fin 10) (hk : k.val ≤ 7) :
    cosDihedralKernel k = 0 := by
  fin_cases k <;> first | rfl | exact absurd hk (by decide)

/-- One-parameter path varying local slot `k` about the flat point. -/
def coordPath (k : Fin 10) (t : ℝ) : SqEdges4 :=
  fun j => if j = k then t else seedFlatSqEdges j

/-! ## §5. Generic derivative machinery

Every slot restriction of `cosDihedral` is `N(t) / (2√(P(t)·Q(t)))`
for quadratics `N, P, Q` with flat values `(8, 4, 8)`; the flat
derivative is `√2·(2N' − 2P' − Q')/32`.  One lemma serves all ten
slots. -/

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

private lemma hasDerivAt_numForm {N P Q : ℝ → ℝ} {t0 N' P' Q' : ℝ}
    (hN : HasDerivAt N N' t0) (hP : HasDerivAt P P' t0)
    (hQ : HasDerivAt Q Q' t0)
    (hN0 : N t0 = 8) (hP0 : P t0 = 4) (hQ0 : Q t0 = 8) :
    HasDerivAt (fun t => N t / (2 * Real.sqrt (P t * Q t)))
      (Real.sqrt 2 * (2 * N' - 2 * P' - Q') / 32) t0 := by
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
    rw [hPQ0]
    positivity
  have hdiv := hN.div hden hdenne
  convert hdiv using 1
  have h32 : Real.sqrt (P t0 * Q t0) = 4 * Real.sqrt 2 := by
    rw [hPQ0, show (32 : ℝ) = 4 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 ^ 2) 2,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [h32, hN0, hP0, hQ0]
  have hpow : (2 * (4 * Real.sqrt 2)) ^ 2 = 128 := by
    rw [show (2 * (4 * Real.sqrt 2)) ^ 2
        = 64 * (Real.sqrt 2 * Real.sqrt 2) from by ring, hs2]
    norm_num
  rw [hpow]
  have hdiv2 : ∀ X : ℝ,
      X / (2 * (4 * Real.sqrt 2)) = X * Real.sqrt 2 / 16 := by
    intro X
    rw [div_eq_div_iff (by positivity) (by norm_num : (16 : ℝ) ≠ 0)]
    rw [show X * Real.sqrt 2 * (2 * (4 * Real.sqrt 2))
        = X * 8 * (Real.sqrt 2 * Real.sqrt 2) from by ring, hs2]
    ring
  rw [hdiv2]
  ring

private lemma hasDerivAt_slot (k : Fin 10) (t0 : ℝ)
    (aN bN cN aP bP cP aQ bQ cQ aD bD cD : ℝ)
    (hpath : ∀ t : ℝ,
      apexDotNum (coordPath k t) = aN * t ^ 2 + bN * t + cN
      ∧ apex3NormSqNum (coordPath k t) = aP * t ^ 2 + bP * t + cP
      ∧ apex4NormSqNum (coordPath k t) = aQ * t ^ 2 + bQ * t + cQ
      ∧ hingeGramDet (coordPath k t) = aD * t ^ 2 + bD * t + cD)
    (hN0 : aN * t0 ^ 2 + bN * t0 + cN = 8)
    (hP0 : aP * t0 ^ 2 + bP * t0 + cP = 4)
    (hQ0 : aQ * t0 ^ 2 + bQ * t0 + cQ = 8)
    (hD0 : 0 < aD * t0 ^ 2 + bD * t0 + cD) :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath k t))
      (Real.sqrt 2 * (2 * (2 * aN * t0 + bN) - 2 * (2 * aP * t0 + bP)
        - (2 * aQ * t0 + bQ)) / 32) t0 := by
  have hN := hasDerivAt_quadPoly aN bN cN t0
  have hP := hasDerivAt_quadPoly aP bP cP t0
  have hQ := hasDerivAt_quadPoly aQ bQ cQ t0
  have hmain := hasDerivAt_numForm hN hP hQ hN0 hP0 hQ0
  refine hmain.congr_of_eventuallyEq ?_
  have hDcont : Continuous fun t : ℝ => aD * t ^ 2 + bD * t + cD := by
    continuity
  have hDev : ∀ᶠ t in nhds t0, 0 < aD * t ^ 2 + bD * t + cD :=
    (hDcont.tendsto t0).eventually (eventually_gt_nhds hD0)
  filter_upwards [hDev] with t ht
  have hp := hpath t
  rw [cos_numForm (coordPath k t) (by rw [hp.2.2.2]; exact ht),
    hp.1, hp.2.1, hp.2.2.1]

/-! ## §6. Per-slot path polynomials (verified against the Gram form) -/

private lemma path0_polys : ∀ t : ℝ,
    apexDotNum (coordPath 0 t) = (-2) * t ^ 2 + 12 * t + (-2)
    ∧ apex3NormSqNum (coordPath 0 t) = (-1) * t ^ 2 + 6 * t + (-1)
    ∧ apex4NormSqNum (coordPath 0 t) = (-2) * t ^ 2 + 12 * t + (-2)
    ∧ hingeGramDet (coordPath 0 t) = (-1) * t ^ 2 + 6 * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path1_polys : ∀ t : ℝ,
    apexDotNum (coordPath 1 t) = (-4) * t ^ 2 + 16 * t + (-8)
    ∧ apex3NormSqNum (coordPath 1 t) = (-2) * t ^ 2 + 8 * t + (-4)
    ∧ apex4NormSqNum (coordPath 1 t) = (-3) * t ^ 2 + 12 * t + (-4)
    ∧ hingeGramDet (coordPath 1 t) = (-1) * t ^ 2 + 4 * t + 0 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path2_polys : ∀ t : ℝ,
    apexDotNum (coordPath 2 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ apex3NormSqNum (coordPath 2 t) = (-1) * t ^ 2 + 6 * t + (-5)
    ∧ apex4NormSqNum (coordPath 2 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ hingeGramDet (coordPath 2 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path3_polys : ∀ t : ℝ,
    apexDotNum (coordPath 3 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ apex3NormSqNum (coordPath 3 t) = 0 * t ^ 2 + 0 * t + 4
    ∧ apex4NormSqNum (coordPath 3 t) = (-1) * t ^ 2 + 8 * t + (-8)
    ∧ hingeGramDet (coordPath 3 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path4_polys : ∀ t : ℝ,
    apexDotNum (coordPath 4 t) = (-6) * t ^ 2 + 20 * t + (-6)
    ∧ apex3NormSqNum (coordPath 4 t) = (-3) * t ^ 2 + 10 * t + (-3)
    ∧ apex4NormSqNum (coordPath 4 t) = (-4) * t ^ 2 + 16 * t + (-4)
    ∧ hingeGramDet (coordPath 4 t) = (-1) * t ^ 2 + 6 * t + (-1) := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path5_polys : ∀ t : ℝ,
    apexDotNum (coordPath 5 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ apex3NormSqNum (coordPath 5 t) = (-2) * t ^ 2 + 8 * t + (-4)
    ∧ apex4NormSqNum (coordPath 5 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ hingeGramDet (coordPath 5 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path6_polys : ∀ t : ℝ,
    apexDotNum (coordPath 6 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ apex3NormSqNum (coordPath 6 t) = 0 * t ^ 2 + 0 * t + 4
    ∧ apex4NormSqNum (coordPath 6 t) = (-2) * t ^ 2 + 12 * t + (-10)
    ∧ hingeGramDet (coordPath 6 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path7_polys : ∀ t : ℝ,
    apexDotNum (coordPath 7 t) = 0 * t ^ 2 + 4 * t + 4
    ∧ apex3NormSqNum (coordPath 7 t) = (-1) * t ^ 2 + 6 * t + (-1)
    ∧ apex4NormSqNum (coordPath 7 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ hingeGramDet (coordPath 7 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path8_polys : ∀ t : ℝ,
    apexDotNum (coordPath 8 t) = 0 * t ^ 2 + 4 * t + 0
    ∧ apex3NormSqNum (coordPath 8 t) = 0 * t ^ 2 + 0 * t + 4
    ∧ apex4NormSqNum (coordPath 8 t) = (-1) * t ^ 2 + 8 * t + (-4)
    ∧ hingeGramDet (coordPath 8 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

private lemma path9_polys : ∀ t : ℝ,
    apexDotNum (coordPath 9 t) = 0 * t ^ 2 + (-4) * t + 12
    ∧ apex3NormSqNum (coordPath 9 t) = 0 * t ^ 2 + 0 * t + 4
    ∧ apex4NormSqNum (coordPath 9 t) = 0 * t ^ 2 + 0 * t + 8
    ∧ hingeGramDet (coordPath 9 t) = 0 * t ^ 2 + 0 * t + 4 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [apexDotNum, apex3NormSqNum, apex4NormSqNum, hingeGramDet,
      coordPath] <;> ring

/-! ## §7. The ten coordinate derivatives (deliverable A) -/

theorem hasDerivAt_cosDihedral_slot0 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 0 t)) 0 1 := by
  have h := hasDerivAt_slot 0 1 (-2) 12 (-2) (-1) 6 (-1) (-2) 12 (-2)
    (-1) 6 (-1) path0_polys (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot1 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 1 t)) 0 2 := by
  have h := hasDerivAt_slot 1 2 (-4) 16 (-8) (-2) 8 (-4) (-3) 12 (-4)
    (-1) 4 0 path1_polys (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot2 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 2 t)) 0 3 := by
  have h := hasDerivAt_slot 2 3 0 0 8 (-1) 6 (-5) 0 0 8 0 0 4
    path2_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot3 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 3 t)) 0 4 := by
  have h := hasDerivAt_slot 3 4 0 0 8 0 0 4 (-1) 8 (-8) 0 0 4
    path3_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot4 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 4 t)) 0 1 := by
  have h := hasDerivAt_slot 4 1 (-6) 20 (-6) (-3) 10 (-3) (-4) 16 (-4)
    (-1) 6 (-1) path4_polys (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot5 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 5 t)) 0 2 := by
  have h := hasDerivAt_slot 5 2 0 0 8 (-2) 8 (-4) 0 0 8 0 0 4
    path5_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot6 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 6 t)) 0 3 := by
  have h := hasDerivAt_slot 6 3 0 0 8 0 0 4 (-2) 12 (-10) 0 0 4
    path6_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot7 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 7 t)) 0 1 := by
  have h := hasDerivAt_slot 7 1 0 4 4 (-1) 6 (-1) 0 0 8 0 0 4
    path7_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot8 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 8 t))
      (Real.sqrt 2 / 8) 2 := by
  have h := hasDerivAt_slot 8 2 0 4 0 0 0 4 (-1) 8 (-4) 0 0 4
    path8_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

theorem hasDerivAt_cosDihedral_slot9 :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath 9 t))
      (-(Real.sqrt 2) / 4) 1 := by
  have h := hasDerivAt_slot 9 1 0 (-4) 12 0 0 4 0 0 8 0 0 4
    path9_polys (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  ring

/-- THEOREM (deliverable A): every local squared-length direction has an
explicit flat cosine derivative given by `cosDihedralKernel`. -/
theorem hasDerivAt_cosDihedral_coord (k : Fin 10) :
    HasDerivAt (fun t : ℝ => cosDihedral (coordPath k t))
      (cosDihedralKernel k) (seedFlatSqEdges k) := by
  fin_cases k
  · exact hasDerivAt_cosDihedral_slot0
  · exact hasDerivAt_cosDihedral_slot1
  · exact hasDerivAt_cosDihedral_slot2
  · exact hasDerivAt_cosDihedral_slot3
  · exact hasDerivAt_cosDihedral_slot4
  · exact hasDerivAt_cosDihedral_slot5
  · exact hasDerivAt_cosDihedral_slot6
  · exact hasDerivAt_cosDihedral_slot7
  · exact hasDerivAt_cosDihedral_slot8
  · exact hasDerivAt_cosDihedral_slot9

/-! ## §8. Angle and two-simplex partial-deficit class kernels -/

/-- Angle kernel `θ' = -(1/sin θ)·cos'` with flat `1/sin = √2`. -/
def angleKernel (k : Fin 10) : ℝ := -(Real.sqrt 2) * cosDihedralKernel k

/-- One seed simplex's contribution to the deficit gradient
(`δ = 2π − Σθ`, so per-simplex `-θ'`). -/
def singleSimplexDeficitKernel (k : Fin 10) : ℝ := -angleKernel k

theorem angleKernel_eight : angleKernel 8 = (-1 / 4 : ℝ) := by
  simp only [angleKernel, cosDihedralKernel_eight]
  rw [show -(Real.sqrt 2) * (Real.sqrt 2 / 8)
      = -((Real.sqrt 2 * Real.sqrt 2) / 8) from by ring,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem angleKernel_nine : angleKernel 9 = (1 / 2 : ℝ) := by
  simp only [angleKernel, cosDihedralKernel_nine]
  rw [show -(Real.sqrt 2) * (-(Real.sqrt 2) / 4)
      = (Real.sqrt 2 * Real.sqrt 2) / 4 from by ring,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem singleSimplexDeficitKernel_eight :
    singleSimplexDeficitKernel 8 = (1 / 4 : ℝ) := by
  simp only [singleSimplexDeficitKernel]
  rw [angleKernel_eight]
  norm_num

theorem singleSimplexDeficitKernel_nine :
    singleSimplexDeficitKernel 9 = (-1 / 2 : ℝ) := by
  simp only [singleSimplexDeficitKernel]
  rw [angleKernel_nine]
  norm_num

theorem singleSimplexDeficitKernel_le_seven (k : Fin 10) (hk : k.val ≤ 7) :
    singleSimplexDeficitKernel k = 0 := by
  simp [singleSimplexDeficitKernel, angleKernel,
    cosDihedralKernel_le_seven k hk]

/-- Sum over `Fin 10` of a function supported on slots 8 and 9. -/
private lemma sum_fin10_split (f : Fin 10 → ℝ)
    (hz : ∀ e : Fin 10, e.val ≤ 7 → f e = 0) :
    (∑ e : Fin 10, f e) = f 8 + f 9 := by
  have hmem : ∀ e : Fin 10,
      e ∈ ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 10)) → e.val ≤ 7 := by
    decide
  rw [show (Finset.univ : Finset (Fin 10))
      = insert 8 (insert 9 ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 10)))
      from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_eq_zero (fun e he => hz e (hmem e he))]
  ring

/-- Assemble a local Fin-10 kernel onto the 15 edge classes through one
simplex's local edge table. -/
def assembleClassKernel (s : Fin 24) (localK : Fin 10 → ℝ) : Fin 15 → ℝ :=
  fun d => ∑ e : Fin 10, if localEdgeClass s e = d then localK e else 0

/-- Two-simplex partial deficit class kernel
`∂(2π − θ₀ − θ₁)/∂ℓ²_class` at flat. -/
def partialDeficitClassKernel : Fin 15 → ℝ :=
  fun d =>
    assembleClassKernel 0 singleSimplexDeficitKernel d +
      assembleClassKernel 1 singleSimplexDeficitKernel d

/-- THEOREM: the assembly reduces to the two active local slots. -/
theorem assembleClassKernel_eval (s : Fin 24) (d : Fin 15) :
    assembleClassKernel s singleSimplexDeficitKernel d =
      (if localEdgeClass s 8 = d then singleSimplexDeficitKernel 8 else 0)
      + (if localEdgeClass s 9 = d then singleSimplexDeficitKernel 9
          else 0) := by
  unfold assembleClassKernel
  exact sum_fin10_split _
    (fun e he => by rw [singleSimplexDeficitKernel_le_seven e he, ite_self])

theorem partialDeficitClassKernel_three :
    partialDeficitClassKernel 3 = (-1 / 2 : ℝ) := by
  simp only [partialDeficitClassKernel]
  rw [assembleClassKernel_eval, assembleClassKernel_eval]
  rw [if_neg (by decide : ¬ localEdgeClass 0 8 = 3),
    if_neg (by decide : ¬ localEdgeClass 0 9 = 3),
    if_neg (by decide : ¬ localEdgeClass 1 8 = 3),
    if_pos (by decide : localEdgeClass 1 9 = 3),
    singleSimplexDeficitKernel_nine]
  norm_num

theorem partialDeficitClassKernel_seven :
    partialDeficitClassKernel 7 = (-1 / 2 : ℝ) := by
  simp only [partialDeficitClassKernel]
  rw [assembleClassKernel_eval, assembleClassKernel_eval]
  rw [if_neg (by decide : ¬ localEdgeClass 0 8 = 7),
    if_pos (by decide : localEdgeClass 0 9 = 7),
    if_neg (by decide : ¬ localEdgeClass 1 8 = 7),
    if_neg (by decide : ¬ localEdgeClass 1 9 = 7),
    singleSimplexDeficitKernel_nine]
  norm_num

theorem partialDeficitClassKernel_eleven :
    partialDeficitClassKernel 11 = (1 / 2 : ℝ) := by
  simp only [partialDeficitClassKernel]
  rw [assembleClassKernel_eval, assembleClassKernel_eval]
  rw [if_pos (by decide : localEdgeClass 0 8 = 11),
    if_neg (by decide : ¬ localEdgeClass 0 9 = 11),
    if_pos (by decide : localEdgeClass 1 8 = 11),
    if_neg (by decide : ¬ localEdgeClass 1 9 = 11),
    singleSimplexDeficitKernel_eight]
  norm_num

/-- THEOREM: the partial deficit kernel vanishes off classes 3, 7, 11. -/
theorem partialDeficitClassKernel_zero_off (d : Fin 15)
    (h3 : d ≠ 3) (h7 : d ≠ 7) (h11 : d ≠ 11) :
    partialDeficitClassKernel d = 0 := by
  simp only [partialDeficitClassKernel]
  rw [assembleClassKernel_eval, assembleClassKernel_eval]
  rw [show localEdgeClass 0 8 = 11 from by decide,
    show localEdgeClass 0 9 = 7 from by decide,
    show localEdgeClass 1 8 = 11 from by decide,
    show localEdgeClass 1 9 = 3 from by decide]
  rw [if_neg (show ¬((11 : Fin 15) = d) from fun h => h11 h.symm),
    if_neg (show ¬((7 : Fin 15) = d) from fun h => h7 h.symm),
    if_neg (show ¬((3 : Fin 15) = d) from fun h => h3 h.symm)]
  norm_num

theorem partialDeficitClassKernel_values :
    partialDeficitClassKernel 3 = (-1 / 2 : ℝ) ∧
      partialDeficitClassKernel 7 = (-1 / 2 : ℝ) ∧
        partialDeficitClassKernel 11 = (1 / 2 : ℝ) :=
  ⟨partialDeficitClassKernel_three, partialDeficitClassKernel_seven,
    partialDeficitClassKernel_eleven⟩

/-! ## §9. Nonvacuity, symmetry, decoy -/

/-- THEOREM (nonvacuity): the slot-9 cosine kernel is nonzero. -/
theorem cosDihedralKernel_nonvacuous : cosDihedralKernel 9 ≠ 0 := by
  rw [cosDihedralKernel_nine]
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  linarith

/-- Directional cosine derivative along a local direction `v`. -/
def cosDirectional (v : Fin 10 → ℝ) : ℝ :=
  ∑ k : Fin 10, v k * cosDihedralKernel k

/-- THEOREM (decoy, computed honestly): uniform scaling of the squared
lengths is NOT stationary; the value is `-√2/8`. -/
theorem cosDihedral_uniformScale_decoy :
    cosDirectional (fun _ => (1 : ℝ)) = -(Real.sqrt 2) / 8 := by
  simp only [cosDirectional]
  rw [sum_fin10_split _
    (fun e he => by rw [cosDihedralKernel_le_seven e he, mul_zero])]
  rw [cosDihedralKernel_eight, cosDihedralKernel_nine]
  ring

/-- THEOREM: the true homothety direction (scaling every flat squared
length by the same factor) is stationary, as scale invariance of the
angle demands. -/
theorem cosDihedral_homothety_stationary :
    cosDirectional seedFlatSqEdges = 0 := by
  simp only [cosDirectional]
  rw [sum_fin10_split _
    (fun e he => by rw [cosDihedralKernel_le_seven e he, mul_zero])]
  rw [cosDihedralKernel_eight, cosDihedralKernel_nine, seedFlat_8,
    seedFlat_9]
  ring

/-- THEOREM (symmetry): the partial deficit class kernel is invariant
under the hinge-fixing axis swap `2 ↔ 3` of the incidence layer. -/
theorem partialDeficitClassKernel_swap23 (d : Fin 15) :
    partialDeficitClassKernel (swap23Class d) =
      partialDeficitClassKernel d := by
  have hinv : ∀ x : Fin 15, swap23Class (swap23Class x) = x := by decide
  have hs3 : swap23Class 3 = 7 := by decide
  have hs7 : swap23Class 7 = 3 := by decide
  have hs11 : swap23Class 11 = 11 := by decide
  by_cases h3 : d = 3
  · subst h3
    rw [hs3, partialDeficitClassKernel_seven, partialDeficitClassKernel_three]
  by_cases h7 : d = 7
  · subst h7
    rw [hs7, partialDeficitClassKernel_three, partialDeficitClassKernel_seven]
  by_cases h11 : d = 11
  · subst h11
    rw [hs11]
  have g3 : swap23Class d ≠ 3 := fun h => h7 (by rw [← hinv d, h, hs3])
  have g7 : swap23Class d ≠ 7 := fun h => h3 (by rw [← hinv d, h, hs7])
  have g11 : swap23Class d ≠ 11 := fun h => h11 (by rw [← hinv d, h, hs11])
  rw [partialDeficitClassKernel_zero_off _ g3 g7 g11,
    partialDeficitClassKernel_zero_off _ h3 h7 h11]

/-! ## §10. Status -/

structure Hinge4DDihedralKernelStatus where
  seedCosineFlatClosed : Bool
  tenCoordDerivativesClosed : Bool
  twoSimplexPartialDeficitClosed : Bool
  fullLatticeOrbitOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DDihedralKernelStatus : Hinge4DDihedralKernelStatus where
  seedCosineFlatClosed := true
  tenCoordDerivativesClosed := true
  twoSimplexPartialDeficitClosed := true
  fullLatticeOrbitOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DDihedralKernelStatus_flags :
    hinge4DDihedralKernelStatus.seedCosineFlatClosed = true ∧
      hinge4DDihedralKernelStatus.tenCoordDerivativesClosed = true ∧
        hinge4DDihedralKernelStatus.twoSimplexPartialDeficitClosed = true ∧
          hinge4DDihedralKernelStatus.fullLatticeOrbitOpen = true ∧
            hinge4DDihedralKernelStatus.convergesEH4d = false ∧
              hinge4DDihedralKernelStatus.gapActionRecovery = false := by
  decide

end

end ReggeHinge4DDihedralKernel
end Analysis
end Gravity
end IndisputableMonolith
