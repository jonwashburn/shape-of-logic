import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D Freudenthal hinge incidence + flat-Hessian assembly skeleton

QG full-theory campaign, next kernel-checked increment after
`ReggeEdgeStencil4D`.  The 15-class stencil is imported, never redefined.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* MODEL: the flat-Hessian assembly formula (definition only; OPEN
  per-hinge deficit / area kernels are parameters, not evaluated).
* OPEN: the true per-hinge flat second-variation kernels — the dihedral /
  Cayley–Menger calculus that supplies numeric class weights.
* This does **not** complete the flat Hessian of the 4D Regge action.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.
* This does **not** reverse-engineer weights from Einstein–Hilbert.

## What is proved (honest scope: deliverable B, with A-shaped gates
on the combinatorial support)

1. **Freudenthal / Kuhn 4-cube cell.** Explicit enumeration of the 24
   monotone 4-simplices (permutations of the four axes) and their
   five nested vertices / ten edge-class masks (among the 15 of
   `ReggeEdgeStencil4D`).
2. **Seed hinge orbit.** The triangle with vertices `0`, `e₀`,
   `e₀+e₁` (masks `0,1,3`).  Exactly two of the 24 simplices contain
   it; they are the permutations that begin `(0,1,…)`.
3. **Incidence multiplicities.** For each of the 15 edge classes, the
   number of containing seed-simplices in which that class appears as
   a local edge.  Three classes are absent (combinatorial decoys);
   the three hinge-boundary classes each have multiplicity `2`.
4. **Nonvacuity / symmetry / decoy (combinatorial).** The incidence
   support is nonempty; it is invariant under the axis swap `2 ↔ 3`
   that fixes the seed hinge; three explicit classes lie outside the
   support.
5. **Assembly skeleton (MODEL).** The flat-Hessian class form that
   contracts OPEN per-hinge area weights against OPEN per-hinge
   deficit kernels, forced to vanish off the incidence support.

## What remains for the true weights

Lift the 3D Schläfli-reduced chain of `ReggeTTFlatSecondVariation` to
4D: for this seed hinge (then every orbit), express the dihedral angle
at the triangle in each incident 4-simplex as a Cayley–Menger / cosine
function of the ten squared edge lengths, differentiate at the flat
Freudenthal point, and assemble `d²S = Σ_h dA_h · dδ_h` into class
weights on the 15-stencil.  The incidence table here is the
combinatorial factor those kernels must contract against.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DFlatKernel

open BigOperators
open ReggeEdgeStencil4D

/-! ## §1. Freudenthal / Kuhn 24-simplex cell -/

/-- Lexicographic enumeration of the 24 permutations of `Fin 4`:
`permAxes s = (σ(0), σ(1), σ(2), σ(3))`. -/
def permAxes : Fin 24 → Fin 4 × Fin 4 × Fin 4 × Fin 4
  | 0 => (0, 1, 2, 3)
  | 1 => (0, 1, 3, 2)
  | 2 => (0, 2, 1, 3)
  | 3 => (0, 2, 3, 1)
  | 4 => (0, 3, 1, 2)
  | 5 => (0, 3, 2, 1)
  | 6 => (1, 0, 2, 3)
  | 7 => (1, 0, 3, 2)
  | 8 => (1, 2, 0, 3)
  | 9 => (1, 2, 3, 0)
  | 10 => (1, 3, 0, 2)
  | 11 => (1, 3, 2, 0)
  | 12 => (2, 0, 1, 3)
  | 13 => (2, 0, 3, 1)
  | 14 => (2, 1, 0, 3)
  | 15 => (2, 1, 3, 0)
  | 16 => (2, 3, 0, 1)
  | 17 => (2, 3, 1, 0)
  | 18 => (3, 0, 1, 2)
  | 19 => (3, 0, 2, 1)
  | 20 => (3, 1, 0, 2)
  | 21 => (3, 1, 2, 0)
  | 22 => (3, 2, 0, 1)
  | 23 => (3, 2, 1, 0)
  | ⟨n + 24, h⟩ => absurd h (by omega)

/-- Axis image `σ(i)` for simplex `s`. -/
def permOf (s : Fin 24) (i : Fin 4) : Fin 4 :=
  match i, permAxes s with
  | 0, (a, _, _, _) => a
  | 1, (_, b, _, _) => b
  | 2, (_, _, c, _) => c
  | 3, (_, _, _, d) => d

/-- Bit mask of the standard basis vector `e_i`. -/
def axisMask (i : Fin 4) : ℕ := 2 ^ i.val

/-- Nested Freudenthal vertex after `k` steps along simplex `s`
(bit mask in `{0,…,15}`). -/
def vertexMask (s : Fin 24) : Fin 5 → ℕ
  | 0 => 0
  | 1 => axisMask (permOf s 0)
  | 2 => axisMask (permOf s 0) + axisMask (permOf s 1)
  | 3 =>
      axisMask (permOf s 0) + axisMask (permOf s 1) + axisMask (permOf s 2)
  | 4 => 15

theorem vertexMask_start (s : Fin 24) : vertexMask s 0 = 0 := rfl

theorem vertexMask_end (s : Fin 24) : vertexMask s 4 = 15 := rfl

/-- Local 4-simplex edge slots: the ten pairs among five vertices. -/
def localEdgePair : Fin 10 → Fin 5 × Fin 5
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | 9 => (3, 4)
  | ⟨n + 10, h⟩ => absurd h (by omega)

/-- XOR mask of local edge `e` in simplex `s`. -/
def localEdgeMask (s : Fin 24) (e : Fin 10) : ℕ :=
  let p := localEdgePair e
  Nat.xor (vertexMask s p.1) (vertexMask s p.2)

theorem localEdgeMask_bounds (s : Fin 24) (e : Fin 10) :
    0 < localEdgeMask s e ∧ localEdgeMask s e ≤ 15 := by
  fin_cases s <;> fin_cases e <;> decide

/-- Local edge class of slot `e` in simplex `s`. -/
def localEdgeClass (s : Fin 24) (e : Fin 10) : Fin 15 :=
  ⟨localEdgeMask s e - 1, by
    have h := localEdgeMask_bounds s e
    omega⟩

theorem localEdgeClass_mask (s : Fin 24) (e : Fin 10) :
    maskOf (localEdgeClass s e) = localEdgeMask s e := by
  unfold localEdgeClass maskOf
  have h := (localEdgeMask_bounds s e).1
  exact Nat.sub_add_cancel h

/-- Whether simplex `s` carries edge class `d` among its ten local edges. -/
def simplexHasClass (s : Fin 24) (d : Fin 15) : Bool :=
  decide (∃ e : Fin 10, localEdgeClass s e = d)

theorem permOf_eq_of_eq (s : Fin 24) {i j : Fin 4}
    (h : permOf s i = permOf s j) : i = j := by
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    first | rfl | exact (nomatch h)

/-! ## §2. Seed hinge orbit `{0, e₀, e₀+e₁}` -/

/-- Whether the five vertices of simplex `s` contain the seed hinge
masks `{0,1,3}`. -/
def containsSeedHinge (s : Fin 24) : Bool :=
  decide (∃ i : Fin 5, vertexMask s i = 1) &&
    decide (∃ i : Fin 5, vertexMask s i = 3)

/-- THEOREM: the seed hinge sits in simplex `s` iff the permutation
begins with axes `(0,1)`. -/
theorem containsSeedHinge_iff (s : Fin 24) :
    containsSeedHinge s = true ↔ permOf s 0 = 0 ∧ permOf s 1 = 1 := by
  fin_cases s <;> decide

/-- THEOREM: exactly two of the 24 Freudenthal simplices contain the
seed hinge. -/
theorem seedHinge_simplex_count :
    (Finset.univ.filter (fun s : Fin 24 => containsSeedHinge s = true)).card =
      2 := by
  decide

/-- THEOREM: those two simplices are indices `0` and `1`. -/
theorem seedHinge_simplices :
    Finset.univ.filter (fun s : Fin 24 => containsSeedHinge s = true) =
      ({0, 1} : Finset (Fin 24)) := by
  decide

/-! ## §3. Incidence multiplicities on the 15 edge classes -/

/-- Edge-class set of Freudenthal simplex `0` = perm `(0,1,2,3)`. -/
def simplex0Classes : Finset (Fin 15) :=
  {0, 1, 2, 3, 5, 6, 7, 11, 13, 14}

/-- Edge-class set of Freudenthal simplex `1` = perm `(0,1,3,2)`. -/
def simplex1Classes : Finset (Fin 15) :=
  {0, 1, 2, 3, 7, 9, 10, 11, 13, 14}

/-- THEOREM: the table for simplex `0` matches the computed local edges. -/
theorem simplex0Classes_correct (e : Fin 10) :
    localEdgeClass 0 e ∈ simplex0Classes := by
  fin_cases e <;> decide

/-- THEOREM: the table for simplex `1` matches the computed local edges. -/
theorem simplex1Classes_correct (e : Fin 10) :
    localEdgeClass 1 e ∈ simplex1Classes := by
  fin_cases e <;> decide

/-- THEOREM: every class in the simplex-`0` table is realized by some slot. -/
theorem simplex0Classes_complete (d : Fin 15) (hd : d ∈ simplex0Classes) :
    simplexHasClass 0 d = true := by
  revert hd
  fin_cases d <;> decide

/-- THEOREM: every class in the simplex-`1` table is realized by some slot. -/
theorem simplex1Classes_complete (d : Fin 15) (hd : d ∈ simplex1Classes) :
    simplexHasClass 1 d = true := by
  revert hd
  fin_cases d <;> decide

/-- Combinatorial incidence: how many seed-containing simplices carry class `d`. -/
def seedHingeIncidenceNat (d : Fin 15) : ℕ :=
  (if d ∈ simplex0Classes then 1 else 0) +
    (if d ∈ simplex1Classes then 1 else 0)

/-- Closed-form incidence values. -/
theorem seedHingeIncidenceNat_values :
    seedHingeIncidenceNat ⟨0, by decide⟩ = 2 ∧
      seedHingeIncidenceNat ⟨1, by decide⟩ = 2 ∧
        seedHingeIncidenceNat ⟨2, by decide⟩ = 2 ∧
          seedHingeIncidenceNat ⟨3, by decide⟩ = 2 ∧
            seedHingeIncidenceNat ⟨4, by decide⟩ = 0 ∧
              seedHingeIncidenceNat ⟨5, by decide⟩ = 1 ∧
                seedHingeIncidenceNat ⟨6, by decide⟩ = 1 ∧
                  seedHingeIncidenceNat ⟨7, by decide⟩ = 2 ∧
                    seedHingeIncidenceNat ⟨8, by decide⟩ = 0 ∧
                      seedHingeIncidenceNat ⟨9, by decide⟩ = 1 ∧
                        seedHingeIncidenceNat ⟨10, by decide⟩ = 1 ∧
                          seedHingeIncidenceNat ⟨11, by decide⟩ = 2 ∧
                            seedHingeIncidenceNat ⟨12, by decide⟩ = 0 ∧
                              seedHingeIncidenceNat ⟨13, by decide⟩ = 2 ∧
                                seedHingeIncidenceNat ⟨14, by decide⟩ = 2 := by
  decide

/-- Total incidence mass on the seed hinge (= 2 simplices × 10 edges). -/
theorem sum_seedHingeIncidenceNat :
    (∑ d : Fin 15, seedHingeIncidenceNat d) = 20 := by
  unfold seedHingeIncidenceNat simplex0Classes simplex1Classes
  decide

/-! ## §4. Nonvacuity, symmetry, decoy (combinatorial A-shaped gates) -/

/-- THEOREM (nonvacuity): class `0` (hinge-boundary edge `e₀`) has
multiplicity `2`. -/
theorem seedHingeIncidence_nonvacuous :
    seedHingeIncidenceNat (0 : Fin 15) = 2 ∧
      seedHingeIncidenceNat (0 : Fin 15) ≠ 0 := by
  decide

/-- Bit-mask image under the axis swap `2 ↔ 3`. -/
def swap23Mask (m : ℕ) : ℕ :=
  (if Nat.testBit m 0 then 1 else 0) +
    (if Nat.testBit m 1 then 2 else 0) +
      (if Nat.testBit m 2 then 8 else 0) +
        (if Nat.testBit m 3 then 4 else 0)

theorem swap23Mask_bounds (d : Fin 15) :
    0 < swap23Mask (maskOf d) ∧ swap23Mask (maskOf d) ≤ 15 := by
  fin_cases d <;> decide

/-- Class image under axis swap `2 ↔ 3`. -/
def swap23Class (d : Fin 15) : Fin 15 :=
  ⟨swap23Mask (maskOf d) - 1, by
    have h := swap23Mask_bounds d
    omega⟩

/-- THEOREM (symmetry): seed-hinge incidence is invariant under the
lattice symmetry that swaps axes `2` and `3` and fixes the hinge. -/
theorem seedHingeIncidence_swap23 (d : Fin 15) :
    seedHingeIncidenceNat (swap23Class d) = seedHingeIncidenceNat d := by
  fin_cases d <;> decide

/-- Combinatorial decoy classes: masks `5,9,13` (classes `4,8,12`). -/
def decoyClass4 : Fin 15 := ⟨4, by decide⟩
def decoyClass8 : Fin 15 := ⟨8, by decide⟩
def decoyClass12 : Fin 15 := ⟨12, by decide⟩

/-- THEOREM (decoy): three explicit edge classes have zero seed-hinge
incidence. -/
theorem seedHingeIncidence_decoy_zero :
    seedHingeIncidenceNat decoyClass4 = 0 ∧
      seedHingeIncidenceNat decoyClass8 = 0 ∧
        seedHingeIncidenceNat decoyClass12 = 0 := by
  decide

/-- Hinge-boundary edge classes of the seed triangle. -/
def hingeBoundaryClass : Fin 3 → Fin 15
  | 0 => 0
  | 1 => 1
  | 2 => 2

/-- THEOREM: every seed-hinge boundary class has positive incidence. -/
theorem hingeBoundary_incidence_pos (i : Fin 3) :
    0 < seedHingeIncidenceNat (hingeBoundaryClass i) := by
  fin_cases i <;> decide

/-! ## §5. Full-cell edge-class inventory (sanity) -/

/-- Whether class `d` appears in simplex `s` (Nat indicator). -/
def classInSimplexNat (s : Fin 24) (d : Fin 15) : ℕ :=
  if simplexHasClass s d then 1 else 0

/-- Every Freudenthal 4-simplex carries exactly ten edge classes. -/
theorem simplex_class_count (s : Fin 24) :
    (∑ d : Fin 15, classInSimplexNat s d) = 10 := by
  fin_cases s <;> decide

/-- The 24-simplex cell covers every one of the 15 nonzero 0/1 classes. -/
theorem cell_covers_all_classes (d : Fin 15) :
    ∃ s : Fin 24, simplexHasClass s d = true := by
  fin_cases d <;> decide

/-! ## §6. Flat-Hessian assembly skeleton (MODEL; kernels OPEN) -/

/-- MODEL: flat second-variation class form for one hinge orbit,
`Σ_{e,f} Aweight_e · Kdeficit_{e f} · c_e · c_f`.

This is the 4D skeleton of the 3D Schläfli-reduced contraction
`−Σ_τ Σ_f L' · θ'` in `ReggeTTFlatSecondVariation`: here `Aweight`
plays the role of the area / hinge-volume first derivative and
`Kdeficit` the outer product of deficit gradients.  Both maps are OPEN. -/
def flatHessianOrbitForm
    (Aweight : Fin 15 → ℝ)
    (Kdeficit : Fin 15 → Fin 15 → ℝ)
    (c : Fin 15 → ℝ) : ℝ :=
  ∑ e : Fin 15, ∑ f : Fin 15, Aweight e * Kdeficit e f * c e * c f

/-- MODEL: cell-local seed-orbit contribution with incidence cutoff
hard-wired so off-support classes cannot contribute. -/
def seedOrbitAssembly
    (Aweight : Fin 15 → ℝ)
    (Kdeficit : Fin 15 → Fin 15 → ℝ)
    (c : Fin 15 → ℝ) : ℝ :=
  flatHessianOrbitForm
    (fun e => (seedHingeIncidenceNat e : ℝ) * Aweight e)
    (fun e f =>
      if seedHingeIncidenceNat e = 0 ∨ seedHingeIncidenceNat f = 0 then 0
      else Kdeficit e f)
    c

/-- THEOREM: a decoy-only bump in the area weight is annihilated by the
incidence cutoff. -/
theorem seedOrbitAssembly_decoy_area
    (Aweight : Fin 15 → ℝ) (Kdeficit : Fin 15 → Fin 15 → ℝ)
    (c : Fin 15 → ℝ) :
    seedOrbitAssembly
        (fun e => if e = decoyClass4 then (1 : ℝ) else Aweight e)
        Kdeficit c =
      seedOrbitAssembly Aweight Kdeficit c := by
  unfold seedOrbitAssembly flatHessianOrbitForm
  have hzN : seedHingeIncidenceNat decoyClass4 = 0 := by decide
  have hz : (seedHingeIncidenceNat decoyClass4 : ℝ) = 0 := by
    exact_mod_cast hzN
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases he : e = decoyClass4
  · subst he
    simp only [hz, zero_mul]
  · simp [he]

/-- Support projection onto positive-incidence classes. -/
def supportProject (c : Fin 15 → ℝ) : Fin 15 → ℝ :=
  fun d => if seedHingeIncidenceNat d = 0 then 0 else c d

/-- THEOREM: assembly depends on `c` only through supported classes
(incidence cutoff already zeros off-support deficit slots). -/
theorem seedOrbitAssembly_support_projection
    (Aweight : Fin 15 → ℝ)
    (Kdeficit : Fin 15 → Fin 15 → ℝ)
    (c : Fin 15 → ℝ) :
    seedOrbitAssembly Aweight Kdeficit c =
      seedOrbitAssembly Aweight Kdeficit (supportProject c) := by
  unfold seedOrbitAssembly flatHessianOrbitForm supportProject
  refine Finset.sum_congr rfl fun e _ => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases he : seedHingeIncidenceNat e = 0
  · simp [he]
  · by_cases hf : seedHingeIncidenceNat f = 0
    · simp [he, hf]
    · simp [he, hf]

/-- Status record: combinatorial layer closed; true kernels OPEN. -/
structure Hinge4DFlatKernelStatus where
  freudenthal24Enumerated : Bool
  seedHingeIncidenceClosed : Bool
  trueDeficitKernelOpen : Bool
  convergesEH4d : Bool
  gapActionRecovery : Bool

def hinge4DFlatKernelStatus : Hinge4DFlatKernelStatus where
  freudenthal24Enumerated := true
  seedHingeIncidenceClosed := true
  trueDeficitKernelOpen := true
  convergesEH4d := false
  gapActionRecovery := false

theorem hinge4DFlatKernelStatus_flags :
    hinge4DFlatKernelStatus.freudenthal24Enumerated = true ∧
      hinge4DFlatKernelStatus.seedHingeIncidenceClosed = true ∧
        hinge4DFlatKernelStatus.trueDeficitKernelOpen = true ∧
          hinge4DFlatKernelStatus.convergesEH4d = false ∧
            hinge4DFlatKernelStatus.gapActionRecovery = false := by
  decide

end ReggeHinge4DFlatKernel
end Analysis
end Gravity
end IndisputableMonolith
