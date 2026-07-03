import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.FoldOrientation
import IndisputableMonolith.Masses.TrailingFoldBridge
import IndisputableMonolith.Masses.TrailingSpanDistribution

/-!
# Golden Fold Forcing (compression of the residual MODEL floor)

`Masses/FoldOrientation.lean` shrank the trailing-torsion premise ledger from two bare
numbers (S2 `sign = -1`, B2 `prefactor = φ`) to one structural commitment: the fold *is*
the specific Fibonacci `Q`-matrix `goldenMul = !![0,1;1,1]`. That specific matrix was still
a MODEL input — it posits four particular entries.

This module removes the specific matrix. It replaces "the fold is `goldenMul`" with the
weaker, kernel-level premise

    the fold is an **integral rank-2 operator** `F` satisfying the **golden relation**
    `F² = F + I`,

and then proves that this premise *forces* the same two numbers:

* **det `F = -1`** (the S2 closure sign / orientation), for *any* integral `F` with
  `F² = F + I`. `goldenMul` is no longer privileged — it is one witness among the whole
  `GL₂(ℤ)` conjugacy class of golden-relation operators, and every member has the same
  determinant.
* **the positive eigenvalue of `F` is `φ`** (the B2 scale), for *any* real operator with
  `F² = F + I`.

## Why this is a genuine compression, not a relabel

`F² = F + I` is the *operator lift of the kernel's self-similarity fixed point*
`φ² = φ + 1` (T6: `Constants.phi_sq_eq`). The recognition module is a **rank-2 ℤ-module**
(integer ledger), so the fold is an integer matrix. Those are the two structural facts;
the two numbers fall out.

The integrality is load-bearing and the theorem is false without it: over `ℝ` the scalar
operator `φ • I` also satisfies `F² = F + I` but has `det = φ² = +1`. It is exactly the
*integer* ledger that excludes the exotic scalar root (`no_integer_golden_root`) and forces
`trace = 1`, `det = -1`. So the premise is not vacuous: `F² = F + I` picks out a
2-dimensional variety of integer matrices (`bc = a + 1 - a²`, `d = 1 - a`), on all of which
`det = -1`.

## Honest status

- `no_integer_golden_root`, `goldenRelation_of_goldenMulZ`, `golden_integral_forces`
  (trace = 1 ∧ det = -1), `goldenRelation_pos_eigen_eq_phi`, `golden_integral_closureSign`,
  `goldenMulZ_cast_eq`, `GoldenForcingCert`, `goldenForcingCert_holds`: THEOREM (no `sorry`,
  Mathlib-base axioms only).
- `IntegralGoldenFoldPremise` (`F : Matrix (Fin 2) (Fin 2) ℤ` with `GoldenRelation F`) is the
  relocated MODEL layer. It is strictly weaker than `FoldOrientation`'s "the fold is
  `goldenMul`": it names no entries, only the relation `F² = F + I` (T6 in operator form)
  and the rank-2 integer structure. The remaining MODEL commitment is that the generation
  fold IS such an operator; that identification is not proved from the kernel here, but the
  two *numbers* it used to carry are now derived, not posited.

Lean status: no `sorry`; no new axioms beyond Mathlib base.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenFoldForcing

open Constants
open scoped BigOperators

/-! ## The golden relation as an operator predicate -/

/-- The **golden relation** on a `2×2` operator: `F² = F + I`. This is the operator lift of
the golden self-similarity `φ² = φ + 1` (`Constants.phi_sq_eq`, the T6 fixed point). -/
def GoldenRelation {R : Type*} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) : Prop :=
  F * F = F + 1

/-- The integer Fibonacci `Q`-matrix `!![0,1;1,1]`, the canonical golden-relation witness. -/
def goldenMulZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 1]

/-- The canonical witness satisfies the golden relation over `ℤ`. -/
theorem goldenRelation_of_goldenMulZ : GoldenRelation goldenMulZ := by
  unfold GoldenRelation goldenMulZ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]

/-! ## No integer golden root (the integrality lever) -/

/-- **No integer satisfies the golden equation.** There is no `n : ℤ` with `n² = n + 1`.
This is what makes the integer ledger exclude the exotic scalar solution `φ • I`. -/
theorem no_integer_golden_root (n : ℤ) : n * n ≠ n + 1 := by
  intro h
  have hu : n * (n - 1) = 1 := by ring_nf; linarith
  have huni : IsUnit n := IsUnit.of_mul_eq_one (n - 1) hu
  rcases Int.isUnit_iff.mp huni with h1 | h1 <;> subst h1 <;> norm_num at h

/-! ## The forcing theorem: integral golden relation ⟹ trace 1, det −1 -/

/-- **Compression theorem.** Any *integral* `2×2` operator satisfying the golden relation
`F² = F + I` is forced to have `trace F = 1` and `det F = -1`. The `-1` is the S2 closure
sign, now derived from (integer ledger) + (golden self-similarity), not posited. -/
theorem golden_integral_forces {F : Matrix (Fin 2) (Fin 2) ℤ} (h : GoldenRelation F) :
    F.trace = 1 ∧ F.det = -1 := by
  have e00 : F 0 0 * F 0 0 + F 0 1 * F 1 0 = F 0 0 + 1 := by
    have hh := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply] using hh
  have e01 : F 0 0 * F 0 1 + F 0 1 * F 1 1 = F 0 1 := by
    have hh := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply] using hh
  have e11 : F 1 0 * F 0 1 + F 1 1 * F 1 1 = F 1 1 + 1 := by
    have hh := congrFun (congrFun h 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply] using hh
  -- `b · (trace − 1) = 0`
  have hb : F 0 1 * (F 0 0 + F 1 1 - 1) = 0 := by linear_combination e01
  have htr : F 0 0 + F 1 1 = 1 := by
    by_contra hne
    have hb0 : F 0 1 = 0 := by
      rcases mul_eq_zero.mp hb with h' | h'
      · exact h'
      · exact absurd (by linarith : F 0 0 + F 1 1 = 1) hne
    have haa : F 0 0 * F 0 0 = F 0 0 + 1 := by
      have hh := e00; rw [hb0] at hh; linarith [hh]
    exact no_integer_golden_root (F 0 0) haa
  refine ⟨?_, ?_⟩
  · rw [Matrix.trace_fin_two]; exact htr
  · rw [Matrix.det_fin_two]
    have hbc : F 0 1 * F 1 0 = F 0 0 + 1 - F 0 0 * F 0 0 := by linarith [e00]
    linear_combination (F 0 0) * htr - hbc

/-! ## Cayley–Hamilton for `2×2` and the exact characterization -/

/-- **Cayley–Hamilton, `2×2`, any commutative ring.** `F² = (tr F)·F − (det F)·I`.
Proved entry-wise; no Mathlib CH machinery needed at this size. -/
theorem cayley_hamilton_two {R : Type*} [CommRing R] (F : Matrix (Fin 2) (Fin 2) R) :
    F * F = F.trace • F - F.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul] <;> ring

/-- **Converse.** Over any commutative ring, `trace F = 1` and `det F = -1` force the golden
relation `F² = F + I` (immediate from Cayley–Hamilton). -/
theorem goldenRelation_of_trace_det {R : Type*} [CommRing R] {F : Matrix (Fin 2) (Fin 2) R}
    (htr : F.trace = 1) (hdet : F.det = -1) : GoldenRelation F := by
  unfold GoldenRelation
  rw [cayley_hamilton_two F, htr, hdet]
  simp [one_smul, neg_smul]

/-- **Exact characterization on the integer ledger.** For an integer `2×2` operator the golden
relation is *equivalent* to having the golden characteristic polynomial `x² − x − 1`
(`trace = 1`, `det = -1`). So `F² = F + I` carries no content beyond "integer rank-2 with the
golden char poly": the S2 sign (`det = -1`) and the forced `trace = 1` are the whole of it. -/
theorem golden_iff_trace_det {F : Matrix (Fin 2) (Fin 2) ℤ} :
    GoldenRelation F ↔ (F.trace = 1 ∧ F.det = -1) :=
  ⟨golden_integral_forces, fun h => goldenRelation_of_trace_det h.1 h.2⟩

/-! ## The scale: the positive eigenvalue is `φ` -/

/-- **Scale theorem.** Any positive eigenvalue of a real golden-relation operator is `φ`.
The eigen-equation `F v = λ v` with `F² = F + I` gives `λ² = λ + 1`, and positivity selects
the golden root. This is the B2 scale, read off the *relation* rather than a fixed matrix. -/
theorem goldenRelation_pos_eigen_eq_phi {F : Matrix (Fin 2) (Fin 2) ℝ}
    (h : GoldenRelation F) {v : Fin 2 → ℝ} (hv : v ≠ 0) {lam : ℝ}
    (hpos : 0 < lam) (heig : F.mulVec v = lam • v) : lam = phi := by
  have h1 : F.mulVec (F.mulVec v) = (lam * lam) • v := by
    rw [heig, Matrix.mulVec_smul, heig, smul_smul]
  have h2 : F.mulVec (F.mulVec v) = (lam + 1) • v := by
    rw [Matrix.mulVec_mulVec, h, Matrix.add_mulVec, Matrix.one_mulVec, heig, add_smul, one_smul]
  have key : (lam * lam) • v = (lam + 1) • v := by rw [← h1, h2]
  have hz : (lam * lam - (lam + 1)) • v = 0 := by rw [sub_smul, key, sub_self]
  have hquad0 : lam * lam - (lam + 1) = 0 := by
    rcases smul_eq_zero.mp hz with h' | h'
    · exact h'
    · exact absurd h' hv
  have hquad : lam ^ 2 = lam + 1 := by nlinarith [hquad0]
  have hfac : (lam - phi) * (lam + phi - 1) = 0 := by nlinarith [hquad, phi_sq_eq]
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith [sub_eq_zero.mp h']
  · exfalso; nlinarith [hpos, one_lt_phi]

/-! ## Relocating S2 onto the weaker integral-golden premise -/

/-- **MODEL premise (integral golden fold), relocating both S2 and the specific matrix.**
The fold is an integer rank-2 operator satisfying the golden relation `F² = F + I`. This
carries no numeric commitment (`-1`, `φ`) and no specific entries — only the operator lift of
`φ² = φ + 1` on the integer ledger. -/
def IntegralGoldenFoldPremise (F : Matrix (Fin 2) (Fin 2) ℤ) : Prop := GoldenRelation F

/-- **S2 is forced by the integral golden fold.** The closure sign is the real determinant of
the fold operator, and the integral golden premise forces it to `-1`. `goldenMul` never
appears — the sign is forced for *every* integral golden-relation operator. -/
theorem golden_integral_closureSign {F : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IntegralGoldenFoldPremise F) :
    TrailingSpanDistribution.ClosureSignPremise ((F.det : ℝ)) := by
  show (F.det : ℝ) = -1
  have hdet := (golden_integral_forces h).2
  rw [hdet]; norm_num

/-! ## Tie-back: the specific `goldenMul` is the cast of the canonical integer witness -/

/-- The real `FoldOrientation.goldenMul` is the `ℤ → ℝ` cast of the canonical integer
witness `goldenMulZ`. So the old specific matrix is just one instance of the new premise,
and its `det = -1` is now a *consequence* of `golden_integral_forces`, not an input. -/
theorem goldenMulZ_cast_eq :
    goldenMulZ.map (Int.castRingHom ℝ) = FoldOrientation.goldenMul := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenMulZ, FoldOrientation.goldenMul, Matrix.map_apply]

/-- The canonical integer witness has determinant `-1` as a corollary of the general forcing
theorem (independent recomputation of `FoldOrientation.goldenMul_det`). -/
theorem goldenMulZ_det : goldenMulZ.det = -1 :=
  (golden_integral_forces goldenRelation_of_goldenMulZ).2

/-- The canonical integer witness has trace `1`. -/
theorem goldenMulZ_trace : goldenMulZ.trace = 1 :=
  (golden_integral_forces goldenRelation_of_goldenMulZ).1

/-! ## Certificate bundling the compression -/

/-- THEOREM-grade certificate for the compression: the canonical witness satisfies the golden
relation; every integral golden-relation operator has trace `1` and det `-1`; every positive
eigenvalue of a real golden-relation operator is `φ`; and the real `goldenMul` is the cast of
the integer witness. -/
structure GoldenForcingCert where
  witness_relation : GoldenRelation goldenMulZ
  no_int_root : ∀ n : ℤ, n * n ≠ n + 1
  integral_forces_trace_det :
    ∀ {F : Matrix (Fin 2) (Fin 2) ℤ}, GoldenRelation F → F.trace = 1 ∧ F.det = -1
  pos_eigen_forces_phi :
    ∀ {F : Matrix (Fin 2) (Fin 2) ℝ}, GoldenRelation F → ∀ {v : Fin 2 → ℝ}, v ≠ 0 →
      ∀ {lam : ℝ}, 0 < lam → F.mulVec v = lam • v → lam = phi
  integral_forces_S2 :
    ∀ {F : Matrix (Fin 2) (Fin 2) ℤ}, IntegralGoldenFoldPremise F →
      TrailingSpanDistribution.ClosureSignPremise ((F.det : ℝ))
  witness_is_cast :
    goldenMulZ.map (Int.castRingHom ℝ) = FoldOrientation.goldenMul

theorem goldenForcingCert_holds : Nonempty GoldenForcingCert :=
  ⟨{ witness_relation := goldenRelation_of_goldenMulZ
     no_int_root := no_integer_golden_root
     integral_forces_trace_det := by
       intro F h; exact golden_integral_forces h
     pos_eigen_forces_phi := by
       intro F h v hv lam hpos heig
       exact goldenRelation_pos_eigen_eq_phi h hv hpos heig
     integral_forces_S2 := by
       intro F h; exact golden_integral_closureSign h
     witness_is_cast := goldenMulZ_cast_eq }⟩

end GoldenFoldForcing
end Masses
end IndisputableMonolith
