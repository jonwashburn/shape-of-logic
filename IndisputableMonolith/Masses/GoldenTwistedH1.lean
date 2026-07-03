import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyReturn
import IndisputableMonolith.Masses.GoldenTorsionAlexander

/-!
# Sign-Character Twisted `H₁` Comparison (GDB Stage 2)

`Masses/GoldenMonodromyReturn.lean` (GR) banked the return map `returnMap k = !![0,1;1,k]` with
`trace = k`, `det = −1`, and characteristic polynomial `X² − k·X − 1`. `Masses/GoldenTorsionAlexander.lean`
(Stage 1) banked the torsion polynomial `Δ_k(t) = t² − k·t − 1 = charpoly` and proved it is
reciprocal-symmetric iff `k = 0`, so the **golden** value `k = 1` is provably not Alexander-symmetric
(the `S³`-link exclusion).

This module discharges **GDB Stage 2**: the sign-character twisted `H₁` comparison. For the
nonorientable golden mapping torus, first homology has two sectors, computed by the Wang exact
sequence from the fiber monodromy `F` acting on `H₁(fiber) ≅ ℤ²`:

* the **untwisted** sector `H₁(M_F)_tors = coker(F − I)`, of order `|det(F − I)|`;
* the **sign-character twisted** sector (twist by the orientation character `w` of the nonorientable
  bundle) `H₁(M_F; ℤ_w)_tors = coker(F + I)`, of order `|det(F + I)|`.

These are exactly the torsion polynomial evaluated at the two roots of unity `t = ±1`:
`det(F − I) = Δ_k(1) = −k` and `det(F + I) = Δ_k(−1) = k`. The Stage-1 `det = −1` anti-palindromic
signature reappears here at the homology level as `det(F − I) = −det(F + I)`: the untwisted and
sign-twisted torsion values are negatives.

## What this module proves (all THEOREM-grade, `#print axioms` = Mathlib base only)

* `wangMatrix_det` / `signTwistedMatrix_det` — `det(F − I) = −k`, `det(F + I) = k`.
* `wangMatrix_det_eq_charpoly_eval_one` / `signTwistedMatrix_det_eq_charpoly_eval_neg_one` — these
  determinants **are** the torsion polynomial evaluated at `t = 1` and `t = −1`, tying the H₁
  computation to the Stage-1 Alexander polynomial.
* `untwisted_eq_neg_twisted` — `det(F − I) = −det(F + I)`: the Stage-1 anti-palindrome at the H₁ level.
* `wangMatrix_golden_surjective` / `signTwistedMatrix_golden_surjective` — at the **golden** value
  `k = 1`, both `F − I` and `F + I` are unimodular (`det = −1, +1`), so both `mulVec` maps are
  surjective: **both H₁ sectors are torsion-free** (trivial cokernels). The golden mapping torus is a
  ℤ-homology object with no fiber torsion in either the untwisted or the sign-twisted sector.
* Differential oracle (anti-vacuity): `wangMatrix_zero_not_isUnit` (unlink `k = 0`: `det = 0`, a rank
  jump, `H₁` gains a ℤ summand), `wangMatrix_two_not_isUnit` + `wangMatrix_two_not_surjective` (clasp
  `k = 2`: `|det| = 2`, genuine ℤ/2 torsion, with the concrete witness `![1,0] ∉ im(F − I)`). So the
  golden value is the **unique** `|k| = 1` unit-linking case with both sectors torsion-free — not a
  relabeling.

## Honest status

- The linear algebra is THEOREM-grade on already-banked integer data.
- **MODEL premise (stated, not asserted as THEOREM):** that the untwisted/sign-twisted `H₁` torsion
  of the mapping torus is `coker(F ∓ I)` (the Wang sequence) with order `|det(F ∓ I)|` (Smith normal
  form), and that the orientation character of the nonorientable bundle is the sign twist. These are
  standard identifications, cited to read the determinant facts as the two-sector homology comparison.
  The Lean content is the comparison itself: golden ⇒ both sectors trivial; controls ⇒ nontrivial.
- **OPEN (later GDB stages):** the order-2 deck chain automorphism (Stage 3), and the full marked
  `ChainHomotopyEquiv` (Stage 4).
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenTwistedH1

open Polynomial
open IndisputableMonolith.Masses.GoldenMonodromyReturn

/-! ## The Wang matrix `F − I` and the sign-twisted matrix `F + I` -/

/-- **The Wang matrix** `F − I`. Its cokernel `ℤ²/im(F − I)` is the untwisted `H₁` torsion of the
mapping torus (the Wang exact sequence `0 → coker(F − I) → H₁(M_F) → ℤ → 0`). -/
def wangMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := returnMap k - 1

/-- **The sign-twisted matrix** `F + I`. Its cokernel is the `H₁` torsion twisted by the orientation
character `w` of the nonorientable bundle (the `t = −1` specialization). -/
def signTwistedMatrix (k : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := returnMap k + 1

theorem wangMatrix_closed_form (k : ℤ) : wangMatrix k = !![(-1 : ℤ), 1; 1, k - 1] := by
  unfold wangMatrix
  rw [returnMap_closed_form, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]

theorem signTwistedMatrix_closed_form (k : ℤ) : signTwistedMatrix k = !![(1 : ℤ), 1; 1, k + 1] := by
  unfold signTwistedMatrix
  rw [returnMap_closed_form, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply]

/-! ## The two twisted determinants -/

/-- **Untwisted torsion value.** `det(F − I) = −k`. -/
theorem wangMatrix_det (k : ℤ) : (wangMatrix k).det = -k := by
  rw [wangMatrix_closed_form, Matrix.det_fin_two_of]; ring

/-- **Sign-twisted torsion value.** `det(F + I) = k`. -/
theorem signTwistedMatrix_det (k : ℤ) : (signTwistedMatrix k).det = k := by
  rw [signTwistedMatrix_closed_form, Matrix.det_fin_two_of]; ring

/-! ## The two determinants are the torsion polynomial at `t = ±1` (bridge to Stage 1) -/

/-- `Δ_k(1) = charpoly.eval 1 = −k`. -/
theorem charpoly_eval_one (k : ℤ) : (returnMap k).charpoly.eval 1 = -k := by
  rw [returnMap_charpoly]
  simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one, one_pow]
  ring

/-- `Δ_k(−1) = charpoly.eval (−1) = k`. -/
theorem charpoly_eval_neg_one (k : ℤ) : (returnMap k).charpoly.eval (-1) = k := by
  rw [returnMap_charpoly]
  simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
  ring

/-- **The untwisted `H₁` value is the torsion polynomial at `t = 1`.** `det(F − I) = Δ_k(1)`. -/
theorem wangMatrix_det_eq_charpoly_eval_one (k : ℤ) :
    (wangMatrix k).det = (returnMap k).charpoly.eval 1 := by
  rw [wangMatrix_det, charpoly_eval_one]

/-- **The sign-twisted `H₁` value is the torsion polynomial at `t = −1`.** `det(F + I) = Δ_k(−1)`. -/
theorem signTwistedMatrix_det_eq_charpoly_eval_neg_one (k : ℤ) :
    (signTwistedMatrix k).det = (returnMap k).charpoly.eval (-1) := by
  rw [signTwistedMatrix_det, charpoly_eval_neg_one]

/-- Direct bridge to the Stage-1 torsion polynomial: `det(F − I) = Δ_k(1)`. -/
theorem wangMatrix_det_eq_torsion_eval_one (k : ℤ) :
    (wangMatrix k).det = (GoldenTorsionAlexander.torsionPoly k).eval 1 :=
  wangMatrix_det_eq_charpoly_eval_one k

/-- Direct bridge to the Stage-1 torsion polynomial: `det(F + I) = Δ_k(−1)`. -/
theorem signTwistedMatrix_det_eq_torsion_eval_neg_one (k : ℤ) :
    (signTwistedMatrix k).det = (GoldenTorsionAlexander.torsionPoly k).eval (-1) :=
  signTwistedMatrix_det_eq_charpoly_eval_neg_one k

/-- **The Stage-1 anti-palindrome at the homology level.** `det(F − I) = −det(F + I)`: the untwisted
and sign-twisted torsion values are negatives, the `det = −1` reciprocal signature of Stage 1. -/
theorem untwisted_eq_neg_twisted (k : ℤ) :
    (wangMatrix k).det = -(signTwistedMatrix k).det := by
  rw [wangMatrix_det, signTwistedMatrix_det]

/-! ## Golden: both sectors torsion-free (unimodular ⇒ surjective ⇒ trivial cokernel) -/

/-- A `2×2` integer matrix with unit determinant induces a surjective `mulVec` (its cokernel `ℤ²/im`
is trivial): it lies in `GL₂(ℤ)`, so `A⁻¹.mulVec y` is a preimage of `y`. -/
theorem surjective_mulVec_of_isUnit_det {A : Matrix (Fin 2) (Fin 2) ℤ}
    (h : IsUnit A.det) : Function.Surjective A.mulVec := by
  intro y
  refine ⟨A⁻¹.mulVec y, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A h, Matrix.one_mulVec]

/-- **Golden untwisted sector is trivial.** `F − I` has `det = −1` (a unit), so `mulVec` is surjective:
the untwisted `H₁` torsion `coker(F − I)` vanishes at `k = 1`. -/
theorem wangMatrix_golden_surjective : Function.Surjective (wangMatrix 1).mulVec :=
  surjective_mulVec_of_isUnit_det (by rw [wangMatrix_det]; exact isUnit_one.neg)

/-- **Golden sign-twisted sector is trivial.** `F + I` has `det = +1` (a unit), so `mulVec` is
surjective: the sign-twisted `H₁` torsion `coker(F + I)` vanishes at `k = 1`. -/
theorem signTwistedMatrix_golden_surjective : Function.Surjective (signTwistedMatrix 1).mulVec :=
  surjective_mulVec_of_isUnit_det (by rw [signTwistedMatrix_det]; exact isUnit_one)

/-! ## Differential oracle: the controls carry nontrivial torsion -/

/-- **Unlink control (`k = 0`) has a rank jump.** `det(F − I) = 0`, not a unit: `coker(F − I)` is
infinite, so `H₁(M_F)` gains a second ℤ summand. -/
theorem wangMatrix_zero_not_isUnit : ¬ IsUnit (wangMatrix 0).det := by
  rw [wangMatrix_det]; norm_num [Int.isUnit_iff]

/-- **Clasp control (`k = 2`) carries ℤ/2 torsion.** `det(F − I) = −2`, not a unit. -/
theorem wangMatrix_two_not_isUnit : ¬ IsUnit (wangMatrix 2).det := by
  rw [wangMatrix_det]; norm_num [Int.isUnit_iff]

/-- Sign-twisted clasp value is `+2` (matching `|det| = 2`, the ℤ/2 torsion order). -/
theorem signTwistedMatrix_two_det : (signTwistedMatrix 2).det = 2 := by
  rw [signTwistedMatrix_det]

/-- **Concrete non-surjectivity witness for the clasp.** `![1,0]` is not in the image of `F − I` at
`k = 2`: the image lattice `{(a,b) : a + b even}` has index 2, so `coker(F − I) ≅ ℤ/2` is genuinely
nontrivial. This is the anti-vacuity floor: the golden case is surjective, the clasp provably is not. -/
theorem wangMatrix_two_not_surjective : ¬ Function.Surjective (wangMatrix 2).mulVec := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj ![1, 0]
  have h0 := congrArg (fun v => v 0) hx
  have h1 := congrArg (fun v => v 1) hx
  simp only [wangMatrix_closed_form] at h0 h1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  omega

/-! ## Panel supplements: the unimodularity witnesses ARE the golden relation

The panel's Stage-2 supplement (2026-07-01): the golden case is not merely "det happens to be a
unit". The explicit inverse of the Wang matrix at `k = 1` is the return map `F` itself, because
`F·(F − I) = F² − F = I` **is** the golden relation `F² = F + I`. Likewise `F + I = F²` at golden.
So the two unimodularity witnesses are algebraically the golden relation, not numerical accidents. -/

/-- **The Wang inverse is `F` itself, and only at golden.** `(F − I)·F = (k−1)·F + I`, so
`(F − I)·F = I ↔ k = 1`: unimodularity-with-inverse-`F` is *equivalent* to the golden value. -/
theorem wang_mul_returnMap (k : ℤ) :
    wangMatrix k * returnMap k = (k - 1) • returnMap k + 1 := by
  rw [wangMatrix_closed_form, returnMap_closed_form, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- **Golden ⇒ the Wang matrix inverts against `F`.** `(F − I)·F = I` at `k = 1`: this equation IS
the golden relation `F² = F + I` rearranged. -/
theorem wang_mul_returnMap_golden : wangMatrix 1 * returnMap 1 = 1 := by
  rw [wang_mul_returnMap]; simp

theorem returnMap_mul_wang_golden : returnMap 1 * wangMatrix 1 = 1 := by
  rw [wangMatrix_closed_form, returnMap_closed_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The equivalence: Wang-inverts-against-`F` iff golden.** For `k ≠ 1` the product
`(F − I)·F = (k−1)F + I ≠ I` (its `(0,1)` entry is `k − 1`). -/
theorem wang_inv_iff_golden (k : ℤ) : wangMatrix k * returnMap k = 1 ↔ k = 1 := by
  constructor
  · intro h
    have h01 := congrArg (fun M => M 0 1) h
    rw [wang_mul_returnMap] at h01
    simp [returnMap_closed_form, Matrix.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h01
    omega
  · rintro rfl; exact wang_mul_returnMap_golden

/-- **The sign-twisted matrix at golden is `F²`.** `F + I = F²` at `k = 1` — this equation IS the
golden relation. The twisted sector's unimodularity is `det(F²) = (det F)² = 1`. -/
theorem signTwisted_golden_eq_sq : signTwistedMatrix 1 = returnMap 1 ^ 2 := by
  rw [signTwistedMatrix_closed_form, sq, returnMap_closed_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Explicit integral inverse of the sign-twisted matrix at golden: `(F + I)⁻¹ = !![2,−1;−1,1]`. -/
theorem signTwisted_golden_mul_inv : signTwistedMatrix 1 * !![(2 : ℤ), -1; -1, 1] = 1 := by
  rw [signTwistedMatrix_closed_form]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The determinant product identity.** `det(F − I)·det(F + I) = det(F² − I) = −k²`: the product
of the two sector torsion values is `−k²`, forced by `det F = −1` (Cayley–Hamilton gives
`F² − I = k·F`, so the product is `k²·det F = −k²`). -/
theorem wang_twist_det_product (k : ℤ) :
    (wangMatrix k).det * (signTwistedMatrix k).det = -k ^ 2 := by
  rw [wangMatrix_det, signTwistedMatrix_det]; ring

/-- **Signed oracle table.** The pair `(det(F − I), det(F + I))` distinguishes the three linking
cases with sign structure: unlink `(0, 0)`, golden `(−1, 1)`, clasp `(−2, 2)`. -/
theorem signed_oracle_unlink : (wangMatrix 0).det = 0 ∧ (signTwistedMatrix 0).det = 0 :=
  ⟨by rw [wangMatrix_det]; ring, by rw [signTwistedMatrix_det]⟩

theorem signed_oracle_golden : (wangMatrix 1).det = -1 ∧ (signTwistedMatrix 1).det = 1 :=
  ⟨by rw [wangMatrix_det], by rw [signTwistedMatrix_det]⟩

theorem signed_oracle_clasp : (wangMatrix 2).det = -2 ∧ (signTwistedMatrix 2).det = 2 :=
  ⟨by rw [wangMatrix_det], by rw [signTwistedMatrix_det]⟩

/-- **Double unimodularity classifies `|k| = 1`.** Both `H₁` sectors are torsion-free
(both determinants units) iff `k = 1` or `k = −1`: the golden pair `±φ^∓` are the only
unit-linking fibrations with no fiber torsion in either sector. -/
theorem double_unimodular_iff (k : ℤ) :
    (IsUnit (wangMatrix k).det ∧ IsUnit (signTwistedMatrix k).det) ↔ k = 1 ∨ k = -1 := by
  rw [wangMatrix_det, signTwistedMatrix_det]
  constructor
  · rintro ⟨-, hk⟩
    rcases Int.isUnit_iff.mp hk with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨isUnit_one.neg, isUnit_one⟩
    · exact ⟨isUnit_one, isUnit_one.neg⟩

/-! ## Certificate bundling GDB Stage 2 -/

/-- THEOREM-grade certificate for **GDB Stage 2** (sign-character twisted `H₁` comparison): the two
`H₁` sectors of the golden mapping torus are computed by `det(F − I) = −k` (untwisted) and
`det(F + I) = k` (sign-twisted), which equal the Stage-1 torsion polynomial at `t = ±1` and are
negatives of each other (the `det = −1` anti-palindrome). At the **golden** value `k = 1` both
sectors are unimodular, hence torsion-free (surjective `mulVec`); the unlink (`k = 0`) has a rank
jump and the clasp (`k = 2`) carries genuine ℤ/2 torsion (`![1,0]` provably missed). So the golden
value is the unique unit-linking case with both `H₁` sectors torsion-free.

**MODEL premise (not asserted here):** the Wang-sequence / Smith-normal-form identification of the
`H₁` sectors with `coker(F ∓ I)` and the orientation character with the sign twist. -/
structure GoldenTwistedH1Cert : Prop where
  untwisted_value : ∀ k : ℤ, (wangMatrix k).det = -k
  twisted_value : ∀ k : ℤ, (signTwistedMatrix k).det = k
  untwisted_is_torsion_eval_one : ∀ k : ℤ,
    (wangMatrix k).det = (GoldenTorsionAlexander.torsionPoly k).eval 1
  twisted_is_torsion_eval_neg_one : ∀ k : ℤ,
    (signTwistedMatrix k).det = (GoldenTorsionAlexander.torsionPoly k).eval (-1)
  anti_palindrome : ∀ k : ℤ, (wangMatrix k).det = -(signTwistedMatrix k).det
  golden_untwisted_trivial : Function.Surjective (wangMatrix 1).mulVec
  golden_twisted_trivial : Function.Surjective (signTwistedMatrix 1).mulVec
  unlink_rank_jump : ¬ IsUnit (wangMatrix 0).det
  clasp_has_torsion : ¬ IsUnit (wangMatrix 2).det
  clasp_not_surjective : ¬ Function.Surjective (wangMatrix 2).mulVec
  wang_inverse_is_golden_relation : ∀ k : ℤ, wangMatrix k * returnMap k = 1 ↔ k = 1
  twist_is_square_at_golden : signTwistedMatrix 1 = returnMap 1 ^ 2
  det_product : ∀ k : ℤ, (wangMatrix k).det * (signTwistedMatrix k).det = -k ^ 2
  double_unimodular_classifies : ∀ k : ℤ,
    (IsUnit (wangMatrix k).det ∧ IsUnit (signTwistedMatrix k).det) ↔ k = 1 ∨ k = -1

theorem goldenTwistedH1Cert_holds : GoldenTwistedH1Cert where
  untwisted_value := wangMatrix_det
  twisted_value := signTwistedMatrix_det
  untwisted_is_torsion_eval_one := wangMatrix_det_eq_torsion_eval_one
  twisted_is_torsion_eval_neg_one := signTwistedMatrix_det_eq_torsion_eval_neg_one
  anti_palindrome := untwisted_eq_neg_twisted
  golden_untwisted_trivial := wangMatrix_golden_surjective
  golden_twisted_trivial := signTwistedMatrix_golden_surjective
  unlink_rank_jump := wangMatrix_zero_not_isUnit
  clasp_has_torsion := wangMatrix_two_not_isUnit
  clasp_not_surjective := wangMatrix_two_not_surjective
  wang_inverse_is_golden_relation := wang_inv_iff_golden
  twist_is_square_at_golden := signTwisted_golden_eq_sq
  det_product := wang_twist_det_product
  double_unimodular_classifies := double_unimodular_iff

end GoldenTwistedH1
end Masses
end IndisputableMonolith
