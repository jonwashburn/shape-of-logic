import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.GoldenFoldForcing

/-!
# Golden Minimal Integral Realization (the head of `GD_fold_is_golden`)

`Masses/GoldenFoldForcing.lean` compressed the fold to the **golden relation** `F² = F + I`
on the integer ledger and forced `trace = 1`, `det = -1`, positive eigenvalue `φ`.
`Masses/GoldenGenerationForcing.lean` banked the algebra spine (cube, mod-2 order three, the
Cayley–Hamilton converse, the swap·shear factorization, the duality-closed spectrum).

This module banks the **head statement** the longer-range goal exits through: `goldenMulZ` is
the **minimal integral realization of the T6 self-similarity mode** `r² = r + 1`. The claim is
made non-vacuous by proving four independent facts and bundling them:

1. **Realization.** `goldenMulZ` satisfies the golden relation and its characteristic polynomial
   is the *mode polynomial* `X² − X − 1` (`goldenMulZ_charpoly`). The mode `r² = r + 1` is exactly
   `p(r) = 0` for `p = X² − X − 1`.

2. **Char-poly canonicity.** *Every* integer `2×2` golden-relation operator has the same
   characteristic polynomial `X² − X − 1` (`golden_charpoly`). So `goldenMulZ` is not one choice
   among many spectra; the spectrum is forced. (This is `charpoly_fin_two` fed by the banked
   `trace = 1`, `det = −1`.)

3. **Dimensional minimality.** There is *no* `1×1` integer realization: no integer `n` satisfies
   `n² = n + 1` (`no_dim_one_realization`, from `no_integer_golden_root`). So dimension `2` is the
   least dimension in which an integer operator realizes the mode.

4. **Mode root.** The real root of the characteristic polynomial *is* the forced scale ratio `φ`:
   `aeval φ (goldenMulZ.charpoly) = 0` (`phi_root_of_charpoly`), which unfolds to `φ² − φ − 1 = 0`,
   i.e. `Constants.phi_sq_eq`.

5. **Char poly = minimal polynomial (the strong form of "minimal").** The mode polynomial
   `X² − X − 1` is *irreducible over ℚ* (`modePoly_irreducible`, via `no_rat_golden_root`: no
   rational scalar satisfies the mode, because both real roots `φ` and `1 − φ` are irrational).
   Hence it *is* the minimal polynomial of `φ` over ℚ (`modePoly_eq_minpoly`), and therefore the
   fold operator's characteristic polynomial, cast to `ℚ[X]`, **is** `minpoly ℚ φ`
   (`charpoly_map_eq_minpoly`). "Minimal" is thus not a convention: no polynomial of lower degree
   over ℚ annihilates `φ`, so no `1×1` operator over ℚ (a fortiori over ℤ) realizes the mode, and
   the `2×2` fold operator realizes it with the smallest possible annihilating polynomial.

## Honest status and scope

- All declarations here are THEOREM-grade (no `sorry`, Mathlib-base axioms only).
- "Minimal integral realization" here means **least dimension (over ℚ, hence over ℤ) + canonical
  (forced) characteristic polynomial + char poly = `minpoly ℚ φ` + mode root `φ`**. It does
  **not** claim `GL₂(ℤ)`-conjugacy uniqueness (that every integer realization is `GL₂(ℤ)`-conjugate
  to `goldenMulZ`); that is the strictly stronger class-number-one statement about `ℤ[φ]` and is
  left OPEN, out of scope here.
- The OPEN part of `GD_fold_is_golden` remains the **monodromy front-end**: constructing the T7/T8
  two-cycle configuration whose `H₁` return map *is* this operator. That is not attempted here.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenMinimalRealization

open Constants
open Polynomial
open IndisputableMonolith.Masses.GoldenFoldForcing

/-! ## Char-poly canonicity: every integer golden operator has char poly `X² − X − 1` -/

/-- **Char-poly canonicity.** Every integer `2×2` operator satisfying the golden relation
`F² = F + I` has characteristic polynomial `X² − X − 1`. Immediate from the `2×2` formula
`charpoly = X² − (tr)·X + (det)` fed by the banked forcing `trace = 1`, `det = −1`.
The spectrum of an integer golden operator is *forced*, not chosen. -/
theorem golden_charpoly {F : Matrix (Fin 2) (Fin 2) ℤ} (h : GoldenRelation F) :
    F.charpoly = X ^ 2 - X - 1 := by
  rw [Matrix.charpoly_fin_two]
  rw [(golden_integral_forces h).1, (golden_integral_forces h).2]
  simp only [map_one, map_neg]
  ring

/-- The canonical witness `goldenMulZ = !![0,1;1,1]` (the Fibonacci `Q`-matrix, and the standard
companion matrix of `X² − X − 1`) has characteristic polynomial `X² − X − 1`. -/
theorem goldenMulZ_charpoly : goldenMulZ.charpoly = X ^ 2 - X - 1 :=
  golden_charpoly goldenRelation_of_goldenMulZ

/-! ## Dimensional minimality: no `1×1` realization, over ℤ or even over ℚ -/

/-- **No rational golden root.** No rational number satisfies the T6 mode `q² = q + 1`: the two
real roots of `x² − x − 1` are `φ` and `1 − φ`, and both are irrational (`Constants.phi_irrational`).
This upgrades dimensional minimality from the integer ledger to the whole rational field, and it is
exactly the statement that the mode polynomial has no degree-1 factor over ℚ. -/
theorem no_rat_golden_root (q : ℚ) : q * q ≠ q + 1 := by
  intro h
  have hr : (q : ℝ) * (q : ℝ) = (q : ℝ) + 1 := by exact_mod_cast h
  have hfactor : ((q : ℝ) - phi) * ((q : ℝ) - (1 - phi)) = 0 := by
    linear_combination hr - phi_sq_eq
  rcases mul_eq_zero.mp hfactor with h1 | h2
  · have hphi_eq : phi = ((q : ℚ) : ℝ) := by linarith
    exact Rat.not_irrational q (hphi_eq ▸ phi_irrational)
  · have hphi_eq : phi = ((1 - q : ℚ) : ℝ) := by push_cast; linarith
    exact Rat.not_irrational (1 - q) (hphi_eq ▸ phi_irrational)

/-- **No `1×1` integer realization.** No integer `1×1` operator `G` satisfies `G² = G + I`,
because that reduces to `(G 0 0)² = G 0 0 + 1`, which has no integer solution
(`no_integer_golden_root`). Hence dimension `2` is the least dimension in which an integer
operator realizes the T6 mode. -/
theorem no_dim_one_realization (G : Matrix (Fin 1) (Fin 1) ℤ) : G * G ≠ G + 1 := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply, Matrix.one_apply_eq] at hh
  exact no_integer_golden_root (G 0 0) hh

/-- **No `1×1` rational realization.** Minimality is not an artifact of integrality: even over
the field ℚ no `1×1` operator satisfies `G² = G + I` (from `no_rat_golden_root`). -/
theorem no_dim_one_realization_rat (G : Matrix (Fin 1) (Fin 1) ℚ) : G * G ≠ G + 1 := by
  intro h
  have hh := congrFun (congrFun h 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.add_apply, Matrix.one_apply_eq] at hh
  exact no_rat_golden_root (G 0 0) hh

/-! ## Mode root: the char-poly root is the forced scale ratio `φ` -/

/-- **Mode root.** The scale ratio `φ` is a root of the fold's characteristic polynomial:
`aeval φ (goldenMulZ.charpoly) = 0`. Unfolding, this is `φ² − φ − 1 = 0`, i.e.
`Constants.phi_sq_eq` — the T6 self-similarity mode `r² = r + 1`. So the characteristic polynomial
`X² − X − 1` is exactly the (degree-2, minimal) polynomial pinning the T6 fixed point. -/
theorem phi_root_of_charpoly : aeval phi goldenMulZ.charpoly = 0 := by
  rw [goldenMulZ_charpoly]
  simp only [map_sub, map_pow, map_one, aeval_X]
  linear_combination phi_sq_eq

/-! ## The mode polynomial IS the minimal polynomial of `φ` over ℚ -/

/-- The mode polynomial `X² − X − 1` over ℚ is monic. -/
theorem modePolyQ_monic : (X ^ 2 - X - 1 : ℚ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℚ[X]) = X ^ 2 - (X + 1) := by ring
  rw [h]
  apply monic_X_pow_sub
  have hd : (X + 1 : ℚ[X]).degree = 1 := by
    simpa using degree_X_add_C (1 : ℚ)
  rw [hd]
  norm_num

/-- The mode polynomial has degree exactly `2` over ℚ. -/
theorem modePolyQ_natDegree : (X ^ 2 - X - 1 : ℚ[X]).natDegree = 2 := by
  compute_degree!

/-- **Irreducibility of the mode.** `X² − X − 1` is irreducible over ℚ. A monic quadratic over a
field is irreducible iff it has no roots, and the mode has no rational root
(`no_rat_golden_root`: both real roots `φ`, `1 − φ` are irrational). -/
theorem modePoly_irreducible : Irreducible (X ^ 2 - X - 1 : ℚ[X]) := by
  have h2 : (X ^ 2 - X - 1 : ℚ[X]).natDegree = 2 := modePolyQ_natDegree
  rw [modePolyQ_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (le_of_eq h2.symm) (by rw [h2]; norm_num)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro q hq
  rw [mem_roots modePolyQ_monic.ne_zero] at hq
  have hroot : q ^ 2 - q - 1 = 0 := by simpa [IsRoot] using hq
  exact no_rat_golden_root q (by linear_combination hroot)

/-- **The mode polynomial is `minpoly ℚ φ`.** Irreducible + monic + `φ` is a root, so by
`minpoly.eq_of_irreducible_of_monic` the mode polynomial `X² − X − 1` is *the* minimal polynomial
of the forced scale ratio over ℚ. "Minimal" is now a theorem, not a naming convention: no rational
polynomial of degree `< 2` annihilates `φ`. -/
theorem modePoly_eq_minpoly : (X ^ 2 - X - 1 : ℚ[X]) = minpoly ℚ phi :=
  minpoly.eq_of_irreducible_of_monic modePoly_irreducible
    (by simp only [map_sub, map_pow, map_one, aeval_X]; linear_combination phi_sq_eq)
    modePolyQ_monic

/-- The minimal polynomial of `φ` over ℚ has degree exactly `2` — the quantitative form of
dimensional minimality over the field. -/
theorem minpoly_phi_natDegree : (minpoly ℚ phi).natDegree = 2 := by
  rw [← modePoly_eq_minpoly]
  exact modePolyQ_natDegree

/-- **Char poly = minimal polynomial.** The fold operator's characteristic polynomial, cast to
`ℚ[X]`, *is* the minimal polynomial of `φ` over ℚ. This is the strong sense in which `goldenMulZ`
is the *minimal* integral realization: its spectrum polynomial is the smallest-degree rational
polynomial pinning the T6 fixed point, and (`goldenMulZ` being its companion matrix) `2×2` is the
least dimension in which any ℚ-linear operator — a fortiori any integer operator — realizes the
mode. -/
theorem charpoly_map_eq_minpoly :
    goldenMulZ.charpoly.map (Int.castRingHom ℚ) = minpoly ℚ phi := by
  rw [goldenMulZ_charpoly, ← modePoly_eq_minpoly]
  simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one]

/-! ## Certificate bundling the minimal integral realization -/

/-- THEOREM-grade certificate: `goldenMulZ` is the **minimal integral realization of the T6
self-similarity mode** `r² = r + 1`, in the precise sense of

* **realization** — it satisfies the golden relation `F² = F + I` and its characteristic
  polynomial is the mode polynomial `X² − X − 1`;
* **canonical spectrum** — every integer `2×2` golden operator has that same char poly;
* **dimensional minimality** — no `1×1` operator realizes the mode, over ℤ *or over ℚ*;
* **mode root** — the char-poly's real root is the forced scale ratio `φ` (`φ² = φ + 1`);
* **char poly = minpoly** — the char poly, cast to `ℚ[X]`, *is* `minpoly ℚ φ` (irreducible over
  ℚ, degree 2), so no lower-degree rational polynomial annihilates `φ` and "minimal" is proved,
  not conventional.

(GL₂(ℤ)-conjugacy uniqueness of the realization is strictly stronger and is *not* asserted.) -/
structure MinimalIntegralRealizationCert where
  realizes_relation : GoldenRelation goldenMulZ
  realizes_charpoly : goldenMulZ.charpoly = X ^ 2 - X - 1
  charpoly_canonical :
    ∀ {F : Matrix (Fin 2) (Fin 2) ℤ}, GoldenRelation F → F.charpoly = X ^ 2 - X - 1
  no_lower_dimension : ∀ G : Matrix (Fin 1) (Fin 1) ℤ, G * G ≠ G + 1
  no_lower_dimension_rat : ∀ G : Matrix (Fin 1) (Fin 1) ℚ, G * G ≠ G + 1
  mode_root : aeval phi goldenMulZ.charpoly = 0
  mode_poly_irreducible : Irreducible (X ^ 2 - X - 1 : ℚ[X])
  charpoly_is_minpoly : goldenMulZ.charpoly.map (Int.castRingHom ℚ) = minpoly ℚ phi

theorem minimalIntegralRealizationCert_holds : Nonempty MinimalIntegralRealizationCert :=
  ⟨{ realizes_relation := goldenRelation_of_goldenMulZ
     realizes_charpoly := goldenMulZ_charpoly
     charpoly_canonical := fun h => golden_charpoly h
     no_lower_dimension := no_dim_one_realization
     no_lower_dimension_rat := no_dim_one_realization_rat
     mode_root := phi_root_of_charpoly
     mode_poly_irreducible := modePoly_irreducible
     charpoly_is_minpoly := charpoly_map_eq_minpoly }⟩

end GoldenMinimalRealization
end Masses
end IndisputableMonolith
