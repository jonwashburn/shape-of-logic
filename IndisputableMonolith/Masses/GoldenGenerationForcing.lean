import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.GoldenFoldForcing

/-!
# Golden Generation Forcing (the algebra spine of `GD_fold_is_golden`)

`Masses/GoldenFoldForcing.lean` compressed the residual MODEL floor from "the fold is the
specific matrix `goldenMul`" to "the fold is an integer rank-2 operator satisfying the
**golden relation** `F² = F + I`", and proved that this forces `det = -1` and positive
eigenvalue `φ`.

This module banks the **algebra spine** the longer-range goal (identify the generation fold
with the minimal integral realization of the T6 self-similarity mode) exits through, plus the
theorem that raises the ceiling beyond the stated goal:

1. **Three generations, as a theorem.** `F² = F + I ⟹ F³ = 2F + I`, so on the mod-2 parity
   ledger `F³ ≡ I (mod 2)` while `F³ ≠ I` over `ℤ`; the reduction has order **exactly 3** in
   `GL₂(ℤ/2)` (`golden_mod_two_order_three`). The count "three" is forced by the relation and
   the integer ledger, not posited. (Bonus target flagged by the panel.)

2. **`eigenvalue_phi_forces_golden` (the Cayley–Hamilton tail).** If `φ` is an eigenvalue of the
   real fold operator (i.e. `det(F_ℝ − φ·I) = 0`, the standard singular-matrix characterization
   of an eigenvalue over a field), then the *integer* fold is forced into the golden relation.
   The lever is irrationality: `φ` cannot satisfy a rational linear equation, so the integer
   trace and determinant are pinned to `1` and `−1`. This is the converse direction to
   `GoldenFoldForcing.goldenRelation_pos_eigen_eq_phi`.

3. **`goldenMul = swap · shear`.** The canonical witness factors as an orientation-reversing
   swap (`det = −1`, the S2 Galois/orientation generator) composed with a unipotent shear
   (`det = +1`, the recognition magnitude). The `det = −1` of the fold is then exactly the
   determinant of its swap factor, by `det_mul`.

4. **Duality-closed spectrum.** The involution `x ↦ 1 − x` (trace-complement) preserves the
   golden relation, so the spectrum `{φ, 1−φ}` is closed under it; the Galois norm
   `φ·(1−φ) = −1` is the determinant of the fold.

## Honest status

- All declarations here are THEOREM-grade (no `sorry`, Mathlib-base axioms only). They are the
  fixed-statement algebraic tail of the two-layer program; the OPEN part remains the monodromy
  front-end (constructing the T7/T8 two-cycle configuration whose H₁ return map *is* this
  operator), which is not attempted here.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenGenerationForcing

open Constants
open IndisputableMonolith.Masses.GoldenFoldForcing

/-! ## The cube: `F³ = 2F + I` -/

/-- **The golden cube.** Any operator with `F² = F + I` satisfies `F³ = F + F + I` (`= 2F + I`).
Pure algebra of the relation over any commutative ring; no integrality needed. -/
theorem golden_cube {R : Type*} [CommRing R] {F : Matrix (Fin 2) (Fin 2) R}
    (h : GoldenRelation F) : F ^ 3 = F + F + 1 := by
  have hFF : F * F = F + 1 := h
  rw [pow_three, hFF, mul_add, mul_one, hFF]
  abel

/-! ## Three generations: order exactly 3 on the mod-2 parity ledger -/

/-- **Cube collapses to the identity mod 2.** Reducing `F³ = 2F + I` modulo 2 kills the `2F`
term, so the mod-2 image of any golden operator cubes to the identity. -/
theorem golden_cube_mod_two {F : Matrix (Fin 2) (Fin 2) ℤ} (h : GoldenRelation F) :
    (F.map (Int.castRingHom (ZMod 2))) ^ 3 = 1 := by
  have hself : ∀ x : ZMod 2, x + x = 0 := by decide
  have hzero :
      (F.map (Int.castRingHom (ZMod 2))) + (F.map (Int.castRingHom (ZMod 2))) = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.map_apply]
    exact hself _
  have h3 : F ^ 3 = F + F + 1 := golden_cube h
  calc (F.map (Int.castRingHom (ZMod 2))) ^ 3
      = ((Int.castRingHom (ZMod 2)).mapMatrix) (F ^ 3) := by
        rw [map_pow, RingHom.mapMatrix_apply]
    _ = ((Int.castRingHom (ZMod 2)).mapMatrix) (F + F + 1) := by rw [h3]
    _ = (F.map (Int.castRingHom (ZMod 2))) + (F.map (Int.castRingHom (ZMod 2))) + 1 := by
        rw [map_add, map_add, map_one, RingHom.mapMatrix_apply]
    _ = 0 + 1 := by rw [hzero]
    _ = 1 := by rw [zero_add]

/-- **Three generations, as a theorem.** The mod-2 reduction of any integral golden operator has
order **exactly 3** in `GL₂(ℤ/2)`. Cube = identity (from `golden_cube_mod_two`) gives order
dividing 3; the reduction is not the identity because its trace is `1 ≠ 0` (the identity's trace
in `ℤ/2`), which forces the order past 1. Since 3 is prime, the order is exactly 3. -/
theorem golden_mod_two_order_three {F : Matrix (Fin 2) (Fin 2) ℤ} (h : GoldenRelation F) :
    orderOf (F.map (Int.castRingHom (ZMod 2))) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcube : (F.map (Int.castRingHom (ZMod 2))) ^ 3 = 1 := golden_cube_mod_two h
  have hne : (F.map (Int.castRingHom (ZMod 2))) ≠ 1 := by
    intro hEq
    have htr_one : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).trace = 0 := by
      rw [Matrix.trace_fin_two, Matrix.one_apply_eq, Matrix.one_apply_eq]; decide
    have htrF : (F.map (Int.castRingHom (ZMod 2))).trace = 1 := by
      have e : (F.map (Int.castRingHom (ZMod 2))).trace
          = ((F 0 0 + F 1 1 : ℤ) : ZMod 2) := by
        simp [Matrix.trace_fin_two, Matrix.map_apply, Int.coe_castRingHom]
      rw [e]
      have hsum := (golden_integral_forces h).1
      rw [Matrix.trace_fin_two] at hsum
      rw [hsum]; simp
    rw [hEq, htr_one] at htrF
    exact absurd htrF (by decide)
  exact orderOf_eq_prime hcube hne

/-- The canonical integer witness cubes past the identity over `ℤ` (its order is *infinite*
there — the mod-2 order 3 is genuinely a reduction phenomenon, not an integer coincidence). -/
theorem golden_cube_ne_one {F : Matrix (Fin 2) (Fin 2) ℤ} (h : GoldenRelation F) :
    F ^ 3 ≠ 1 := by
  intro hEq
  have h3 : F + F + 1 = 1 := by rw [← golden_cube h]; exact hEq
  have hFF : F + F = 0 := by
    have hz : F + F + 1 = 0 + 1 := by rw [h3, zero_add]
    exact add_right_cancel hz
  have hF0 : F = 0 := by
    ext i j
    have hij := congrFun (congrFun hFF i) j
    simp only [Matrix.add_apply, Matrix.zero_apply] at hij ⊢
    omega
  rw [hF0] at h
  have htr := (golden_integral_forces h).1
  rw [Matrix.trace_fin_two] at htr
  simp only [Matrix.zero_apply, add_zero] at htr
  exact absurd htr (by norm_num)

theorem goldenMulZ_cube_ne_one : goldenMulZ ^ 3 ≠ 1 :=
  golden_cube_ne_one goldenRelation_of_goldenMulZ

/-! ## The Cayley–Hamilton tail: `φ` as an eigenvalue forces the golden relation -/

/-- **`eigenvalue_phi_forces_golden`.** If `φ` is an eigenvalue of the real fold operator — i.e.
`det(F_ℝ − φ·I) = 0`, the standard characterization of an eigenvalue over the field `ℝ` — then the
*integer* fold `F` is forced to satisfy the golden relation `F² = F + I`.

The mechanism (integrality via irrationality): the characteristic condition gives, after using
`φ² = φ + 1`, the scalar equation `(tr F − 1)·φ = det F + 1`. If `tr F ≠ 1`, then `φ` equals a
ratio of integers — but `φ` is irrational, contradiction. So `tr F = 1`, hence `det F = −1`, hence
golden. This is the converse of `GoldenFoldForcing.goldenRelation_pos_eigen_eq_phi`. -/
theorem eigenvalue_phi_forces_golden {F : Matrix (Fin 2) (Fin 2) ℤ}
    (heig : (F.map (Int.castRingHom ℝ) - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0) :
    GoldenRelation F := by
  set Fr := F.map (Int.castRingHom ℝ) with hFr
  have e00 : (Fr - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = (F 0 0 : ℝ) - phi := by
    simp [hFr, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Int.coe_castRingHom]
  have e11 : (Fr - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = (F 1 1 : ℝ) - phi := by
    simp [hFr, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Int.coe_castRingHom]
  have e01 : (Fr - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = (F 0 1 : ℝ) := by
    simp [hFr, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Int.coe_castRingHom]
  have e10 : (Fr - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = (F 1 0 : ℝ) := by
    simp [hFr, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, Int.coe_castRingHom]
  have hexp : (Fr - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      = ((F 0 0 : ℝ) - phi) * ((F 1 1 : ℝ) - phi) - (F 0 1 : ℝ) * (F 1 0 : ℝ) := by
    rw [Matrix.det_fin_two, e00, e11, e01, e10]
  rw [hexp] at heig
  have hkey : ((F.trace : ℝ) - 1) * phi = (F.det : ℝ) + 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    push_cast
    linear_combination (-1 : ℝ) * heig + phi_sq_eq
  have htr : F.trace = 1 := by
    by_contra htne
    have hk : (F.trace - 1 : ℤ) ≠ 0 := sub_ne_zero.mpr htne
    have hirr : Irrational (((F.trace - 1 : ℤ) : ℝ) * phi) := phi_irrational.intCast_mul hk
    have heqcast : (((F.trace - 1 : ℤ)) : ℝ) * phi = (((F.det + 1 : ℤ)) : ℝ) := by
      have h1 : ((F.trace - 1 : ℤ) : ℝ) = (F.trace : ℝ) - 1 := by
        exact_mod_cast Int.cast_sub F.trace 1
      have h2 : ((F.det + 1 : ℤ) : ℝ) = (F.det : ℝ) + 1 := by
        exact_mod_cast Int.cast_add F.det 1
      rw [h1, h2]; exact hkey
    rw [heqcast] at hirr
    exact (Int.not_irrational (F.det + 1)) hirr
  have hdet : F.det = -1 := by
    have htrR : (F.trace : ℝ) = 1 := by exact_mod_cast htr
    have hdetR : (F.det : ℝ) = -1 := by linear_combination -hkey + phi * htrR
    exact_mod_cast hdetR
  exact goldenRelation_of_trace_det htr hdet

/-! ## `goldenMul = swap · shear`: the orientation/magnitude factorization -/

/-- The orientation-reversing **swap** generator `!![0,1;1,0]` (`det = −1`, the S2 sign). -/
def foldSwap : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- The unipotent **shear** `!![1,1;0,1]` (`det = +1`, the recognition magnitude). -/
def foldShear : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- **The fold factors as swap ∘ shear.** `goldenMul = foldSwap · foldShear`. -/
theorem goldenMul_swap_shear : goldenMulZ = foldSwap * foldShear := by
  unfold goldenMulZ foldSwap foldShear
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The swap factor carries the orientation sign: `det = −1`. -/
theorem foldSwap_det : foldSwap.det = -1 := by
  simp [foldSwap, Matrix.det_fin_two]

/-- The shear factor is orientation-preserving: `det = +1`. -/
theorem foldShear_det : foldShear.det = 1 := by
  simp [foldShear, Matrix.det_fin_two]

/-- **The `det = −1` of the fold is the determinant of its swap factor.** The shear contributes
`+1`, so the whole orientation sign lives in the swap. -/
theorem goldenMul_det_factor : goldenMulZ.det = foldSwap.det * foldShear.det := by
  rw [goldenMul_swap_shear, Matrix.det_mul]

/-! ## Duality-closed spectrum: the involution `x ↦ 1 − x` -/

/-- **The trace-complement involution preserves the golden relation.** If `x² = x + 1` then
`(1−x)² = (1−x) + 1`. So the two roots `φ, 1−φ` of `x² − x − 1` are exchanged by `x ↦ 1 − x`,
and the spectrum is closed under it. -/
theorem golden_conj_closed {R : Type*} [CommRing R] {x : R} (hx : x * x = x + 1) :
    (1 - x) * (1 - x) = (1 - x) + 1 := by
  linear_combination hx

/-- The golden conjugate `1 − φ` also satisfies the golden relation. -/
theorem phi_conj_golden : (1 - phi) * (1 - phi) = (1 - phi) + 1 :=
  golden_conj_closed (by linear_combination phi_sq_eq)

/-- **The Galois norm is `−1`.** `φ · (1 − φ) = −1`: the product of the two eigenvalues is the
determinant of the fold. -/
theorem phi_conj_norm : phi * (1 - phi) = -1 := by
  linear_combination -phi_sq_eq

/-- The trace is `1`: `φ + (1 − φ) = 1`. -/
theorem phi_conj_trace : phi + (1 - phi) = 1 := by ring

/-- The Galois norm `φ·(1−φ)` equals the (real cast of the) determinant of the canonical
fold witness `goldenMul`. -/
theorem phi_conj_norm_eq_det : phi * (1 - phi) = ((goldenMulZ.det : ℤ) : ℝ) := by
  rw [phi_conj_norm, goldenMulZ_det]; norm_num

/-! ## Certificate bundling the algebra spine -/

/-- THEOREM-grade certificate for the algebra spine of `GD_fold_is_golden`: the golden cube,
the exact mod-2 order 3 (three generations), the eigenvalue→golden forcing (C–H tail), the
swap·shear factorization with its determinant split, and the duality-closed spectrum with
Galois norm `−1`. -/
structure GoldenGenerationCert where
  cube : ∀ {F : Matrix (Fin 2) (Fin 2) ℤ}, GoldenRelation F → F ^ 3 = F + F + 1
  order_three : ∀ {F : Matrix (Fin 2) (Fin 2) ℤ}, GoldenRelation F →
    orderOf (F.map (Int.castRingHom (ZMod 2))) = 3
  eigen_phi_forces : ∀ {F : Matrix (Fin 2) (Fin 2) ℤ},
    (F.map (Int.castRingHom ℝ) - phi • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 →
      GoldenRelation F
  swap_shear : goldenMulZ = foldSwap * foldShear
  det_factor : goldenMulZ.det = foldSwap.det * foldShear.det
  duality_closed : ∀ {R : Type*} [CommRing R] {x : R},
    x * x = x + 1 → (1 - x) * (1 - x) = (1 - x) + 1
  galois_norm : phi * (1 - phi) = -1

theorem goldenGenerationCert_holds : Nonempty GoldenGenerationCert :=
  ⟨{ cube := fun h => golden_cube h
     order_three := fun h => golden_mod_two_order_three h
     eigen_phi_forces := fun h => eigenvalue_phi_forces_golden h
     swap_shear := goldenMul_swap_shear
     det_factor := goldenMul_det_factor
     duality_closed := fun {R} [CommRing R] {_x} hx => golden_conj_closed hx
     galois_norm := phi_conj_norm }⟩

end GoldenGenerationForcing
end Masses
end IndisputableMonolith
