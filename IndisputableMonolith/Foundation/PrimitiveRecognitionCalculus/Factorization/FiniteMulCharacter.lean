/-
  PrimitiveRecognitionCalculus/Factorization/FiniteMulCharacter.lean

  A first δ-native finite multiplicative character interface. This is not the
  older PRC cost-character/orientation surface; it is a residue-unit character
  surface meant for period and Dirichlet-style arithmetic.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PeriodSpectrum

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A finite multiplicative character on unit residues modulo `N`, represented
as a complex-valued function on orbit representatives that respects the native
residue relation and multiplies on unit residues. -/
structure FiniteMulCharacter (N : DistinctionNat) where
  eval : DistinctionNat → ℂ
  respects_residue :
    ∀ {a b : DistinctionNat} {hN : N ≠ zero},
      sameResidue N hN a b → eval a = eval b
  map_one : eval one = 1
  map_mul_units :
    ∀ {a b : DistinctionNat},
      unitResidue N a → unitResidue N b →
        eval (a * b) = eval a * eval b

namespace FiniteMulCharacter

/-- The constant-one principal character on unit residues. -/
def principal (N : DistinctionNat) : FiniteMulCharacter N where
  eval := fun _ => 1
  respects_residue := by
    intro a b hN h
    rfl
  map_one := rfl
  map_mul_units := by
    intro a b ha hb
    norm_num

@[simp] theorem principal_eval (N a : DistinctionNat) :
    (principal N).eval a = 1 := rfl

theorem principal_map_mul_units (N a b : DistinctionNat)
    (ha : unitResidue N a) (hb : unitResidue N b) :
    (principal N).eval (a * b) =
      (principal N).eval a * (principal N).eval b := by
  exact (principal N).map_mul_units ha hb

/-- Product of two finite multiplicative characters. -/
def mul {N : DistinctionNat}
    (χ ψ : FiniteMulCharacter N) : FiniteMulCharacter N where
  eval := fun a => χ.eval a * ψ.eval a
  respects_residue := by
    intro a b hN h
    rw [χ.respects_residue h, ψ.respects_residue h]
  map_one := by
    rw [χ.map_one, ψ.map_one]
    norm_num
  map_mul_units := by
    intro a b ha hb
    rw [χ.map_mul_units ha hb, ψ.map_mul_units ha hb]
    ring

theorem mul_eval {N : DistinctionNat}
    (χ ψ : FiniteMulCharacter N) (a : DistinctionNat) :
    (mul χ ψ).eval a = χ.eval a * ψ.eval a := rfl

/-- Sum of a character over a finite representative list after left
multiplication by a unit. -/
theorem scaled_list_eval_sum {N : DistinctionNat}
    (χ : FiniteMulCharacter N) (t : DistinctionNat)
    (L : List DistinctionNat)
    (ht : unitResidue N t)
    (hunits : ∀ a ∈ L, unitResidue N a) :
    (L.map (fun a => χ.eval (t * a))).sum =
      χ.eval t * (L.map χ.eval).sum := by
  induction L with
  | nil =>
      simp
  | cons a rest ih =>
      have ha : unitResidue N a := hunits a (by simp)
      have hrest : ∀ b ∈ rest, unitResidue N b := by
        intro b hb
        exact hunits b (by simp [hb])
      have ih' := ih hrest
      simp [χ.map_mul_units ht ha, ih', mul_add]

/-- Finite-character orthogonality in the form needed by the δ residue layer.
If left multiplication by a unit `t` cycles the chosen representative list and
the character is nontrivial on `t`, then the character sum over that list is
zero. -/
theorem orthogonality_nonprincipal_sum_zero {N : DistinctionNat}
    (χ : FiniteMulCharacter N) (t : DistinctionNat)
    (L : List DistinctionNat)
    (ht : unitResidue N t)
    (hunits : ∀ a ∈ L, unitResidue N a)
    (hcycle : L.map (fun a => t * a) = L)
    (hnontrivial : χ.eval t ≠ 1) :
    (L.map χ.eval).sum = 0 := by
  let S : ℂ := (L.map χ.eval).sum
  have hscaled :
      (L.map (fun a => χ.eval (t * a))).sum = S := by
    have hcycleEval :=
      congrArg (fun M : List DistinctionNat => (M.map χ.eval).sum) hcycle
    simpa [List.map_map, S] using hcycleEval
  have hmul :
      (L.map (fun a => χ.eval (t * a))).sum = χ.eval t * S := by
    exact scaled_list_eval_sum χ t L ht hunits
  have hmulEq : χ.eval t * S = S := by
    rw [← hmul, hscaled]
  have hzero : (χ.eval t - 1) * S = 0 := by
    rw [sub_mul, one_mul, hmulEq, sub_self]
  rcases mul_eq_zero.mp hzero with hleft | hright
  · exfalso
    exact hnontrivial (sub_eq_zero.mp hleft)
  · exact hright

end FiniteMulCharacter

/-- Certificate for the finite character interface. -/
structure FiniteMulCharacterCertificate : Prop where
  principal_exists :
    ∀ N : DistinctionNat, (FiniteMulCharacter.principal N).eval one = 1
  principal_multiplicative :
    ∀ N a b : DistinctionNat,
      unitResidue N a → unitResidue N b →
        (FiniteMulCharacter.principal N).eval (a * b) =
          (FiniteMulCharacter.principal N).eval a *
            (FiniteMulCharacter.principal N).eval b
  character_product_eval :
    ∀ {N : DistinctionNat} (χ ψ : FiniteMulCharacter N) (a : DistinctionNat),
      (FiniteMulCharacter.mul χ ψ).eval a = χ.eval a * ψ.eval a
  scaled_list_eval_sum :
    ∀ {N : DistinctionNat} (χ : FiniteMulCharacter N)
      (t : DistinctionNat) (L : List DistinctionNat),
      unitResidue N t →
        (∀ a ∈ L, unitResidue N a) →
          (L.map (fun a => χ.eval (t * a))).sum =
            χ.eval t * (L.map χ.eval).sum
  orthogonality_nonprincipal_sum_zero :
    ∀ {N : DistinctionNat} (χ : FiniteMulCharacter N)
      (t : DistinctionNat) (L : List DistinctionNat),
      unitResidue N t →
        (∀ a ∈ L, unitResidue N a) →
          L.map (fun a => t * a) = L →
            χ.eval t ≠ 1 →
              (L.map χ.eval).sum = 0

theorem finite_mul_character_certificate : FiniteMulCharacterCertificate where
  principal_exists := by
    intro N
    exact (FiniteMulCharacter.principal N).map_one
  principal_multiplicative := by
    intro N a b ha hb
    exact FiniteMulCharacter.principal_map_mul_units N a b ha hb
  character_product_eval := by
    intro N χ ψ a
    exact FiniteMulCharacter.mul_eval χ ψ a
  scaled_list_eval_sum := by
    intro N χ t L ht hunits
    exact FiniteMulCharacter.scaled_list_eval_sum χ t L ht hunits
  orthogonality_nonprincipal_sum_zero := by
    intro N χ t L ht hunits hcycle hnontrivial
    exact FiniteMulCharacter.orthogonality_nonprincipal_sum_zero
      χ t L ht hunits hcycle hnontrivial

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
