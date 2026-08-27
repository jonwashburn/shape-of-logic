import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Ambient isotopy invariance of complement homology

A homeomorphism of a space carrying one subspace onto another restricts
to a homeomorphism of the complements. Singular homology is a
homeomorphism invariant, so the groups of the two complements agree in
every degree.

An ambient isotopy is a path of homeomorphisms; the time-1 map is a
homeomorphism, so the conclusion applies to isotopy as well.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace IsotopyComplementHomology

open CategoryTheory

lemma mem_compl_image_of_mem_compl {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A : Set Y} {x : Y} (hx : x ∈ Aᶜ) :
    f x ∈ (f '' A)ᶜ := by
  intro hxA
  obtain ⟨y, hyA, hyf⟩ := hxA
  have : y = x := f.injective hyf
  exact hx (this ▸ hyA)

lemma mem_compl_of_symm_mem_compl_image {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A : Set Y} {y : Y} (hy : y ∈ (f '' A)ᶜ) :
    f.symm y ∈ Aᶜ := by
  intro hyA
  exact hy ⟨f.symm y, hyA, f.apply_symm_apply y⟩

/-- A homeomorphism of `Y` carrying `A` onto `B` restricts to a
homeomorphism of the complements. -/
def complementHomeomorph {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A B : Set Y} (hAB : f '' A = B) :
    {x : Y // x ∈ Aᶜ} ≃ₜ {y : Y // y ∈ Bᶜ} where
  toFun := fun x =>
    ⟨f x, by
      have : f x ∈ (f '' A)ᶜ := mem_compl_image_of_mem_compl f x.property
      simpa [hAB] using this⟩
  invFun := fun y =>
    ⟨f.symm y, mem_compl_of_symm_mem_compl_image f (by simpa [hAB] using y.property)⟩
  left_inv := fun x => Subtype.ext (f.left_inv x)
  right_inv := fun y => Subtype.ext (f.right_inv y)
  continuous_toFun :=
    (f.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (f.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem complementHomeomorph_apply {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A B : Set Y} (hAB : f '' A = B)
    (x : {x : Y // x ∈ Aᶜ}) :
    (complementHomeomorph f hAB x : Y) = f x :=
  rfl

/-- A homeomorphism of spaces induces an isomorphism of their `TopCat`
objects. -/
def topIsoOfHomeo {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) : TopCat.of X ≅ TopCat.of Z where
  hom := TopCat.ofHom e
  inv := TopCat.ofHom e.symm
  hom_inv_id := by
    ext x
    exact e.left_inv x
  inv_hom_id := by
    ext y
    exact e.right_inv y

/-- Complement homology is invariant under a homeomorphism of the ambient
space that carries one subspace onto the other. -/
theorem complement_homology_homeomorph_invariant {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A B : Set Y} (hAB : f '' A = B)
    (n : ℕ) :
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of {x : Y // x ∈ Aᶜ})) ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of {y : Y // y ∈ Bᶜ}))) :=
  ⟨((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).mapIso
    (topIsoOfHomeo (complementHomeomorph f hAB))⟩

/-- First homology of the complements is likewise invariant. -/
theorem complement_H1_homeomorph_invariant {Y : Type} [TopologicalSpace Y]
    (f : Y ≃ₜ Y) {A B : Set Y} (hAB : f '' A = B) :
    Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of {x : Y // x ∈ Aᶜ})) ≅
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of {y : Y // y ∈ Bᶜ}))) :=
  complement_homology_homeomorph_invariant f hAB 1

end IsotopyComplementHomology
end Foundation
end IndisputableMonolith
