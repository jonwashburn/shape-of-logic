/-
Arc-complement acyclicity (Hatcher 2B.1, arc case): every topological
embedding of the unit interval into `S^D` has `H₁`-acyclic complement.

Campaign P-d3link, THE FINAL WALL.  This file discharges the single
remaining hypothesis parameter `ArcComplementsAcyclic D` of
`LinkingVanishingHighDim`, unconditionally and for every `D`.

## Proof (compact-support bisection over the banked Mayer-Vietoris layer)

Suppose some 1-cycle `z` in the complement of the embedded arc `a([0,1])`
is not a boundary.

* **Elementwise class toolkit** (`classOf`, `classOf_eq_zero_iff`,
  `exists_classOf`, `classOf_natural`): concrete homology classes of
  cycles in a chain complex of `ℤ`-modules, built on Mathlib's
  `moduleCatLeftHomologyData` and the banked `lhMapData` of layer 4;
  a class vanishes iff its cycle bounds, and classes push forward along
  chain maps.
* **The bisection step** (`bounds_of_mv`, `bounds_of_halves`): the two
  half-arc complements form an open cover of the midpoint complement
  (contractible, so `H₂ = 0`); exactness of the banked Mayer-Vietoris
  sequence at `H₁(U ∩ V)` makes the pair map injective, so a cycle whose
  pushforwards bound in both half-arc complements already bounds in the
  full arc complement.  Hence `z` stays nonbounding in the complement of
  one of the two halves; iterate.
* **The limit step**: the nested intervals shrink to a point `t*`; the
  complement of `a(t*)` is contractible (stereographic projection), so the
  pushforward of `z` bounds there, via a 2-chain `w` with compact support
  (`suppOf`, finitely many singular simplices with compact images).  The
  support misses `a(t*)`, so by continuity it misses `a(I_k)` for some
  large `k`; the bounding chain lifts (`exists_chain_lift`), so `z`
  already bounds in the complement of `a(I_k)` — contradiction.

## Instance-diamond note (load-bearing, inherited from layers 4-5b)

For `R = ℤ` every `ModuleCat ℤ` carrier has two `Module ℤ` instances,
propositionally but not definitionally equal, and synthesis prefers the
generic one.  This file deprioritizes `AddCommGroup.toIntModule` and
`SubNegMonoid.toZSMul` locally, matching layers 1-5b.
-/
import IndisputableMonolith.Foundation.LinkingVanishingHighDim

namespace IndisputableMonolith
namespace Foundation
namespace ArcComplementAcyclic

open CategoryTheory Category Limits AlgebraicTopology Simplicial Opposite
open SingularPrism SingularSubdivision SingularMayerVietoris SingularSphere
open SingularSphereGeometry LinkingVanishingHighDim
open Metric Set

attribute [local instance 10] Classical.decEq

/- See the instance-diamond note in the module header. -/
attribute [local instance 0] AddCommGroup.toIntModule
attribute [local instance 0] SubNegMonoid.toZSMul

set_option maxHeartbeats 800000

/-! ## Elementwise helpers for isomorphisms of `ℤ`-modules -/

section IsoElements

variable {M N : ModuleCat.{0} ℤ}

lemma inv_hom_apply (e : M ≅ N) (x : ↥M) : e.inv (e.hom x) = x := by
  rw [← ModuleCat.comp_apply, e.hom_inv_id, ModuleCat.id_apply]

lemma hom_inv_apply (e : M ≅ N) (x : ↥N) : e.hom (e.inv x) = x := by
  rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]

lemma hom_apply_eq_zero_iff (e : M ≅ N) (x : ↥M) : e.hom x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h2 : e.inv (e.hom x) = e.inv 0 := by rw [h]
    rw [inv_hom_apply, map_zero] at h2
    exact h2
  · intro h
    rw [h, map_zero]

/-- Every element of a zero object vanishes. -/
lemma eq_zero_of_isZero (hM : IsZero M) (x : ↥M) : x = 0 := by
  have h : 𝟙 M = 0 := hM.eq_of_src _ _
  calc x = (𝟙 M) x := (ModuleCat.id_apply _ _).symm
    _ = (0 : M ⟶ M) x := by rw [h]
    _ = 0 := zeroApp x

end IsoElements

/-! ## The elementwise homology class toolkit

Concrete homology classes of cycles of a chain complex of `ℤ`-modules,
through the honest-index short complex `K.sc' (n+2) (n+1) n` and Mathlib's
`moduleCatLeftHomologyData` (whose `H` is `ker ⧸ range` on the nose). -/

section ClassToolkit

variable (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The canonical isomorphism from `K.sc (n+1)` to the honest-index short
complex `K.X (n+2) ⟶ K.X (n+1) ⟶ K.X n`. -/
noncomputable def scIso (n : ℕ) : K.sc (n + 1) ≅ K.sc' (n + 2) (n + 1) n :=
  K.isoSc' (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)

/-- The homology class of a cycle, as an element of the abstract homology
object `K.homology (n+1)`. -/
noncomputable def classOf (n : ℕ) (z : ↥(K.X (n + 1))) (hz : K.d (n + 1) n z = 0) :
    ↥(K.homology (n + 1)) :=
  CategoryTheory.ShortComplex.homologyMap (scIso K n).inv
    ((K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
      (Submodule.Quotient.mk ⟨z, hz⟩))

/-- **The vanishing criterion.** The class of a cycle is zero iff the cycle
is a boundary. -/
lemma classOf_eq_zero_iff (n : ℕ) (z : ↥(K.X (n + 1))) (hz : K.d (n + 1) n z = 0) :
    classOf K n z hz = 0 ↔ ∃ w : ↥(K.X (n + 2)), z = K.d (n + 2) (n + 1) w := by
  have h1 : ∀ x : ↥((K.sc' (n + 2) (n + 1) n).homology),
      CategoryTheory.ShortComplex.homologyMap (scIso K n).inv x = 0 ↔ x = 0 := fun x =>
    hom_apply_eq_zero_iff (CategoryTheory.ShortComplex.homologyMapIso (scIso K n)).symm x
  have h2 : ∀ q, (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv q = 0 ↔
      q = 0 := fun q =>
    hom_apply_eq_zero_iff (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.symm q
  unfold classOf
  rw [h1, h2, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (congrArg Subtype.val hw).symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw.symm⟩

/-- **Representability.** Every homology element is the class of a cycle. -/
lemma exists_classOf (n : ℕ) (h : ↥(K.homology (n + 1))) :
    ∃ (z : ↥(K.X (n + 1))) (hz : K.d (n + 1) n z = 0), classOf K n z hz = h := by
  obtain ⟨⟨z, hz⟩, hzq⟩ := Submodule.mkQ_surjective
    (LinearMap.range (K.sc' (n + 2) (n + 1) n).moduleCatToCycles)
    ((K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.hom
      (CategoryTheory.ShortComplex.homologyMap (scIso K n).hom h))
  refine ⟨z, hz, ?_⟩
  unfold classOf
  have hzq' : Submodule.Quotient.mk
      (p := LinearMap.range (K.sc' (n + 2) (n + 1) n).moduleCatToCycles) ⟨z, hz⟩ =
      (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.hom
        (CategoryTheory.ShortComplex.homologyMap (scIso K n).hom h) := hzq
  rw [hzq', inv_hom_apply]
  exact inv_hom_apply (CategoryTheory.ShortComplex.homologyMapIso (scIso K n)) h

variable {K L}

/-- **Naturality.** Classes push forward along chain maps. -/
lemma classOf_natural (φ : K ⟶ L) (n : ℕ) (z : ↥(K.X (n + 1)))
    (hz : K.d (n + 1) n z = 0) (hz' : L.d (n + 1) n (φ.f (n + 1) z) = 0) :
    HomologicalComplex.homologyMap φ (n + 1) (classOf K n z hz) =
      classOf L n (φ.f (n + 1) z) hz' := by
  set ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{0} ℤ)
    (ComplexShape.down ℕ) (n + 2) (n + 1) n).map φ with hψ
  set e := HomologicalComplex.natIsoSc' (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)
    (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n) with he
  have hnat := e.hom.naturality φ
  have hcomm : (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) (n + 1)).map φ =
      (scIso K n).hom ≫ ψ ≫ (scIso L n).inv := by
    show (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) (n + 1)).map φ = e.hom.app K ≫ ψ ≫ e.inv.app L
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have h1 : HomologicalComplex.homologyMap φ (n + 1) =
      CategoryTheory.ShortComplex.homologyMap ((scIso K n).hom ≫ ψ ≫ (scIso L n).inv) := by
    show CategoryTheory.ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) (n + 1)).map φ) = _
    rw [hcomm]
  have h2 : CategoryTheory.ShortComplex.homologyMap (scIso K n).hom (classOf K n z hz) =
      (K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
        (Submodule.Quotient.mk ⟨z, hz⟩) := by
    unfold classOf
    exact hom_inv_apply (CategoryTheory.ShortComplex.homologyMapIso (scIso K n)) _
  have h3 : CategoryTheory.ShortComplex.homologyMap ψ
      ((K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
        (Submodule.Quotient.mk ⟨z, hz⟩)) =
      (L.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
        (Submodule.Quotient.mk ⟨φ.f (n + 1) z, hz'⟩) := by
    rw [(SingularMayerVietoris.lhMapData ψ).homologyMap_eq, ModuleCat.comp_apply,
      ModuleCat.comp_apply, hom_inv_apply]
    have h5 : (SingularMayerVietoris.lhMapData ψ).φH
        (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk (SingularMayerVietoris.kerMap ψ ⟨z, hz⟩) := rfl
    rw [h5]
    congr 1
  calc HomologicalComplex.homologyMap φ (n + 1) (classOf K n z hz)
      = CategoryTheory.ShortComplex.homologyMap (scIso L n).inv
          (CategoryTheory.ShortComplex.homologyMap ψ
            (CategoryTheory.ShortComplex.homologyMap (scIso K n).hom
              (classOf K n z hz))) := by
        have hmor : HomologicalComplex.homologyMap φ (n + 1) =
            CategoryTheory.ShortComplex.homologyMap (scIso K n).hom ≫
              CategoryTheory.ShortComplex.homologyMap ψ ≫
              CategoryTheory.ShortComplex.homologyMap (scIso L n).inv := by
          rw [h1, CategoryTheory.ShortComplex.homologyMap_comp,
            CategoryTheory.ShortComplex.homologyMap_comp]
        exact congrArg (fun m : K.homology (n + 1) ⟶ L.homology (n + 1) =>
          m (classOf K n z hz)) hmor
    _ = CategoryTheory.ShortComplex.homologyMap (scIso L n).inv
          (CategoryTheory.ShortComplex.homologyMap ψ
            ((K.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
              (Submodule.Quotient.mk ⟨z, hz⟩))) :=
        congrArg _ (congrArg _ h2)
    _ = CategoryTheory.ShortComplex.homologyMap (scIso L n).inv
          ((L.sc' (n + 2) (n + 1) n).moduleCatLeftHomologyData.homologyIso.inv
            (Submodule.Quotient.mk ⟨φ.f (n + 1) z, hz'⟩)) :=
        congrArg _ h3
    _ = classOf L n (φ.f (n + 1) z) hz' := rfl

end ClassToolkit

/-! ## Topological wrappers: cycles, bounding, and classes of `1`-chains -/

section TopWrappers

/-- Elementwise boundary/chain-map commutation. -/
lemma chainMap_bnd {A B : TopCat.{0}} (f : A ⟶ B) (n : ℕ) (x : ↥(Cgrp A (n + 1))) :
    bnd B n (chainMap f (n + 1) x) = chainMap f n (bnd A n x) := by
  have h := HomologicalComplex.Hom.comm (sChainMap f) (n + 1) n
  have h2 := congrArg (fun ψ : Cgrp A (n + 1) ⟶ Cgrp B n => ψ x) h
  simpa only [ModuleCat.comp_apply] using h2

/-- Pushforwards of cycles are cycles. -/
lemma chainMap_cycle {A B : TopCat.{0}} (f : A ⟶ B) (z : ↥(Cgrp A 1))
    (hz : bnd A 0 z = 0) : bnd B 0 (chainMap f 1 z) = 0 := by
  rw [chainMap_bnd f 0 z, hz, map_zero]

/-- Functoriality of the chain map, elementwise. -/
lemma chainMap_chainMap {A B C' : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C') (n : ℕ)
    (x : ↥(Cgrp A n)) : chainMap g n (chainMap f n x) = chainMap (f ≫ g) n x := by
  have h : sChainMap (f ≫ g) = sChainMap f ≫ sChainMap g :=
    CategoryTheory.Functor.map_comp _ _ _
  have h2 := congrArg (fun ψ : SC A ⟶ SC C' => ψ.f n) h
  have h3 : chainMap (f ≫ g) n = chainMap f n ≫ chainMap g n := h2
  rw [h3, ModuleCat.comp_apply]

lemma chainMap_id (A : TopCat.{0}) (n : ℕ) (x : ↥(Cgrp A n)) :
    chainMap (𝟙 A) n x = x := by
  have h : sChainMap (𝟙 A) = 𝟙 (SC A) := CategoryTheory.Functor.map_id _ _
  have h2 := congrArg (fun ψ : SC A ⟶ SC A => ψ.f n) h
  have h3 : chainMap (𝟙 A) n = 𝟙 (Cgrp A n) := h2
  rw [h3, ModuleCat.id_apply]

/-- Bounding pushes forward along any continuous map. -/
lemma bounds_map {A B : TopCat.{0}} (f : A ⟶ B) (z : ↥(Cgrp A 1))
    (h : ∃ w, z = bnd A 1 w) : ∃ w, chainMap f 1 z = bnd B 1 w := by
  obtain ⟨w, hw⟩ := h
  exact ⟨chainMap f 2 w, by rw [hw, chainMap_bnd f 1 w]⟩

/-- Bounding pulls back along a retraction (in particular a homeomorphism). -/
lemma bounds_of_retract {A B : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) (z : ↥(Cgrp A 1))
    (h : ∃ w, chainMap f 1 z = bnd B 1 w) : ∃ w, z = bnd A 1 w := by
  obtain ⟨w, hw⟩ := h
  refine ⟨chainMap g 2 w, ?_⟩
  calc z = chainMap (𝟙 A) 1 z := (chainMap_id A 1 z).symm
    _ = chainMap g 1 (chainMap f 1 z) := by rw [chainMap_chainMap, hfg]
    _ = chainMap g 1 (bnd B 1 w) := by rw [hw]
    _ = bnd A 1 (chainMap g 2 w) := (chainMap_bnd g 1 w).symm

/-- The degree-`1` homology class of a `1`-cycle. -/
noncomputable def cls (W : TopCat.{0}) (z : ↥(Cgrp W 1)) (hz : bnd W 0 z = 0) :
    ↥(Hgrp W 1) :=
  classOf (SC W) 0 z hz

lemma cls_eq_zero_iff (W : TopCat.{0}) (z : ↥(Cgrp W 1)) (hz : bnd W 0 z = 0) :
    cls W z hz = 0 ↔ ∃ w : ↥(Cgrp W 2), z = bnd W 1 w :=
  classOf_eq_zero_iff (SC W) 0 z hz

lemma cls_natural {A B : TopCat.{0}} (f : A ⟶ B) (z : ↥(Cgrp A 1))
    (hz : bnd A 0 z = 0) :
    HomologicalComplex.homologyMap (sChainMap f) 1 (cls A z hz) =
      cls B (chainMap f 1 z) (chainMap_cycle f z hz) :=
  classOf_natural (sChainMap f) 0 z hz (chainMap_cycle f z hz)

/-- A nonvanishing `H₁` yields a nonbounding cycle. -/
lemma exists_nonbounding {W : TopCat.{0}} (hW : ¬ IsZero (Hgrp W 1)) :
    ∃ z : ↥(Cgrp W 1), bnd W 0 z = 0 ∧ ¬ ∃ w, z = bnd W 1 w := by
  have hnz : ∃ h : ↥(Hgrp W 1), h ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hW
    haveI : Subsingleton ↥(Hgrp W 1) := ⟨fun x y => by rw [hall x, hall y]⟩
    exact ModuleCat.isZero_of_subsingleton _
  obtain ⟨h, hh⟩ := hnz
  obtain ⟨z, hz, hcl⟩ := exists_classOf (SC W) 0 h
  refine ⟨z, hz, fun hb => hh ?_⟩
  rw [← hcl]
  exact (classOf_eq_zero_iff (SC W) 0 z hz).mpr hb

/-- A vanishing `H₁` makes every cycle bound. -/
lemma bounds_of_isZero {W : TopCat.{0}} (hW : IsZero (Hgrp W 1))
    (z : ↥(Cgrp W 1)) (hz : bnd W 0 z = 0) : ∃ w, z = bnd W 1 w :=
  (cls_eq_zero_iff W z hz).mp (eq_zero_of_isZero hW _)

end TopWrappers

/-! ## Complement-space plumbing -/

section Complements

variable {W : TopCat.{0}}

/-- The inclusion of the complement of a bigger set into the complement of a
smaller one. -/
noncomputable def cInc {S T : Set ↥W} (hST : S ⊆ T) :
    TopCat.of {y : ↥W // y ∉ T} ⟶ TopCat.of {y : ↥W // y ∉ S} :=
  TopCat.ofHom ⟨fun y => ⟨y.1, fun h => y.2 (hST h)⟩,
    Continuous.subtype_mk continuous_subtype_val _⟩

/-- The complement subtype's inclusion into the ambient space. -/
noncomputable def cVal (S : Set ↥W) : TopCat.of {y : ↥W // y ∉ S} ⟶ W :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

lemma cVal_injective (S : Set ↥W) : Function.Injective (cVal S).hom :=
  fun _ _ h => Subtype.ext h

lemma cInc_comp {S T R : Set ↥W} (h1 : T ⊆ R) (h2 : S ⊆ T) :
    cInc h1 ≫ cInc h2 = cInc (h2.trans h1) := by
  ext x
  rfl

lemma cInc_comp_cVal {S T : Set ↥W} (h : S ⊆ T) :
    cInc h ≫ cVal S = cVal T := by
  ext x
  rfl

lemma cInc_cInc_id {S T : Set ↥W} (h1 : S ⊆ T) (h2 : T ⊆ S) :
    cInc h1 ≫ cInc h2 = 𝟙 (TopCat.of {y : ↥W // y ∉ T}) := by
  ext x
  rfl

/-- A `TopCat` morphism from a homeomorphism. -/
noncomputable def homeoHom {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨e, e.continuous⟩

lemma homeoHom_comp_symm {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : homeoHom e ≫ homeoHom e.symm = 𝟙 (TopCat.of A) := by
  ext x
  exact e.symm_apply_apply x

lemma homeoHom_symm_comp {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : homeoHom e.symm ≫ homeoHom e = 𝟙 (TopCat.of B) := by
  ext x
  exact e.apply_symm_apply x

/-! ### Simplex pushing and lifting between complement subtypes -/

/-- The ambient simplex underlying a simplex of a complement subtype. -/
noncomputable def cPush {S : Set ↥W} {n : ℕ}
    (s : Idx (TopCat.of {y : ↥W // y ∉ S}) n) : Idx W n :=
  (TopCat.toSSet.map (cVal S)).app (op ⦋n⦌) s

lemma range_cPush {S : Set ↥W} {n : ℕ} (s : Idx (TopCat.of {y : ↥W // y ∉ S}) n) :
    ∀ x ∈ Set.range ⇑(simplexEquiv W n (cPush s)), x ∉ S := by
  intro x hx
  unfold cPush at hx
  rw [simplexEquiv_map, ContinuousMap.coe_comp] at hx
  obtain ⟨t, ht⟩ := hx
  rw [← ht]
  exact ((simplexEquiv (TopCat.of {y : ↥W // y ∉ S}) n s) t).2

/-- Lifting an ambient simplex avoiding `T` into the complement subtype. -/
noncomputable def cLift (T : Set ↥W) {n : ℕ} (s : Idx W n)
    (h : ∀ x ∈ Set.range ⇑(simplexEquiv W n s), x ∉ T) :
    Idx (TopCat.of {y : ↥W // y ∉ T}) n :=
  (simplexEquiv (TopCat.of {y : ↥W // y ∉ T}) n).symm
    ⟨fun t => ⟨simplexEquiv W n s t, h _ ⟨t, rfl⟩⟩,
      (map_continuous (simplexEquiv W n s)).subtype_mk _⟩

lemma cPush_cLift (T : Set ↥W) {n : ℕ} (s : Idx W n)
    (h : ∀ x ∈ Set.range ⇑(simplexEquiv W n s), x ∉ T) :
    cPush (cLift T s h) = s := by
  apply (simplexEquiv W n).injective
  unfold cPush cLift
  rw [simplexEquiv_map, Equiv.apply_symm_apply]
  ext t
  rfl

lemma chainMap_cVal_unitOf {S : Set ↥W} {n : ℕ}
    (s : Idx (TopCat.of {y : ↥W // y ∉ S}) n) :
    chainMap (cVal S) n (unitOf s) = unitOf (cPush s) :=
  chainMap_unitOf _ s

/-- **Compact-support lifting.** A chain of the complement of `S` whose
support avoids `T` (in the ambient space) comes from a chain of the
complement of `T`, up to the common ambient pushforward. -/
lemma exists_chain_lift {S T : Set ↥W} {n : ℕ}
    (c : ↥(Cgrp (TopCat.of {y : ↥W // y ∉ S}) n))
    (h : ∀ s ∈ suppOf c, ∀ x ∈ Set.range ⇑(simplexEquiv W n (cPush s)), x ∉ T) :
    ∃ c' : ↥(Cgrp (TopCat.of {y : ↥W // y ∉ T}) n),
      chainMap (cVal T) n c' = chainMap (cVal S) n c := by
  refine ⟨∑ i ∈ (suppOf c).attach,
    coordAt i.1 c • unitOf (cLift T (cPush i.1) (h i.1 i.2)), ?_⟩
  have hterm : ∀ i ∈ (suppOf c).attach,
      chainMap (cVal T) n (coordAt i.1 c • unitOf (cLift T (cPush i.1) (h i.1 i.2))) =
        coordAt i.1 c • unitOf (cPush i.1) := by
    intro i _
    rw [mapSmul, chainMap_cVal_unitOf, cPush_cLift]
  have hc : chainMap (cVal S) n c = ∑ i ∈ suppOf c, coordAt i c • unitOf (cPush i) := by
    conv_lhs => rw [sum_coordAt_smul_unitOf c]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [mapSmul, chainMap_cVal_unitOf]
  calc chainMap (cVal T) n (∑ i ∈ (suppOf c).attach,
        coordAt i.1 c • unitOf (cLift T (cPush i.1) (h i.1 i.2)))
      = ∑ i ∈ (suppOf c).attach, coordAt i.1 c • unitOf (cPush i.1) := by
        rw [map_sum]
        exact Finset.sum_congr rfl hterm
    _ = ∑ i ∈ suppOf c, coordAt i c • unitOf (cPush i) :=
        Finset.sum_attach (suppOf c) (fun i => coordAt i c • unitOf (cPush i))
    _ = chainMap (cVal S) n c := hc.symm

end Complements

/-! ## The elementwise Mayer-Vietoris bisection step -/

section MVStep

/-- **Elementwise MV injectivity at `H₁(U ∩ V)`.** With `H₂(X) = 0`, a
1-cycle of `U ∩ V` whose pushforwards bound in `U` and in `V` bounds in
`U ∩ V`. -/
theorem bounds_of_mv {X : TopCat.{0}} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (hX2 : IsZero (Hgrp X 2))
    (z : ↥(Cgrp (TopCat.of (U ∩ V : Set X)) 1))
    (hz : bnd (TopCat.of (U ∩ V : Set X)) 0 z = 0)
    (hzU : ∃ w, chainMap (mvInclU U V) 1 z = bnd (TopCat.of U) 1 w)
    (hzV : ∃ w, chainMap (mvInclV U V) 1 z = bnd (TopCat.of V) 1 w) :
    ∃ w, z = bnd (TopCat.of (U ∩ V : Set X)) 1 w := by
  rw [← cls_eq_zero_iff (TopCat.of (U ∩ V : Set X)) z hz]
  have hU0 : cls (TopCat.of U) (chainMap (mvInclU U V) 1 z)
      (chainMap_cycle (mvInclU U V) z hz) = 0 :=
    (cls_eq_zero_iff _ _ _).mpr hzU
  have hV0 : cls (TopCat.of V) (chainMap (mvInclV U V) 1 z)
      (chainMap_cycle (mvInclV U V) z hz) = 0 :=
    (cls_eq_zero_iff _ _ _).mpr hzV
  have hfst : (biprod.fst : Hgrp (TopCat.of U) 1 ⊞ Hgrp (TopCat.of V) 1 ⟶ _)
      (mvPair U V 1 (cls (TopCat.of (U ∩ V : Set X)) z hz)) = 0 := by
    have h1 : mvPair U V 1 ≫
        (biprod.fst : Hgrp (TopCat.of U) 1 ⊞ Hgrp (TopCat.of V) 1 ⟶ _) =
        HomologicalComplex.homologyMap (sChainMap (mvInclU U V)) 1 :=
      biprod.lift_fst _ _
    rw [← ModuleCat.comp_apply, h1, cls_natural (mvInclU U V) z hz, hU0]
  have hsnd : (biprod.snd : Hgrp (TopCat.of U) 1 ⊞ Hgrp (TopCat.of V) 1 ⟶ _)
      (mvPair U V 1 (cls (TopCat.of (U ∩ V : Set X)) z hz)) = 0 := by
    have h1 : mvPair U V 1 ≫
        (biprod.snd : Hgrp (TopCat.of U) 1 ⊞ Hgrp (TopCat.of V) 1 ⟶ _) =
        -(HomologicalComplex.homologyMap (sChainMap (mvInclV U V)) 1) :=
      biprod.lift_snd _ _
    rw [← ModuleCat.comp_apply, h1, negApp, cls_natural (mvInclV U V) z hz,
      hV0, neg_zero]
  have hpair : mvPair U V 1 (cls (TopCat.of (U ∩ V : Set X)) z hz) = 0 := by
    apply biprod_elem_ext
    · rw [hfst]
      exact (map_zero _).symm
    · rw [hsnd]
      exact (map_zero _).symm
  have hex := mv_exact₁ hU hV hUV 1
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨y, hy⟩ := hex (cls (TopCat.of (U ∩ V : Set X)) z hz) hpair
  rw [← hy, eq_zero_of_isZero hX2 y, map_zero]

/-- The homeomorphism from the union complement to the Mayer-Vietoris
intersection inside the complement of `KP ∩ KM`. -/
noncomputable def unionComplHomeo {W : TopCat.{0}} (KP KM : Set ↥W) :
    {y : ↥W // y ∉ KP ∪ KM} ≃ₜ
      ↥(({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} ∩
        {x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM} :
          Set ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)))) where
  toFun y := ⟨⟨y.1, fun h => y.2 (Set.mem_union_left _ h.1)⟩,
    fun h => y.2 (Set.mem_union_left _ h),
    fun h => y.2 (Set.mem_union_right _ h)⟩
  invFun x := ⟨x.1.1, fun h => h.elim (fun hP => x.2.1 hP) (fun hM => x.2.2 hM)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- **The bisection step** (elementwise two-arc Mayer-Vietoris): a 1-cycle
of the complement of `KU = KP ∪ KM` whose pushforwards bound in the
complements of both halves bounds already, provided `H₂((KP ∩ KM)ᶜ) = 0`. -/
theorem bounds_of_halves {W : TopCat.{0}} {KP KM KU : Set ↥W}
    (hKPc : IsClosed KP) (hKMc : IsClosed KM) (hunion : KU = KP ∪ KM)
    (hX2 : IsZero (Hgrp (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) 2))
    (z : ↥(Cgrp (TopCat.of {y : ↥W // y ∉ KU}) 1))
    (hz : bnd (TopCat.of {y : ↥W // y ∉ KU}) 0 z = 0)
    (hPU : KP ⊆ KU) (hMU : KM ⊆ KU)
    (hP : ∃ w, chainMap (cInc hPU) 1 z = bnd (TopCat.of {y : ↥W // y ∉ KP}) 1 w)
    (hM : ∃ w, chainMap (cInc hMU) 1 z = bnd (TopCat.of {y : ↥W // y ∉ KM}) 1 w) :
    ∃ w, z = bnd (TopCat.of {y : ↥W // y ∉ KU}) 1 w := by
  subst hunion
  -- the MV cover of the midpoint complement by the two half complements
  have hUopen : IsOpen
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W))) :=
    hKPc.isOpen_compl.preimage continuous_subtype_val
  have hVopen : IsOpen
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W))) :=
    hKMc.isOpen_compl.preimage continuous_subtype_val
  have hUVcover :
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W))) ∪
      {x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hxP : x.1 ∈ KP
    · right
      intro hxM
      exact x.2 ⟨hxP, hxM⟩
    · left
      exact hxP
  set e := unionComplHomeo KP KM with hedef
  set z' := chainMap (homeoHom e) 1 z with hz'def
  have hz'c : bnd _ 0 z' = 0 := chainMap_cycle _ z hz
  -- backward transfer of bounding, U side
  have hU_bounds : ∃ w, chainMap (mvInclU
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP})
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM}) : _) 1 z' =
      bnd (TopCat.of ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)))) 1 w := by
    set fP := flattenComplHomeo (W := W) (KP ∩ KM) KP Set.inter_subset_left with hfP
    apply bounds_of_retract (homeoHom fP) (homeoHom fP.symm) (homeoHom_comp_symm fP)
    have hcommP : homeoHom e ≫ mvInclU _ _ ≫ homeoHom fP = cInc hPU := by
      ext x
      rfl
    have heq : chainMap (homeoHom fP) 1 (chainMap (mvInclU _ _) 1 z') =
        chainMap (cInc hPU) 1 z := by
      rw [hz'def, chainMap_chainMap, chainMap_chainMap, hcommP]
    rw [heq]
    exact hP
  -- backward transfer of bounding, V side
  have hV_bounds : ∃ w, chainMap (mvInclV
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP})
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM}) : _) 1 z' =
      bnd (TopCat.of ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)))) 1 w := by
    set fM := flattenComplHomeo (W := W) (KP ∩ KM) KM Set.inter_subset_right with hfM
    apply bounds_of_retract (homeoHom fM) (homeoHom fM.symm) (homeoHom_comp_symm fM)
    have hcommM : homeoHom e ≫ mvInclV _ _ ≫ homeoHom fM = cInc hMU := by
      ext x
      rfl
    have heq : chainMap (homeoHom fM) 1 (chainMap (mvInclV _ _) 1 z') =
        chainMap (cInc hMU) 1 z := by
      rw [hz'def, chainMap_chainMap, chainMap_chainMap, hcommM]
    rw [heq]
    exact hM
  have hmid := bounds_of_mv hUopen hVopen hUVcover hX2 z' hz'c hU_bounds hV_bounds
  exact bounds_of_retract (homeoHom e) (homeoHom e.symm) (homeoHom_comp_symm e) z hmid

end MVStep

/-! ## The geometric bisection on an embedded arc -/

section Geometry

variable {D : ℕ} (a : C(unitInterval, ↥(Sph D)))

/-- The image of the parameter subinterval `[u, v]` under the arc. -/
noncomputable def seg (u v : ℝ) : Set ↥(Sph D) :=
  ⇑a '' {q : unitInterval | u ≤ (q : ℝ) ∧ (q : ℝ) ≤ v}

lemma seg_subset_range (u v : ℝ) : seg a u v ⊆ Set.range ⇑a :=
  Set.image_subset_range _ _

lemma range_subset_seg : Set.range ⇑a ⊆ seg a 0 1 := by
  rintro _ ⟨q, rfl⟩
  exact ⟨q, ⟨q.2.1, q.2.2⟩, rfl⟩

lemma seg_mono {u v u' v' : ℝ} (hu : u' ≤ u) (hv : v ≤ v') :
    seg a u v ⊆ seg a u' v' := by
  rintro _ ⟨q, ⟨h1, h2⟩, rfl⟩
  exact ⟨q, ⟨hu.trans h1, h2.trans hv⟩, rfl⟩

lemma isCompact_seg (u v : ℝ) : IsCompact (seg a u v) := by
  apply IsCompact.image _ (map_continuous a)
  have hcl : IsClosed {q : unitInterval | u ≤ (q : ℝ) ∧ (q : ℝ) ≤ v} := by
    have h : {q : unitInterval | u ≤ (q : ℝ) ∧ (q : ℝ) ≤ v} =
        (fun q : unitInterval => (q : ℝ)) ⁻¹' (Set.Icc u v) := rfl
    rw [h]
    exact isClosed_Icc.preimage continuous_subtype_val
  exact hcl.isCompact

lemma isClosed_seg (u v : ℝ) : IsClosed (seg a u v) := by
  haveI : T2Space ↥(Sph D) :=
    inferInstanceAs (T2Space (sphere (0 : Esp D) 1))
  exact (isCompact_seg a u v).isClosed

lemma seg_union {u v m : ℝ} (h1 : u ≤ m) (h2 : m ≤ v) :
    seg a u v = seg a u m ∪ seg a m v := by
  unfold seg
  rw [← Set.image_union]
  congr 1
  ext q
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h3, h4⟩
    rcases le_total (q : ℝ) m with h5 | h5
    · exact Or.inl ⟨h3, h5⟩
    · exact Or.inr ⟨h5, h4⟩
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩)
    · exact ⟨h3, h4.trans h2⟩
    · exact ⟨h1.trans h3, h4⟩

lemma seg_inter (hinj : Function.Injective ⇑a) {u v m : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (h1 : u ≤ m) (h2 : m ≤ v) :
    seg a u m ∩ seg a m v = {a ⟨m, hm0, hm1⟩} := by
  unfold seg
  rw [← Set.image_inter hinj]
  have hq : {q : unitInterval | u ≤ (q : ℝ) ∧ (q : ℝ) ≤ m} ∩
      {q : unitInterval | m ≤ (q : ℝ) ∧ (q : ℝ) ≤ v} =
      {(⟨m, hm0, hm1⟩ : unitInterval)} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, h4⟩, ⟨h5, _⟩⟩
      exact Subtype.ext (le_antisymm h4 h5)
    · rintro rfl
      exact ⟨⟨h1, le_refl m⟩, ⟨le_refl m, h2⟩⟩
  rw [hq, Set.image_singleton]

variable (z : ↥(Cgrp (TopCat.of {y : ↥(Sph D) // y ∉ Set.range ⇑a}) 1))

/-- The pushforward of the reference cycle into the complement of
`a([u, v])`. -/
noncomputable def zSeg (u v : ℝ) :
    ↥(Cgrp (TopCat.of {y : ↥(Sph D) // y ∉ seg a u v}) 1) :=
  chainMap (cInc (seg_subset_range a u v)) 1 z

/-- The bisection invariant: `[u, v] ⊆ [0, 1]` and the pushforward of the
reference cycle into the complement of `a([u, v])` is not a boundary. -/
def Bad (u v : ℝ) : Prop :=
  0 ≤ u ∧ v ≤ 1 ∧ u ≤ v ∧
    ¬ ∃ w, zSeg a z u v = bnd (TopCat.of {y : ↥(Sph D) // y ∉ seg a u v}) 1 w

lemma zSeg_cycle (hz : bnd (TopCat.of {y : ↥(Sph D) // y ∉ Set.range ⇑a}) 0 z = 0)
    (u v : ℝ) :
    bnd (TopCat.of {y : ↥(Sph D) // y ∉ seg a u v}) 0 (zSeg a z u v) = 0 :=
  chainMap_cycle _ z hz

/-- Restriction of the pushforward to a smaller parameter interval. -/
lemma zSeg_restrict {u v u' v' : ℝ}
    (hseg : seg a u' v' ⊆ seg a u v) :
    chainMap (cInc hseg) 1 (zSeg a z u v) = zSeg a z u' v' := by
  unfold zSeg
  rw [chainMap_chainMap, cInc_comp]

/-- **The bisection step**: a bad interval has a bad half. -/
lemma bad_step (hinj : Function.Injective ⇑a)
    (hz : bnd (TopCat.of {y : ↥(Sph D) // y ∉ Set.range ⇑a}) 0 z = 0)
    {u v : ℝ} (h : Bad a z u v) :
    ∃ q : ℝ × ℝ, Bad a z q.1 q.2 ∧ u ≤ q.1 ∧ q.2 ≤ v ∧
      q.2 - q.1 = (v - u) / 2 := by
  obtain ⟨hu0, hv1, huv, hnb⟩ := h
  set m := (u + v) / 2 with hm
  have hum : u ≤ m := by rw [hm]; linarith
  have hmv : m ≤ v := by rw [hm]; linarith
  have hm0 : 0 ≤ m := hu0.trans hum
  have hm1 : m ≤ 1 := hmv.trans hv1
  by_cases hb1 : Bad a z u m
  · exact ⟨(u, m), hb1, le_refl u, hmv, by rw [hm]; ring⟩
  · refine ⟨(m, v), ⟨hm0, hv1, hmv, ?_⟩, hum, le_refl v, by rw [hm]; ring⟩
    intro hb2
    -- both halves bound: assemble the MV contradiction
    have hb1' : ∃ w, zSeg a z u m =
        bnd (TopCat.of {y : ↥(Sph D) // y ∉ seg a u m}) 1 w := by
      by_contra hb1''
      exact hb1 ⟨hu0, hm1, hum, hb1''⟩
    apply hnb
    -- H₂ of the midpoint complement vanishes (punctured sphere contractible)
    have hinter : seg a u m ∩ seg a m v = {a ⟨m, hm0, hm1⟩} :=
      seg_inter a hinj hm0 hm1 hum hmv
    haveI hcontr : ContractibleSpace
        ↥((({a ⟨m, hm0, hm1⟩} : Set ↥(Sph D))ᶜ : Set ↥(Sph D))) :=
      contractibleSpace_compl_singleton_sphere (a ⟨m, hm0, hm1⟩)
    have hX2 : IsZero (Hgrp (TopCat.of
        ((seg a u m ∩ seg a m v)ᶜ : Set ↥(Sph D))) 2) := by
      rw [hinter]
      exact isZero_homology_of_contractible _ (by norm_num)
    -- run the two-arc MV step
    have hPU : seg a u m ⊆ seg a u v := seg_mono a (le_refl u) hmv
    have hMU : seg a m v ⊆ seg a u v := seg_mono a hum (le_refl v)
    refine bounds_of_halves (isClosed_seg a u m) (isClosed_seg a m v)
      (seg_union a hum hmv) hX2 (zSeg a z u v) (zSeg_cycle a z hz u v)
      hPU hMU ?_ ?_
    · rw [zSeg_restrict a z hPU]
      exact hb1'
    · rw [zSeg_restrict a z hMU]
      exact hb2

/-- The nested bad-interval sequence, carrying its invariant. -/
noncomputable def badSeq (hinj : Function.Injective ⇑a)
    (hz : bnd (TopCat.of {y : ↥(Sph D) // y ∉ Set.range ⇑a}) 0 z = 0)
    (h0 : Bad a z 0 1) : ℕ → {p : ℝ × ℝ // Bad a z p.1 p.2}
  | 0 => ⟨(0, 1), h0⟩
  | (k + 1) =>
      ⟨(bad_step a z hinj hz (badSeq hinj hz h0 k).2).choose,
        (bad_step a z hinj hz (badSeq hinj hz h0 k).2).choose_spec.1⟩

variable (hinj : Function.Injective ⇑a)
  (hz : bnd (TopCat.of {y : ↥(Sph D) // y ∉ Set.range ⇑a}) 0 z = 0)
  (h0 : Bad a z 0 1)

lemma badSeq_zero : (badSeq a z hinj hz h0 0).1 = (0, 1) := rfl

lemma badSeq_succ (k : ℕ) :
    (badSeq a z hinj hz h0 k).1.1 ≤ (badSeq a z hinj hz h0 (k + 1)).1.1 ∧
    (badSeq a z hinj hz h0 (k + 1)).1.2 ≤ (badSeq a z hinj hz h0 k).1.2 ∧
    (badSeq a z hinj hz h0 (k + 1)).1.2 - (badSeq a z hinj hz h0 (k + 1)).1.1 =
      ((badSeq a z hinj hz h0 k).1.2 - (badSeq a z hinj hz h0 k).1.1) / 2 := by
  have hspec := (bad_step a z hinj hz (badSeq a z hinj hz h0 k).2).choose_spec
  exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩

lemma badSeq_width (k : ℕ) :
    (badSeq a z hinj hz h0 k).1.2 - (badSeq a z hinj hz h0 k).1.1 =
      (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      rw [badSeq_zero]
      norm_num
  | succ k IH =>
      rw [(badSeq_succ a z hinj hz h0 k).2.2, IH]
      ring

lemma badSeq_mono : Monotone (fun k => (badSeq a z hinj hz h0 k).1.1) :=
  monotone_nat_of_le_succ fun k => (badSeq_succ a z hinj hz h0 k).1

lemma badSeq_anti : Antitone (fun k => (badSeq a z hinj hz h0 k).1.2) :=
  antitone_nat_of_succ_le fun k => (badSeq_succ a z hinj hz h0 k).2.1

lemma badSeq_le (j k : ℕ) :
    (badSeq a z hinj hz h0 j).1.1 ≤ (badSeq a z hinj hz h0 k).1.2 := by
  rcases le_total j k with h | h
  · exact (badSeq_mono a z hinj hz h0 h).trans
      (badSeq a z hinj hz h0 k).2.2.2.1
  · exact ((badSeq a z hinj hz h0 j).2.2.2.1).trans
      (badSeq_anti a z hinj hz h0 h)

/-- The interval endpoints of a bad interval, extracted with names (the
`Bad` conjunction, destructured once for reuse). -/
lemma badSeq_props (k : ℕ) :
    0 ≤ (badSeq a z hinj hz h0 k).1.1 ∧ (badSeq a z hinj hz h0 k).1.2 ≤ 1 ∧
      (badSeq a z hinj hz h0 k).1.1 ≤ (badSeq a z hinj hz h0 k).1.2 :=
  ⟨(badSeq a z hinj hz h0 k).2.1, (badSeq a z hinj hz h0 k).2.2.1,
    (badSeq a z hinj hz h0 k).2.2.2.1⟩

end Geometry

/-! ## The main theorem -/

/-- **Arc-complement acyclicity** (Hatcher 2B.1, arc case, formal):
every topological embedding of the unit interval into `S^D` has
`H₁`-acyclic complement, in every dimension `D`. -/
theorem arcComplementsAcyclic (D : ℕ) :
    LinkingVanishingHighDim.ArcComplementsAcyclic D := by
  intro a hemb
  by_contra hH
  haveI : T2Space ↥(Sph D) :=
    inferInstanceAs (T2Space (sphere (0 : Esp D) 1))
  obtain ⟨z, hz, hznb⟩ := exists_nonbounding hH
  have hinj : Function.Injective ⇑a := hemb.injective
  -- the initial bad interval
  have h0 : Bad a z 0 1 := by
    refine ⟨le_refl 0, le_refl 1, zero_le_one, ?_⟩
    intro hb
    apply hznb
    refine bounds_of_retract (cInc (seg_subset_range a 0 1))
      (cInc (range_subset_seg a)) (cInc_cInc_id _ _) z ?_
    exact hb
  -- the nested bad intervals and their limit point
  set s : ℕ → ℝ := fun k => (badSeq a z hinj hz h0 k).1.1 with hs
  set t : ℕ → ℝ := fun k => (badSeq a z hinj hz h0 k).1.2 with ht
  have hbdd : BddAbove (Set.range s) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact ((badSeq a z hinj hz h0 k).2.2.2.1).trans (badSeq a z hinj hz h0 k).2.2.1
  set tstar : ℝ := ⨆ k, s k with htstar
  have hst : ∀ k, s k ≤ tstar := fun k => le_ciSup hbdd k
  have hts : ∀ k, tstar ≤ t k := fun k =>
    ciSup_le fun j => badSeq_le a z hinj hz h0 j k
  have h0t : (0 : ℝ) ≤ tstar := by
    have h := hst 0
    rw [show s 0 = 0 from congrArg Prod.fst (badSeq_zero a z hinj hz h0)] at h
    exact h
  have ht1 : tstar ≤ 1 := by
    have h := hts 0
    rw [show t 0 = 1 from congrArg Prod.snd (badSeq_zero a z hinj hz h0)] at h
    exact h
  set tI : unitInterval := ⟨tstar, h0t, ht1⟩ with htI
  set p : ↥(Sph D) := a tI with hp
  -- the point complement is contractible, so the pushforward bounds there
  have hpr : ({p} : Set ↥(Sph D)) ⊆ Set.range ⇑a := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨tI, hx.symm⟩
  haveI hcontr : ContractibleSpace
      ↥((({p} : Set ↥(Sph D))ᶜ : Set ↥(Sph D))) :=
    contractibleSpace_compl_singleton_sphere p
  have hzero : IsZero (Hgrp (TopCat.of
      {y : ↥(Sph D) // y ∉ ({p} : Set ↥(Sph D))}) 1) := by
    have h := isZero_homology_of_contractible
      (TopCat.of ((({p} : Set ↥(Sph D))ᶜ : Set ↥(Sph D)))) one_ne_zero
    exact h
  obtain ⟨w, hw⟩ := bounds_of_isZero hzero (chainMap (cInc hpr) 1 z)
    (chainMap_cycle _ z hz)
  -- the compact support of the bounding chain misses `a(t*)`
  set Kc : Set ↥(Sph D) :=
    ⋃ i ∈ suppOf w, Set.range ⇑(simplexEquiv (Sph D) 2 (cPush i)) with hKc
  have hKc_compact : IsCompact Kc := by
    rw [hKc]
    exact (suppOf w).isCompact_biUnion fun i _ => isCompact_range (map_continuous _)
  have hKc_closed : IsClosed Kc := hKc_compact.isClosed
  have hKc_avoids : ∀ x ∈ Kc, x ∉ ({p} : Set ↥(Sph D)) := by
    intro x hx
    rw [hKc, Set.mem_iUnion₂] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact range_cPush i x hxi
  -- an ε-neighbourhood of `t*` avoids the support
  have hA_closed : IsClosed (⇑a ⁻¹' Kc) := hKc_closed.preimage (map_continuous a)
  have htA : tI ∈ (⇑a ⁻¹' Kc)ᶜ := by
    intro hmem
    exact hKc_avoids (a tI) hmem (by rw [hp]; exact Set.mem_singleton _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA_closed.isOpen_compl tI htA
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  -- the k-th interval's arc image avoids the support
  have hclaim : ∀ x ∈ seg a (s k) (t k), x ∉ Kc := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩ hxK
    have hqball : q ∈ Metric.ball tI ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have hwidth : t k - s k = (1 / 2 : ℝ) ^ k := badSeq_width a z hinj hz h0 k
      have h1 : s k ≤ tstar := hst k
      have h2 : tstar ≤ t k := hts k
      have habs : |(q : ℝ) - tstar| ≤ (1 / 2 : ℝ) ^ k := by
        rw [abs_le]
        constructor
        · linarith
        · linarith
      show |(q : ℝ) - tstar| < ε
      exact lt_of_le_of_lt habs hk
    exact hball hqball hxK
  -- lift the bounding chain below the k-th arc complement
  obtain ⟨w', hw'⟩ := exists_chain_lift (S := ({p} : Set ↥(Sph D)))
    (T := seg a (s k) (t k)) w
    (fun i hi x hx hxT => hclaim x hxT (Set.mem_biUnion hi hx))
  -- contradiction with the k-th bad interval
  apply (badSeq a z hinj hz h0 k).2.2.2.2
  refine ⟨w', ?_⟩
  apply chainMap_injective (cVal (seg a (s k) (t k))) (cVal_injective _) 1
  have hL : chainMap (cVal (seg a (s k) (t k))) 1 (zSeg a z (s k) (t k)) =
      chainMap (cVal (Set.range ⇑a)) 1 z := by
    unfold zSeg
    rw [chainMap_chainMap, cInc_comp_cVal]
  have hR : chainMap (cVal (seg a (s k) (t k))) 1
      (bnd (TopCat.of {y : ↥(Sph D) // y ∉ seg a (s k) (t k)}) 1 w') =
      chainMap (cVal (Set.range ⇑a)) 1 z := by
    rw [← chainMap_bnd (cVal (seg a (s k) (t k))) 1 w', hw',
      chainMap_bnd (cVal ({p} : Set ↥(Sph D))) 1 w, ← hw,
      chainMap_chainMap, cInc_comp_cVal]
  rw [hL, hR]

end ArcComplementAcyclic
end Foundation
end IndisputableMonolith
