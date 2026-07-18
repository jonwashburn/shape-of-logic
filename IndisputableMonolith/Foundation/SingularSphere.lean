/-
Sphere homology `H_*(Sⁿ; ℤ)` by Mayer-Vietoris induction.

Layer 5 of the excision spine (layer 1: `SingularPrism`, homotopy invariance;
layer 2: `SingularPair`, the LES of a pair; layer 3: `SingularSubdivision`,
barycentric subdivision; layer 4: `SingularMayerVietoris`, the MV long exact
sequence).

## Contents (staged)

* Stage A/B: homology of points and contractible spaces.  Mathlib already
  computes the singular homology of totally disconnected spaces
  (`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`), which
  covers both the one-point space and `S⁰`; combining with layer 1's
  homotopy invariance gives `IsZero (H_m X)` for contractible `X`, `m ≠ 0`
  (`isZero_homology_of_contractible`).  For `H₀` we build the augmentation
  apparatus: the class of a point (`ptH`), the augmentation against a
  clopen set (`augH`), their pairing (`ptH_augH`), homotopy invariance of
  the point class (`ptH_eq_of_joined`), and the computation
  `IsIso (augH X univ)` for path-connected `X`
  (`isIso_augH_of_pathConnected`), via layer 4's concrete homology-map
  criterion.
* Stage A/B exports: `h0_iso_int` (`H₀(X) ≅ ℤ`, path-connected `X`),
  `h0_pt_iso_int`, `hn_pt_isZero`, `h0_contractible_iso_int`.
* Stage C (abstract half, DONE): the Mayer-Vietoris consequences over
  layer 4, for any open cover `U ∪ V = univ`:
  - `isIso_mvδ` / `isIso_mvδ_of_contractible`: the suspension step,
    `∂ : H_{n+2}(X) ≅ H_{n+1}(U ∩ V)` when `U, V` have vanishing homology
    there (e.g. contractible);
  - `isZero_of_isZero_inter`: vanishing transported across `∂`;
  - `mono_mvPair_zero`: the degree-0 pair map is mono when `U ∩ V` is
    path connected (split by the augmentation);
  - `isZero_h1` / `isZero_h1_of_contractible`: `H₁(X) = 0` when `U, V`
    kill `H₁` and `U ∩ V` is path connected.

## FRONTIER (for the next worker; everything above builds green, 0 sorry)

Stage C (geometric half) and Stage D remain.  Recommended decomposition:

1. Sphere model: `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` as
   `TopCat.of`.  `U := {x | x ≠ south}`, `V := {x | x ≠ north}` are open
   (complement of a singleton in a T1 space) and cover.
2. `ContractibleSpace ↥U`: `Mathlib.Geometry.Manifold.Instances.Sphere`
   has `stereographic` (a `PartialHomeomorph` from the sphere with source
   `{pole}ᶜ` onto the orthogonal complement); extract a `Homeomorph` from
   `↥U` to a normed space via `PartialHomeomorph.toHomeomorphSourceTarget`
   (mind the subtype-of-subtype plumbing: `↥U` here is a subtype of the
   sphere subtype), then `Homeomorph.contractibleSpace` against the convex
   target (`Convex.contractibleSpace` is imported).
3. `U ∩ V ≃ₕ Sⁿ⁻¹` (homotopy equivalence): the retraction normalizes the
   first `n` coordinates; away from both poles the horizontal component is
   nonzero, so the map is continuous; the straight-line homotopy stays in
   `U ∩ V` after renormalization.  This is the one genuinely geometric
   proof.  Combine with layer 1's `homotopyEquiv_homology_iso` to move
   `Hgrp` across, then feed `isIso_mvδ_of_contractible` /
   `isZero_h1_of_contractible` to run the induction
   `H_{k+1}(Sⁿ) ≅ H_k(Sⁿ⁻¹)` (`k ≥ 1`) with `H₁(Sⁿ) = 0` for `n ≥ 2`.
4. `H₁(S¹) ≅ ℤ`: the degree-0 end.  Use `mv_exact₂` at degree 0,
   `mvSum_epi_zero`, `mono_mvPair_zero`-style splitting, and the `H₀`
   computations (this file's `augH`/`ptH` toolkit: `ptH_augH` pairs point
   classes against clopen augmentations, `ptH_eq_of_joined` merges joined
   points; for `U ∩ V ≃ₕ S⁰`, two components give `H₀ ≅ ℤ ⊕ ℤ` via the
   two clopen augmentations).  Alternatively settle for
   `¬ IsZero (H₁(S¹))` (enough for Stage D's corollary) by showing `mvδ 0`
   is nonzero: the class `ptH a − ptH b` of the two-point difference in
   `H₀(U ∩ V)` is in `ker (mvPair 0)` (the points join inside `U` and
   inside `V`) but nonzero (pair against a clopen augmentation separating
   the two arcs, using `ptH_augH`); exactness (`mv_exact₁`) lifts it
   through `mvδ`.
5. Stage D: `sphere_homology_top` (`H_n(Sⁿ) ≠ 0`, i.e. `¬ IsZero`; the
   `≅ ℤ` form needs the iso carried through the induction, harder),
   `sphere_homology_vanish` (`IsZero (H_k(Sⁿ))`, `k ≠ 0, n`), and
   `spheres_not_homotopy_equivalent` via layer 1's
   `homotopyEquiv_homology_iso` (transport `IsZero` across the iso and
   contradict).  `S⁰` base: totally disconnected, so
   `isZero_homology_of_totallyDisconnected` gives all positive degrees.

## Instance-diamond note (load-bearing, inherited from layer 4)

For `R = ℤ` every `ModuleCat ℤ` carrier has two `Module ℤ` instances
(`isModule` and `AddCommGroup.toIntModule`), propositionally but not
definitionally equal, and synthesis prefers the generic one.  This file
deprioritizes `AddCommGroup.toIntModule` and `SubNegMonoid.toZSMul`
locally, matching layers 1-4.
-/
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere
import IndisputableMonolith.Foundation.SingularPrism
import IndisputableMonolith.Foundation.SingularPair
import IndisputableMonolith.Foundation.SingularSubdivision
import IndisputableMonolith.Foundation.SingularMayerVietoris

namespace IndisputableMonolith
namespace Foundation
namespace SingularSphere

open CategoryTheory Category Limits AlgebraicTopology Simplicial Opposite
open SingularPrism SingularSubdivision SingularMayerVietoris

attribute [local instance 10] Classical.decEq

/- See the instance-diamond note in the module header. -/
attribute [local instance 0] AddCommGroup.toIntModule
attribute [local instance 0] SubNegMonoid.toZSMul

/-! ## Stage A toolkit: points, augmentations, and the class of a point -/

/-- The degree-`n` singular homology of `X` with `ℤ` coefficients. -/
noncomputable abbrev Hgrp (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  (SC X).homology n

/-- `ℤ` as a chain complex concentrated in degree `0`. -/
noncomputable abbrev Zsingle : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)

/-- The unique point of the standard `0`-simplex. -/
noncomputable def v0 : stdSimplex ℝ (Fin 1) :=
  ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩

instance : Subsingleton (stdSimplex ℝ (Fin (0 + 1))) :=
  ⟨fun a b => Subtype.ext (funext fun i => by
    have ha : a.1 0 = 1 := by
      have h2 := a.2.2
      rw [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
        add_zero] at h2
      exact h2
    have hb : b.1 0 = 1 := by
      have h2 := b.2.2
      rw [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
        add_zero] at h2
      exact h2
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi, ha, hb])⟩

/-- The underlying point of a singular `0`-simplex. -/
noncomputable def pointOf {X : TopCat.{0}} (s : Idx X 0) : X :=
  simplexEquiv X 0 s v0

/-- The singular `0`-simplex sitting at a point. -/
noncomputable def constSimplex (X : TopCat.{0}) (x : X) : Idx X 0 :=
  (simplexEquiv X 0).symm (ContinuousMap.const _ x)

@[simp] lemma pointOf_constSimplex (X : TopCat.{0}) (x : X) :
    pointOf (constSimplex X x) = x := by
  unfold pointOf constSimplex
  rw [Equiv.apply_symm_apply]
  rfl

/-- Singular `0`-simplices are determined by their underlying point. -/
lemma idx0_ext {X : TopCat.{0}} {s t : Idx X 0} (h : pointOf s = pointOf t) :
    s = t := by
  apply (simplexEquiv X 0).injective
  ext z
  rw [Subsingleton.elim z v0]
  exact h

lemma constSimplex_pointOf {X : TopCat.{0}} (s : Idx X 0) :
    constSimplex X (pointOf s) = s :=
  idx0_ext (by rw [pointOf_constSimplex])

/-- The point of a pushforward simplex is the image of the point. -/
lemma pointOf_map {X Y : TopCat.{0}} (f : X ⟶ Y) (s : Idx X 0) :
    pointOf ((TopCat.toSSet.map f).app (op ⦋0⦌) s) = f.hom (pointOf s) := by
  unfold pointOf
  rw [simplexEquiv_map]
  rfl

/-- The point of the `k`-th face of a singular `1`-simplex. -/
lemma pointOf_δ {X : TopCat.{0}} (σ : Idx X 1) (k : Fin 2) :
    pointOf ((TopCat.toSSet.obj X).δ k σ) =
      simplexEquiv X 1 σ (SingularPrism.face k v0) := by
  unfold pointOf
  rw [simplexEquiv_δ]
  rfl

open Classical in
/-- The partial augmentation against a set `A`: a `0`-simplex counts with
coefficient `1` when its point lies in `A` and `0` otherwise. -/
noncomputable def augFun (X : TopCat.{0}) (A : Set X) :
    Cgrp X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc fun s => if pointOf s ∈ A then 𝟙 (ModuleCat.of ℤ ℤ) else 0

open Classical in
lemma gen_augFun {X : TopCat.{0}} {A : Set X} (s : Idx X 0) :
    gen X 0 s ≫ augFun X A =
      if pointOf s ∈ A then 𝟙 (ModuleCat.of ℤ ℤ) else 0 :=
  Sigma.ι_desc _ _

open Classical in
lemma augFun_genUnit {X : TopCat.{0}} {A : Set X} (s : Idx X 0) :
    augFun X A (genUnit X 0 s) = if pointOf s ∈ A then (1 : ℤ) else 0 := by
  rw [genUnit_eq, ← ModuleCat.comp_apply, gen_augFun]
  by_cases h : pointOf s ∈ A
  · rw [if_pos h, if_pos h, ModuleCat.id_apply]
  · rw [if_neg h, if_neg h, zeroApp]

/-- Both endpoints of a singular `1`-simplex lie on the same side of a
clopen set (the image of the connected `Δ¹` cannot cross it). -/
lemma mem_iff_of_clopen_δ {X : TopCat.{0}} {A : Set X} (hA : IsClopen A)
    (σ : Idx X 1) :
    (pointOf ((TopCat.toSSet.obj X).δ (0 : Fin 2) σ) ∈ A ↔
      pointOf ((TopCat.toSSet.obj X).δ (1 : Fin 2) σ) ∈ A) := by
  rw [pointOf_δ, pointOf_δ]
  set f := simplexEquiv X 1 σ with hf
  have hS : IsClopen (⇑f ⁻¹' A) := hA.preimage f.continuous
  rcases isClopen_iff.mp hS with h | h
  · constructor
    · intro hx
      exact absurd (show SingularPrism.face (0 : Fin 2) v0 ∈ ⇑f ⁻¹' A from hx)
        (by rw [h]; exact Set.notMem_empty _)
    · intro hx
      exact absurd (show SingularPrism.face (1 : Fin 2) v0 ∈ ⇑f ⁻¹' A from hx)
        (by rw [h]; exact Set.notMem_empty _)
  · constructor
    · intro _
      have : SingularPrism.face (1 : Fin 2) v0 ∈ ⇑f ⁻¹' A := by
        rw [h]; trivial
      exact this
    · intro _
      have : SingularPrism.face (0 : Fin 2) v0 ∈ ⇑f ⁻¹' A := by
        rw [h]; trivial
      exact this

open Classical in
/-- The partial augmentation against a clopen set kills boundaries. -/
lemma bnd_augFun {X : TopCat.{0}} {A : Set X} (hA : IsClopen A) :
    bnd X 0 ≫ augFun X A = 0 := by
  apply Sigma.hom_ext
  intro σ
  rw [comp_zero, ← assoc]
  rw [show Sigma.ι (fun _ : Idx X 1 => ModuleCat.of ℤ ℤ) σ ≫ bnd X 0 =
    ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
      gen X 0 ((TopCat.toSSet.obj X).δ k σ) from gen_d X 0 σ]
  rw [Preadditive.sum_comp, Fin.sum_univ_two, Preadditive.zsmul_comp,
    Preadditive.zsmul_comp, gen_augFun, gen_augFun]
  by_cases h : pointOf ((TopCat.toSSet.obj X).δ (0 : Fin 2) σ) ∈ A
  · rw [if_pos h, if_pos ((mem_iff_of_clopen_δ hA σ).mp h)]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      one_smul]
    exact add_neg_cancel _
  · rw [if_neg h, if_neg (fun h1 => h ((mem_iff_of_clopen_δ hA σ).mpr h1))]
    simp only [smul_zero, add_zero]

open Classical in
/-- The augmentation against a clopen set, as a chain map to `ℤ`
concentrated in degree `0`. -/
noncomputable def augTo (X : TopCat.{0}) (A : Set X) (hA : IsClopen A) :
    SC X ⟶ Zsingle :=
  HomologicalComplex.mkHomToSingle (augFun X A) (by
    rintro i (hi : 0 + 1 = i)
    obtain rfl : i = 1 := by omega
    exact bnd_augFun hA)

open Classical in
lemma augTo_f_zero (X : TopCat.{0}) (A : Set X) (hA : IsClopen A) :
    (augTo X A hA).f 0 = augFun X A := by
  rw [augTo, HomologicalComplex.mkHomToSingle_f, ChainComplex.single₀ObjXSelf,
    Iso.refl_inv]
  exact comp_id _

/-- The class of a point, as a chain map from `ℤ` concentrated in degree
`0`. -/
noncomputable def ptFrom (X : TopCat.{0}) (x : X) : Zsingle ⟶ SC X :=
  HomologicalComplex.mkHomFromSingle (gen X 0 (constSimplex X x)) (by
    rintro k (hk : k + 1 = 0)
    exact absurd hk (by omega))

lemma ptFrom_f_zero (X : TopCat.{0}) (x : X) :
    (ptFrom X x).f 0 = gen X 0 (constSimplex X x) := by
  rw [ptFrom, HomologicalComplex.mkHomFromSingle_f, ChainComplex.single₀ObjXSelf,
    Iso.refl_hom, id_comp]

open Classical in
/-- Pairing the class of a point against a clopen augmentation. -/
lemma ptFrom_augTo (X : TopCat.{0}) (x : X) (A : Set X) (hA : IsClopen A) :
    ptFrom X x ≫ augTo X A hA =
      if x ∈ A then 𝟙 Zsingle else 0 := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, ptFrom_f_zero, augTo_f_zero, gen_augFun,
    pointOf_constSimplex]
  by_cases h : x ∈ A
  · rw [if_pos h, if_pos h, HomologicalComplex.id_f]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The canonical identification `H₀(ℤ[0]) ≅ ℤ`. -/
noncomputable abbrev ZsingleH0Iso : Zsingle.homology 0 ≅ ModuleCat.of ℤ ℤ :=
  HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _

/-- The degree-`0` homology augmentation against a clopen set. -/
noncomputable def augH (X : TopCat.{0}) (A : Set X) (hA : IsClopen A) :
    Hgrp X 0 ⟶ ModuleCat.of ℤ ℤ :=
  HomologicalComplex.homologyMap (augTo X A hA) 0 ≫ ZsingleH0Iso.hom

/-- The degree-`0` homology class of a point. -/
noncomputable def ptH (X : TopCat.{0}) (x : X) :
    ModuleCat.of ℤ ℤ ⟶ Hgrp X 0 :=
  ZsingleH0Iso.inv ≫ HomologicalComplex.homologyMap (ptFrom X x) 0

open Classical in
/-- The pairing of the class of a point against a clopen augmentation. -/
lemma ptH_augH (X : TopCat.{0}) (x : X) (A : Set X) (hA : IsClopen A) :
    ptH X x ≫ augH X A hA =
      if x ∈ A then 𝟙 (ModuleCat.of ℤ ℤ) else 0 := by
  unfold ptH augH
  rw [assoc, ← assoc (HomologicalComplex.homologyMap (ptFrom X x) 0),
    ← HomologicalComplex.homologyMap_comp, ptFrom_augTo]
  by_cases h : x ∈ A
  · rw [if_pos h, if_pos h, HomologicalComplex.homologyMap_id, id_comp,
      Iso.inv_hom_id]
  · rw [if_neg h, if_neg h, HomologicalComplex.homologyMap_zero, zero_comp,
      comp_zero]

/-- The identity of `ℤ` is not the zero morphism (used to convert split
monos out of `ℤ` into non-vanishing statements). -/
lemma id_int_ne_zero : 𝟙 (ModuleCat.of ℤ ℤ) ≠ 0 := by
  intro h
  have h1 : (𝟙 (ModuleCat.of ℤ ℤ)) (1 : ℤ) = (0 : ModuleCat.of ℤ ℤ ⟶ _) (1 : ℤ) := by
    rw [h]
  rw [ModuleCat.id_apply, zeroApp] at h1
  exact one_ne_zero h1

/-! ## Stage A toolkit: path simplices -/

/-- The homeomorphism `Δ¹ ≃ₜ I`, as a continuous map. -/
noncomputable def simplexToI : C(stdSimplex ℝ (Fin 2), unitInterval) :=
  ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The singular `1`-simplex of a path. -/
noncomputable def pathSimplex {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    Idx X 1 :=
  (simplexEquiv X 1).symm (γ.toContinuousMap.comp simplexToI)

lemma coord_face_v0 (k : Fin 2) :
    (SingularPrism.face k v0).1 1 = if k = 0 then (1 : ℝ) else 0 := by
  have h := SingularPrism.sum_filter_map_apply (a := Fin 1) (b := Fin 2)
    k.succAbove (fun j => j = (1 : Fin 2)) v0
  have hL : ∑ j with j = (1 : Fin 2), stdSimplex.map k.succAbove v0 j =
      stdSimplex.map k.succAbove v0 1 := by
    rw [Finset.filter_eq', if_pos (Finset.mem_univ _), Finset.sum_singleton]
  have hcoord : ((k.succAbove 0 : Fin 2) : ℕ) = if k = 0 then 1 else 0 := by
    rw [coe_succAbove]
    fin_cases k <;> simp
  have hR : ∑ m with k.succAbove m = (1 : Fin 2), v0.1 m =
      if k = 0 then (1 : ℝ) else 0 := by
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      have hfil : ({m : Fin 1 | (0 : Fin 2).succAbove m = 1} : Finset (Fin 1)) =
          {0} := by
        apply Finset.ext
        intro m
        rw [Subsingleton.elim m (0 : Fin 1)]
        constructor
        · intro _
          exact Finset.mem_singleton_self 0
        · intro _
          rw [Finset.mem_filter_univ]
          decide
      rw [hfil, Finset.sum_singleton]
      show (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) 0 = 1
      rw [Pi.single_eq_same]
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro m hm
      exfalso
      rw [Finset.mem_filter_univ] at hm
      have h0 : ((k.succAbove m : Fin 2) : ℕ) = 1 := by rw [hm]; decide
      rw [Subsingleton.elim m 0] at h0
      rw [hcoord, if_neg hk] at h0
      exact one_ne_zero h0.symm
  show (stdSimplex.map k.succAbove v0).1 1 = _
  calc (stdSimplex.map k.succAbove v0).1 1
      = ∑ j with j = (1 : Fin 2), stdSimplex.map k.succAbove v0 j := hL.symm
    _ = ∑ m with k.succAbove m = (1 : Fin 2), v0 m := h
    _ = if k = 0 then (1 : ℝ) else 0 := hR

lemma simplexToI_face_v0 (k : Fin 2) :
    simplexToI (SingularPrism.face k v0) = if k = 0 then 1 else 0 := by
  apply Subtype.ext
  show ((SingularPrism.face k v0).1 1) = _
  rw [coord_face_v0]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

lemma pointOf_δ_pathSimplex {X : TopCat.{0}} {x y : X} (γ : Path x y)
    (k : Fin 2) :
    pointOf ((TopCat.toSSet.obj X).δ k (pathSimplex γ)) =
      if k = 0 then y else x := by
  rw [pointOf_δ]
  unfold pathSimplex
  rw [Equiv.apply_symm_apply]
  show γ (simplexToI (SingularPrism.face k v0)) = _
  rw [simplexToI_face_v0]
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, Path.target]
  · rw [if_neg hk, if_neg hk, Path.source]

/-- The boundary of a path simplex: `∂[γ] = [target] − [source]`. -/
lemma gen_pathSimplex_bnd {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    gen X 1 (pathSimplex γ) ≫ bnd X 0 =
      gen X 0 (constSimplex X y) - gen X 0 (constSimplex X x) := by
  rw [gen_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  rw [show (TopCat.toSSet.obj X).δ (0 : Fin 2) (pathSimplex γ) = constSimplex X y from
      idx0_ext (by rw [pointOf_δ_pathSimplex, if_pos rfl, pointOf_constSimplex]),
    show (TopCat.toSSet.obj X).δ (1 : Fin 2) (pathSimplex γ) = constSimplex X x from
      idx0_ext (by rw [pointOf_δ_pathSimplex, if_neg (by decide), pointOf_constSimplex]),
    one_zsmul, neg_one_zsmul, ← sub_eq_add_neg]

lemma subApp {M N : ModuleCat.{0} ℤ} (f g : M ⟶ N) (z : M) :
    (f - g) z = f z - g z := by
  rw [sub_eq_add_neg, addApp, negApp, ← sub_eq_add_neg]

/-- Elementwise boundary of a path simplex. -/
lemma bnd_genUnit_pathSimplex {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    bnd X 0 (genUnit X 1 (pathSimplex γ)) =
      genUnit X 0 (constSimplex X y) - genUnit X 0 (constSimplex X x) := by
  rw [genUnit_eq, ← ModuleCat.comp_apply]
  calc (gen X 1 (pathSimplex γ) ≫ bnd X 0) (1 : ℤ)
      = (gen X 0 (constSimplex X y) - gen X 0 (constSimplex X x)) (1 : ℤ) := by
        rw [gen_pathSimplex_bnd]
    _ = genUnit X 0 (constSimplex X y) - genUnit X 0 (constSimplex X x) := by
        rw [subApp, genUnit_eq, genUnit_eq]

/-- Joined points have homologous point chains. -/
lemma exists_bnd_eq_sub {X : TopCat.{0}} {x y : X} (h : Joined x y) :
    ∃ w : ↥(Cgrp X 1),
      bnd X 0 w = genUnit X 0 (constSimplex X y) -
        genUnit X 0 (constSimplex X x) :=
  ⟨genUnit X 1 (pathSimplex h.somePath), bnd_genUnit_pathSimplex h.somePath⟩

/-! ## Stage A: `H₀` of a path-connected space -/

open Classical in
/-- In a path-connected space, every `0`-chain is homologous to its total
augmentation times a base point. -/
lemma exists_bnd_of_pathConnected {X : TopCat.{0}} [PathConnectedSpace X]
    (x₀ : X) (z : ↥(Cgrp X 0)) :
    ∃ v : ↥(Cgrp X 1),
      bnd X 0 v =
        z - gen X 0 (constSimplex X x₀) (augFun X Set.univ z) := by
  induction z using freeInduction with
  | unit s =>
      obtain ⟨w, hw⟩ := exists_bnd_eq_sub
        (PathConnectedSpace.joined x₀ (pointOf s))
      refine ⟨w, ?_⟩
      rw [hw, constSimplex_pointOf]
      rw [show (unitOf s : ↥(Cgrp X 0)) = genUnit X 0 s from rfl,
        augFun_genUnit, if_pos (Set.mem_univ _), ← genUnit_eq]
  | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, map_zero, sub_zero]
  | add a b ha hb =>
      obtain ⟨va, hva⟩ := ha
      obtain ⟨vb, hvb⟩ := hb
      refine ⟨va + vb, ?_⟩
      rw [map_add, hva, hvb, map_add, map_add]
      abel
  | smulz c a ha =>
      obtain ⟨v, hv⟩ := ha
      refine ⟨c • v, ?_⟩
      rw [mapSmul, hv, mapSmul, mapSmul, smul_sub]

open Classical in
/-- Elementwise form of `augTo_f_zero`, bridging the coercion at
`Zsingle.X 0` against the coercion at `ModuleCat.of ℤ ℤ`. -/
lemma augTo_f_zero_apply (X : TopCat.{0}) (A : Set X) (hA : IsClopen A)
    (c : ↥(Cgrp X 0)) :
    (ConcreteCategory.hom ((augTo X A hA).f 0)) c = augFun X A c :=
  congrArg (fun ψ => (ConcreteCategory.hom ψ) c) (augTo_f_zero X A hA)

/-- The differential out of degree `1` of the single complex vanishes. -/
lemma Zsingle_d_one_zero : Zsingle.d 1 0 = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
    (ModuleCat.of ℤ ℤ) 1 one_ne_zero).eq_of_src _ _

open Classical in
/-- **`H₀` of a path-connected space.** The augmentation induces an
isomorphism `H₀(X) ≅ ℤ` on homology. -/
theorem isIso_homologyMap_augTo (X : TopCat.{0}) [PathConnectedSpace X] :
    IsIso (HomologicalComplex.homologyMap
      (augTo X Set.univ isClopen_univ) 0) := by
  obtain ⟨x₀⟩ : Nonempty ↥X := PathConnectedSpace.nonempty
  apply isIso_homologyMap_chain_zero
  · intro y
    refine ⟨gen X 0 (constSimplex X x₀) (show ℤ from y), 0, ?_⟩
    rw [Zsingle_d_one_zero, zeroApp, add_zero, augTo_f_zero_apply,
      ← ModuleCat.comp_apply, gen_augFun, if_pos (Set.mem_univ _)]
    exact ModuleCat.id_apply _ _
  · intro z hz
    obtain ⟨w, hw⟩ := hz
    have hz0 : augFun X Set.univ z = 0 := by
      rw [augTo_f_zero_apply, Zsingle_d_one_zero, zeroApp] at hw
      exact hw
    obtain ⟨v, hv⟩ := exists_bnd_of_pathConnected x₀ z
    rw [hz0, map_zero, sub_zero] at hv
    exact ⟨v, hv.symm⟩

/-- The homology augmentation `H₀(X) ⟶ ℤ` of a path-connected space is an
isomorphism. -/
theorem isIso_augH_of_pathConnected (X : TopCat.{0}) [PathConnectedSpace X] :
    IsIso (augH X Set.univ isClopen_univ) := by
  haveI := isIso_homologyMap_augTo X
  unfold augH
  infer_instance

/-! ## Stage A/B: vanishing in positive degrees -/

instance : TotallyDisconnectedSpace Unit :=
  ⟨fun _ _ _ => Set.subsingleton_of_subsingleton⟩

/-- Positive-degree singular homology of a totally disconnected space
vanishes (Mathlib), retyped onto `Hgrp`. -/
lemma isZero_homology_of_totallyDisconnected (X : TopCat.{0})
    [TotallyDisconnectedSpace X] {m : ℕ} (hm : m ≠ 0) :
    IsZero (Hgrp X m) :=
  isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) m (ModuleCat.of ℤ ℤ) X hm

/-- **Stage B.** Positive-degree singular homology of a contractible space
vanishes. -/
theorem isZero_homology_of_contractible (X : TopCat.{0})
    [ContractibleSpace X] {m : ℕ} (hm : m ≠ 0) :
    IsZero (Hgrp X m) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (X : Type)
  have hzero : IsZero (Hgrp (TopCat.of Unit) m) :=
    isZero_homology_of_totallyDisconnected (TopCat.of Unit) hm
  exact hzero.of_iso
    (homotopyEquiv_homology_iso (X := X) (Y := TopCat.of Unit) e m)

/-! ## Stage A/B: naturality of augmentations and point classes -/

open Classical in
lemma sChainMap_augTo {X Y : TopCat.{0}} (f : X ⟶ Y) :
    sChainMap f ≫ augTo Y Set.univ isClopen_univ =
      augTo X Set.univ isClopen_univ := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, augTo_f_zero, augTo_f_zero]
  show chainMap f 0 ≫ augFun Y Set.univ = augFun X Set.univ
  apply Sigma.hom_ext
  intro s
  rw [← assoc]
  rw [show Sigma.ι (fun _ : Idx X 0 => ModuleCat.of ℤ ℤ) s ≫ chainMap f 0 =
    gen Y 0 ((TopCat.toSSet.map f).app (op ⦋0⦌) s) from gen_map f 0 s]
  rw [gen_augFun, gen_augFun, if_pos (Set.mem_univ _), if_pos (Set.mem_univ _)]

lemma homologyMap_augH {X Y : TopCat.{0}} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (sChainMap f) 0 ≫
      augH Y Set.univ isClopen_univ = augH X Set.univ isClopen_univ := by
  unfold augH
  rw [← assoc, ← HomologicalComplex.homologyMap_comp, sChainMap_augTo]

lemma ptFrom_sChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    ptFrom X x ≫ sChainMap f = ptFrom Y (f.hom x) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, ptFrom_f_zero, ptFrom_f_zero]
  show gen X 0 (constSimplex X x) ≫ chainMap f 0 = gen Y 0 (constSimplex Y (f.hom x))
  rw [gen_map,
    show (TopCat.toSSet.map f).app (op ⦋0⦌) (constSimplex X x) =
      constSimplex Y (f.hom x) from idx0_ext
        (by rw [pointOf_map, pointOf_constSimplex, pointOf_constSimplex])]

lemma ptH_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    ptH X x ≫ HomologicalComplex.homologyMap (sChainMap f) 0 =
      ptH Y (f.hom x) := by
  unfold ptH
  rw [assoc, ← HomologicalComplex.homologyMap_comp, ptFrom_sChainMap]

/-- A path between points gives a chain homotopy between the point chain
maps. -/
noncomputable def ptFromHomotopy {X : TopCat.{0}} {x y : X} (γ : Path x y) :
    Homotopy (ptFrom X x) (ptFrom X y) where
  hom i j :=
    if h : i = 0 ∧ j = 1 then
      eqToHom (by rw [h.1]) ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
            (ModuleCat.of ℤ ℤ)).hom ≫ gen X 1 (pathSimplex γ.symm)) ≫
          eqToHom (by rw [h.2]; rfl)
    else 0
  zero i j hij := by
    rw [dif_neg]
    rintro ⟨rfl, rfl⟩
    exact hij rfl
  comm i := by
    match i with
    | 0 =>
        rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
        rw [dif_pos ⟨rfl, rfl⟩, eqToHom_refl, eqToHom_refl, id_comp, comp_id]
        rw [ptFrom, HomologicalComplex.mkHomFromSingle_f,
          show (ptFrom X y).f 0 = (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ ℤ)).hom ≫
              gen X 0 (constSimplex X y) from
            HomologicalComplex.mkHomFromSingle_f _ _]
        rw [assoc]
        rw [show gen X 1 (pathSimplex γ.symm) ≫ (SC X).d 1 0 =
          gen X 0 (constSimplex X x) - gen X 0 (constSimplex X y) from
          gen_pathSimplex_bnd γ.symm]
        rw [zero_add, ← Preadditive.comp_add]
        congr 1
        abel
    | n + 1 =>
        exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
          (ModuleCat.of ℤ ℤ) (n + 1) (by omega)).eq_of_src _ _

/-- Joined points have equal degree-`0` homology classes. -/
lemma ptH_eq_of_joined {X : TopCat.{0}} {x y : X} (h : Joined x y) :
    ptH X x = ptH X y := by
  unfold ptH
  rw [(ptFromHomotopy h.somePath).homologyMap_eq 0]

/-! ## Stage A/B exports -/

/-- **Stage A/B.** `H₀(X) ≅ ℤ` for a path-connected space, via the
augmentation. -/
noncomputable def h0_iso_int (X : TopCat.{0}) [PathConnectedSpace X] :
    Hgrp X 0 ≅ ModuleCat.of ℤ ℤ :=
  haveI := isIso_augH_of_pathConnected X
  asIso (augH X Set.univ isClopen_univ)

/-- **Stage A.** `H₀(pt) ≅ ℤ`. -/
noncomputable def h0_pt_iso_int :
    Hgrp (TopCat.of Unit) 0 ≅ ModuleCat.of ℤ ℤ :=
  h0_iso_int (TopCat.of Unit)

/-- **Stage A.** `H_m(pt) = 0` for `m ≠ 0`. -/
lemma hn_pt_isZero {m : ℕ} (hm : m ≠ 0) : IsZero (Hgrp (TopCat.of Unit) m) :=
  isZero_homology_of_totallyDisconnected (TopCat.of Unit) hm

/-- **Stage B.** `H₀(X) ≅ ℤ` for a contractible space. -/
noncomputable def h0_contractible_iso_int (X : TopCat.{0})
    [ContractibleSpace X] : Hgrp X 0 ≅ ModuleCat.of ℤ ℤ :=
  h0_iso_int X

/-! ## Stage C (abstract): Mayer-Vietoris consequences -/

section AbstractMV

variable {X : TopCat.{0}} {U V : Set X}

/-- **The suspension step.** If `H_{n+1}` and `H_n` of both `U` and `V`
vanish, the Mayer-Vietoris connecting map `∂ : H_{n+1}(X) ⟶ H_n(U ∩ V)` is
an isomorphism. -/
theorem isIso_mvδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ)
    (hU1 : IsZero (Hgrp (TopCat.of U) (n + 1)))
    (hV1 : IsZero (Hgrp (TopCat.of V) (n + 1)))
    (hUn : IsZero (Hgrp (TopCat.of U) n))
    (hVn : IsZero (Hgrp (TopCat.of V) n)) :
    IsIso (mvδ hU hV hUV n) := by
  haveI : Mono (mvδ hU hV hUV n) :=
    (mv_exact₃ hU hV hUV n).mono_g
      (((biprod_isZero_iff _ _).mpr ⟨hU1, hV1⟩).eq_of_src _ _)
  haveI : Epi (mvδ hU hV hUV n) :=
    (mv_exact₁ hU hV hUV n).epi_f
      (((biprod_isZero_iff _ _).mpr ⟨hUn, hVn⟩).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- With contractible pieces the connecting map is an isomorphism
`∂ : H_{n+2}(X) ≅ H_{n+1}(U ∩ V)` in all degrees `≥ 2`. -/
theorem isIso_mvδ_of_contractible (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    [ContractibleSpace ↥U] [ContractibleSpace ↥V] :
    IsIso (mvδ hU hV hUV (n + 1)) :=
  isIso_mvδ hU hV hUV (n + 1)
    (isZero_homology_of_contractible _ (by omega))
    (isZero_homology_of_contractible _ (by omega))
    (isZero_homology_of_contractible _ (by omega))
    (isZero_homology_of_contractible _ (by omega))

/-- Vanishing transported across the connecting isomorphism:
if `H_{n+1}(U ∩ V) = 0` then `H_{n+2}(X) = 0` (contractible pieces). -/
theorem isZero_of_isZero_inter (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    (h : IsZero (Hgrp (TopCat.of (U ∩ V : Set X)) (n + 1))) :
    IsZero (Hgrp X (n + 2)) := by
  haveI := isIso_mvδ_of_contractible hU hV hUV n
  exact h.of_iso (asIso (mvδ hU hV hUV (n + 1)))

/-- The Mayer-Vietoris pair map is mono in degree `0` when `U ∩ V` is path
connected (its first component is split by the augmentation). -/
theorem mono_mvPair_zero (U V : Set X)
    [PathConnectedSpace ↥(U ∩ V : Set X)] :
    Mono (mvPair U V 0) := by
  haveI : IsIso (augH (TopCat.of (U ∩ V : Set X)) Set.univ isClopen_univ) :=
    isIso_augH_of_pathConnected _
  haveI hm1 : Mono (HomologicalComplex.homologyMap
      (sChainMap (mvInclU U V)) 0 ≫
        augH (TopCat.of U) Set.univ isClopen_univ) := by
    rw [homologyMap_augH]
    infer_instance
  haveI hm2 : Mono (HomologicalComplex.homologyMap
      (sChainMap (mvInclU U V)) 0) :=
    mono_of_mono _ (augH (TopCat.of U) Set.univ isClopen_univ)
  have hfac : mvPair U V 0 ≫
      (biprod.fst : _ ⟶ Hgrp (TopCat.of U) 0) =
      HomologicalComplex.homologyMap (sChainMap (mvInclU U V)) 0 :=
    biprod.lift_fst _ _
  haveI : Mono (mvPair U V 0 ≫
      (biprod.fst : _ ⟶ Hgrp (TopCat.of U) 0)) := by
    rw [hfac]
    exact hm2
  exact mono_of_mono (mvPair U V 0) biprod.fst

/-- **Low degree.** If `U, V` kill `H₁` and `U ∩ V` is path connected,
then `H₁(X) = 0`. -/
theorem isZero_h1 (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [PathConnectedSpace ↥(U ∩ V : Set X)]
    (hU1 : IsZero (Hgrp (TopCat.of U) 1))
    (hV1 : IsZero (Hgrp (TopCat.of V) 1)) :
    IsZero (Hgrp X 1) := by
  haveI : Mono (mvδ hU hV hUV 0) :=
    (mv_exact₃ hU hV hUV 0).mono_g
      (((biprod_isZero_iff _ _).mpr ⟨hU1, hV1⟩).eq_of_src _ _)
  haveI := mono_mvPair_zero U V
  have h0 : mvδ hU hV hUV 0 = 0 :=
    zero_of_comp_mono (mvPair U V 0) (mvδ_comp_mvPair hU hV hUV 0)
  exact IsZero.of_mono_eq_zero _ h0

/-- `H₁` vanishing with contractible pieces and path-connected
intersection. -/
theorem isZero_h1_of_contractible (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    [PathConnectedSpace ↥(U ∩ V : Set X)] :
    IsZero (Hgrp X 1) :=
  isZero_h1 hU hV hUV
    (isZero_homology_of_contractible _ one_ne_zero)
    (isZero_homology_of_contractible _ one_ne_zero)

end AbstractMV

end SingularSphere
end Foundation
end IndisputableMonolith
