/-
Homotopy invariance of singular homology: the prism operator.

This file works toward the theorem that homotopic maps `f g : X ⟶ Y` of
topological spaces induce the same map on singular homology (with `ℤ`
coefficients), via the classical prism operator (Hatcher, Theorem 2.10).

## Contents (staged; see the frontier note at the end of the file)

* Stage 1: the prism decomposition maps `prism i : Δ^{n+1} → Δⁿ × I`
  (affine maps onto the simplices of the standard triangulation of the
  prism `Δⁿ × I`), as explicit continuous maps.
* Stage 2: the face identities between the `prism i` and the topological
  face inclusions `face j : Δⁿ → Δ^{n+1}` (the combinatorial heart of the
  prism argument): top, bottom, cancellation of adjacent prisms, and the
  two commutation identities with lower-dimensional faces.

The model: `Δⁿ` is `stdSimplex ℝ (Fin (n+1))` (as used by
`SimplexCategory.toTop` and hence by `TopCat.toSSet` and
`AlgebraicTopology.singularHomologyFunctor`), and `I` is `unitInterval`.
The vertices of the prism `Δⁿ × I` are `vⱼ = (eⱼ, 0)` and `wⱼ = (eⱼ, 1)`;
`prism i` is the affine map `Δ^{n+1} → Δⁿ × I` sending the vertices
`e₀, …, eₙ₊₁` of `Δ^{n+1}` to `v₀, …, vᵢ, wᵢ, …, wₙ`.  Concretely, on
barycentric coordinates the first component is induced by the vertex map
`Fin.predAbove i` (which collapses `i, i+1` to `i`) and the second
component is the sum of the coordinates strictly above `i`.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv

namespace IndisputableMonolith
namespace Foundation
namespace SingularPrism

open scoped unitInterval
open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

/-! ## `Fin` coordinate arithmetic for `succAbove` / `predAbove` -/

lemma coe_succAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    ((p.succAbove i : Fin (n + 1)) : ℕ) =
      if (i : ℕ) < (p : ℕ) then (i : ℕ) else (i : ℕ) + 1 := by
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using not_lt.mp h)]
    simp [h]

lemma coe_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    ((p.predAbove i : Fin n) : ℕ) =
      if (p : ℕ) < (i : ℕ) then (i : ℕ) - 1 else (i : ℕ) := by
  by_cases h : (p : ℕ) < (i : ℕ)
  · rw [Fin.predAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.predAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using not_lt.mp h)]
    simp [h]

/-! ## Stage 1: the prism decomposition maps -/

variable {n : ℕ}

/-- The second coordinate of the `i`-th prism map: the sum of the barycentric
coordinates strictly above `i`. -/
def prismSndFun (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) : ℝ :=
  ∑ k with i.castSucc < k, x k

lemma prismSndFun_nonneg (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    0 ≤ prismSndFun i x :=
  Finset.sum_nonneg fun k _ => x.2.1 k

lemma prismSndFun_le_one (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    prismSndFun i x ≤ 1 := by
  calc prismSndFun i x ≤ ∑ k, x k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => x.2.1 k)
    _ = 1 := x.2.2

lemma prismSndFun_mem_unitInterval (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    prismSndFun i x ∈ I :=
  Set.mem_Icc.mpr ⟨prismSndFun_nonneg i x, prismSndFun_le_one i x⟩

lemma continuous_prismSndFun (i : Fin (n + 1)) :
    Continuous (prismSndFun (n := n) i) :=
  continuous_finset_sum _ fun k _ =>
    (continuous_apply k).comp continuous_subtype_val

/-- The `i`-th prism map `Δ^{n+1} → Δⁿ × I`: the affine map sending the
vertices `e₀, …, eₙ₊₁` of `Δ^{n+1}` to `v₀, …, vᵢ, wᵢ, …, wₙ`, where
`vⱼ = (eⱼ, 0)` and `wⱼ = (eⱼ, 1)` are the vertices of the prism. -/
noncomputable def prism (i : Fin (n + 1)) :
    C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I) where
  toFun x := (stdSimplex.map i.predAbove x,
    ⟨prismSndFun i x, prismSndFun_mem_unitInterval i x⟩)
  continuous_toFun :=
    (stdSimplex.continuous_map _).prodMk
      ((continuous_prismSndFun i).subtype_mk _)

@[simp] lemma prism_apply_fst (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    (prism i x).1 = stdSimplex.map i.predAbove x := rfl

@[simp] lemma prism_apply_snd (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 2))) :
    ((prism i x).2 : ℝ) = prismSndFun i x := rfl

/-- The `j`-th topological face inclusion `Δⁿ → Δ^{n+1}`, induced by the
vertex map `Fin.succAbove j` (skipping the vertex `j`).  This is the
topological realization of the simplicial face map `SimplexCategory.δ j`. -/
noncomputable def face (j : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map j.succAbove, stdSimplex.continuous_map _⟩

@[simp] lemma face_apply (j : Fin (n + 2)) (x : stdSimplex ℝ (Fin (n + 1))) :
    face j x = stdSimplex.map j.succAbove x := rfl

/-! ## Stage 2: the face identities

The composite of a prism map with a face inclusion is computed in the four
classical cases (Hatcher, proof of Theorem 2.10):

* `j = 0, i = 0`: the top of the prism, `x ↦ (x, 1)`;
* `j = n+2, i = n+1` (last indices): the bottom of the prism, `x ↦ (x, 0)`;
* `j = i+1` interior: consecutive prism maps agree on the shared face
  (these are the cancelling terms in `∂P`);
* `j ≤ i` or `j ≥ i+2`: the composite factors through a prism map in one
  dimension lower, followed by a face inclusion of the prism (these match
  the terms of `P∂`).
-/

/-- Composites of `stdSimplex.map` agree as soon as the underlying vertex
maps agree pointwise. -/
lemma map_map_eq_map_map {a b b' c : Type*}
    [Fintype a] [Fintype b] [Fintype b'] [Fintype c]
    (f : a → b) (g : b → c) (f' : a → b') (g' : b' → c)
    (h : ∀ k, g (f k) = g' (f' k)) (x : stdSimplex ℝ a) :
    stdSimplex.map g (stdSimplex.map f x) = stdSimplex.map g' (stdSimplex.map f' x) := by
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply,
    show g ∘ f = g' ∘ f' from funext h]

/-- Composite of `stdSimplex.map` with the identity vertex map. -/
lemma map_map_eq_self {a b : Type*} [Fintype a] [Fintype b]
    (f : a → b) (g : b → a) (h : ∀ k, g (f k) = k) (x : stdSimplex ℝ a) :
    stdSimplex.map g (stdSimplex.map f x) = x := by
  rw [stdSimplex.map_comp_apply, show g ∘ f = id from funext h,
    stdSimplex.map_id_apply]

/-- A filtered coordinate-sum of `stdSimplex.map f x` reindexes along `f`. -/
lemma sum_filter_map_apply {a b : Type*} [Fintype a] [Fintype b] [DecidableEq b]
    (f : a → b) (p : b → Prop) [DecidablePred p] (x : stdSimplex ℝ a) :
    ∑ k with p k, stdSimplex.map f x k = ∑ m with p (f m), x m := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [Finset.sum_fiberwise_eq_sum_filter Finset.univ (Finset.univ.filter p) f (⇑x)]
  exact Finset.sum_congr (by ext m; simp) fun _ _ => rfl

lemma prismSndFun_map_succAbove (c : Fin (n + 1)) (j : Fin (n + 2))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    prismSndFun c (stdSimplex.map j.succAbove x) =
      ∑ m with c.castSucc < j.succAbove m, x m :=
  sum_filter_map_apply j.succAbove (fun k => c.castSucc < k) x

/-- Top of the prism: `prism 0 ∘ face 0 = (x ↦ (x, 1))`. -/
theorem prism_comp_face_top :
    (prism (0 : Fin (n + 1))).comp (face (0 : Fin (n + 2))) =
      (ContinuousMap.id _).prodMk (ContinuousMap.const _ 1) := by
  refine ContinuousMap.ext fun x => Prod.ext ?_ (Subtype.ext ?_)
  · show stdSimplex.map (Fin.predAbove 0) (stdSimplex.map (Fin.succAbove 0) x) = x
    refine map_map_eq_self _ _ (fun k => ?_) x
    apply Fin.ext
    simp only [coe_predAbove, coe_succAbove, Fin.val_zero]
    split_ifs <;> omega
  · show prismSndFun 0 (stdSimplex.map (Fin.succAbove 0) x) = 1
    rw [prismSndFun_map_succAbove]
    calc ∑ m with (0 : Fin (n + 1)).castSucc < (0 : Fin (n + 2)).succAbove m, x m
        = ∑ m, x m := by
          apply Finset.sum_congr _ fun _ _ => rfl
          rw [Finset.filter_true_of_mem]
          intro m _
          simp only [Fin.lt_def, coe_succAbove, Fin.val_castSucc, Fin.val_zero]
          split_ifs <;> omega
      _ = 1 := x.2.2

/-- Bottom of the prism: `prism (last) ∘ face (last) = (x ↦ (x, 0))`. -/
theorem prism_comp_face_bot :
    (prism (Fin.last n)).comp (face (Fin.last (n + 1))) =
      (ContinuousMap.id _).prodMk (ContinuousMap.const _ 0) := by
  refine ContinuousMap.ext fun x => Prod.ext ?_ (Subtype.ext ?_)
  · show stdSimplex.map (Fin.predAbove (Fin.last n))
        (stdSimplex.map (Fin.succAbove (Fin.last (n + 1))) x) = x
    refine map_map_eq_self _ _ (fun k => ?_) x
    apply Fin.ext
    have hk := k.isLt
    simp only [coe_predAbove, coe_succAbove, Fin.val_last]
    split_ifs <;> omega
  · show prismSndFun (Fin.last n) (stdSimplex.map (Fin.succAbove (Fin.last (n + 1))) x) = 0
    rw [prismSndFun_map_succAbove]
    apply Finset.sum_eq_zero
    intro m hm
    exfalso
    rw [Finset.mem_filter] at hm
    have hm' := hm.2
    have hm2 := m.isLt
    rw [Fin.lt_def] at hm'
    revert hm'
    simp only [coe_succAbove, Fin.val_castSucc, Fin.val_last]
    split_ifs
    all_goals omega

/-- Adjacent prism maps agree on their shared face (the cancelling terms
of `∂P`): `prism i ∘ face (i+1) = prism (i+1) ∘ face (i+1)`. -/
theorem prism_comp_face_cancel (i : Fin (n + 1)) :
    (prism i.castSucc).comp (face i.succ.castSucc) =
      (prism i.succ).comp (face i.succ.castSucc) := by
  refine ContinuousMap.ext fun x => Prod.ext ?_ (Subtype.ext ?_)
  · show stdSimplex.map (Fin.predAbove i.castSucc)
        (stdSimplex.map (Fin.succAbove i.succ.castSucc) x) =
      stdSimplex.map (Fin.predAbove i.succ)
        (stdSimplex.map (Fin.succAbove i.succ.castSucc) x)
    refine map_map_eq_map_map _ _ _ _ (fun k => ?_) x
    apply Fin.ext
    have hk := k.isLt
    simp only [coe_predAbove, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · show prismSndFun i.castSucc (stdSimplex.map (Fin.succAbove i.succ.castSucc) x) =
      prismSndFun i.succ (stdSimplex.map (Fin.succAbove i.succ.castSucc) x)
    rw [prismSndFun_map_succAbove, prismSndFun_map_succAbove]
    refine Finset.sum_congr (Finset.filter_congr fun m _ => ?_) fun _ _ => rfl
    have hm := m.isLt
    simp only [Fin.lt_def, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-- Commutation with lower faces (`j ≤ i`): the composite of a prism map
with a low face factors through the prism one dimension down.  This matches
the `(i, j)` terms of `∂P` with `j < i+1` against the terms of `P∂`. -/
theorem prism_comp_face_of_le {i : Fin (n + 1)} {j : Fin (n + 2)}
    (hij : j ≤ i.castSucc) :
    (prism i.succ).comp (face j.castSucc) =
      ((face j).prodMap (ContinuousMap.id I)).comp (prism i) := by
  have hij' : (j : ℕ) ≤ (i : ℕ) := by simpa [Fin.le_def] using hij
  refine ContinuousMap.ext fun x => Prod.ext ?_ (Subtype.ext ?_)
  · show stdSimplex.map (Fin.predAbove i.succ)
        (stdSimplex.map (Fin.succAbove j.castSucc) x) =
      stdSimplex.map (Fin.succAbove j) (stdSimplex.map (Fin.predAbove i) x)
    refine map_map_eq_map_map _ _ _ _ (fun k => ?_) x
    apply Fin.ext
    have hk := k.isLt
    simp only [coe_predAbove, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · show prismSndFun i.succ (stdSimplex.map (Fin.succAbove j.castSucc) x) =
      prismSndFun i x
    rw [prismSndFun_map_succAbove, prismSndFun]
    refine Finset.sum_congr (Finset.filter_congr fun m _ => ?_) fun _ _ => rfl
    have hm := m.isLt
    simp only [Fin.lt_def, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-- Commutation with high faces (`j > i`): the composite of a prism map
with a high face factors through the prism one dimension down.  This
matches the `(i, j)` terms of `∂P` with `j > i+1` against the terms of
`P∂`. -/
theorem prism_comp_face_of_gt {i : Fin (n + 1)} {j : Fin (n + 2)}
    (hij : i.castSucc < j) :
    (prism i.castSucc).comp (face j.succ) =
      ((face j).prodMap (ContinuousMap.id I)).comp (prism i) := by
  have hij' : (i : ℕ) < (j : ℕ) := by simpa [Fin.lt_def] using hij
  refine ContinuousMap.ext fun x => Prod.ext ?_ (Subtype.ext ?_)
  · show stdSimplex.map (Fin.predAbove i.castSucc)
        (stdSimplex.map (Fin.succAbove j.succ) x) =
      stdSimplex.map (Fin.succAbove j) (stdSimplex.map (Fin.predAbove i) x)
    refine map_map_eq_map_map _ _ _ _ (fun k => ?_) x
    apply Fin.ext
    have hk := k.isLt
    simp only [coe_predAbove, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · show prismSndFun i.castSucc (stdSimplex.map (Fin.succAbove j.succ) x) =
      prismSndFun i x
    rw [prismSndFun_map_succAbove, prismSndFun]
    refine Finset.sum_congr (Finset.filter_congr fun m _ => ?_) fun _ _ => rfl
    have hm := m.isLt
    simp only [Fin.lt_def, coe_succAbove, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-! ## Stage 3: the chain-level prism operator

We now assemble the topological prism maps into a morphism of the singular
chain groups.  With `ℤ` coefficients, the singular chain group in degree `n`
of a space `X` is the coproduct `∐_{σ} ℤ` indexed by the singular
`n`-simplices of `X` (`Idx X n`); see `SSet.singularChainComplexFunctor`.
-/

/-- The type of singular `n`-simplices of `X` (the index set of the degree-`n`
singular chain group). -/
abbrev Idx (X : TopCat.{0}) (n : ℕ) : Type := (TopCat.toSSet.obj X).obj (op ⦋n⦌)

/-- The degree-`n` singular chain group of `X` with `ℤ` coefficients:
`∐_{σ ∈ Idx X n} ℤ`. -/
noncomputable abbrev Cgrp (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} ℤ :=
  ∐ fun _ : Idx X n => ModuleCat.of ℤ ℤ

/-- The generator of the singular chain group attached to a singular
simplex `a`. -/
noncomputable abbrev gen (X : TopCat.{0}) (n : ℕ) (a : Idx X n) :
    ModuleCat.of ℤ ℤ ⟶ Cgrp X n :=
  Sigma.ι (fun _ : Idx X n => ModuleCat.of ℤ ℤ) a

/-- Given a homotopy `H : I × X → Y`, a topological prism map
`pr : Δ^{n+1} → Δⁿ × I`, and a singular `n`-simplex `σ : Δⁿ → X` of `X`, the
associated singular `(n+1)`-simplex of `Y`: `t ↦ H(π₂(pr t), σ(π₁(pr t)))`. -/
noncomputable def prismSimplex {X Y : TopCat.{0}} (H : C(I × X, Y)) (n : ℕ)
    (pr : C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I))
    (s : Idx X n) : Idx Y (n + 1) :=
  (Y.toSSetObjEquiv (op ⦋n + 1⦌)).symm
    (H.comp (ContinuousMap.prodSwap.comp
      (((X.toSSetObjEquiv (op ⦋n⦌) s).prodMap (ContinuousMap.id I)).comp pr)))

/-- The prism operator on a generator: the signed sum
`∑ᵢ (-1)ⁱ [prismSimplex i]` over the prism decomposition maps `prisms i`. -/
noncomputable def Pgen {X Y : TopCat.{0}} (H : C(I × X, Y)) (n : ℕ)
    (prisms : Fin (n + 1) →
      C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I))
    (s : Idx X n) : ModuleCat.of ℤ ℤ ⟶ Cgrp Y (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • gen Y (n + 1) (prismSimplex H n (prisms i) s)

/-- The prism operator `P : C_n(X) → C_{n+1}(Y)`, extended from `Pgen` by the
universal property of the coproduct. -/
noncomputable def prismOp {X Y : TopCat.{0}} (H : C(I × X, Y)) (n : ℕ)
    (prisms : Fin (n + 1) →
      C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I)) :
    Cgrp X n ⟶ Cgrp Y (n + 1) :=
  Sigma.desc (Pgen H n prisms)

/-! ## Stage 4a: normal forms for the singular simplicial set

The singular simplicial set `TopCat.toSSet.obj X` is the restricted Yoneda
presheaf of `SimplexCategory.toTop`; through `TopCat.toSSetObjEquiv` its
simplicial structure maps become precomposition with the topological face
inclusions, and the functorial action of `TopCat.toSSet` becomes
postcomposition.
-/

/-- Naturality of `TopCat.toSSetObjEquiv`: the simplicial face map `δ j` of
the singular simplicial set is precomposition with the topological face
inclusion `face j`. -/
lemma toSSetObjEquiv_δ {X : TopCat.{0}} {n : ℕ} (j : Fin (n + 2)) (a : Idx X (n + 1)) :
    X.toSSetObjEquiv (op ⦋n⦌) ((TopCat.toSSet.obj X).δ j a) =
      (X.toSSetObjEquiv (op ⦋n + 1⦌) a).comp (face j) := by
  ext x
  rfl

/-- Naturality of `TopCat.toSSetObjEquiv`: the functorial action of
`TopCat.toSSet` on a continuous map `f` is postcomposition with `f`. -/
lemma toSSetObjEquiv_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ} (a : Idx X n) :
    Y.toSSetObjEquiv (op ⦋n⦌) ((TopCat.toSSet.map f).app (op ⦋n⦌) a) =
      f.hom.comp (X.toSSetObjEquiv (op ⦋n⦌) a) := by
  ext x
  rfl

/-! ## Stage 4b: generator normal forms for the singular chain complex -/

/-- The singular chain complex of `X` with `ℤ` coefficients. -/
noncomputable abbrev SC (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

/-- The simplicial `ℤ`-module underlying the singular chain complex of `X`. -/
noncomputable abbrev SOb (X : TopCat.{0}) : SimplicialObject (ModuleCat.{0} ℤ) :=
  ((SimplicialObject.whiskering _ _).obj
    (sigmaConst.obj (ModuleCat.of ℤ ℤ))).obj (TopCat.toSSet.obj X)

lemma SC_eq (X : TopCat.{0}) : SC X = AlternatingFaceMapComplex.obj (SOb X) := rfl

/-- The boundary out of degree `n+1` of the singular chain complex, typed on
the coproduct presentation of the chain groups. -/
noncomputable abbrev bnd (X : TopCat.{0}) (n : ℕ) : Cgrp X (n + 1) ⟶ Cgrp X n :=
  (SC X).d (n + 1) n

/-- The chain map induced by a continuous map, in degree `n`, typed on the
coproduct presentation of the chain groups. -/
noncomputable abbrev chainMap {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    Cgrp X n ⟶ Cgrp Y n :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map f).f n

/-- The boundary of a generator is the alternating sum of its faces. -/
lemma gen_d (X : TopCat.{0}) (n : ℕ) (a : Idx X (n + 1)) :
    gen X (n + 1) a ≫ bnd X n =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • gen X n ((TopCat.toSSet.obj X).δ k a) := by
  show gen X (n + 1) a ≫ (AlternatingFaceMapComplex.obj (SOb X)).d (n + 1) n = _
  rw [AlternatingFaceMapComplex.obj_d_eq, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.comp_zsmul]
  congr 1
  show gen X (n + 1) a ≫ Sigma.map' (f := fun _ : Idx X (n + 1) => ModuleCat.of ℤ ℤ)
      (g := fun _ : Idx X n => ModuleCat.of ℤ ℤ)
      ((TopCat.toSSet.obj X).δ k) (fun _ => 𝟙 _) = _
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- The induced chain map sends a generator to the generator of the
postcomposed simplex. -/
lemma gen_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Idx X n) :
    gen X n a ≫ chainMap f n = gen Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) a) := by
  show gen X n a ≫ Sigma.map' (f := fun _ : Idx X n => ModuleCat.of ℤ ℤ)
      (g := fun _ : Idx Y n => ModuleCat.of ℤ ℤ)
      ((TopCat.toSSet.map f).app (op ⦋n⦌)) (fun _ => 𝟙 _) = _
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- The prism operator sends a generator to the signed prism sum. -/
lemma gen_prismOp {X Y : TopCat.{0}} (H : C(I × X, Y)) (n : ℕ)
    (prisms : Fin (n + 1) →
      C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I))
    (s : Idx X n) :
    gen X n s ≫ prismOp H n prisms = Pgen H n prisms s :=
  Sigma.ι_desc _ _

/-! ## Stage 4c: the alternating double-sum cancellation (abstract form)

The combinatorial heart of Hatcher's Theorem 2.10: given two doubly-indexed
families related by the prism face identities (`hle`, `hgt` off the diagonal,
`hcancel` on the two diagonals), the signed double sums collapse to the two
end terms.  Here `G i j` abstracts the `j`-th face of the `i`-th prism of a
simplex (`∂P`), and `G' k i'` abstracts the `i'`-th prism of the `k`-th face
(`P∂`).
-/

/-- Telescoping over `Fin`: if `S i.castSucc = D i.succ` then the sum of the
differences `D i - S i` collapses to `D 0 - S last`. -/
lemma sum_sub_telescope {M : Type*} [AddCommGroup M] :
    ∀ (m : ℕ) (D S : Fin (m + 1) → M), (∀ i : Fin m, S i.castSucc = D i.succ) →
      ∑ i, (D i - S i) = D 0 - S (Fin.last m)
  | 0, D, S, _ => by simp
  | m + 1, D, S, h => by
    rw [Fin.sum_univ_succ,
      sum_sub_telescope m (fun i => D i.succ) (fun i => S i.succ) (fun i => by
        show S i.castSucc.succ = D i.succ.succ
        rw [Fin.succ_castSucc]
        exact h i.succ)]
    have h0 : S 0 = D 1 := by simpa using h 0
    have hlast : (Fin.last m).succ = Fin.last (m + 1) := rfl
    rw [h0, hlast]
    simp only [Fin.succ_zero_eq_one]
    abel

/-- The four-way partition of the `∂P` index set `Fin (n+2) × Fin (n+3)`:
below the diagonal, the diagonal, the superdiagonal, above the
superdiagonal. -/
lemma sum_prod_partition {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : Fin (n + 2) × Fin (n + 3) → M) :
    ∑ p, F p =
      ((∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) < (p.1 : ℕ))}, F p) +
        ∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ))}, F p) +
      ((∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ) + 1)}, F p) +
        ∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.1 : ℕ) + 1 < (p.2 : ℕ))}, F p) := by
  classical
  have h2 : (∑ p ∈ Finset.univ.filter (fun p : Fin (n + 2) × Fin (n + 3) =>
      ¬ (p.2 : ℕ) < (p.1 : ℕ) ∧ ¬ (p.2 : ℕ) = (p.1 : ℕ)), F p) =
      (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ) + 1)}, F p) +
        ∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.1 : ℕ) + 1 < (p.2 : ℕ))}, F p := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 3) =>
        ¬ (p.2 : ℕ) < (p.1 : ℕ) ∧ ¬ (p.2 : ℕ) = (p.1 : ℕ))
      (fun p => (p.2 : ℕ) = (p.1 : ℕ) + 1) F]
    congr 1
    · apply Finset.sum_congr _ fun _ _ => rfl
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      omega
    · apply Finset.sum_congr _ fun _ _ => rfl
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      omega
  have h1 : (∑ p ∈ Finset.univ.filter (fun p : Fin (n + 2) × Fin (n + 3) =>
      ¬ (p.2 : ℕ) < (p.1 : ℕ)), F p) =
      (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ))}, F p) +
        ((∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ) + 1)}, F p) +
          ∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.1 : ℕ) + 1 < (p.2 : ℕ))}, F p) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun p : Fin (n + 2) × Fin (n + 3) => ¬ (p.2 : ℕ) < (p.1 : ℕ))
      (fun p => (p.2 : ℕ) = (p.1 : ℕ)) F]
    congr 1
    · apply Finset.sum_congr _ fun _ _ => rfl
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      omega
    · rw [← h2]
      apply Finset.sum_congr _ fun _ _ => rfl
      rw [Finset.filter_filter]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 2) × Fin (n + 3) => (p.2 : ℕ) < (p.1 : ℕ)) F, h1]
  abel

/-- The two-way partition of the `P∂` index set `Fin (n+2) × Fin (n+1)`. -/
lemma sum_prod_partition' {M : Type*} [AddCommGroup M] (n : ℕ)
    (F : Fin (n + 2) × Fin (n + 1) → M) :
    ∑ q, F q =
      (∑ q ∈ {q : Fin (n + 2) × Fin (n + 1) | ((q.1 : ℕ) ≤ (q.2 : ℕ))}, F q) +
        ∑ q ∈ {q : Fin (n + 2) × Fin (n + 1) | ((q.2 : ℕ) < (q.1 : ℕ))}, F q := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun q : Fin (n + 2) × Fin (n + 1) => (q.1 : ℕ) ≤ (q.2 : ℕ)) F]
  congr 1
  apply Finset.sum_congr _ fun _ _ => rfl
  apply Finset.filter_congr
  intro q _
  omega

/-- Hatcher's Theorem 2.10 alternating double-sum cancellation, abstractly:
if `G` (the faces of the prisms, i.e. `∂P`) and `G'` (the prisms of the
faces, i.e. `P∂`) satisfy the three prism face identities, the two signed
double sums collapse to `G 0 0 - G last last` (i.e. `g♯ - f♯`). -/
lemma prism_sum_cancellation {M : Type*} [AddCommGroup M] (n : ℕ)
    (G : Fin (n + 2) → Fin (n + 3) → M) (G' : Fin (n + 2) → Fin (n + 1) → M)
    (hle : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)), (j : ℕ) ≤ (i : ℕ) →
      G i.succ j.castSucc = G' j i)
    (hgt : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)), (i : ℕ) < (j : ℕ) →
      G i.castSucc j.succ = G' j i)
    (hcancel : ∀ i : Fin (n + 1),
      G i.castSucc i.succ.castSucc = G i.succ i.succ.castSucc) :
    ((∑ i : Fin (n + 2), ∑ j : Fin (n + 3), (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) • G i j) +
      ∑ k : Fin (n + 2), ∑ i' : Fin (n + 1), (-1 : ℤ) ^ ((k : ℕ) + (i' : ℕ)) • G' k i') =
      G 0 0 - G (Fin.last (n + 1)) (Fin.last (n + 2)) := by
  classical
  have hB : (∑ i : Fin (n + 2), ∑ j : Fin (n + 3),
      (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) • G i j) =
      ∑ p : Fin (n + 2) × Fin (n + 3), (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2 := by
    rw [← Finset.sum_product']
    rfl
  have hA : (∑ k : Fin (n + 2), ∑ i' : Fin (n + 1),
      (-1 : ℤ) ^ ((k : ℕ) + (i' : ℕ)) • G' k i') =
      ∑ q : Fin (n + 2) × Fin (n + 1), (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ)) • G' q.1 q.2 := by
    rw [← Finset.sum_product']
    rfl
  rw [hB, hA,
    sum_prod_partition n (fun p => (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2),
    sum_prod_partition' n (fun q => (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ)) • G' q.1 q.2)]
  -- the below-diagonal `∂P` terms cancel the `k ≤ i'` half of `P∂`
  have e1 : (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) < (p.1 : ℕ))},
      (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2) =
      -∑ q ∈ {q : Fin (n + 2) × Fin (n + 1) | ((q.1 : ℕ) ≤ (q.2 : ℕ))},
        (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ)) • G' q.1 q.2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij'
      (i := fun p hp => ((⟨(p.2 : ℕ), by
        simp only [Finset.mem_filter_univ] at hp; omega⟩ : Fin (n + 2)),
        (⟨(p.1 : ℕ) - 1, by
          simp only [Finset.mem_filter_univ] at hp; omega⟩ : Fin (n + 1))))
      (j := fun q hq => (q.2.succ, q.1.castSucc)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp ⊢
      omega
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq ⊢
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      ext
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq
      ext
      · simp only [Fin.val_castSucc]
      · simp only [Fin.val_succ]; omega
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      set k : Fin (n + 2) := ⟨(p.2 : ℕ), by omega⟩ with hk
      set i' : Fin (n + 1) := ⟨(p.1 : ℕ) - 1, by omega⟩ with hi'
      have hp1 : p.1 = i'.succ := by ext; simp only [Fin.val_succ, hi']; omega
      have hp2 : p.2 = k.castSucc := by ext; simp only [Fin.val_castSucc, hk]
      rw [hp1, hp2, hle i' k (by simp only [hk, hi']; omega)]
      have hsign : ((i'.succ : ℕ) + (k.castSucc : ℕ)) = ((k : ℕ) + (i' : ℕ)) + 1 := by
        simp only [Fin.val_succ, Fin.val_castSucc]; omega
      rw [hsign, pow_succ, mul_neg_one, neg_smul]
  -- the above-superdiagonal `∂P` terms cancel the `i' < k` half of `P∂`
  have e2 : (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.1 : ℕ) + 1 < (p.2 : ℕ))},
      (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2) =
      -∑ q ∈ {q : Fin (n + 2) × Fin (n + 1) | ((q.2 : ℕ) < (q.1 : ℕ))},
        (-1 : ℤ) ^ ((q.1 : ℕ) + (q.2 : ℕ)) • G' q.1 q.2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij'
      (i := fun p hp => ((⟨(p.2 : ℕ) - 1, by
        simp only [Finset.mem_filter_univ] at hp; omega⟩ : Fin (n + 2)),
        (⟨(p.1 : ℕ), by
          simp only [Finset.mem_filter_univ] at hp; omega⟩ : Fin (n + 1))))
      (j := fun q hq => (q.2.castSucc, q.1.succ)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp ⊢
      omega
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq ⊢
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      ext
      · simp only [Fin.val_castSucc]
      · simp only [Fin.val_succ]; omega
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq
      ext
      · simp only [Fin.val_succ]; omega
      · simp only [Fin.val_castSucc]
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      set k : Fin (n + 2) := ⟨(p.2 : ℕ) - 1, by omega⟩ with hk
      set i' : Fin (n + 1) := ⟨(p.1 : ℕ), by omega⟩ with hi'
      have hp1 : p.1 = i'.castSucc := by ext; simp only [Fin.val_castSucc, hi']
      have hp2 : p.2 = k.succ := by ext; simp only [Fin.val_succ, hk]; omega
      rw [hp1, hp2, hgt i' k (by simp only [hk, hi']; omega)]
      have hsign : ((i'.castSucc : ℕ) + (k.succ : ℕ)) = ((k : ℕ) + (i' : ℕ)) + 1 := by
        simp only [Fin.val_succ, Fin.val_castSucc]; omega
      rw [hsign, pow_succ, mul_neg_one, neg_smul]
  -- the diagonal terms
  have e3 : (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ))},
      (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2) =
      ∑ i : Fin (n + 2), G i i.castSucc := by
    refine Finset.sum_bij' (i := fun p _ => p.1)
      (j := fun i _ => (i, i.castSucc)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · intro i _
      simp only [Finset.mem_filter_univ, Fin.val_castSucc]
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      ext
      · rfl
      · simp only [Fin.val_castSucc]; omega
    · intro i _; rfl
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      have hp2 : p.2 = p.1.castSucc := by ext; simp only [Fin.val_castSucc]; omega
      rw [hp2]
      have : (-1 : ℤ) ^ ((p.1 : ℕ) + (p.1.castSucc : ℕ)) = 1 :=
        Even.neg_one_pow (by simp only [Fin.val_castSucc]; exact ⟨(p.1 : ℕ), rfl⟩)
      rw [this, one_smul]
  -- the superdiagonal terms
  have e4 : (∑ p ∈ {p : Fin (n + 2) × Fin (n + 3) | ((p.2 : ℕ) = (p.1 : ℕ) + 1)},
      (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) • G p.1 p.2) =
      ∑ i : Fin (n + 2), -G i i.succ := by
    refine Finset.sum_bij' (i := fun p _ => p.1)
      (j := fun i _ => (i, i.succ)) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact Finset.mem_univ _
    · intro i _
      simp only [Finset.mem_filter_univ, Fin.val_succ]
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      ext
      · rfl
      · simp only [Fin.val_succ]; omega
    · intro i _; rfl
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      have hp2 : p.2 = p.1.succ := by ext; simp only [Fin.val_succ]; omega
      rw [hp2]
      have : (-1 : ℤ) ^ ((p.1 : ℕ) + (p.1.succ : ℕ)) = -1 :=
        Odd.neg_one_pow (by simp only [Fin.val_succ]; exact ⟨(p.1 : ℕ), by omega⟩)
      rw [this, neg_one_smul]
  -- the telescope
  have e5 : (∑ i : Fin (n + 2), G i i.castSucc) + (∑ i : Fin (n + 2), -G i i.succ) =
      G 0 0 - G (Fin.last (n + 1)) (Fin.last (n + 2)) := by
    rw [← Finset.sum_add_distrib]
    have := sum_sub_telescope (n + 1) (fun i : Fin (n + 2) => G i i.castSucc)
      (fun i : Fin (n + 2) => G i i.succ) (fun i => by
        show G i.castSucc i.castSucc.succ = G i.succ i.succ.castSucc
        rw [Fin.succ_castSucc]
        exact hcancel i)
    simp only [sub_eq_add_neg] at this
    rw [this, show ((Fin.last (n + 1)).succ : Fin (n + 3)) = Fin.last (n + 2) from rfl]
    simp only [Fin.castSucc_zero, sub_eq_add_neg]
  rw [e1, e2, e3, e4, ← e5]
  abel

/-! ## Stage 4d: transporting the face identities to singular simplices -/

section FaceTransport

variable {X Y : TopCat.{0}}

/-- A face identity between prism maps transports to the corresponding
identity of singular simplices: if `pr ∘ face j = (face j' × id) ∘ pr'`,
then the `j`-th face of the prism simplex on `s` is the prism simplex of
the `j'`-th face of `s`. -/
lemma δ_prismSimplex_of_face (H : C(I × X, Y)) {n : ℕ}
    (pr : C(stdSimplex ℝ (Fin (n + 3)), stdSimplex ℝ (Fin (n + 2)) × I))
    (pr' : C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I))
    {j : Fin (n + 3)} {j' : Fin (n + 2)}
    (hface : pr.comp (face j) = ((face j').prodMap (ContinuousMap.id I)).comp pr')
    (s : Idx X (n + 1)) :
    (TopCat.toSSet.obj Y).δ j (prismSimplex H (n + 1) pr s) =
      prismSimplex H n pr' ((TopCat.toSSet.obj X).δ j' s) := by
  apply (Y.toSSetObjEquiv (op ⦋n + 1⦌)).injective
  rw [toSSetObjEquiv_δ, prismSimplex, Equiv.apply_symm_apply, prismSimplex,
    Equiv.apply_symm_apply, toSSetObjEquiv_δ]
  ext t
  have h := ContinuousMap.congr_fun hface t
  simp only [ContinuousMap.comp_apply] at h ⊢
  exact (congrArg (fun z => H (ContinuousMap.prodSwap
    (((X.toSSetObjEquiv (op ⦋n + 1⦌) s).prodMap (ContinuousMap.id I)) z))) h).trans rfl

/-- Two prism maps agreeing on a face give equal faces of the prism
simplices (the cancelling pairs of `∂P`). -/
lemma δ_prismSimplex_congr (H : C(I × X, Y)) {n : ℕ}
    (pr pr' : C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1)) × I))
    {j : Fin (n + 2)} (hface : pr.comp (face j) = pr'.comp (face j)) (s : Idx X n) :
    (TopCat.toSSet.obj Y).δ j (prismSimplex H n pr s) =
      (TopCat.toSSet.obj Y).δ j (prismSimplex H n pr' s) := by
  apply (Y.toSSetObjEquiv (op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_δ, prismSimplex, Equiv.apply_symm_apply,
    prismSimplex, Equiv.apply_symm_apply]
  ext t
  have h := ContinuousMap.congr_fun hface t
  simp only [ContinuousMap.comp_apply] at h ⊢
  exact congrArg (fun z => H (ContinuousMap.prodSwap
    (((X.toSSetObjEquiv (op ⦋n⦌) s).prodMap (ContinuousMap.id I)) z))) h

/-- The `0`-th face of the `0`-th prism simplex is the pushforward of the
simplex along the end `F₁` of the homotopy (the top of the prism). -/
lemma δ_prismSimplex_top {F₀ F₁ : X ⟶ Y} (Ho : ContinuousMap.Homotopy F₀.hom F₁.hom)
    (n : ℕ) (s : Idx X n) :
    (TopCat.toSSet.obj Y).δ 0 (prismSimplex Ho.toContinuousMap n (prism 0) s) =
      (TopCat.toSSet.map F₁).app (op ⦋n⦌) s := by
  apply (Y.toSSetObjEquiv (op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, prismSimplex, Equiv.apply_symm_apply, toSSetObjEquiv_map]
  ext t
  have h := ContinuousMap.congr_fun (prism_comp_face_top (n := n)) t
  simp only [ContinuousMap.comp_apply] at h ⊢
  exact (congrArg (fun z => Ho.toContinuousMap (ContinuousMap.prodSwap
    (((X.toSSetObjEquiv (op ⦋n⦌) s).prodMap (ContinuousMap.id I)) z))) h).trans
    (Ho.apply_one _)

/-- The last face of the last prism simplex is the pushforward of the
simplex along the start `F₀` of the homotopy (the bottom of the prism). -/
lemma δ_prismSimplex_bot {F₀ F₁ : X ⟶ Y} (Ho : ContinuousMap.Homotopy F₀.hom F₁.hom)
    (n : ℕ) (s : Idx X n) :
    (TopCat.toSSet.obj Y).δ (Fin.last (n + 1))
        (prismSimplex Ho.toContinuousMap n (prism (Fin.last n)) s) =
      (TopCat.toSSet.map F₀).app (op ⦋n⦌) s := by
  apply (Y.toSSetObjEquiv (op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, prismSimplex, Equiv.apply_symm_apply, toSSetObjEquiv_map]
  ext t
  have h := ContinuousMap.congr_fun (prism_comp_face_bot (n := n)) t
  simp only [ContinuousMap.comp_apply] at h ⊢
  exact (congrArg (fun z => Ho.toContinuousMap (ContinuousMap.prodSwap
    (((X.toSSetObjEquiv (op ⦋n⦌) s).prodMap (ContinuousMap.id I)) z))) h).trans
    (Ho.apply_zero _)

end FaceTransport

/-! ## Stage 4e: the chain homotopy identity `∂P + P∂ = g♯ − f♯` -/

section ChainHomotopyIdentity

variable {X Y : TopCat.{0}} {F₀ F₁ : X ⟶ Y}

/-- The chain homotopy identity in positive degrees:
`∂ ∘ P + P ∘ ∂ = (F₁)♯ − (F₀)♯` on the degree-`(n+1)` chain group. -/
lemma prism_chain_homotopy_succ (Ho : ContinuousMap.Homotopy F₀.hom F₁.hom) (n : ℕ) :
    bnd X n ≫ prismOp Ho.toContinuousMap n prism +
        prismOp Ho.toContinuousMap (n + 1) prism ≫ bnd Y (n + 1) =
      chainMap F₁ (n + 1) - chainMap F₀ (n + 1) := by
  apply Sigma.hom_ext
  intro s
  have hL1 : gen X (n + 1) s ≫ (bnd X n ≫ prismOp Ho.toContinuousMap n prism) =
      ∑ k : Fin (n + 2), ∑ i' : Fin (n + 1), (-1 : ℤ) ^ ((k : ℕ) + (i' : ℕ)) •
        gen Y (n + 1) (prismSimplex Ho.toContinuousMap n (prism i')
          ((TopCat.toSSet.obj X).δ k s)) := by
    rw [← Category.assoc, gen_d, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Preadditive.zsmul_comp, gen_prismOp, Pgen, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [smul_smul, ← pow_add]
  have hL2 : gen X (n + 1) s ≫ (prismOp Ho.toContinuousMap (n + 1) prism ≫ bnd Y (n + 1)) =
      ∑ i : Fin (n + 2), ∑ j : Fin (n + 3), (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
        gen Y (n + 1) ((TopCat.toSSet.obj Y).δ j
          (prismSimplex Ho.toContinuousMap (n + 1) (prism i) s)) := by
    rw [← Category.assoc, gen_prismOp, Pgen, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, gen_d, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_add]
  rw [Preadditive.comp_add, hL1, hL2, Preadditive.comp_sub, gen_map, gen_map,
    add_comm (∑ k : Fin (n + 2), ∑ i' : Fin (n + 1), (-1 : ℤ) ^ ((k : ℕ) + (i' : ℕ)) •
      gen Y (n + 1) (prismSimplex Ho.toContinuousMap n (prism i')
        ((TopCat.toSSet.obj X).δ k s)))]
  refine Eq.trans (prism_sum_cancellation n
    (fun i j => gen Y (n + 1) ((TopCat.toSSet.obj Y).δ j
      (prismSimplex Ho.toContinuousMap (n + 1) (prism i) s)))
    (fun k i' => gen Y (n + 1) (prismSimplex Ho.toContinuousMap n (prism i')
      ((TopCat.toSSet.obj X).δ k s)))
    (fun i j hij => congrArg (gen Y (n + 1)) (δ_prismSimplex_of_face
      Ho.toContinuousMap (prism i.succ) (prism i)
      (prism_comp_face_of_le (Fin.le_def.mpr (by simpa using hij))) s))
    (fun i j hij => congrArg (gen Y (n + 1)) (δ_prismSimplex_of_face
      Ho.toContinuousMap (prism i.castSucc) (prism i)
      (prism_comp_face_of_gt (Fin.lt_def.mpr (by simpa using hij))) s))
    (fun i => congrArg (gen Y (n + 1)) (δ_prismSimplex_congr
      Ho.toContinuousMap (prism i.castSucc) (prism i.succ)
      (prism_comp_face_cancel i) s))) ?_
  congr 1
  · exact congrArg (gen Y (n + 1)) (δ_prismSimplex_top Ho (n + 1) s)
  · exact congrArg (gen Y (n + 1)) (δ_prismSimplex_bot Ho (n + 1) s)

/-- The chain homotopy identity in degree `0`:
`∂ ∘ P = (F₁)♯ − (F₀)♯` on the degree-`0` chain group. -/
lemma prism_chain_homotopy_zero (Ho : ContinuousMap.Homotopy F₀.hom F₁.hom) :
    prismOp Ho.toContinuousMap 0 prism ≫ bnd Y 0 = chainMap F₁ 0 - chainMap F₀ 0 := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, gen_prismOp, Pgen, Fin.sum_univ_one, Preadditive.comp_sub,
    gen_map, gen_map]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [gen_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [congrArg (gen Y 0) (δ_prismSimplex_top Ho 0 s)]
  rw [congrArg (gen Y 0) (show (TopCat.toSSet.obj Y).δ (1 : Fin 2)
      (prismSimplex Ho.toContinuousMap 0 (prism (0 : Fin 1)) s) =
      (TopCat.toSSet.map F₀).app (op ⦋0⦌) s from δ_prismSimplex_bot Ho 0 s)]
  abel

end ChainHomotopyIdentity

/-! ## Stage 5: packaging and homotopy invariance of singular homology -/

section Packaging

variable {X Y : TopCat.{0}}

/-- The singular chain map induced by a continuous map. -/
noncomputable abbrev sChainMap (f : X ⟶ Y) : SC X ⟶ SC Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map f

/-- A homotopy of continuous maps induces a chain homotopy of the induced
maps of singular chain complexes, via the prism operator. -/
noncomputable def prismHomotopy {F₀ F₁ : X ⟶ Y}
    (Ho : ContinuousMap.Homotopy F₀.hom F₁.hom) :
    Homotopy (sChainMap F₀) (sChainMap F₁) where
  hom i j :=
    if h : i + 1 = j then
      (-prismOp Ho.toContinuousMap i prism) ≫ eqToHom (by subst h; rfl)
    else 0
  zero i j hij := by
    rw [dif_neg]
    intro h
    exact hij (by simpa using h)
  comm i := by
    match i with
    | 0 =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      rw [dif_pos rfl, eqToHom_refl, Category.comp_id, Preadditive.neg_comp]
      show chainMap F₀ 0 =
        0 + -prismOp Ho.toContinuousMap 0 prism ≫ bnd Y 0 + chainMap F₁ 0
      have h0 := prism_chain_homotopy_zero Ho
      rw [eq_sub_iff_add_eq] at h0
      rw [← h0]
      abel
    | n + 1 =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      rw [dif_pos rfl, dif_pos rfl, eqToHom_refl, eqToHom_refl, Category.comp_id,
        Category.comp_id, Preadditive.neg_comp, Preadditive.comp_neg]
      show chainMap F₀ (n + 1) =
        -bnd X n ≫ prismOp Ho.toContinuousMap n prism +
          -prismOp Ho.toContinuousMap (n + 1) prism ≫ bnd Y (n + 1) +
          chainMap F₁ (n + 1)
      have h0 := prism_chain_homotopy_succ Ho n
      rw [eq_sub_iff_add_eq] at h0
      rw [← h0]
      abel

/-- **Homotopy invariance of singular homology**: homotopic continuous maps
induce the same map on singular homology with `ℤ` coefficients
(Hatcher, Theorem 2.10). -/
theorem homotopic_maps_induce_same_homology
    {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).map g :=
  (prismHomotopy h).homologyMap_eq n

/-- A homotopy equivalence of spaces induces a homotopy equivalence of
singular chain complexes. -/
noncomputable def chainHomotopyEquiv (h : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (SC X) (SC Y) where
  hom := sChainMap (TopCat.ofHom h.toFun)
  inv := sChainMap (TopCat.ofHom h.invFun)
  homotopyHomInvId :=
    (Homotopy.ofEq ((CategoryTheory.Functor.map_comp _ _ _).symm)).trans
      ((prismHomotopy (F₀ := TopCat.ofHom h.toFun ≫ TopCat.ofHom h.invFun)
          (F₁ := 𝟙 X) h.left_inv.some).trans
        (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))
  homotopyInvHomId :=
    (Homotopy.ofEq ((CategoryTheory.Functor.map_comp _ _ _).symm)).trans
      ((prismHomotopy (F₀ := TopCat.ofHom h.invFun ≫ TopCat.ofHom h.toFun)
          (F₁ := 𝟙 Y) h.right_inv.some).trans
        (Homotopy.ofEq (CategoryTheory.Functor.map_id _ _)))

/-- A homotopy equivalence of spaces induces an isomorphism on singular
homology with `ℤ` coefficients. -/
noncomputable def homotopyEquiv_homology_iso
    (h : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj X ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ ℤ)).obj Y :=
  (chainHomotopyEquiv h).toHomologyIso n

/-- The map on singular homology induced by (the forward map of) a homotopy
equivalence is an isomorphism. -/
theorem isIso_homology_map_of_homotopyEquiv
    (h : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom h.toFun)) :=
  inferInstanceAs (IsIso ((homotopyEquiv_homology_iso h n).hom))

end Packaging

/-! ### Frontier note: CLOSED (all stages complete)

All five stages are complete and axiom-clean (only `propext`, `Classical.choice`,
`Quot.sound`); the module builds green with 0 `sorry`.

* Stages 1–3: the topological prism maps (`prism`), the five face identities
  (`prism_comp_face_top`, `prism_comp_face_bot`, `prism_comp_face_cancel`,
  `prism_comp_face_of_le`, `prism_comp_face_of_gt`), and the chain-level
  prism operator (`prismOp`).
* Stage 4: generator normal forms (`gen_d`, `gen_map`, `gen_prismOp`), the
  abstract alternating double-sum cancellation (`prism_sum_cancellation`,
  built from `sum_sub_telescope`, `sum_prod_partition`,
  `sum_prod_partition'`), the transported face identities
  (`δ_prismSimplex_of_face`, `δ_prismSimplex_congr`, `δ_prismSimplex_top`,
  `δ_prismSimplex_bot`), and the chain homotopy identity
  `∂ ∘ P + P ∘ ∂ = (F₁)♯ − (F₀)♯` in every degree
  (`prism_chain_homotopy_succ`, `prism_chain_homotopy_zero`).
* Stage 5: `prismHomotopy : Homotopy (sChainMap F₀) (sChainMap F₁)`,
  the main theorem `homotopic_maps_induce_same_homology` (homotopy
  invariance of Mathlib singular homology with `ℤ` coefficients,
  Hatcher Theorem 2.10), plus the homotopy-equivalence corollaries
  `chainHomotopyEquiv`, `homotopyEquiv_homology_iso`, and
  `isIso_homology_map_of_homotopyEquiv`.

Nothing remains on this frontier.  Possible follow-ups (new scope, not
required here): coefficients in an arbitrary `R`-module (the whole argument
is coefficient-independent; only the `ModuleCat ℤ` instances would change),
and upstreaming to Mathlib.
-/

end SingularPrism
end Foundation
end IndisputableMonolith
