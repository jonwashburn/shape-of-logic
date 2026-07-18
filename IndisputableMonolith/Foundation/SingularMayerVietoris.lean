/-
Mayer-Vietoris for Mathlib's singular homology (with `ℤ` coefficients).

Layer 4 of the excision spine (layer 1: `SingularPrism`, homotopy invariance;
layer 2: `SingularPair`, the LES of a pair; layer 3: `SingularSubdivision`,
barycentric subdivision and the small-simplices theorem).

## Contents (staged)

* Stage 1: for `U V : Set X`, the small-chains subcomplex `SSC U V` of the
  singular chain complex `SC X`, generated in each degree by the singular
  simplices whose range lies in `U` or in `V`; the degreewise split-mono
  inclusion `smallι : SSC U V ⟶ SC X`.
* Stage 2: the small-chains theorem (Hatcher, Prop 2.21): for open `U, V`
  covering `X` the inclusion induces an isomorphism on homology in every
  degree (`smallι_isIso_homologyMap`, `smallChainsHomologyIso`), via the
  subdivision operators and the telescoped homotopies of
  `SingularSubdivision`.
* Stage 3: the Mayer-Vietoris short exact sequence of chain complexes
  `0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0` (`mvSES`,
  `mvSES_shortExact`; no openness/covering hypotheses needed).  Left map
  `x ↦ (i_* x, −j_* x)` (`mvα`), right map `(a, b) ↦ k_* a + l_* b`
  (`mvβ`); degreewise exactness by coordinate tracking on the free basis
  (`coordAt`, `suppOf`, `mv_middle_exact`).
* Stage 4: the honest Mayer-Vietoris long exact sequence on Mathlib
  singular homology of the spaces, with `H_n(SSC)` transported to `H_n(X)`
  across the Stage-2 isomorphism and `H_n(C(U) ⊞ C(V))` split by additivity
  of the homology functor (`homologyBiprodIso`):
  `⋯ → H_n(U ∩ V) → H_n(U) ⊞ H_n(V) → H_n(X) → H_{n−1}(U ∩ V) → ⋯`.
  Maps `mvPair` (from the space-level inclusions `U ∩ V ↪ U, V`), `mvSum`
  (from `U, V ↪ X`), connecting map `mvδ`; exactness `mv_exact₁/₂/₃`;
  degree-0 tail `mvSum_epi_zero`; sanity lock `mvSum_epi_of_left_univ`
  (for `U = univ` the sum map is epi in every degree, since its first
  component comes from the homeomorphism `univ ≃ X`).

## Frontier (layer 5, not yet formalized)

* `H_*(Sⁿ)` by Mayer-Vietoris induction: cover `Sⁿ` by two open
  hemispheres `U, V` (each contractible, `U ∩ V ≃ Sⁿ⁻¹` up to homotopy),
  use layer-1 homotopy invariance to evaluate the `H_*(U)`, `H_*(V)` spots
  and this file's `mv_exact₁/₂/₃` + `mvδ` to walk the induction.  Missing
  ingredients: `H_*(pt)` (a direct computation on the singular complex of
  a point), homotopy equivalences between the hemispheres/pt and
  `U ∩ V`/`Sⁿ⁻¹`, and the two-space case split in degree `0`
  (`mvSum_epi_zero` supplies the tail).

## Instance-diamond note (load-bearing)

For `R = ℤ` every `ModuleCat ℤ` carrier has two `Module ℤ` instances
(`isModule` and `AddCommGroup.toIntModule`), propositionally but not
definitionally equal, and synthesis prefers the generic one. This file
deprioritizes `AddCommGroup.toIntModule` and `SubNegMonoid.toZSMul` locally;
any continuation working elementwise in these chain groups must keep those
two local-attribute lines.
-/
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import IndisputableMonolith.Foundation.SingularPrism
import IndisputableMonolith.Foundation.SingularPair
import IndisputableMonolith.Foundation.SingularSubdivision

namespace IndisputableMonolith
namespace Foundation
namespace SingularMayerVietoris

open CategoryTheory Category Limits AlgebraicTopology Simplicial Opposite
open SingularPrism SingularSubdivision

attribute [local instance 10] Classical.decEq

/- For `R = ℤ` every carrier has two `Module ℤ` instances: the canonical one
recorded in the `ModuleCat` structure and the generic
`AddCommGroup.toIntModule`. They are propositionally but not definitionally
equal, and instance synthesis prefers the generic one, which breaks
elementwise reasoning. Deprioritizing the generic instance restores the
canonical one everywhere in this file. -/
attribute [local instance 0] AddCommGroup.toIntModule
attribute [local instance 0] SubNegMonoid.toZSMul

/-! ## Stage 1: the small-chains subcomplex -/

variable {X : TopCat.{0}}

/-- A singular `n`-simplex of `X` is *small* (relative to the pair of subsets
`U, V`) when its range lies in `U` or in `V`. -/
def Small (U V : Set X) {n : ℕ} (s : Idx X n) : Prop :=
  Set.range ⇑(simplexEquiv X n s) ⊆ U ∨ Set.range ⇑(simplexEquiv X n s) ⊆ V

/-- Faces of small simplices are small. -/
lemma Small.δ {U V : Set X} {n : ℕ} {s : Idx X (n + 1)} (hs : Small U V s)
    (k : Fin (n + 2)) : Small U V ((TopCat.toSSet.obj X).δ k s) := by
  have hrange : Set.range ⇑(simplexEquiv X n ((TopCat.toSSet.obj X).δ k s)) ⊆
      Set.range ⇑(simplexEquiv X (n + 1) s) := by
    rw [simplexEquiv_δ, ContinuousMap.coe_comp]
    exact Set.range_comp_subset_range _ _
  rcases hs with h | h
  · exact Or.inl (hrange.trans h)
  · exact Or.inr (hrange.trans h)

variable (U V : Set X)

/-- The index type of the degree-`n` small chain group: small singular
`n`-simplices. -/
def SIdx (n : ℕ) : Type := { s : Idx X n // Small U V s }

/-- The degree-`n` small chain group: the free `ℤ`-module on the small
singular `n`-simplices, presented as a coproduct. -/
noncomputable abbrev sCgrp (n : ℕ) : ModuleCat.{0} ℤ :=
  ∐ fun _ : SIdx U V n => ModuleCat.of ℤ ℤ

/-- The generator of the small chain group attached to a small simplex. -/
noncomputable def sgen (n : ℕ) (t : SIdx U V n) : ModuleCat.of ℤ ℤ ⟶ sCgrp U V n :=
  Sigma.ι (fun _ : SIdx U V n => ModuleCat.of ℤ ℤ) t

/-- The degree-`n` inclusion of the small chain group into the singular
chain group. -/
noncomputable def sInc (n : ℕ) : sCgrp U V n ⟶ Cgrp X n :=
  Sigma.desc fun t => gen X n t.1

lemma sgen_sInc {n : ℕ} (t : SIdx U V n) :
    sgen U V n t ≫ sInc U V n = gen X n t.1 :=
  Sigma.ι_desc _ _

open Classical in
/-- The retraction of the degree-`n` inclusion: a small simplex goes to its
small generator, everything else goes to `0`. -/
noncomputable def sRet (n : ℕ) : Cgrp X n ⟶ sCgrp U V n :=
  Sigma.desc fun s =>
    if h : Small U V s then sgen U V n ⟨s, h⟩ else 0

lemma sInc_comp_sRet (n : ℕ) : sInc U V n ≫ sRet U V n = 𝟙 (sCgrp U V n) := by
  apply Sigma.hom_ext
  intro t
  show sgen U V n t ≫ sInc U V n ≫ sRet U V n = sgen U V n t ≫ 𝟙 (sCgrp U V n)
  rw [Category.comp_id, ← assoc, sgen_sInc]
  show Sigma.ι (fun _ : Idx X n => ModuleCat.of ℤ ℤ) t.1 ≫ sRet U V n = sgen U V n t
  unfold sRet
  rw [Sigma.ι_desc, dif_pos t.2]
  congr 1

/-- The degree-`n` inclusion is a (split) monomorphism. -/
lemma sInc_mono (n : ℕ) : Mono (sInc U V n) :=
  mono_of_mono_fac (sInc_comp_sRet U V n)

/-- The boundary of the small chain complex: the alternating sum of faces,
which are small by `Small.δ`. -/
noncomputable def sBnd (n : ℕ) : sCgrp U V (n + 1) ⟶ sCgrp U V n :=
  Sigma.desc fun t => ∑ k : Fin (n + 2),
    (-1 : ℤ) ^ (k : ℕ) • sgen U V n ⟨(TopCat.toSSet.obj X).δ k t.1, t.2.δ k⟩

lemma sgen_sBnd {n : ℕ} (t : SIdx U V (n + 1)) :
    sgen U V (n + 1) t ≫ sBnd U V n = ∑ k : Fin (n + 2),
      (-1 : ℤ) ^ (k : ℕ) • sgen U V n ⟨(TopCat.toSSet.obj X).δ k t.1, t.2.δ k⟩ :=
  Sigma.ι_desc _ _

/-- The inclusion intertwines the small boundary and the singular boundary. -/
lemma sBnd_comp_sInc (n : ℕ) :
    sBnd U V n ≫ sInc U V n = sInc U V (n + 1) ≫ bnd X n := by
  apply Sigma.hom_ext
  intro t
  rw [← assoc, ← assoc]
  show (sgen U V (n + 1) t ≫ sBnd U V n) ≫ sInc U V n =
    (sgen U V (n + 1) t ≫ sInc U V (n + 1)) ≫ bnd X n
  rw [sgen_sBnd, sgen_sInc, gen_d, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Preadditive.zsmul_comp]
  congr 1
  exact sgen_sInc U V _

/-- The small boundary squares to zero. -/
lemma sBnd_comp_sBnd (n : ℕ) : sBnd U V (n + 1) ≫ sBnd U V n = 0 := by
  have := sInc_mono U V n
  rw [← cancel_mono (sInc U V n), zero_comp, assoc, sBnd_comp_sInc,
    ← assoc, sBnd_comp_sInc, assoc]
  show sInc U V (n + 2) ≫ (SC X).d (n + 2) (n + 1) ≫ (SC X).d (n + 1) n = 0
  rw [HomologicalComplex.d_comp_d, comp_zero]

/-- **Stage 1.** The small-chains subcomplex `C^{U,V}_*(X)`: the chain
complex of chains generated by singular simplices landing in `U` or in
`V`. -/
noncomputable def SSC : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  ChainComplex.of (sCgrp U V) (sBnd U V) (sBnd_comp_sBnd U V)

@[simp] lemma SSC_X (n : ℕ) : (SSC U V).X n = sCgrp U V n := rfl

lemma SSC_d (n : ℕ) : (SSC U V).d (n + 1) n = sBnd U V n :=
  ChainComplex.of_d _ _ _ _

/-- The inclusion of the small-chains subcomplex into the singular chain
complex, as a chain map. -/
noncomputable def smallι : SSC U V ⟶ SC X where
  f n := sInc U V n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [SSC_d]
    exact (sBnd_comp_sInc U V j).symm

@[simp] lemma smallι_f (n : ℕ) : (smallι U V).f n = sInc U V n := rfl

/-- The inclusion of the small-chains subcomplex is a monomorphism of chain
complexes. -/
lemma smallι_mono : Mono (smallι U V) :=
  HomologicalComplex.mono_of_mono_f _ fun n => sInc_mono U V n

/-! ## Stage 2 toolkit A: elements of free coproducts of copies of `ℤ` -/

section Elements

/-- Elementwise `ℤ`-linearity of a `ModuleCat` morphism (stated through the
underlying linear map, to avoid instance-resolution issues on carriers). -/
lemma mapSmul {M N : ModuleCat.{0} ℤ} (φ : M ⟶ N) (c : ℤ) (x : M) :
    φ (c • x) = c • φ x :=
  φ.hom.map_smul c x

lemma zeroApp {M N : ModuleCat.{0} ℤ} (x : M) : (0 : M ⟶ N) x = 0 := by
  show (0 : M ⟶ N).hom x = 0
  rw [ModuleCat.hom_zero]
  rfl

/-- Evaluation at `1 : ℤ` of morphisms out of `ℤ`, as a linear map. -/
noncomputable def ev1 {M : ModuleCat.{0} ℤ} : (ModuleCat.of ℤ ℤ ⟶ M) →ₗ[ℤ] M where
  toFun f := f (1 : ℤ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma ev1_apply {M : ModuleCat.{0} ℤ} (f : ModuleCat.of ℤ ℤ ⟶ M) :
    ev1 f = f (1 : ℤ) := rfl

variable {κ : Type}

/-- The generating element of the free `ℤ`-module `∐_κ ℤ` attached to an
index. -/
noncomputable def unitOf (i : κ) : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ) :=
  Sigma.ι (fun _ : κ => ModuleCat.of ℤ ℤ) i (1 : ℤ)

lemma comp_unitOf {M : ModuleCat.{0} ℤ}
    (φ : (∐ fun _ : κ => ModuleCat.of ℤ ℤ) ⟶ M) (i : κ) :
    φ (unitOf i) = ev1 (Sigma.ι (fun _ : κ => ModuleCat.of ℤ ℤ) i ≫ φ) := by
  rw [ev1_apply, ModuleCat.comp_apply]
  rfl

/-- The generating elements span the free module `∐_κ ℤ`. -/
lemma span_unitOf_eq_top :
    Submodule.span ℤ (Set.range (unitOf (κ := κ))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro z
  set e := ModuleCat.coprodIsoDirectSum (fun _ : κ => ModuleCat.of ℤ ℤ) with he
  have h1 : e.inv (e.hom z) = z := by
    rw [← ModuleCat.comp_apply, e.hom_inv_id, ModuleCat.id_apply]
  have h2 : e.hom z =
      ∑ i ∈ (e.hom z).support, DirectSum.lof ℤ κ (fun _ => ℤ) i ((e.hom z) i) := by
    conv_lhs => rw [← DirectSum.sum_support_of (e.hom z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.lof_eq_of]
  have h3 : z = ∑ i ∈ (e.hom z).support, ((e.hom z) i) • unitOf i := by
    conv_lhs => rw [← h1]
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h4 : DirectSum.lof ℤ κ (fun _ => ℤ) i ((e.hom z) i) =
        ((e.hom z) i) • DirectSum.lof ℤ κ (fun _ => ℤ) i (1 : ℤ) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h4, mapSmul]
    congr 1
    rw [he]
    exact ModuleCat.lof_coprodIsoDirectSum_inv_apply
      (fun _ : κ => ModuleCat.of ℤ ℤ) i (1 : ℤ)
  rw [h3]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Induction principle: to prove a property of all elements of `∐_κ ℤ`
closed under `0`, `+`, `ℤ • ·`, it suffices to prove it for the generating
elements. -/
lemma freeInduction {p : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ) → Prop}
    (unit : ∀ i : κ, p (unitOf i)) (zero : p 0)
    (add : ∀ x y, p x → p y → p (x + y))
    (smulz : ∀ (c : ℤ) (x), p x → p (c • x))
    (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) : p z := by
  have hz : z ∈ Submodule.span ℤ (Set.range (unitOf (κ := κ))) := by
    rw [span_unitOf_eq_top]; trivial
  refine Submodule.span_induction ?_ zero (fun x y _ _ hx hy => add x y hx hy)
    (fun c x _ hx => smulz c x hx) hz
  rintro _ ⟨i, rfl⟩
  exact unit i

end Elements

/-! ## Stage 2 toolkit B: the small span and support tracking -/

section SmallSpan

/-- The generating element of the singular chain group attached to a
singular simplex. -/
noncomputable def genUnit (X : TopCat.{0}) (n : ℕ) (s : Idx X n) : Cgrp X n :=
  unitOf (κ := Idx X n) s

lemma genUnit_eq (X : TopCat.{0}) (n : ℕ) (s : Idx X n) :
    genUnit X n s = gen X n s (1 : ℤ) := rfl

/-- The submodule of small chains inside the singular chain group. -/
noncomputable def smallSpan (U V : Set X) (n : ℕ) : Submodule ℤ (Cgrp X n) :=
  Submodule.span ℤ {z | ∃ s : Idx X n, Small U V s ∧ z = genUnit X n s}

lemma genUnit_mem_smallSpan {U V : Set X} {n : ℕ} {s : Idx X n}
    (hs : Small U V s) : genUnit X n s ∈ smallSpan U V n :=
  Submodule.subset_span ⟨s, hs, rfl⟩

/-- The generating element of the small chain group attached to a small
simplex. -/
noncomputable def sUnit (U V : Set X) (n : ℕ) (t : SIdx U V n) : ↥(sCgrp U V n) :=
  unitOf (κ := SIdx U V n) t

lemma sInc_sUnit {U V : Set X} {n : ℕ} (t : SIdx U V n) :
    sInc U V n (sUnit U V n t) = genUnit X n t.1 := by
  show sInc U V n (unitOf t) = genUnit X n t.1
  rw [comp_unitOf]
  have h2 : Sigma.ι (fun _ : SIdx U V n => ModuleCat.of ℤ ℤ) t ≫ sInc U V n =
      gen X n t.1 := sgen_sInc U V t
  rw [h2]
  rfl

/-- Elementwise injectivity of the degree-`n` inclusion. -/
lemma sInc_injective (U V : Set X) (n : ℕ) :
    Function.Injective (sInc U V n) := by
  intro a b hab
  have h := congrArg (sRet U V n) hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, sInc_comp_sRet,
    ModuleCat.id_apply, ModuleCat.id_apply] at h
  exact h

/-- The inclusion maps small chains into the small span. -/
lemma sInc_mem_smallSpan (U V : Set X) (n : ℕ) (z' : ↥(sCgrp U V n)) :
    sInc U V n z' ∈ smallSpan U V n := by
  induction z' using freeInduction with
  | unit t =>
      have h : sInc U V n (sUnit U V n t) = genUnit X n t.1 := sInc_sUnit t
      rw [show (unitOf t : ↥(sCgrp U V n)) = sUnit U V n t from rfl, h]
      exact genUnit_mem_smallSpan t.2
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smulz c x hx => rw [mapSmul]; exact Submodule.smul_mem _ _ hx

/-- Membership of small chains in the range of the inclusion. -/
lemma exists_sInc_eq {U V : Set X} {n : ℕ} {z : Cgrp X n}
    (hz : z ∈ smallSpan U V n) : ∃ z' : ↥(sCgrp U V n), sInc U V n z' = z := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨sUnit U V n ⟨s, hs⟩, sInc_sUnit ⟨s, hs⟩⟩
  · exact ⟨0, map_zero _⟩
  · rintro x y _ _ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  · rintro c x _ ⟨a, ha⟩
    exact ⟨c • a, by rw [mapSmul, ha]⟩

/-- Evaluation of an affine chain along `σ` lands in the small span as soon
as every support piece pushes to a small simplex. -/
lemma toChain_one_mem_smallSpan {U V : Set X} {n m : ℕ}
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (c : AC (stdSimplex ℝ (Fin (n + 1))) m)
    (h : ∀ w ∈ c.support, Small U V (pushSimplex σ w)) :
    ev1 (toChain σ m c) ∈ smallSpan U V m := by
  rw [toChain, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [map_zsmul]
  exact zsmul_mem (genUnit_mem_smallSpan (h w hw)) _

/-- Pushing a simplex along an affine piece keeps it inside a small
simplex's range: smallness is inherited. -/
lemma small_pushSimplex {U V : Set X} {n m : ℕ} {s : Idx X n}
    (hs : Small U V s) (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) :
    Small U V (pushSimplex (simplexEquiv X n s) w) := by
  have hrange : Set.range ⇑(simplexEquiv X m (pushSimplex (simplexEquiv X n s) w)) ⊆
      Set.range ⇑(simplexEquiv X n s) := by
    rw [simplexEquiv_pushSimplex, ContinuousMap.coe_comp]
    exact Set.range_comp_subset_range _ _
  rcases hs with h | h
  · exact Or.inl (hrange.trans h)
  · exact Or.inr (hrange.trans h)

/-- The singular subdivision operator preserves the small span. -/
lemma sdOp_mem_smallSpan {U V : Set X} {n : ℕ} {z : Cgrp X n}
    (hz : z ∈ smallSpan U V n) : sdOp X n z ∈ smallSpan U V n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, rfl⟩
    rw [genUnit_eq, ← ModuleCat.comp_apply, gen_sdOp]
    show ev1 (toChain (simplexEquiv X n s) n
      (asub (baryFn n) n (asimplex (idTuple n)))) ∈ smallSpan U V n
    exact toChain_one_mem_smallSpan _ _ fun w _ => small_pushSimplex hs w
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mapSmul]; exact Submodule.smul_mem _ _ hx

/-- The subdivision homotopy maps the small span into the small span one
degree up. -/
lemma tOp_mem_smallSpan {U V : Set X} {n : ℕ} {z : Cgrp X n}
    (hz : z ∈ smallSpan U V n) : tOp X n z ∈ smallSpan U V (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨s, hs, rfl⟩
    rw [genUnit_eq, ← ModuleCat.comp_apply, gen_tOp]
    show ev1 (toChain (simplexEquiv X n s) (n + 1)
      (atee (baryFn n) n (asimplex (idTuple n)))) ∈ smallSpan U V (n + 1)
    exact toChain_one_mem_smallSpan _ _ fun w _ => small_pushSimplex hs w
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [mapSmul]; exact Submodule.smul_mem _ _ hx

/-- Iterated subdivision preserves the small span. -/
lemma sdOpIter_mem_smallSpan {U V : Set X} {n : ℕ} (k : ℕ) {z : Cgrp X n}
    (hz : z ∈ smallSpan U V n) : sdOpIter X n k z ∈ smallSpan U V n := by
  induction k with
  | zero => rw [sdOpIter_zero, ModuleCat.id_apply]; exact hz
  | succ k IH =>
      rw [sdOpIter_succ, ModuleCat.comp_apply]
      exact sdOp_mem_smallSpan IH

/-- The telescoped homotopy maps the small span into the small span one
degree up. -/
lemma tOpIter_mem_smallSpan {U V : Set X} {n : ℕ} :
    ∀ (k : ℕ) {z : Cgrp X n}, z ∈ smallSpan U V n →
      tOpIter X n k z ∈ smallSpan U V (n + 1)
  | 0, z, _ => by
      rw [tOpIter_zero]
      show (0 : Cgrp X n ⟶ Cgrp X (n + 1)) z ∈ _
      rw [zeroApp]
      exact Submodule.zero_mem _
  | k + 1, z, hz => by
      rw [tOpIter_succ]
      show (tOp X n + sdOp X n ≫ tOpIter X n k) z ∈ _
      have hadd : (tOp X n + sdOp X n ≫ tOpIter X n k) z =
          tOp X n z + (sdOp X n ≫ tOpIter X n k) z := rfl
      rw [hadd, ModuleCat.comp_apply]
      exact Submodule.add_mem _ (tOp_mem_smallSpan hz)
        (tOpIter_mem_smallSpan k (sdOp_mem_smallSpan hz))

/-- Additivity of the subdivision iterate. -/
lemma sdOpIter_add (X : TopCat.{0}) (n a b : ℕ) :
    sdOpIter X n (a + b) = sdOpIter X n a ≫ sdOpIter X n b := by
  induction b with
  | zero => rw [Nat.add_zero, sdOpIter_zero, Category.comp_id]
  | succ b IH =>
      rw [show a + (b + 1) = (a + b) + 1 from rfl, sdOpIter_succ, IH,
        sdOpIter_succ, Category.assoc]

/-- **Uniform smallness.** For open `U, V` covering `X`, every singular
chain admits an iterate of the subdivision landing in the small span. -/
lemma exists_sdOpIter_mem_smallSpan {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) {n : ℕ} (z : Cgrp X n) :
    ∃ k, sdOpIter X n k z ∈ smallSpan U V n := by
  induction z using freeInduction with
  | unit s =>
      obtain ⟨k, hk⟩ := exists_sdOpIter_small U V hU hV hUV s
      refine ⟨k, ?_⟩
      have h1 : sdOpIter X n k (unitOf s) = ev1 (gen X n s ≫ sdOpIter X n k) := by
        rw [show unitOf (κ := Idx X n) s = genUnit X n s from rfl, genUnit_eq,
          ← ModuleCat.comp_apply]
        rfl
      rw [h1, gen_comp_sdOpIter]
      exact toChain_one_mem_smallSpan _ _ fun w hw => hk w hw
  | zero => exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y hx hy =>
      obtain ⟨k₁, h₁⟩ := hx
      obtain ⟨k₂, h₂⟩ := hy
      refine ⟨k₁ + k₂, ?_⟩
      rw [map_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [sdOpIter_add, ModuleCat.comp_apply]
        exact sdOpIter_mem_smallSpan k₂ h₁
      · rw [Nat.add_comm k₁ k₂, sdOpIter_add, ModuleCat.comp_apply]
        exact sdOpIter_mem_smallSpan k₁ h₂
  | smulz c x hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by rw [mapSmul]; exact Submodule.smul_mem _ _ hk⟩

/-- Elementwise telescoped homotopy identity in positive degrees, on
cycles. -/
lemma sub_sdOpIter_eq_bnd_succ {n k : ℕ} (z : Cgrp X (n + 1))
    (hz : bnd X n z = 0) :
    z - sdOpIter X (n + 1) k z = bnd X (n + 1) (tOpIter X (n + 1) k z) := by
  have h := congrArg (fun f : Cgrp X (n + 1) ⟶ Cgrp X (n + 1) => f z)
    (tOpIter_chain_homotopy_succ X n k)
  have h1 : (bnd X n ≫ tOpIter X n k + tOpIter X (n + 1) k ≫ bnd X (n + 1)) z =
      tOpIter X n k (bnd X n z) + bnd X (n + 1) (tOpIter X (n + 1) k z) := by
    show (bnd X n ≫ tOpIter X n k) z + (tOpIter X (n + 1) k ≫ bnd X (n + 1)) z = _
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  have h2 : (𝟙 (Cgrp X (n + 1)) - sdOpIter X (n + 1) k) z =
      z - sdOpIter X (n + 1) k z := by
    show (𝟙 (Cgrp X (n + 1))) z - sdOpIter X (n + 1) k z = _
    rw [ModuleCat.id_apply]
  simp only [h1, h2] at h
  rw [hz, map_zero, zero_add] at h
  exact h.symm

/-- Elementwise telescoped homotopy identity in degree `0`. -/
lemma sub_sdOpIter_eq_bnd_zero {k : ℕ} (z : Cgrp X 0) :
    z - sdOpIter X 0 k z = bnd X 0 (tOpIter X 0 k z) := by
  have h := congrArg (fun f : Cgrp X 0 ⟶ Cgrp X 0 => f z)
    (tOpIter_chain_homotopy_zero X k)
  have h1 : (tOpIter X 0 k ≫ bnd X 0) z = bnd X 0 (tOpIter X 0 k z) :=
    ModuleCat.comp_apply _ _ _
  have h2 : (𝟙 (Cgrp X 0) - sdOpIter X 0 k) z = z - sdOpIter X 0 k z := by
    show (𝟙 (Cgrp X 0)) z - sdOpIter X 0 k z = _
    rw [ModuleCat.id_apply]
  simp only [h1, h2] at h
  exact h.symm

/-- Elementwise chain-map property of the subdivision iterate. -/
lemma sdOpIter_bnd_elem {n k : ℕ} (w : Cgrp X (n + 1)) :
    bnd X n (sdOpIter X (n + 1) k w) = sdOpIter X n k (bnd X n w) := by
  have h := congrArg (fun f : Cgrp X (n + 1) ⟶ Cgrp X n => f w)
    (sdOpIter_comp_bnd X n k)
  simpa only [ModuleCat.comp_apply] using h

/-- Elementwise telescoped homotopy identity in every degree, on
boundaries. -/
lemma sub_sdOpIter_eq_bnd_of_boundary {n : ℕ} (k : ℕ) (z : Cgrp X n)
    (w : Cgrp X (n + 1)) (hw : z = bnd X n w) :
    z - sdOpIter X n k z = bnd X n (tOpIter X n k z) := by
  cases n with
  | zero => exact sub_sdOpIter_eq_bnd_zero z
  | succ m =>
      refine sub_sdOpIter_eq_bnd_succ z ?_
      rw [hw, ← ModuleCat.comp_apply]
      have hdd : bnd X (m + 1) ≫ bnd X m = 0 := by
        show (SC X).d (m + 2) (m + 1) ≫ (SC X).d (m + 1) m = 0
        exact HomologicalComplex.d_comp_d _ _ _ _
      rw [hdd]
      exact zeroApp w

end SmallSpan

/-! ## Stage 2 toolkit C: a concrete homology-isomorphism criterion for
short complexes of `ℤ`-modules -/

section HomologyCriterion

open ShortComplex

variable {S T : ShortComplex (ModuleCat.{0} ℤ)}

lemma τ₂_maps_ker (ψ : S ⟶ T) : ∀ x ∈ LinearMap.ker S.g.hom,
    ψ.τ₂ x ∈ LinearMap.ker T.g.hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h := congrArg (fun f : S.X₂ ⟶ T.X₃ => f x) ψ.comm₂₃
  simp only [ModuleCat.comp_apply] at h
  show T.g (ψ.τ₂ x) = 0
  rw [h, show S.g x = (0 : S.X₃) from hx, map_zero]

/-- The induced map on concrete cycles. -/
noncomputable def kerMap (ψ : S ⟶ T) :
    ↥(LinearMap.ker S.g.hom) →ₗ[ℤ] ↥(LinearMap.ker T.g.hom) :=
  LinearMap.restrict ψ.τ₂.hom (τ₂_maps_ker ψ)

@[simp] lemma kerMap_coe (ψ : S ⟶ T) (x : ↥(LinearMap.ker S.g.hom)) :
    (kerMap ψ x : T.X₂) = ψ.τ₂ (x : S.X₂) := rfl

lemma kerMap_range_le (ψ : S ⟶ T) :
    LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap (kerMap ψ) := by
  rintro _ ⟨a, rfl⟩
  refine ⟨ψ.τ₁ a, ?_⟩
  apply Subtype.ext
  show T.f (ψ.τ₁ a) = ψ.τ₂ (S.f a)
  have h := congrArg (fun f : S.X₁ ⟶ T.X₂ => f a) ψ.comm₁₂
  simpa only [ModuleCat.comp_apply] using h

/-- The induced map on concrete homology. -/
noncomputable def quotMap (ψ : S ⟶ T) :
    (↥(LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[ℤ]
      (↥(LinearMap.ker T.g.hom) ⧸ LinearMap.range T.moduleCatToCycles) :=
  Submodule.mapQ _ _ (kerMap ψ) (kerMap_range_le ψ)

/-- The concrete left-homology map data for `ψ` relative to the
`moduleCat` left homology data on both sides. -/
noncomputable def lhMapData (ψ : S ⟶ T) :
    LeftHomologyMapData ψ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (kerMap ψ)
  φH := ModuleCat.ofHom (quotMap ψ)
  commi := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rfl
  commf' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    apply Subtype.ext
    show ψ.τ₂ (S.f a) = T.f (ψ.τ₁ a)
    have h := congrArg (fun f : S.X₁ ⟶ T.X₂ => f a) ψ.comm₁₂
    simpa only [ModuleCat.comp_apply] using h.symm
  commπ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show quotMap ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (kerMap ψ x)
    rfl

lemma quotMap_surjective (ψ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ (x : S.X₂) (w : T.X₁), S.g x = 0 ∧ ψ.τ₂ x = y + T.f w) :
    Function.Surjective (quotMap ψ) := by
  intro q
  obtain ⟨⟨y, hy⟩, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range T.moduleCatToCycles) q
  obtain ⟨x, w, hgx, hx⟩ := hsurj y (LinearMap.mem_ker.mp hy)
  refine ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr hgx⟩, ?_⟩
  show quotMap ψ (Submodule.Quotient.mk _) =
    Submodule.Quotient.mk (⟨y, hy⟩ : ↥(LinearMap.ker T.g.hom))
  rw [quotMap, Submodule.mapQ_apply]
  refine (Submodule.Quotient.eq _).mpr ⟨w, ?_⟩
  apply Subtype.ext
  show T.f w = ψ.τ₂ x - y
  rw [hx]
  abel

lemma quotMap_injective (ψ : S ⟶ T)
    (hinj : ∀ x : S.X₂, S.g x = 0 → (∃ w : T.X₁, ψ.τ₂ x = T.f w) →
      ∃ v : S.X₁, x = S.f v) :
    Function.Injective (quotMap ψ) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨⟨x, hx⟩, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles) q
  have hq' : Submodule.Quotient.mk (p := LinearMap.range T.moduleCatToCycles)
      (kerMap ψ ⟨x, hx⟩) = 0 := by
    rw [← Submodule.mapQ_apply (LinearMap.range S.moduleCatToCycles)
      (h := kerMap_range_le ψ)]
    exact hq
  rw [Submodule.Quotient.mk_eq_zero] at hq'
  replace hq := hq'
  obtain ⟨w, hw⟩ := hq
  have hw' : ψ.τ₂ x = T.f w := by
    have := congrArg (Subtype.val) hw
    exact this.symm
  obtain ⟨v, hv⟩ := hinj x (LinearMap.mem_ker.mp hx) ⟨w, hw'⟩
  show Submodule.Quotient.mk (⟨x, hx⟩ : ↥(LinearMap.ker S.g.hom)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨v, Subtype.ext (by simpa using hv.symm)⟩

/-- **The concrete criterion.** A morphism of short complexes of
`ℤ`-modules induces an isomorphism on homology as soon as the two
elementwise conditions hold. -/
lemma isIso_homologyMap_of_elementwise (ψ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ (x : S.X₂) (w : T.X₁), S.g x = 0 ∧ ψ.τ₂ x = y + T.f w)
    (hinj : ∀ x : S.X₂, S.g x = 0 → (∃ w : T.X₁, ψ.τ₂ x = T.f w) →
      ∃ v : S.X₁, x = S.f v) :
    IsIso (ShortComplex.homologyMap ψ) := by
  rw [(lhMapData ψ).homologyMap_eq]
  have hbij : Function.Bijective (quotMap ψ) :=
    ⟨quotMap_injective ψ hinj, quotMap_surjective ψ hsurj⟩
  have hiso : IsIso (lhMapData ψ).φH := by
    show IsIso (ModuleCat.ofHom (quotMap ψ))
    have hmono : Mono (ModuleCat.ofHom (quotMap ψ)) :=
      (ModuleCat.mono_iff_injective _).mpr hbij.1
    have hepi : Epi (ModuleCat.ofHom (quotMap ψ)) :=
      (ModuleCat.epi_iff_surjective _).mpr hbij.2
    exact isIso_of_mono_of_epi _
  infer_instance

lemma epi_homologyMap_of_elementwise (ψ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ (x : S.X₂) (w : T.X₁), S.g x = 0 ∧ ψ.τ₂ x = y + T.f w) :
    Epi (ShortComplex.homologyMap ψ) := by
  rw [(lhMapData ψ).homologyMap_eq]
  have hepi : Epi (lhMapData ψ).φH := by
    show Epi (ModuleCat.ofHom (quotMap ψ))
    exact (ModuleCat.epi_iff_surjective _).mpr (quotMap_surjective ψ hsurj)
  apply epi_comp
end HomologyCriterion

/-! ## Stage 2 toolkit D: chain-complex wrappers for the criterion -/

section ChainCriterion

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}

/-- Transport of `IsIso` on `homologyMap` through the honest-index short
complex functor `shortComplexFunctor'`. -/
lemma isIso_homologyMap_of_sc' (φ : K ⟶ L) (i j k : ℕ)
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (h : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) i j k).map φ))) :
    IsIso (HomologicalComplex.homologyMap φ j) := by
  set e := HomologicalComplex.natIsoSc' (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)
    i j k hi hk with he
  have hnat := e.hom.naturality φ
  have hcomm : (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) j).map φ =
      e.hom.app K ≫ (HomologicalComplex.shortComplexFunctor' (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) i j k).map φ ≫ e.inv.app L := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have h1 : IsIso (ShortComplex.homologyMap (e.hom.app K)) :=
    (inferInstance : IsIso (ShortComplex.homologyMapIso (e.app K)).hom)
  have h2 : IsIso (ShortComplex.homologyMap (e.inv.app L)) :=
    (inferInstance : IsIso (ShortComplex.homologyMapIso (e.app L)).inv)
  show IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) j).map φ))
  rw [hcomm, ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp]
  infer_instance

/-- Transport of `Epi` on `homologyMap` through the honest-index short
complex functor. -/
lemma epi_homologyMap_of_sc' (φ : K ⟶ L) (i j k : ℕ)
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (h : Epi (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) i j k).map φ))) :
    Epi (HomologicalComplex.homologyMap φ j) := by
  set e := HomologicalComplex.natIsoSc' (ModuleCat.{0} ℤ) (ComplexShape.down ℕ)
    i j k hi hk with he
  have hnat := e.hom.naturality φ
  have hcomm : (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) j).map φ =
      e.hom.app K ≫ (HomologicalComplex.shortComplexFunctor' (ModuleCat.{0} ℤ)
        (ComplexShape.down ℕ) i j k).map φ ≫ e.inv.app L := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have h1 : IsIso (ShortComplex.homologyMap (e.hom.app K)) :=
    (inferInstance : IsIso (ShortComplex.homologyMapIso (e.app K)).hom)
  have h2 : IsIso (ShortComplex.homologyMap (e.inv.app L)) :=
    (inferInstance : IsIso (ShortComplex.homologyMapIso (e.app L)).inv)
  show Epi (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ)
      (ComplexShape.down ℕ) j).map φ))
  rw [hcomm, ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp]
  exact epi_comp _ _

/-- Criterion for `homologyMap` in positive degree, with honest indices. -/
lemma isIso_homologyMap_chain_succ (φ : K ⟶ L) (n : ℕ)
    (hsurj : ∀ y : L.X (n + 1), L.d (n + 1) n y = 0 →
      ∃ (x : K.X (n + 1)) (w : L.X (n + 2)),
        K.d (n + 1) n x = 0 ∧ φ.f (n + 1) x = y + L.d (n + 2) (n + 1) w)
    (hinj : ∀ x : K.X (n + 1), K.d (n + 1) n x = 0 →
      (∃ w : L.X (n + 2), φ.f (n + 1) x = L.d (n + 2) (n + 1) w) →
      ∃ v : K.X (n + 2), x = K.d (n + 2) (n + 1) v) :
    IsIso (HomologicalComplex.homologyMap φ (n + 1)) := by
  refine isIso_homologyMap_of_sc' φ (n + 2) (n + 1) n
    (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n) ?_
  exact isIso_homologyMap_of_elementwise _ hsurj hinj

/-- Criterion for `homologyMap` in degree `0`, with honest indices. -/
lemma isIso_homologyMap_chain_zero (φ : K ⟶ L)
    (hsurj : ∀ y : L.X 0,
      ∃ (x : K.X 0) (w : L.X 1), φ.f 0 x = y + L.d 1 0 w)
    (hinj : ∀ x : K.X 0, (∃ w : L.X 1, φ.f 0 x = L.d 1 0 w) →
      ∃ v : K.X 1, x = K.d 1 0 v) :
    IsIso (HomologicalComplex.homologyMap φ 0) := by
  have hdK : K.d 0 0 = 0 := K.shape 0 0 (by simp [ComplexShape.down_Rel])
  refine isIso_homologyMap_of_sc' φ 1 0 0
    (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero ?_
  refine isIso_homologyMap_of_elementwise _ ?_ ?_
  · intro y _
    obtain ⟨x, w, hx⟩ := hsurj y
    refine ⟨x, w, ?_, hx⟩
    show (K.d 0 0) x = 0
    rw [hdK]
    exact zeroApp x
  · intro x _ hx
    exact hinj x hx

/-- Epi criterion for `homologyMap` in degree `0`. -/
lemma epi_homologyMap_chain_zero (φ : K ⟶ L)
    (hsurj : ∀ y : L.X 0,
      ∃ (x : K.X 0) (w : L.X 1), φ.f 0 x = y + L.d 1 0 w) :
    Epi (HomologicalComplex.homologyMap φ 0) := by
  have hdK : K.d 0 0 = 0 := K.shape 0 0 (by simp [ComplexShape.down_Rel])
  refine epi_homologyMap_of_sc' φ 1 0 0
    (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero ?_
  refine epi_homologyMap_of_elementwise _ ?_
  intro y _
  obtain ⟨x, w, hx⟩ := hsurj y
  refine ⟨x, w, ?_, hx⟩
  show (K.d 0 0) x = 0
  rw [hdK]
  exact zeroApp x

end ChainCriterion

/-! ## Stage 2: the small-chains theorem (Hatcher, Prop 2.21) -/

section SmallChainsTheorem

variable {U V : Set X}

/-- Surjectivity input in positive degrees. -/
lemma small_surj_succ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) (y : Cgrp X (n + 1)) (hy : bnd X n y = 0) :
    ∃ (x : ↥(sCgrp U V (n + 1))) (w : Cgrp X (n + 2)),
      sBnd U V n x = 0 ∧ sInc U V (n + 1) x = y + bnd X (n + 1) w := by
  obtain ⟨k, hk⟩ := exists_sdOpIter_mem_smallSpan hU hV hUV y
  obtain ⟨x, hx⟩ := exists_sInc_eq hk
  refine ⟨x, -(tOpIter X (n + 1) k y), ?_, ?_⟩
  · -- x is a cycle in the small complex
    apply sInc_injective U V n
    have h1 : sInc U V n (sBnd U V n x) = bnd X n (sInc U V (n + 1) x) := by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, sBnd_comp_sInc]
    rw [h1, hx, sdOpIter_bnd_elem, hy, map_zero, map_zero]
  · rw [hx, map_neg]
    have h2 := sub_sdOpIter_eq_bnd_succ (k := k) y hy
    have : sdOpIter X (n + 1) k y = y - bnd X (n + 1) (tOpIter X (n + 1) k y) := by
      rw [← h2]; abel
    rw [this]; abel

/-- Injectivity input in every degree `n` (with boundary from degree
`n + 1`). -/
lemma small_inj (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) (x : ↥(sCgrp U V n)) (w : Cgrp X (n + 1))
    (hw : sInc U V n x = bnd X n w) :
    ∃ v : ↥(sCgrp U V (n + 1)), x = sBnd U V n v := by
  set z := sInc U V n x with hz
  have hzsmall : z ∈ smallSpan U V n := sInc_mem_smallSpan U V n x
  obtain ⟨k, hks⟩ := exists_sdOpIter_mem_smallSpan hU hV hUV w
  -- the corrected chain c := T_k z + sd^k w is small and has boundary z
  have hsd : sdOpIter X n k z = bnd X n (sdOpIter X (n + 1) k w) := by
    rw [sdOpIter_bnd_elem, hw]
  have hcorr : z - sdOpIter X n k z = bnd X n (tOpIter X n k z) :=
    sub_sdOpIter_eq_bnd_of_boundary k z w hw
  have hzbnd : z = bnd X n (tOpIter X n k z + sdOpIter X (n + 1) k w) := by
    rw [map_add, ← hcorr, ← hsd]
    abel
  have hcsmall : tOpIter X n k z + sdOpIter X (n + 1) k w ∈ smallSpan U V (n + 1) :=
    Submodule.add_mem _ (tOpIter_mem_smallSpan k hzsmall) hks
  obtain ⟨v, hv⟩ := exists_sInc_eq hcsmall
  refine ⟨v, ?_⟩
  apply sInc_injective U V n
  have h1 : sInc U V n (sBnd U V n v) = bnd X n (sInc U V (n + 1) v) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, sBnd_comp_sInc]
  rw [h1, hv, ← hzbnd, hz]

/-- **Stage 2: the small-chains theorem.** For open `U, V` covering `X`,
the inclusion of the small-chains subcomplex induces an isomorphism on
homology in every degree. -/
theorem smallι_isIso_homologyMap (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallι U V) n) := by
  match n with
  | 0 =>
      refine isIso_homologyMap_chain_zero (smallι U V) ?_ ?_
      · intro y
        obtain ⟨k, hk⟩ := exists_sdOpIter_mem_smallSpan hU hV hUV y
        obtain ⟨x, hx⟩ := exists_sInc_eq hk
        refine ⟨x, -(tOpIter X 0 k y), ?_⟩
        let y' : ↥(Cgrp X 0) := y
        have hx' : sInc U V 0 x = sdOpIter X 0 k y' := hx
        have h2 := sub_sdOpIter_eq_bnd_zero (k := k) y'
        have h3 : sInc U V 0 x = y' + bnd X 0 (-(tOpIter X 0 k y')) := by
          rw [hx', map_neg]
          have h4 : sdOpIter X 0 k y' = y' - bnd X 0 (tOpIter X 0 k y') := by
            rw [← h2]; abel
          rw [h4]; abel
        exact h3
      · intro x hx
        obtain ⟨w, hw⟩ := hx
        have hw' : sInc U V 0 x = bnd X 0 w := hw
        obtain ⟨v, hv⟩ := small_inj hU hV hUV 0 x w hw'
        refine ⟨v, ?_⟩
        show x = (SSC U V).d 1 0 v
        rw [SSC_d]
        exact hv
  | n + 1 =>
      refine isIso_homologyMap_chain_succ (smallι U V) n ?_ ?_
      · intro y hy
        obtain ⟨x, w, h1, h2⟩ := small_surj_succ hU hV hUV n y hy
        refine ⟨x, w, ?_, h2⟩
        show (SSC U V).d (n + 1) n x = 0
        rw [SSC_d]
        exact h1
      · intro x hx hw
        obtain ⟨w, hw'⟩ := hw
        obtain ⟨v, hv⟩ := small_inj hU hV hUV (n + 1) x w hw'
        refine ⟨v, ?_⟩
        show x = (SSC U V).d (n + 2) (n + 1) v
        rw [SSC_d]
        exact hv

/-- The small-chains homology isomorphism `H_n(C^{U,V}) ≅ H_n(X)`. -/
noncomputable def smallChainsHomologyIso (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (SSC U V).homology n ≅ (SC X).homology n :=
  have := smallι_isIso_homologyMap hU hV hUV n
  asIso (HomologicalComplex.homologyMap (smallι U V) n)

end SmallChainsTheorem

/-! ## Stage 3 toolkit A: coordinates on free coproducts of copies of `ℤ` -/

section Coordinates

variable {κ κ' : Type}

/-- The coordinate of an element of `∐_κ ℤ` at an index, through the
direct-sum presentation. -/
noncomputable def coordAt (i : κ) (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) : ℤ :=
  (ModuleCat.coprodIsoDirectSum (fun _ : κ => ModuleCat.of ℤ ℤ)).hom z i

lemma coordAt_unitOf (i j : κ) :
    coordAt j (unitOf i) = if i = j then 1 else 0 := by
  unfold coordAt unitOf
  rw [← ModuleCat.comp_apply, ModuleCat.ι_coprodIsoDirectSum_hom]
  show (DirectSum.lof ℤ κ (fun _ => ℤ) i (1 : ℤ)) j = _
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · rw [if_neg h, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]

lemma coordAt_zero (i : κ) :
    coordAt i (0 : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) = 0 := by
  unfold coordAt
  rw [map_zero]
  exact DFinsupp.zero_apply i

lemma coordAt_add (j : κ) (x y : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) :
    coordAt j (x + y) = coordAt j x + coordAt j y := by
  unfold coordAt
  rw [map_add]
  exact DFinsupp.add_apply _ _ _

lemma coordAt_smul (j : κ) (c : ℤ) (x : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) :
    coordAt j (c • x) = c • coordAt j x := by
  unfold coordAt
  rw [mapSmul]
  exact DFinsupp.smul_apply _ _ _

/-- The support of an element of `∐_κ ℤ`. -/
noncomputable def suppOf (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) : Finset κ :=
  ((ModuleCat.coprodIsoDirectSum (fun _ : κ => ModuleCat.of ℤ ℤ)).hom z).support

lemma mem_suppOf_iff {i : κ} {z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)} :
    i ∈ suppOf z ↔ coordAt i z ≠ 0 := by
  unfold suppOf coordAt
  exact DFinsupp.mem_support_iff

/-- Every element of `∐_κ ℤ` is the (finite) sum of its coordinates times
the generating elements. -/
lemma sum_coordAt_smul_unitOf (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) :
    z = ∑ i ∈ suppOf z, coordAt i z • unitOf i := by
  unfold suppOf coordAt
  set e := ModuleCat.coprodIsoDirectSum (fun _ : κ => ModuleCat.of ℤ ℤ) with he
  have h1 : e.inv (e.hom z) = z := by
    rw [← ModuleCat.comp_apply, e.hom_inv_id, ModuleCat.id_apply]
  have h2 : e.hom z =
      ∑ i ∈ (e.hom z).support, DirectSum.lof ℤ κ (fun _ => ℤ) i ((e.hom z) i) := by
    conv_lhs => rw [← DirectSum.sum_support_of (e.hom z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DirectSum.lof_eq_of]
  have h3 : z = ∑ i ∈ (e.hom z).support, ((e.hom z) i) • unitOf i := by
    conv_lhs => rw [← h1]
    conv_lhs => rw [h2]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h4 : DirectSum.lof ℤ κ (fun _ => ℤ) i ((e.hom z) i) =
        ((e.hom z) i) • DirectSum.lof ℤ κ (fun _ => ℤ) i (1 : ℤ) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h4, mapSmul]
    congr 1
    rw [he]
    exact ModuleCat.lof_coprodIsoDirectSum_inv_apply
      (fun _ : κ => ModuleCat.of ℤ ℤ) i (1 : ℤ)
  exact h3

/-- Coordinate tracking through a basis-index map: at an index in the image
of an injective index map, the coordinate of the image chain is the source
coordinate. -/
lemma coordAt_map_eq {ψ : κ → κ'} (hψ : Function.Injective ψ)
    {F : (∐ fun _ : κ => ModuleCat.of ℤ ℤ) ⟶ (∐ fun _ : κ' => ModuleCat.of ℤ ℤ)}
    (hF : ∀ i, F (unitOf i) = unitOf (ψ i)) (i : κ)
    (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) :
    coordAt (ψ i) (F z) = coordAt i z := by
  induction z using freeInduction with
  | unit i' =>
      rw [hF, coordAt_unitOf, coordAt_unitOf]
      exact if_congr hψ.eq_iff rfl rfl
  | zero => rw [map_zero, coordAt_zero, coordAt_zero]
  | add x y hx hy => rw [map_add, coordAt_add, coordAt_add, hx, hy]
  | smulz c x hx => rw [mapSmul, coordAt_smul, coordAt_smul, hx]

/-- Coordinate tracking through a basis-index map: at an index outside the
image of the index map, the coordinate of any image chain vanishes. -/
lemma coordAt_map_notMem {ψ : κ → κ'}
    {F : (∐ fun _ : κ => ModuleCat.of ℤ ℤ) ⟶ (∐ fun _ : κ' => ModuleCat.of ℤ ℤ)}
    (hF : ∀ i, F (unitOf i) = unitOf (ψ i)) {t : κ'} (ht : ∀ i, ψ i ≠ t)
    (z : ↥(∐ fun _ : κ => ModuleCat.of ℤ ℤ)) :
    coordAt t (F z) = 0 := by
  induction z using freeInduction with
  | unit i' =>
      rw [hF, coordAt_unitOf]
      exact if_neg (ht i')
  | zero => rw [map_zero, coordAt_zero]
  | add x y hx hy => rw [map_add, coordAt_add, hx, hy, add_zero]
  | smulz c x hx => rw [mapSmul, coordAt_smul, hx, smul_zero]

end Coordinates

/-! ## Stage 3 toolkit B: elements of binary biproducts of `ℤ`-modules -/

section BiprodElements

variable {A B : ModuleCat.{0} ℤ}

lemma addApp {M N : ModuleCat.{0} ℤ} (f g : M ⟶ N) (x : M) :
    (f + g) x = f x + g x := by
  show (f + g).hom x = f.hom x + g.hom x
  rw [ModuleCat.hom_add]
  rfl

lemma negApp {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (x : M) :
    (-f) x = -(f x) := by
  show (-f).hom x = -(f.hom x)
  rw [ModuleCat.hom_neg]
  rfl

/-- Elementwise decomposition of an element of a binary biproduct into its
two components. -/
lemma biprod_decomp (z : ↥(A ⊞ B)) :
    z = (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) z) +
        (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) z) := by
  have h := congrArg
    (fun f : A ⊞ B ⟶ A ⊞ B => f z) (biprod.total (X := A) (Y := B))
  have h1 : (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr :
      A ⊞ B ⟶ A ⊞ B) z =
      (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) z) +
        (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) z) := by
    rw [addApp, ModuleCat.comp_apply, ModuleCat.comp_apply]
  have h2 : (𝟙 (A ⊞ B) : A ⊞ B ⟶ A ⊞ B) z = z := ModuleCat.id_apply _ _
  simp only [h1, h2] at h
  exact h.symm

/-- Elementwise extensionality in a binary biproduct. -/
lemma biprod_elem_ext {z w : ↥(A ⊞ B)}
    (h1 : (biprod.fst : A ⊞ B ⟶ A) z = (biprod.fst : A ⊞ B ⟶ A) w)
    (h2 : (biprod.snd : A ⊞ B ⟶ B) z = (biprod.snd : A ⊞ B ⟶ B) w) :
    z = w := by
  rw [biprod_decomp z, biprod_decomp w, h1, h2]

/-- Elementwise formula for `biprod.desc`. -/
lemma descApp {M : ModuleCat.{0} ℤ} (u : A ⟶ M) (v : B ⟶ M) (z : ↥(A ⊞ B)) :
    biprod.desc u v z =
      u ((biprod.fst : A ⊞ B ⟶ A) z) + v ((biprod.snd : A ⊞ B ⟶ B) z) := by
  have h1 : biprod.desc u v
      ((biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) z)) =
      u ((biprod.fst : A ⊞ B ⟶ A) z) := by
    rw [← ModuleCat.comp_apply, biprod.inl_desc]
  have h2 : biprod.desc u v
      ((biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) z)) =
      v ((biprod.snd : A ⊞ B ⟶ B) z) := by
    rw [← ModuleCat.comp_apply, biprod.inr_desc]
  conv_lhs => rw [biprod_decomp z]
  rw [map_add, h1, h2]

/-- Elementwise first component of `biprod.lift`. -/
lemma fst_liftApp {M : ModuleCat.{0} ℤ} (f : M ⟶ A) (g : M ⟶ B) (x : M) :
    (biprod.fst : A ⊞ B ⟶ A) (biprod.lift f g x) = f x := by
  rw [← ModuleCat.comp_apply, biprod.lift_fst]

/-- Elementwise second component of `biprod.lift`. -/
lemma snd_liftApp {M : ModuleCat.{0} ℤ} (f : M ⟶ A) (g : M ⟶ B) (x : M) :
    (biprod.snd : A ⊞ B ⟶ B) (biprod.lift f g x) = g x := by
  rw [← ModuleCat.comp_apply, biprod.lift_snd]

end BiprodElements

/-! ## Stage 3 toolkit C: subspaces and simplex lifting -/

section Subspaces

/-- The `X`-simplex underlying a singular simplex of the subspace `W`. -/
noncomputable def pushIdx (W : Set X) {n : ℕ} (a : Idx (TopCat.of W) n) :
    Idx X n :=
  (TopCat.toSSet.map (SingularPair.subInc X W)).app (op ⦋n⦌) a

lemma pushIdx_injective (W : Set X) (n : ℕ) :
    Function.Injective (pushIdx (X := X) W (n := n)) :=
  SingularPair.toSSet_map_app_injective (SingularPair.subInc X W)
    (SingularPair.subInc_injective X W) n

lemma range_pushIdx (W : Set X) {n : ℕ} (a : Idx (TopCat.of W) n) :
    Set.range ⇑(simplexEquiv X n (pushIdx W a)) ⊆ W := by
  unfold pushIdx
  rw [simplexEquiv_map, ContinuousMap.coe_comp]
  rintro x ⟨t, rfl⟩
  exact ((simplexEquiv (TopCat.of W) n a) t).2

/-- Lift a singular simplex of `X` whose range lies in `W` to a singular
simplex of the subspace `W`. -/
noncomputable def liftIdx (W : Set X) {n : ℕ} (s : Idx X n)
    (h : Set.range ⇑(simplexEquiv X n s) ⊆ W) : Idx (TopCat.of W) n :=
  (simplexEquiv (TopCat.of W) n).symm
    ⟨fun t => ⟨simplexEquiv X n s t, h ⟨t, rfl⟩⟩,
      (map_continuous (simplexEquiv X n s)).subtype_mk _⟩

lemma pushIdx_liftIdx (W : Set X) {n : ℕ} (s : Idx X n)
    (h : Set.range ⇑(simplexEquiv X n s) ⊆ W) :
    pushIdx W (liftIdx W s h) = s := by
  apply (simplexEquiv X n).injective
  unfold pushIdx liftIdx
  rw [simplexEquiv_map, Equiv.apply_symm_apply]
  ext t
  rfl

/-- The inclusion between nested subspaces of `X`, as a `TopCat`
morphism. -/
noncomputable def subIncl {W W' : Set X} (h : W ⊆ W') :
    TopCat.of W ⟶ TopCat.of W' :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

lemma subIncl_comp_subInc {W W' : Set X} (h : W ⊆ W') :
    subIncl h ≫ SingularPair.subInc X W' = SingularPair.subInc X W := by
  ext x
  rfl

lemma pushIdx_subIncl {W W' : Set X} (h : W ⊆ W') {n : ℕ}
    (a : Idx (TopCat.of W) n) :
    pushIdx W' ((TopCat.toSSet.map (subIncl h)).app (op ⦋n⦌) a) = pushIdx W a := by
  have h1 : (TopCat.toSSet.map (subIncl h ≫ SingularPair.subInc X W')).app
      (op ⦋n⦌) a =
      (TopCat.toSSet.map (SingularPair.subInc X W')).app (op ⦋n⦌)
        ((TopCat.toSSet.map (subIncl h)).app (op ⦋n⦌) a) := by
    rw [Functor.map_comp]
    rfl
  rw [pushIdx, ← h1, subIncl_comp_subInc, pushIdx]

/-- Elementwise action of a chain map on generating elements. -/
lemma chainMap_unitOf {A B : TopCat.{0}} (f : A ⟶ B) {n : ℕ} (s : Idx A n) :
    chainMap f n (unitOf s) =
      unitOf ((TopCat.toSSet.map f).app (op ⦋n⦌) s) := by
  rw [comp_unitOf]
  have h : Sigma.ι (fun _ : Idx A n => ModuleCat.of ℤ ℤ) s ≫ chainMap f n =
      gen B n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) := gen_map f n s
  rw [h, ev1_apply]
  rfl

/-- Elementwise injectivity of the chain map of an injective continuous
map. -/
lemma chainMap_injective {A : TopCat.{0}} (f : A ⟶ X)
    (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective (chainMap f n) := by
  intro a b hab
  have h := congrArg (SingularPair.genRetract f n) hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    SingularPair.chainMap_comp_genRetract f hf n,
    ModuleCat.id_apply, ModuleCat.id_apply] at h
  exact h

end Subspaces

/-! ## Stage 3 toolkit D: the factor maps into the small subcomplex -/

section MVMaps

lemma small_pushIdx_left {n : ℕ} (a : Idx (TopCat.of U) n) :
    Small U V (pushIdx U a) := Or.inl (range_pushIdx U a)

lemma small_pushIdx_right {n : ℕ} (a : Idx (TopCat.of V) n) :
    Small U V (pushIdx V a) := Or.inr (range_pushIdx V a)

/-- The index map from `U`-simplices to small simplices. -/
noncomputable def uIdx {n : ℕ} (a : Idx (TopCat.of U) n) : SIdx U V n :=
  ⟨pushIdx U a, small_pushIdx_left U V a⟩

/-- The index map from `V`-simplices to small simplices. -/
noncomputable def vIdx {n : ℕ} (a : Idx (TopCat.of V) n) : SIdx U V n :=
  ⟨pushIdx V a, small_pushIdx_right U V a⟩

lemma uIdx_injective (n : ℕ) : Function.Injective (uIdx U V (n := n)) :=
  fun _ _ hab => pushIdx_injective U n (congrArg Subtype.val hab)

lemma vIdx_injective (n : ℕ) : Function.Injective (vIdx U V (n := n)) :=
  fun _ _ hab => pushIdx_injective V n (congrArg Subtype.val hab)

/-- The degree-`n` chain map `C_n(U) ⟶ C_n^{U,V}`. -/
noncomputable def uInc (n : ℕ) : Cgrp (TopCat.of U) n ⟶ sCgrp U V n :=
  Sigma.desc fun a => sgen U V n (uIdx U V a)

/-- The degree-`n` chain map `C_n(V) ⟶ C_n^{U,V}`. -/
noncomputable def vInc (n : ℕ) : Cgrp (TopCat.of V) n ⟶ sCgrp U V n :=
  Sigma.desc fun a => sgen U V n (vIdx U V a)

lemma gen_uInc {n : ℕ} (a : Idx (TopCat.of U) n) :
    gen (TopCat.of U) n a ≫ uInc U V n = sgen U V n (uIdx U V a) :=
  Sigma.ι_desc _ _

lemma gen_vInc {n : ℕ} (a : Idx (TopCat.of V) n) :
    gen (TopCat.of V) n a ≫ vInc U V n = sgen U V n (vIdx U V a) :=
  Sigma.ι_desc _ _

lemma uInc_unitOf {n : ℕ} (a : Idx (TopCat.of U) n) :
    uInc U V n (unitOf a) = unitOf (uIdx U V a) := by
  rw [comp_unitOf]
  have h : Sigma.ι (fun _ : Idx (TopCat.of U) n => ModuleCat.of ℤ ℤ) a ≫
      uInc U V n = sgen U V n (uIdx U V a) := gen_uInc U V a
  rw [h, ev1_apply]
  rfl

lemma vInc_unitOf {n : ℕ} (a : Idx (TopCat.of V) n) :
    vInc U V n (unitOf a) = unitOf (vIdx U V a) := by
  rw [comp_unitOf]
  have h : Sigma.ι (fun _ : Idx (TopCat.of V) n => ModuleCat.of ℤ ℤ) a ≫
      vInc U V n = sgen U V n (vIdx U V a) := gen_vInc U V a
  rw [h, ev1_apply]
  rfl

lemma uInc_comp_sInc (n : ℕ) :
    uInc U V n ≫ sInc U V n = chainMap (SingularPair.subInc X U) n := by
  apply Sigma.hom_ext
  intro a
  rw [← assoc]
  rw [show Sigma.ι (fun _ : Idx (TopCat.of U) n => ModuleCat.of ℤ ℤ) a ≫
    uInc U V n = sgen U V n (uIdx U V a) from gen_uInc U V a]
  rw [sgen_sInc, gen_map]
  rfl

lemma vInc_comp_sInc (n : ℕ) :
    vInc U V n ≫ sInc U V n = chainMap (SingularPair.subInc X V) n := by
  apply Sigma.hom_ext
  intro a
  rw [← assoc]
  rw [show Sigma.ι (fun _ : Idx (TopCat.of V) n => ModuleCat.of ℤ ℤ) a ≫
    vInc U V n = sgen U V n (vIdx U V a) from gen_vInc U V a]
  rw [sgen_sInc, gen_map]
  rfl


lemma uInc_injective (n : ℕ) : Function.Injective (uInc U V n) := by
  intro a b hab
  have h := congrArg (sInc U V n) hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, uInc_comp_sInc] at h
  exact chainMap_injective (SingularPair.subInc X U)
    (SingularPair.subInc_injective X U) n h

lemma vInc_injective (n : ℕ) : Function.Injective (vInc U V n) := by
  intro a b hab
  have h := congrArg (sInc U V n) hab
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, vInc_comp_sInc] at h
  exact chainMap_injective (SingularPair.subInc X V)
    (SingularPair.subInc_injective X V) n h

lemma uInc_comm (n : ℕ) :
    uInc U V (n + 1) ≫ sBnd U V n = bnd (TopCat.of U) n ≫ uInc U V n := by
  have := sInc_mono U V n
  rw [← cancel_mono (sInc U V n), assoc, assoc, sBnd_comp_sInc, uInc_comp_sInc,
    ← assoc, uInc_comp_sInc]
  exact HomologicalComplex.Hom.comm (sChainMap (SingularPair.subInc X U)) (n + 1) n

lemma vInc_comm (n : ℕ) :
    vInc U V (n + 1) ≫ sBnd U V n = bnd (TopCat.of V) n ≫ vInc U V n := by
  have := sInc_mono U V n
  rw [← cancel_mono (sInc U V n), assoc, assoc, sBnd_comp_sInc, vInc_comp_sInc,
    ← assoc, vInc_comp_sInc]
  exact HomologicalComplex.Hom.comm (sChainMap (SingularPair.subInc X V)) (n + 1) n

/-- The chain map `C_*(U) ⟶ C^{U,V}_*(X)`: a simplex of `U` is small. -/
noncomputable def smallU : SC (TopCat.of U) ⟶ SSC U V where
  f n := uInc U V n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [SSC_d]
    exact uInc_comm U V j

/-- The chain map `C_*(V) ⟶ C^{U,V}_*(X)`: a simplex of `V` is small. -/
noncomputable def smallV : SC (TopCat.of V) ⟶ SSC U V where
  f n := vInc U V n
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [SSC_d]
    exact vInc_comm U V j

@[simp] lemma smallU_f (n : ℕ) : (smallU U V).f n = uInc U V n := rfl
@[simp] lemma smallV_f (n : ℕ) : (smallV U V).f n = vInc U V n := rfl

lemma smallU_comp_smallι :
    smallU U V ≫ smallι U V = sChainMap (SingularPair.subInc X U) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact uInc_comp_sInc U V n

lemma smallV_comp_smallι :
    smallV U V ≫ smallι U V = sChainMap (SingularPair.subInc X V) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact vInc_comp_sInc U V n

/-- The space-level inclusion `U ∩ V ↪ U`. -/
noncomputable def mvInclU : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
  subIncl Set.inter_subset_left

/-- The space-level inclusion `U ∩ V ↪ V`. -/
noncomputable def mvInclV : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
  subIncl Set.inter_subset_right

lemma pushIdx_mvInclU {n : ℕ} (a : Idx (TopCat.of (U ∩ V : Set X)) n) :
    pushIdx U ((TopCat.toSSet.map (mvInclU U V)).app (op ⦋n⦌) a) =
      pushIdx (U ∩ V : Set X) a :=
  pushIdx_subIncl Set.inter_subset_left a

lemma pushIdx_mvInclV {n : ℕ} (a : Idx (TopCat.of (U ∩ V : Set X)) n) :
    pushIdx V ((TopCat.toSSet.map (mvInclV U V)).app (op ⦋n⦌) a) =
      pushIdx (U ∩ V : Set X) a :=
  pushIdx_subIncl Set.inter_subset_right a

/-- Both routes `C_n(U ∩ V) ⟶ C_n^{U,V}` agree: through `U` and through
`V` a simplex of the intersection lands on the same small generator. -/
lemma inclU_uInc_eq_inclV_vInc (n : ℕ) :
    chainMap (mvInclU U V) n ≫ uInc U V n =
      chainMap (mvInclV U V) n ≫ vInc U V n := by
  apply Sigma.hom_ext
  intro a
  rw [← assoc]
  rw [show Sigma.ι (fun _ : Idx (TopCat.of (U ∩ V : Set X)) n =>
      ModuleCat.of ℤ ℤ) a ≫ chainMap (mvInclU U V) n =
      gen (TopCat.of U) n ((TopCat.toSSet.map (mvInclU U V)).app (op ⦋n⦌) a)
    from gen_map (mvInclU U V) n a]
  rw [gen_uInc, ← assoc]
  rw [show Sigma.ι (fun _ : Idx (TopCat.of (U ∩ V : Set X)) n =>
      ModuleCat.of ℤ ℤ) a ≫ chainMap (mvInclV U V) n =
      gen (TopCat.of V) n ((TopCat.toSSet.map (mvInclV U V)).app (op ⦋n⦌) a)
    from gen_map (mvInclV U V) n a]
  rw [gen_vInc]
  congr 1

lemma sChainMap_inclU_smallU_eq :
    sChainMap (mvInclU U V) ≫ smallU U V =
      sChainMap (mvInclV U V) ≫ smallV U V := by
  apply HomologicalComplex.hom_ext
  intro n
  exact inclU_uInc_eq_inclV_vInc U V n

end MVMaps

/-! ## Stage 3: the Mayer-Vietoris short exact sequence -/

section MVSES

/-- The left map `x ↦ (i_* x, −j_* x)` of the Mayer-Vietoris sequence. -/
noncomputable def mvα :
    SC (TopCat.of (U ∩ V : Set X)) ⟶ SC (TopCat.of U) ⊞ SC (TopCat.of V) :=
  biprod.lift (sChainMap (mvInclU U V)) (-(sChainMap (mvInclV U V)))

/-- The right map `(a, b) ↦ k_* a + l_* b` into the small subcomplex. -/
noncomputable def mvβ :
    SC (TopCat.of U) ⊞ SC (TopCat.of V) ⟶ SSC U V :=
  biprod.desc (smallU U V) (smallV U V)

lemma mvα_comp_mvβ : mvα U V ≫ mvβ U V = 0 := by
  rw [mvα, mvβ, biprod.lift_desc, sChainMap_inclU_smallU_eq,
    Preadditive.neg_comp]
  exact add_neg_cancel _

/-- **Stage 3.** The Mayer-Vietoris short complex of chain complexes
`0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0`. -/
noncomputable def mvSES : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (mvα U V) (mvβ U V) (mvα_comp_mvβ U V)

lemma mvαβ_degreewise_zero (n : ℕ) :
    biprod.lift (chainMap (mvInclU U V) n) (-(chainMap (mvInclV U V) n)) ≫
      biprod.desc (uInc U V n) (vInc U V n) = 0 := by
  rw [biprod.lift_desc, inclU_uInc_eq_inclV_vInc, Preadditive.neg_comp]
  exact add_neg_cancel _

/-- The degree-`n` concrete Mayer-Vietoris short complex of `ℤ`-modules. -/
noncomputable def mvSESdeg (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk
    (biprod.lift (chainMap (mvInclU U V) n) (-(chainMap (mvInclV U V) n)))
    (biprod.desc (uInc U V n) (vInc U V n))
    (mvαβ_degreewise_zero U V n)

lemma mvSESdeg_mono (n : ℕ) : Mono (mvSESdeg U V n).f := by
  show Mono (biprod.lift (chainMap (mvInclU U V) n) (-(chainMap (mvInclV U V) n)))
  haveI h1 : Mono (chainMap (mvInclU U V) n) :=
    SingularPair.chainMap_mono _
      (fun a b hab => Set.inclusion_injective Set.inter_subset_left hab) n
  exact mono_of_mono_fac (biprod.lift_fst _ _)

lemma mvSESdeg_epi (n : ℕ) : Epi (mvSESdeg U V n).g := by
  show Epi (biprod.desc (uInc U V n) (vInc U V n))
  rw [ModuleCat.epi_iff_surjective]
  intro y
  induction y using freeInduction with
  | unit t =>
      rcases t.2 with h | h
      · refine ⟨(biprod.inl : Cgrp (TopCat.of U) n ⟶ _)
          (unitOf (liftIdx U t.1 h)), ?_⟩
        rw [← ModuleCat.comp_apply, biprod.inl_desc, uInc_unitOf]
        congr 1
      · refine ⟨(biprod.inr : Cgrp (TopCat.of V) n ⟶ _)
          (unitOf (liftIdx V t.1 h)), ?_⟩
        rw [← ModuleCat.comp_apply, biprod.inr_desc, vInc_unitOf]
        congr 1
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | smulz c x hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨c • a, by rw [mapSmul, ha]⟩

/-- The heart of the Mayer-Vietoris exactness: a pair of chains on `U` and
`V` whose images in the small complex cancel comes from a chain on
`U ∩ V`. -/
lemma mv_middle_exact (n : ℕ) {a : ↥(Cgrp (TopCat.of U) n)}
    {b : ↥(Cgrp (TopCat.of V) n)}
    (hab : uInc U V n a + vInc U V n b = 0) :
    ∃ x : ↥(Cgrp (TopCat.of (U ∩ V : Set X)) n),
      chainMap (mvInclU U V) n x = a ∧ chainMap (mvInclV U V) n x = -b := by
  classical
  have hsupp : ∀ i ∈ suppOf a,
      Set.range ⇑(simplexEquiv X n (pushIdx U i)) ⊆ U ∩ V := by
    intro i hi
    by_cases hmem : ∃ j : Idx (TopCat.of V) n, vIdx U V j = uIdx U V i
    · obtain ⟨j, hj⟩ := hmem
      have hUV : pushIdx V j = pushIdx U i := congrArg Subtype.val hj
      intro x hx
      refine ⟨range_pushIdx U i hx, ?_⟩
      rw [← hUV] at hx
      exact range_pushIdx V j hx
    · exfalso
      have hne : coordAt i a ≠ 0 := mem_suppOf_iff.mp hi
      have h1 : coordAt (uIdx U V i) (uInc U V n a) = coordAt i a :=
        coordAt_map_eq (uIdx_injective U V n) (uInc_unitOf U V) i a
      have h2 : coordAt (uIdx U V i) (vInc U V n b) = 0 :=
        coordAt_map_notMem (vInc_unitOf U V) (fun j hj => hmem ⟨j, hj⟩) b
      have h3 : coordAt (uIdx U V i) (uInc U V n a) +
          coordAt (uIdx U V i) (vInc U V n b) = 0 := by
        rw [← coordAt_add, hab, coordAt_zero]
      rw [h1, h2, add_zero] at h3
      exact hne h3
  set x : ↥(Cgrp (TopCat.of (U ∩ V : Set X)) n) :=
    ∑ i ∈ (suppOf a).attach,
      coordAt i.1 a • unitOf (liftIdx (U ∩ V : Set X) (pushIdx U i.1)
        (hsupp i.1 i.2)) with hxdef
  have hterm : ∀ i ∈ (suppOf a).attach,
      chainMap (mvInclU U V) n (coordAt i.1 a •
        unitOf (liftIdx (U ∩ V : Set X) (pushIdx U i.1) (hsupp i.1 i.2))) =
        coordAt i.1 a • unitOf i.1 := by
    intro i _
    have hidx : (TopCat.toSSet.map (mvInclU U V)).app (op ⦋n⦌)
        (liftIdx (U ∩ V : Set X) (pushIdx U i.1) (hsupp i.1 i.2)) = i.1 := by
      apply pushIdx_injective U n
      rw [pushIdx_mvInclU, pushIdx_liftIdx]
    rw [mapSmul, chainMap_unitOf, hidx]
  have hxU : chainMap (mvInclU U V) n x = a := by
    calc chainMap (mvInclU U V) n x
        = ∑ i ∈ (suppOf a).attach, coordAt i.1 a • unitOf i.1 := by
          rw [hxdef, map_sum]
          exact Finset.sum_congr rfl hterm
      _ = ∑ i ∈ suppOf a, coordAt i a • unitOf i :=
          Finset.sum_attach (suppOf a) (fun i => coordAt i a • unitOf i)
      _ = a := (sum_coordAt_smul_unitOf a).symm
  have hxV : vInc U V n (chainMap (mvInclV U V) n x) = uInc U V n a := by
    rw [← ModuleCat.comp_apply, ← inclU_uInc_eq_inclV_vInc,
      ModuleCat.comp_apply, hxU]
  refine ⟨x, hxU, ?_⟩
  apply vInc_injective U V n
  rw [map_neg, hxV]
  exact eq_neg_of_add_eq_zero_left hab

lemma mvSESdeg_exact (n : ℕ) : (mvSESdeg U V n).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  have hz' : uInc U V n
      ((biprod.fst : Cgrp (TopCat.of U) n ⊞ Cgrp (TopCat.of V) n ⟶ _) z) +
      vInc U V n
      ((biprod.snd : Cgrp (TopCat.of U) n ⊞ Cgrp (TopCat.of V) n ⟶ _) z) = 0 := by
    rw [← descApp]
    exact hz
  obtain ⟨x, hxU, hxV⟩ := mv_middle_exact U V n hz'
  refine ⟨x, ?_⟩
  apply biprod_elem_ext
  · rw [show (mvSESdeg U V n).f x = biprod.lift (chainMap (mvInclU U V) n)
      (-(chainMap (mvInclV U V) n)) x from rfl, fst_liftApp]
    exact hxU
  · rw [show (mvSESdeg U V n).f x = biprod.lift (chainMap (mvInclU U V) n)
      (-(chainMap (mvInclV U V) n)) x from rfl, snd_liftApp, negApp, hxV,
      neg_neg]

lemma mvSESdeg_shortExact (n : ℕ) : (mvSESdeg U V n).ShortExact where
  exact := mvSESdeg_exact U V n
  mono_f := mvSESdeg_mono U V n
  epi_g := mvSESdeg_epi U V n

lemma mvα_f_compat (n : ℕ) :
    (mvα U V).f n ≫
      (HomologicalComplex.biprodXIso (SC (TopCat.of U)) (SC (TopCat.of V)) n).hom =
      biprod.lift (chainMap (mvInclU U V) n) (-(chainMap (mvInclV U V) n)) := by
  have hf : mvα U V ≫ biprod.fst = sChainMap (mvInclU U V) := biprod.lift_fst _ _
  have hs : mvα U V ≫ biprod.snd = -(sChainMap (mvInclV U V)) := biprod.lift_snd _ _
  apply biprod.hom_ext
  · rw [assoc, HomologicalComplex.biprodXIso_hom_fst,
      ← HomologicalComplex.comp_f, hf]
    exact (biprod.lift_fst _ _).symm
  · rw [assoc, HomologicalComplex.biprodXIso_hom_snd,
      ← HomologicalComplex.comp_f, hs, HomologicalComplex.neg_f_apply]
    exact (biprod.lift_snd _ _).symm

lemma mvβ_f_compat (n : ℕ) :
    (HomologicalComplex.biprodXIso (SC (TopCat.of U)) (SC (TopCat.of V)) n).inv ≫
      (mvβ U V).f n = biprod.desc (uInc U V n) (vInc U V n) := by
  have hu : (biprod.inl : SC (TopCat.of U) ⟶ _) ≫ mvβ U V = smallU U V :=
    biprod.inl_desc _ _
  have hv : (biprod.inr : SC (TopCat.of V) ⟶ _) ≫ mvβ U V = smallV U V :=
    biprod.inr_desc _ _
  apply biprod.hom_ext'
  · rw [← assoc, HomologicalComplex.inl_biprodXIso_inv, biprod.inl_desc,
      ← HomologicalComplex.comp_f, hu, smallU_f]
  · rw [← assoc, HomologicalComplex.inr_biprodXIso_inv, biprod.inr_desc,
      ← HomologicalComplex.comp_f, hv, smallV_f]

/-- Degreewise, the Mayer-Vietoris short complex is isomorphic to the
concrete short complex of `ℤ`-modules. -/
noncomputable def mvSESdegIso (n : ℕ) :
    mvSESdeg U V n ≅ (mvSES U V).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) := by
  refine ShortComplex.isoMk (Iso.refl _)
    (HomologicalComplex.biprodXIso (SC (TopCat.of U)) (SC (TopCat.of V)) n).symm
    (Iso.refl _) ?_ ?_
  · show (Iso.refl _).hom ≫ (mvα U V).f n =
      biprod.lift (chainMap (mvInclU U V) n) (-(chainMap (mvInclV U V) n)) ≫
        (HomologicalComplex.biprodXIso (SC (TopCat.of U)) (SC (TopCat.of V)) n).inv
    rw [Iso.refl_hom, id_comp, ← mvα_f_compat, assoc, Iso.hom_inv_id, comp_id]
  · show (HomologicalComplex.biprodXIso (SC (TopCat.of U))
      (SC (TopCat.of V)) n).inv ≫ (mvβ U V).f n =
      biprod.desc (uInc U V n) (vInc U V n) ≫ (Iso.refl _).hom
    rw [Iso.refl_hom, comp_id, mvβ_f_compat]

lemma mvSES_degreewise_shortExact (n : ℕ) :
    ((mvSES U V).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  ShortComplex.shortExact_of_iso (mvSESdegIso U V n) (mvSESdeg_shortExact U V n)

/-- **Stage 3.** The Mayer-Vietoris sequence
`0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0` is a short exact
sequence of chain complexes (no openness or covering hypotheses needed). -/
theorem mvSES_shortExact : (mvSES U V).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (mvSES_degreewise_shortExact U V)

end MVSES

/-! ## Stage 4: the Mayer-Vietoris long exact sequence -/

section MVLES

attribute [local instance] Limits.preservesBinaryBiproducts_of_preservesBiproducts

/-- The degree-`n` homology functor on chain complexes of `ℤ`-modules. -/
noncomputable abbrev HF (n : ℕ) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ ⥤ ModuleCat.{0} ℤ :=
  HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

/-- Additivity of homology: `H_n(C_*(U) ⊞ C_*(V)) ≅ H_n(U) ⊞ H_n(V)`. -/
noncomputable def homologyBiprodIso (n : ℕ) :
    (SC (TopCat.of U) ⊞ SC (TopCat.of V)).homology n ≅
      (SC (TopCat.of U)).homology n ⊞ (SC (TopCat.of V)).homology n :=
  (HF n).mapBiprod (SC (TopCat.of U)) (SC (TopCat.of V))

/-- The Mayer-Vietoris pair map
`H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V)`, `[c] ↦ ([i_* c], −[j_* c])`, induced by the
space-level inclusions `U ∩ V ↪ U` and `U ∩ V ↪ V`. -/
noncomputable def mvPair (n : ℕ) :
    (SC (TopCat.of (U ∩ V : Set X))).homology n ⟶
      (SC (TopCat.of U)).homology n ⊞ (SC (TopCat.of V)).homology n :=
  biprod.lift (HomologicalComplex.homologyMap (sChainMap (mvInclU U V)) n)
    (-(HomologicalComplex.homologyMap (sChainMap (mvInclV U V)) n))

/-- The Mayer-Vietoris sum map `H_n(U) ⊞ H_n(V) ⟶ H_n(X)`,
`([a], [b]) ↦ [k_* a] + [l_* b]`, induced by the space-level inclusions
`U ↪ X` and `V ↪ X`. -/
noncomputable def mvSum (n : ℕ) :
    (SC (TopCat.of U)).homology n ⊞ (SC (TopCat.of V)).homology n ⟶
      (SC X).homology n :=
  biprod.desc
    (HomologicalComplex.homologyMap (sChainMap (SingularPair.subInc X U)) n)
    (HomologicalComplex.homologyMap (sChainMap (SingularPair.subInc X V)) n)

variable {U V}

/-- **The Mayer-Vietoris connecting homomorphism**
`∂ : H_{n+1}(X) ⟶ H_n(U ∩ V)`, transported across the small-chains
isomorphism of Stage 2. -/
noncomputable def mvδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (SC X).homology (n + 1) ⟶ (SC (TopCat.of (U ∩ V : Set X))).homology n :=
  (smallChainsHomologyIso hU hV hUV (n + 1)).inv ≫
    (mvSES_shortExact U V).δ (n + 1) n (ComplexShape.down_mk _ _ rfl)

lemma smallIso_hom (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (smallChainsHomologyIso hU hV hUV n).hom =
      HomologicalComplex.homologyMap (smallι U V) n := rfl

variable (U V)

lemma homologyMap_mvα_compat (n : ℕ) :
    HomologicalComplex.homologyMap (mvα U V) n ≫ (homologyBiprodIso U V n).hom =
      mvPair U V n := by
  have h := Limits.biprod.map_lift_mapBiprod (HF n)
    (SC (TopCat.of U)) (SC (TopCat.of V))
    (sChainMap (mvInclU U V)) (-(sChainMap (mvInclV U V)))
  rw [Functor.map_neg] at h
  exact h

lemma mvPair_eq (n : ℕ) :
    mvPair U V n = HomologicalComplex.homologyMap (mvα U V) n ≫
      (homologyBiprodIso U V n).hom :=
  (homologyMap_mvα_compat U V n).symm

lemma homologyMap_mvβ_compat (n : ℕ) :
    (homologyBiprodIso U V n).inv ≫
      HomologicalComplex.homologyMap (mvβ U V) n ≫
        HomologicalComplex.homologyMap (smallι U V) n = mvSum U V n := by
  have h := Limits.biprod.mapBiprod_inv_map_desc (HF n)
    (SC (TopCat.of U)) (SC (TopCat.of V)) (smallU U V) (smallV U V)
  have h2 : (homologyBiprodIso U V n).inv ≫
      HomologicalComplex.homologyMap (mvβ U V) n =
      biprod.desc ((HF n).map (smallU U V)) ((HF n).map (smallV U V)) := h
  rw [← assoc, h2]
  apply biprod.hom_ext'
  · rw [← assoc, biprod.inl_desc]
    have h3 : (biprod.inl :
        (SC (TopCat.of U)).homology n ⟶ _) ≫ mvSum U V n =
        HomologicalComplex.homologyMap
          (sChainMap (SingularPair.subInc X U)) n := biprod.inl_desc _ _
    rw [h3, ← smallU_comp_smallι]
    exact ((HF n).map_comp _ _).symm
  · rw [← assoc, biprod.inr_desc]
    have h3 : (biprod.inr :
        (SC (TopCat.of V)).homology n ⟶ _) ≫ mvSum U V n =
        HomologicalComplex.homologyMap
          (sChainMap (SingularPair.subInc X V)) n := biprod.inr_desc _ _
    rw [h3, ← smallV_comp_smallι]
    exact ((HF n).map_comp _ _).symm

lemma mvSum_eq (n : ℕ) :
    mvSum U V n = (homologyBiprodIso U V n).inv ≫
      HomologicalComplex.homologyMap (mvβ U V) n ≫
        HomologicalComplex.homologyMap (smallι U V) n :=
  (homologyMap_mvβ_compat U V n).symm

/-- `H_n(U ∩ V) → H_n(U) ⊞ H_n(V) → H_n(X)` composes to zero. -/
lemma mvPair_comp_mvSum (n : ℕ) : mvPair U V n ≫ mvSum U V n = 0 := by
  rw [mvPair_eq, mvSum_eq, assoc, Iso.hom_inv_id_assoc, ← assoc,
    ← HomologicalComplex.homologyMap_comp]
  have h : mvα U V ≫ mvβ U V = 0 := mvα_comp_mvβ U V
  rw [h, HomologicalComplex.homologyMap_zero, zero_comp]

variable {U V}

/-- `H_{n+1}(U) ⊞ H_{n+1}(V) → H_{n+1}(X) → H_n(U ∩ V)` composes to
zero. -/
lemma mvSum_comp_mvδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    mvSum U V (n + 1) ≫ mvδ hU hV hUV n = 0 := by
  have h : HomologicalComplex.homologyMap (mvβ U V) (n + 1) ≫
      (mvSES_shortExact U V).δ (n + 1) n (ComplexShape.down_mk _ _ rfl) = 0 :=
    (mvSES_shortExact U V).comp_δ (n + 1) n (ComplexShape.down_mk _ _ rfl)
  rw [mvSum_eq, mvδ, ← smallIso_hom hU hV hUV (n + 1)]
  simp only [assoc]
  rw [Iso.hom_inv_id_assoc, h, comp_zero]

/-- `H_{n+1}(X) → H_n(U ∩ V) → H_n(U) ⊞ H_n(V)` composes to zero. -/
lemma mvδ_comp_mvPair (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    mvδ hU hV hUV n ≫ mvPair U V n = 0 := by
  have h : (mvSES_shortExact U V).δ (n + 1) n (ComplexShape.down_mk _ _ rfl) ≫
      HomologicalComplex.homologyMap (mvα U V) n = 0 :=
    (mvSES_shortExact U V).δ_comp (n + 1) n (ComplexShape.down_mk _ _ rfl)
  rw [mvδ, mvPair_eq]
  simp only [assoc]
  rw [reassoc_of% h, zero_comp, comp_zero]

/-- **Mayer-Vietoris, exactness at `H_n(U ∩ V)`**:
`H_{n+1}(X) ⟶ H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V)` is exact. -/
theorem mv_exact₁ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvδ hU hV hUV n) (mvPair U V n)
      (mvδ_comp_mvPair hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((mvSES_shortExact U V).homology_exact₁ (n + 1) n
      (ComplexShape.down_mk _ _ rfl))
  refine ShortComplex.isoMk (smallChainsHomologyIso hU hV hUV (n + 1))
    (Iso.refl _) (homologyBiprodIso U V n) ?_ ?_
  · show (smallChainsHomologyIso hU hV hUV (n + 1)).hom ≫ mvδ hU hV hUV n =
      (mvSES_shortExact U V).δ (n + 1) n (ComplexShape.down_mk _ _ rfl) ≫
        (Iso.refl _).hom
    rw [mvδ, Iso.hom_inv_id_assoc, Iso.refl_hom, comp_id]
  · show (Iso.refl _).hom ≫ mvPair U V n =
      HomologicalComplex.homologyMap (mvα U V) n ≫ (homologyBiprodIso U V n).hom
    rw [Iso.refl_hom, id_comp, mvPair_eq]

/-- **Mayer-Vietoris, exactness at `H_n(U) ⊞ H_n(V)`**:
`H_n(U ∩ V) ⟶ H_n(U) ⊞ H_n(V) ⟶ H_n(X)` is exact (all degrees, including
`0`). -/
theorem mv_exact₂ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvPair U V n) (mvSum U V n)
      (mvPair_comp_mvSum U V n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((mvSES_shortExact U V).homology_exact₂ n)
  refine ShortComplex.isoMk (Iso.refl _) (homologyBiprodIso U V n)
    (smallChainsHomologyIso hU hV hUV n) ?_ ?_
  · show (Iso.refl _).hom ≫ mvPair U V n =
      HomologicalComplex.homologyMap (mvα U V) n ≫ (homologyBiprodIso U V n).hom
    rw [Iso.refl_hom, id_comp, mvPair_eq]
  · show (homologyBiprodIso U V n).hom ≫ mvSum U V n =
      HomologicalComplex.homologyMap (mvβ U V) n ≫
        (smallChainsHomologyIso hU hV hUV n).hom
    rw [mvSum_eq, Iso.hom_inv_id_assoc, smallIso_hom]

/-- **Mayer-Vietoris, exactness at `H_{n+1}(X)`**:
`H_{n+1}(U) ⊞ H_{n+1}(V) ⟶ H_{n+1}(X) ⟶ H_n(U ∩ V)` is exact. -/
theorem mv_exact₃ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvSum U V (n + 1)) (mvδ hU hV hUV n)
      (mvSum_comp_mvδ hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    ((mvSES_shortExact U V).homology_exact₃ (n + 1) n
      (ComplexShape.down_mk _ _ rfl))
  refine ShortComplex.isoMk (homologyBiprodIso U V (n + 1))
    (smallChainsHomologyIso hU hV hUV (n + 1)) (Iso.refl _) ?_ ?_
  · show (homologyBiprodIso U V (n + 1)).hom ≫ mvSum U V (n + 1) =
      HomologicalComplex.homologyMap (mvβ U V) (n + 1) ≫
        (smallChainsHomologyIso hU hV hUV (n + 1)).hom
    rw [mvSum_eq, Iso.hom_inv_id_assoc, smallIso_hom]
  · show (smallChainsHomologyIso hU hV hUV (n + 1)).hom ≫ mvδ hU hV hUV n =
      (mvSES_shortExact U V).δ (n + 1) n (ComplexShape.down_mk _ _ rfl) ≫
        (Iso.refl _).hom
    rw [mvδ, Iso.hom_inv_id_assoc, Iso.refl_hom, comp_id]

/-- **The degree-`0` tail**: `H_0(U) ⊞ H_0(V) ⟶ H_0(X)` is surjective; the
Mayer-Vietoris sequence ends `⋯ ⟶ H_0(U) ⊞ H_0(V) ⟶ H_0(X) ⟶ 0`. -/
theorem mvSum_epi_zero (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) : Epi (mvSum U V 0) := by
  haveI h1 : Epi (HomologicalComplex.homologyMap (mvβ U V) 0) := by
    refine epi_homologyMap_chain_zero (mvβ U V) ?_
    intro y
    have hepi : Epi ((mvβ U V).f 0) := (mvSES_degreewise_shortExact U V 0).epi_g
    have hsurj : Function.Surjective ((mvβ U V).f 0) :=
      (ModuleCat.epi_iff_surjective _).mp hepi
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨x, 0, ?_⟩
    rw [map_zero, add_zero, hx]
  haveI h2 : IsIso (HomologicalComplex.homologyMap (smallι U V) 0) :=
    smallι_isIso_homologyMap hU hV hUV 0
  rw [mvSum_eq]
  infer_instance

/-- **Sanity lock**: when `U = univ` (so `U` alone already covers `X`), the
Mayer-Vietoris sum map `H_n(U) ⊞ H_n(V) ⟶ H_n(X)` is an epimorphism in
every degree, because its first component is induced by the isomorphism
`univ ≃ X`. -/
theorem mvSum_epi_of_left_univ (V : Set X) (n : ℕ) :
    Epi (mvSum (Set.univ : Set X) V n) := by
  haveI hiso : IsIso (SingularPair.subInc X (Set.univ : Set X)) := by
    refine ⟨TopCat.ofHom ⟨fun x => ⟨x, trivial⟩,
      Continuous.subtype_mk continuous_id fun _ => trivial⟩, ?_, ?_⟩
    · ext x
      rfl
    · ext x
      rfl
  haveI h1 : IsIso (sChainMap (SingularPair.subInc X (Set.univ : Set X))) := by
    show IsIso (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map
      (SingularPair.subInc X (Set.univ : Set X)))
    infer_instance
  haveI h2 : Epi (HomologicalComplex.homologyMap
      (sChainMap (SingularPair.subInc X (Set.univ : Set X))) n) := by
    haveI : IsIso (HomologicalComplex.homologyMap
        (sChainMap (SingularPair.subInc X (Set.univ : Set X))) n) := by
      show IsIso ((HF n).map (sChainMap (SingularPair.subInc X (Set.univ : Set X))))
      infer_instance
    infer_instance
  have hfac : (biprod.inl :
      (SC (TopCat.of (Set.univ : Set X))).homology n ⟶ _) ≫
      mvSum (Set.univ : Set X) V n =
      HomologicalComplex.homologyMap
        (sChainMap (SingularPair.subInc X (Set.univ : Set X))) n :=
    biprod.inl_desc _ _
  exact epi_of_epi_fac hfac

end MVLES

end SingularMayerVietoris
end Foundation
end IndisputableMonolith
