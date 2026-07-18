/-
The long exact sequence of a pair in singular homology.

Layer 2 of the excision spine (layer 1: `SingularPrism.lean`, homotopy
invariance).  For an injective continuous map `f : A ⟶ X` (in particular a
subspace inclusion) this file proves, with `ℤ` coefficients:

1. the induced chain map `C_*(A) ⟶ C_*(X)` is a degreewise (split)
   monomorphism, hence a monomorphism of chain complexes
   (`chainMap_mono`, `sChainMap_mono`);
2. the relative singular chain complex `C_*(X, A)` is the cokernel
   (`relSC`), giving a short exact sequence of chain complexes
   `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0` (`pairSES`,
   `pairSES_shortExact`, degreewise form `pairSES_degreewise_shortExact`);
3. the long exact sequence of the pair via Mathlib's homology sequence:
   the connecting homomorphism `pairδ : H_{n+1}(X, A) ⟶ H_n(A)` and the
   three exactness statements `pair_les_exact₁/₂/₃`;
4. the sanity theorem `relative_homology_id_isZero`: for the identity
   inclusion `A = X` the relative homology vanishes in every degree
   (guards against a degenerate cokernel definition).

Conventions (`Idx`, `Cgrp`, `gen`, `SC`, `chainMap`, `sChainMap`,
`gen_map`, `toSSetObjEquiv_map`) are inherited from `SingularPrism`.
-/
import IndisputableMonolith.Foundation.SingularPrism
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence

namespace IndisputableMonolith
namespace Foundation
namespace SingularPair

open CategoryTheory Category Limits AlgebraicTopology Simplicial Opposite
open SingularPrism

/-! ## Part 1: injectivity on singular simplices and the degreewise mono -/

variable {A X : TopCat.{0}}

/-- An injective continuous map induces an injective map on singular
`n`-simplices (postcomposition with an injective map is injective). -/
lemma toSSet_map_app_injective (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (op ⦋n⦌)) := by
  intro a b hab
  have h1 : f.hom.comp (A.toSSetObjEquiv (op ⦋n⦌) a) =
      f.hom.comp (A.toSSetObjEquiv (op ⦋n⦌) b) := by
    rw [← toSSetObjEquiv_map f a, ← toSSetObjEquiv_map f b, hab]
  have h2 : A.toSSetObjEquiv (op ⦋n⦌) a = A.toSSetObjEquiv (op ⦋n⦌) b := by
    ext t
    apply hf
    simpa only [ContinuousMap.comp_apply] using ContinuousMap.congr_fun h1 t
  exact (A.toSSetObjEquiv (op ⦋n⦌)).injective h2

open Classical in
/-- The retraction of the degree-`n` chain map of `f`, defined on generators:
a singular simplex of `X` in the image of `f` goes to (a choice of) its
preimage, everything else goes to `0`.  For injective `f` this splits
`chainMap f n`. -/
noncomputable def genRetract (f : A ⟶ X) (n : ℕ) : Cgrp X n ⟶ Cgrp A n :=
  Sigma.desc fun x =>
    if hx : ∃ a : Idx A n, (TopCat.toSSet.map f).app (op ⦋n⦌) a = x then
      gen A n hx.choose
    else 0

/-- For injective `f`, `genRetract` retracts the chain map on generators. -/
lemma gen_comp_genRetract (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ)
    (a : Idx A n) :
    gen X n ((TopCat.toSSet.map f).app (op ⦋n⦌) a) ≫ genRetract f n = gen A n a := by
  unfold genRetract
  rw [Sigma.ι_desc]
  have hx : ∃ a' : Idx A n, (TopCat.toSSet.map f).app (op ⦋n⦌) a' =
      (TopCat.toSSet.map f).app (op ⦋n⦌) a := ⟨a, rfl⟩
  rw [dif_pos hx]
  exact congrArg (gen A n) (toSSet_map_app_injective f hf n hx.choose_spec)

/-- The chain map splits: `chainMap f n ≫ genRetract f n = 𝟙`. -/
lemma chainMap_comp_genRetract (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    chainMap f n ≫ genRetract f n = 𝟙 (Cgrp A n) := by
  apply Sigma.hom_ext
  intro a
  rw [comp_id, ← assoc, gen_map f n a]
  exact gen_comp_genRetract f hf n a

/-- An injective continuous map induces a degreewise monomorphism of
singular chain complexes. -/
lemma chainMap_mono (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    Mono (chainMap f n) :=
  mono_of_mono_fac (chainMap_comp_genRetract f hf n)

/-- An injective continuous map induces a monomorphism of singular chain
complexes. -/
lemma sChainMap_mono (f : A ⟶ X) (hf : Function.Injective f.hom) :
    Mono (sChainMap f) :=
  HomologicalComplex.mono_of_mono_f _ fun n => chainMap_mono f hf n

/-! ## Part 2: the relative chain complex and the short exact sequence -/

/-- The relative singular chain complex `C_*(X, A)`: the cokernel of the
chain map induced by `f : A ⟶ X` (degreewise the quotient
`C_n(X) / C_n(A)`, with the induced differential). -/
noncomputable def relSC (f : A ⟶ X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (sChainMap f)

/-- The projection `C_*(X) ⟶ C_*(X, A)`. -/
noncomputable def relπ (f : A ⟶ X) : SC X ⟶ relSC f :=
  cokernel.π (sChainMap f)

/-- The short complex `0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0` of singular
chain complexes attached to `f : A ⟶ X`. -/
noncomputable def pairSES (f : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (sChainMap f) (relπ f) (cokernel.condition _)

/-- For an injective continuous map, the sequence
`0 ⟶ C_*(A) ⟶ C_*(X) ⟶ C_*(X, A) ⟶ 0` is short exact. -/
lemma pairSES_shortExact (f : A ⟶ X) (hf : Function.Injective f.hom) :
    (pairSES f).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (sChainMap f))
  mono_f := sChainMap_mono f hf
  epi_g := by
    show Epi (cokernel.π (sChainMap f))
    infer_instance

/-- Degreewise form of the short exact sequence: in every degree `n`,
`0 ⟶ C_n(A) ⟶ C_n(X) ⟶ C_n(X, A) ⟶ 0` is a short exact sequence of
`ℤ`-modules. -/
lemma pairSES_degreewise_shortExact (f : A ⟶ X) (hf : Function.Injective f.hom)
    (n : ℕ) :
    ((pairSES f).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  (pairSES_shortExact f hf).map_of_exact _

/-! ## Part 3: the long exact sequence of the pair -/

/-- The connecting homomorphism `∂ : H_{n+1}(X, A) ⟶ H_n(A)` of the pair. -/
noncomputable def pairδ (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    (relSC f).homology (n + 1) ⟶ (SC A).homology n :=
  (pairSES_shortExact f hf).δ (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- `∂ ≫ H_n(A → X) = 0`. -/
lemma pairδ_comp (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    pairδ f hf n ≫ HomologicalComplex.homologyMap (sChainMap f) n = 0 :=
  (pairSES_shortExact f hf).δ_comp (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- `H_{n+1}(X → (X, A)) ≫ ∂ = 0`. -/
lemma comp_pairδ (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    HomologicalComplex.homologyMap (relπ f) (n + 1) ≫ pairδ f hf n = 0 :=
  (pairSES_shortExact f hf).comp_δ (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- The composite `H_n(A) ⟶ H_n(X) ⟶ H_n(X, A)` vanishes. -/
lemma pair_homologyMap_comp_zero (f : A ⟶ X) (n : ℕ) :
    HomologicalComplex.homologyMap (sChainMap f) n ≫
      HomologicalComplex.homologyMap (relπ f) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, relπ, cokernel.condition,
    HomologicalComplex.homologyMap_zero]

/-- **LES of the pair, exactness at `H_n(A)`**:
`H_{n+1}(X, A) ⟶ H_n(A) ⟶ H_n(X)` is exact. -/
lemma pair_les_exact₁ (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    (ShortComplex.mk (pairδ f hf n)
      (HomologicalComplex.homologyMap (sChainMap f) n)
      (pairδ_comp f hf n)).Exact :=
  (pairSES_shortExact f hf).homology_exact₁ (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-- **LES of the pair, exactness at `H_n(X)`**:
`H_n(A) ⟶ H_n(X) ⟶ H_n(X, A)` is exact (all degrees `n`, including `0`). -/
lemma pair_les_exact₂ (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (sChainMap f) n)
      (HomologicalComplex.homologyMap (relπ f) n)
      (pair_homologyMap_comp_zero f n)).Exact :=
  (pairSES_shortExact f hf).homology_exact₂ n

/-- **LES of the pair, exactness at `H_{n+1}(X, A)`**:
`H_{n+1}(X) ⟶ H_{n+1}(X, A) ⟶ H_n(A)` is exact. -/
lemma pair_les_exact₃ (f : A ⟶ X) (hf : Function.Injective f.hom) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relπ f) (n + 1))
      (pairδ f hf n)
      (comp_pairδ f hf n)).Exact :=
  (pairSES_shortExact f hf).homology_exact₃ (n + 1) n (ComplexShape.down_mk _ _ rfl)

/-! ## Part 4: subspace inclusions -/

/-- The inclusion of a subspace `S : Set X` as a morphism of `TopCat`. -/
noncomputable def subInc (X : TopCat.{0}) (S : Set X) : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

lemma subInc_injective (X : TopCat.{0}) (S : Set X) :
    Function.Injective (subInc X S).hom :=
  fun _ _ h => Subtype.ext h

/-- The short exact sequence `0 ⟶ C_*(S) ⟶ C_*(X) ⟶ C_*(X, S) ⟶ 0` for a
subspace `S : Set X`; all the LES lemmas above apply with
`f := subInc X S`, `hf := subInc_injective X S`. -/
lemma subpair_shortExact (X : TopCat.{0}) (S : Set X) :
    (pairSES (subInc X S)).ShortExact :=
  pairSES_shortExact _ (subInc_injective X S)

/-! ## Part 5: sanity theorem, `H_n(X, X) = 0` -/

/-- For the identity inclusion the relative chain complex is zero. -/
lemma relSC_id_isZero (X : TopCat.{0}) : IsZero (relSC (𝟙 X)) := by
  have h : sChainMap (𝟙 X) = 𝟙 (SC X) := CategoryTheory.Functor.map_id _ _
  have : Epi (sChainMap (𝟙 X)) := by rw [h]; infer_instance
  exact isZero_cokernel_of_epi _

/-- **Sanity**: the relative homology of the identity pair vanishes in every
degree: `H_n(X, X) = 0`.  This locks the semantics of the cokernel
definition of the relative complex. -/
theorem relative_homology_id_isZero (X : TopCat.{0}) (n : ℕ) :
    IsZero ((relSC (𝟙 X)).homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ)
    (ComplexShape.down ℕ) n).map_isZero (relSC_id_isZero X)

/-! ### Frontier note

Complete for this layer: degreewise split mono (`chainMap_mono`,
`sChainMap_mono`), the relative complex as cokernel (`relSC`), the short
exact sequence of chain complexes with its degreewise form
(`pairSES_shortExact`, `pairSES_degreewise_shortExact`), the connecting
homomorphism (`pairδ`) and the three exactness statements of the long
exact sequence of the pair (`pair_les_exact₁/₂/₃`), the subspace
specialization (`subInc`, `subpair_shortExact`), and the sanity theorem
`relative_homology_id_isZero` (`H_n(X, X) = 0`).

Deferred (new scope, not required for the excision spine):

* Reduced homology (augmentation `C_0(X) → ℤ` and the reduced LES): not
  needed by the layer-3 excision argument, which works with the relative
  complexes directly; cheap to add later via the augmented complex.
* A concrete degreewise description `C_n(X, A) ≅ C_n(X)/C_n(A)` as an
  explicit quotient module: downstream work should instead use
  `pairSES_degreewise_shortExact` (degree-`n` projection is the cokernel
  of the degree-`n` inclusion), which is the categorical form of the same
  fact.
-/

end SingularPair
end Foundation
end IndisputableMonolith
