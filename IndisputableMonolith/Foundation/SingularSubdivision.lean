/-
Barycentric subdivision and (toward) the small-simplices theorem for
Mathlib's singular homology (Hatcher §2.1, proof of excision, pp. 119–124).

## Design

Everything possible is done on a purely combinatorial *affine chain* layer:
an affine `n`-simplex in a type `α` is a vertex tuple `Fin (n+1) → α`, and an
affine `n`-chain is a finitely supported `ℤ`-linear combination of tuples,
`AC α n := (Fin (n+1) → α) →₀ ℤ`.  Faces are tuple reindexings along
`Fin.succAbove`, the cone with apex `b` is `Fin.cons b`, and the barycentric
subdivision `asub` and the chain homotopy `atee` are defined by the classical
cone recursions

  `S λ = b_λ · S (∂ λ)`,   `T λ = b_λ · (λ − T (∂ λ))`,

parametrized by an *abstract* apex function `bary`.  All chain identities
(`∂∂ = 0`, the cone identity `∂(b·c) = c − b·∂c`, the chain-map property
`∂S = S∂`, the homotopy identity `∂T + T∂ = 1 − S`, and the telescoped
iterate identity for `S^k`) hold at this combinatorial level, for *any*
apex function (degree 0 needs only `bary 0 w = w 0`).

The geometry (the honest barycenter on `stdSimplex`, the realization of a
vertex tuple as a continuous affine map, the diameter estimate) enters only
in the later stages, and the transport to Mathlib's singular chain complex
reuses the `Idx`/`gen`/`gen_d`/`gen_map` normal forms of
`IndisputableMonolith.Foundation.SingularPrism`.

## Stages (each stage builds green before the next begins)

* Stage 1: affine chains, boundary, cone, augmentation; generator normal
  forms.
* Stage 2: the chain identities: cone identity (positive degrees and
  degree 0), `∂∂ = 0`, `ε∂ = 0`.
* Stage 3: the barycentric subdivision operator `asub` and the chain-map
  property `∂S = S∂`.
* Stage 4: the chain homotopy `atee` with `∂T + T∂ = 1 − S`, and the
  telescoped homotopy for the iterate `S^k`.
* Stage 5a: pushforward `amap` of affine chains along a vertex map and
  equivariance of `abnd`/`acone`/`asub`/`atee` under barycenter-preserving
  maps.
* Stage 5b: geometry on `stdSimplex`: the affine realization `affineMap` of
  a vertex tuple, functoriality, vertices, faces, the identity tuple, the
  honest barycenter `sbary` and its equivariance `sbary_affineMap`.
* Stage 5c: transport to Mathlib's singular chain complex: the singular
  subdivision `sdOp X n : C_n(X) ⟶ C_n(X)` and homotopy
  `tOp X n : C_n(X) ⟶ C_{n+1}(X)`, the chain-map property `sdOp_comp_bnd`,
  the homotopy identities `tOp_chain_homotopy_succ`/`_zero`, naturality
  `sdOp_natural`/`tOp_natural`, and the iterates `sdOpIter`/`tOpIter` with
  `sdOpIter_comp_bnd` and `tOpIter_chain_homotopy_succ`/`_zero`.
* Stage 6: the diameter estimate: support tracking of `asub` through the
  cone recursion (`asub_support_bound`), the `n/(n+1)` contraction with the
  convex-hull maximum principle, iterates (`asubIter_support_bound`), and
  geometric decay (`exists_asubIter_small`).
* Stage 7: the small-simplices theorem `exists_sdOpIter_small`: for open
  `U ∪ V = X` and any singular simplex, some iterate of the singular
  subdivision has every piece landing in `U` or in `V` (Lebesgue number on
  the compact metric `Δⁿ`); combined with `gen_comp_sdOpIter` and the
  homotopy witness `tOpIter_chain_homotopy_succ`/`_zero`, this is the input
  the next layer needs for excision / Mayer-Vietoris.

## Frontier (next layer)

The two-set small-chains subcomplex `C^{U,V}_*(X)` (chains all of whose
generators are `U`-small or `V`-small) and the surjectivity of
`H_*(C^{U,V}) → H_*(C)` remain to be packaged: `exists_sdOpIter_small`
gives, for each cycle generator, an iterate `k` landing in the subcomplex,
and `tOpIter_chain_homotopy_*` gives the homology-class-preserving witness;
the remaining work is uniformizing `k` over the finitely many generators of
a chain (take the max) and assembling the subcomplex as a `ChainComplex`
with the inclusion map, feeding `SingularPair.lean`'s LES machinery toward
Mayer-Vietoris and excision.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import IndisputableMonolith.Foundation.SingularPrism

namespace IndisputableMonolith
namespace Foundation
namespace SingularSubdivision

open CategoryTheory Limits AlgebraicTopology Simplicial Opposite

/-! ## Stage 1: affine chains, boundary, cone, augmentation -/

variable {α β : Type} {n : ℕ}

/-- The group of affine `n`-chains in `α`: finitely supported `ℤ`-linear
combinations of vertex tuples `Fin (n+1) → α`. -/
abbrev AC (α : Type) (n : ℕ) : Type := (Fin (n + 1) → α) →₀ ℤ

/-- The affine simplex (generator) attached to a vertex tuple. -/
noncomputable def asimplex (w : Fin (n + 1) → α) : AC α n := Finsupp.single w 1

/-- Extensionality for linear maps out of `AC α n`: it suffices to agree on
generators. -/
lemma AC.hom_ext {M : Type*} [AddCommGroup M] [Module ℤ M]
    {φ ψ : AC α n →ₗ[ℤ] M} (h : ∀ w, φ (asimplex w) = ψ (asimplex w)) :
    φ = ψ := by
  refine Finsupp.lhom_ext fun a b => ?_
  have hsingle : (Finsupp.single a b : AC α n) = b • asimplex a := by
    rw [asimplex, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, LinearMap.map_smul, LinearMap.map_smul, h]

/-- Evaluation of a `Finsupp.linearCombination`-defined map on a generator. -/
lemma lift_asimplex {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : (Fin (n + 1) → α) → M) (w : Fin (n + 1) → α) :
    Finsupp.linearCombination ℤ f (asimplex w) = f w := by
  rw [asimplex, Finsupp.linearCombination_single, one_smul]

/-- The boundary of affine chains, `∂ : AC α (n+1) → AC α n`, the alternating
sum of the tuple faces `w ∘ Fin.succAbove i`. -/
noncomputable def abnd (n : ℕ) : AC α (n + 1) →ₗ[ℤ] AC α n :=
  Finsupp.linearCombination ℤ
    (fun w : Fin (n + 2) → α =>
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • asimplex (w ∘ i.succAbove))

/-- The boundary of a generator is the alternating sum of its faces. -/
lemma abnd_asimplex (w : Fin (n + 2) → α) :
    abnd n (asimplex w) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • asimplex (w ∘ i.succAbove) :=
  lift_asimplex _ w

/-- The cone with apex `b`, `AC α n → AC α (n+1)`: prepend `b` to every
vertex tuple. -/
noncomputable def acone (b : α) : AC α n →ₗ[ℤ] AC α (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun w => Fin.cons b w)

/-- The cone of a generator. -/
lemma acone_asimplex (b : α) (w : Fin (n + 1) → α) :
    acone b (asimplex w) = asimplex (Fin.cons b w) := by
  rw [acone, asimplex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, asimplex]

/-- The augmentation `ε : AC α 0 → ℤ` (sum of coefficients). -/
noncomputable def eps (α : Type) : AC α 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Fin 1 → α => (1 : ℤ))

lemma eps_asimplex (w : Fin 1 → α) : eps α (asimplex w) = 1 :=
  lift_asimplex _ w

/-! ### Tuple bookkeeping for cones and faces -/

/-- The `0`-th face of a cone is the base tuple. -/
lemma cons_comp_succAbove_zero (b : α) (w : Fin (n + 1) → α) :
    (Fin.cons b w) ∘ (Fin.succAbove 0) = w := by
  funext k
  simp only [Function.comp_apply, Fin.zero_succAbove, Fin.cons_succ]

/-- The `(j+1)`-th face of a cone is the cone on the `j`-th face. -/
lemma cons_comp_succAbove_succ (b : α) (w : Fin (n + 1) → α) (j : Fin (n + 1)) :
    (Fin.cons b w) ∘ (Fin.succAbove j.succ) = Fin.cons b (w ∘ j.succAbove) := by
  funext k
  induction k using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ k => simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

/-! ## Stage 2: the chain identities -/

/-- The cone identity in positive degrees: `∂ (b · c) = c − b · (∂ c)`
for `c : AC α (n+1)`. -/
theorem abnd_comp_acone (b : α) (n : ℕ) :
    (abnd (n + 1)).comp (acone b : AC α (n + 1) →ₗ[ℤ] AC α (n + 2)) =
      LinearMap.id - (acone b).comp (abnd n) := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, acone_asimplex, abnd_asimplex, Fin.sum_univ_succ,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, abnd_asimplex,
    map_sum, Fin.val_zero, pow_zero, one_smul, cons_comp_succAbove_zero,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, acone_asimplex, cons_comp_succAbove_succ, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul]

/-- The cone identity in degree `0`:
`∂ (b · c) = c − ε(c) · [b]` for `c : AC α 0`. -/
theorem abnd_comp_acone_zero (b : α) :
    (abnd 0).comp (acone b : AC α 0 →ₗ[ℤ] AC α 1) =
      LinearMap.id -
        (LinearMap.toSpanSingleton ℤ (AC α 0) (asimplex fun _ => b)).comp (eps α) := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, acone_asimplex, abnd_asimplex, Fin.sum_univ_two]
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, eps_asimplex,
    LinearMap.toSpanSingleton_apply, one_smul]
  have h0 : (Fin.cons b w) ∘ (Fin.succAbove (0 : Fin 2)) = w :=
    cons_comp_succAbove_zero b w
  have h1 : (Fin.cons b w) ∘ (Fin.succAbove (1 : Fin 2)) = (fun _ => b) := by
    funext k
    have hk : k = 0 := Subsingleton.elim k 0
    subst hk
    simp only [Function.comp_apply]
    have h : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := rfl
    rw [h, Fin.cons_zero]
  rw [h0, h1]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [sub_eq_add_neg]

/-- `∂∂ = 0` on affine chains. -/
theorem abnd_comp_abnd (n : ℕ) :
    (abnd n).comp (abnd (n + 1)) = (0 : AC α (n + 2) →ₗ[ℤ] AC α n) := by
  classical
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, abnd_asimplex, map_sum, LinearMap.zero_apply]
  have hexp : ∀ i : Fin (n + 3),
      abnd n ((-1 : ℤ) ^ (i : ℕ) • asimplex (w ∘ i.succAbove)) =
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) •
          asimplex (w ∘ i.succAbove ∘ j.succAbove) := by
    intro i
    rw [map_smul, abnd_asimplex, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_add]
    rfl
  simp only [hexp]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2)))
    (fun p => (p.2 : ℕ) < (p.1 : ℕ))
    (fun p => (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) •
      asimplex (w ∘ p.1.succAbove ∘ p.2.succAbove))
  rw [← hsplit]
  have hcancel : (∑ p ∈ Finset.univ.filter
        (fun p : Fin (n + 3) × Fin (n + 2) => (p.2 : ℕ) < (p.1 : ℕ)),
        (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) •
          asimplex (w ∘ p.1.succAbove ∘ p.2.succAbove)) =
      -∑ p ∈ Finset.univ.filter
        (fun p : Fin (n + 3) × Fin (n + 2) => ¬ (p.2 : ℕ) < (p.1 : ℕ)),
        (-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ)) •
          asimplex (w ∘ p.1.succAbove ∘ p.2.succAbove) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij'
      (i := fun p hp => ((⟨(p.2 : ℕ), by
          simp only [Finset.mem_filter_univ] at hp
          omega⟩ : Fin (n + 3)),
        (⟨(p.1 : ℕ) - 1, by
          have := p.1.isLt
          omega⟩ : Fin (n + 2))))
      (j := fun q hq => ((⟨(q.2 : ℕ) + 1, by
          have := q.2.isLt
          omega⟩ : Fin (n + 3)),
        (⟨(q.1 : ℕ), by
          simp only [Finset.mem_filter_univ] at hq
          have := q.2.isLt
          omega⟩ : Fin (n + 2))))
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp ⊢
      omega
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq ⊢
      omega
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      ext
      all_goals (try dsimp only)
      all_goals omega
    · intro q hq
      simp only [Finset.mem_filter_univ] at hq
      ext
      all_goals (try dsimp only)
      all_goals omega
    · intro p hp
      simp only [Finset.mem_filter_univ] at hp
      have htuple : w ∘ p.1.succAbove ∘ p.2.succAbove =
          w ∘ (⟨(p.2 : ℕ), by omega⟩ : Fin (n + 3)).succAbove ∘
            (⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin (n + 2)).succAbove := by
      -- faces commute: δ_i δ_j = δ_j δ_{i-1} for j < i
        funext k
        apply congrArg w
        apply Fin.ext
        have hk := k.isLt
        simp only [Function.comp_apply, SingularPrism.coe_succAbove]
        split_ifs <;> omega
      rw [htuple]
      have hsign : ((p.1 : ℕ) + (p.2 : ℕ)) =
          (((⟨(p.2 : ℕ), by omega⟩ : Fin (n + 3)) : ℕ) +
            ((⟨(p.1 : ℕ) - 1, by have := p.1.isLt; omega⟩ : Fin (n + 2)) : ℕ)) + 1 := by
        dsimp only
        omega
      rw [hsign, pow_succ, mul_neg_one, neg_smul]
  rw [hcancel, neg_add_cancel]

/-- The augmentation kills boundaries: `ε ∘ ∂ = 0`. -/
theorem eps_comp_abnd : (eps α).comp (abnd 0) = 0 := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, abnd_asimplex, map_sum, Fin.sum_univ_two,
    LinearMap.zero_apply]
  simp only [map_smul, eps_asimplex, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    smul_eq_mul, mul_one]
  omega

/-! ## Stage 3: the barycentric subdivision operator and `∂S = S∂`

The subdivision operator is parametrized by an abstract apex function
`bary` assigning to every vertex tuple a point (the barycenter, in the
geometric realization); all chain identities hold for any such function. -/

/-- The barycentric subdivision operator on affine chains, defined by the
cone recursion `S(σ) = b_σ · S(∂σ)` on generators (`S = id` in degree 0). -/
noncomputable def asub (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    ∀ n, AC α n →ₗ[ℤ] AC α n
  | 0 => LinearMap.id
  | n + 1 => Finsupp.linearCombination ℤ
      (fun w : Fin (n + 2) → α =>
        acone (bary w) (asub bary n (abnd n (asimplex w))))

@[simp] lemma asub_zero (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    asub bary 0 = LinearMap.id := rfl

lemma asub_asimplex (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (n : ℕ)
    (w : Fin (n + 2) → α) :
    asub bary (n + 1) (asimplex w) =
      acone (bary w) (asub bary n (abnd n (asimplex w))) :=
  lift_asimplex _ w

/-- The chain-map property of barycentric subdivision: `∂ ∘ S = S ∘ ∂`. -/
theorem abnd_comp_asub (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    ∀ n, (abnd n).comp (asub bary (n + 1)) = (asub bary n).comp (abnd n)
  | 0 => by
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, asub_asimplex, asub_zero,
      LinearMap.id_apply]
    have hcone := LinearMap.congr_fun (abnd_comp_acone_zero (bary w) (α := α))
      (abnd 0 (asimplex w))
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply] at hcone
    rw [hcone]
    have heps := LinearMap.congr_fun (eps_comp_abnd (α := α)) (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at heps
    rw [heps, map_zero, sub_zero]
  | n + 1 => by
    have IH := abnd_comp_asub bary n
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, asub_asimplex]
    have hcone := LinearMap.congr_fun (abnd_comp_acone (bary w) n (α := α))
      (asub bary (n + 1) (abnd (n + 1) (asimplex w)))
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply] at hcone
    rw [hcone]
    have hIH := LinearMap.congr_fun IH (abnd (n + 1) (asimplex w))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hIH
    rw [hIH]
    have hdd := LinearMap.congr_fun (abnd_comp_abnd n (α := α)) (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    rw [hdd, map_zero, map_zero, sub_zero]

/-! ## Stage 4: the chain homotopy `T` with `∂T + T∂ = id − S`,
and the telescoped homotopy for the iterate `S^k` -/

/-- The subdivision chain homotopy on affine chains, defined by the cone
recursion `T(σ) = b_σ · (σ − T(∂σ))` on generators (`T = 0` in degree 0). -/
noncomputable def atee (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    ∀ n, AC α n →ₗ[ℤ] AC α (n + 1)
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℤ
      (fun w : Fin (n + 2) → α =>
        acone (bary w) (asimplex w - atee bary n (abnd n (asimplex w))))

@[simp] lemma atee_zero (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    atee bary 0 = 0 := rfl

lemma atee_asimplex (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (n : ℕ)
    (w : Fin (n + 2) → α) :
    atee bary (n + 1) (asimplex w) =
      acone (bary w) (asimplex w - atee bary n (abnd n (asimplex w))) :=
  lift_asimplex _ w

/-- The chain homotopy identity in degree 0 (trivially, since `T = 0` and
`S = id` there): `∂ ∘ T = id − S`. -/
theorem abnd_comp_atee_zero (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    (abnd 0).comp (atee bary 0) = LinearMap.id - asub bary (0 : ℕ) := by
  rw [atee_zero, asub_zero, LinearMap.comp_zero, sub_self]

/-- The chain homotopy identity in positive degrees:
`∂ ∘ T + T ∘ ∂ = id − S` on `AC α (n+1)` (Hatcher, proof of Prop. 2.21). -/
theorem abnd_comp_atee (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) :
    ∀ n, (abnd (n + 1)).comp (atee bary (n + 1)) + (atee bary n).comp (abnd n)
      = LinearMap.id - asub bary (n + 1)
  | 0 => by
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, atee_asimplex, atee_zero,
      LinearMap.zero_apply, sub_zero, add_zero, asub_asimplex, asub_zero,
      LinearMap.id_apply]
    have hcone := LinearMap.congr_fun (abnd_comp_acone (bary w) 0 (α := α))
      (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply] at hcone
    rw [hcone]
  | n + 1 => by
    have IH := abnd_comp_atee bary n
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.id_apply, atee_asimplex, asub_asimplex]
    have hcone := LinearMap.congr_fun (abnd_comp_acone (bary w) (n + 1) (α := α))
      (asimplex w - atee bary (n + 1) (abnd (n + 1) (asimplex w)))
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply] at hcone
    rw [hcone, map_sub]
    -- compute `∂(σ − T∂σ) = S∂σ` from the inductive hypothesis and `∂∂ = 0`
    have hIH := LinearMap.congr_fun IH (abnd (n + 1) (asimplex w))
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at hIH
    have hdd := LinearMap.congr_fun (abnd_comp_abnd n (α := α)) (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    rw [hdd, map_zero, add_zero] at hIH
    rw [hIH, sub_sub_cancel]
    abel

/-! ### Iteration: `S^k` is chain homotopic to the identity -/

/-- The `k`-th iterate of the subdivision operator (as a family of chain
endomorphisms). -/
noncomputable def asubIter (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (k n : ℕ) : AC α n →ₗ[ℤ] AC α n :=
  match k with
  | 0 => LinearMap.id
  | k + 1 => (asub bary n).comp (asubIter bary k n)

@[simp] lemma asubIter_zero (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (n : ℕ) :
    asubIter bary 0 n = LinearMap.id := rfl

lemma asubIter_succ (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (k n : ℕ) :
    asubIter bary (k + 1) n = (asub bary n).comp (asubIter bary k n) := rfl

/-- The iterate is a chain map: `∂ ∘ S^k = S^k ∘ ∂`. -/
theorem abnd_comp_asubIter (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (k n : ℕ) :
    (abnd n).comp (asubIter bary k (n + 1)) = (asubIter bary k n).comp (abnd n) := by
  induction k with
  | zero => rw [asubIter_zero, asubIter_zero, LinearMap.comp_id, LinearMap.id_comp]
  | succ k IH =>
      rw [asubIter_succ, asubIter_succ, ← LinearMap.comp_assoc,
        abnd_comp_asub, LinearMap.comp_assoc, IH, LinearMap.comp_assoc]

/-- The telescoped chain homotopy between `S^k` and the identity:
`Tk = T ∘ (1 + S + ⋯ + S^{k−1})`, packaged degreewise by recursion
`T_0 = 0`, `T_{k+1} = T + T_k ∘ S`. -/
noncomputable def ateeIter (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (k n : ℕ) : AC α n →ₗ[ℤ] AC α (n + 1) :=
  match k with
  | 0 => 0
  | k + 1 => atee bary n + (ateeIter bary k n).comp (asub bary n)

@[simp] lemma ateeIter_zero (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (n : ℕ) :
    ateeIter bary 0 n = 0 := rfl

lemma ateeIter_succ (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (k n : ℕ) :
    ateeIter bary (k + 1) n =
      atee bary n + (ateeIter bary k n).comp (asub bary n) := rfl

/-- The subdivision operator commutes with its own iterates. -/
lemma asubIter_comp_asub (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α) (k n : ℕ) :
    (asubIter bary k n).comp (asub bary n) = (asub bary n).comp (asubIter bary k n) := by
  induction k with
  | zero => rw [asubIter_zero, LinearMap.comp_id, LinearMap.id_comp]
  | succ k IH =>
      rw [asubIter_succ, LinearMap.comp_assoc, IH, ← LinearMap.comp_assoc]

/-- The telescoped chain homotopy identity in positive degrees:
`∂ ∘ Tk + Tk ∘ ∂ = id − S^k` on `AC α (n+1)`. -/
theorem abnd_comp_ateeIter (bary : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (k n : ℕ) :
    (abnd (n + 1)).comp (ateeIter bary k (n + 1)) +
        (ateeIter bary k n).comp (abnd n)
      = LinearMap.id - asubIter bary k (n + 1) := by
  induction k with
  | zero =>
      rw [ateeIter_zero, ateeIter_zero, asubIter_zero, LinearMap.comp_zero,
        LinearMap.zero_comp, add_zero, sub_self]
  | succ k IH =>
      rw [ateeIter_succ, ateeIter_succ, asubIter_succ,
        LinearMap.comp_add, LinearMap.add_comp]
      -- rewrite `Tk S ∂` as `Tk ∂ S` via the chain-map property of `S`
      have hswap : ((ateeIter bary k n).comp (asub bary n)).comp (abnd n)
          = ((ateeIter bary k n).comp (abnd n)).comp (asub bary (n + 1)) := by
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← abnd_comp_asub]
      rw [hswap]
      -- regroup as `(∂T + T∂) + (∂Tk + Tk∂) ∘ S`
      have hgroup :
          ((abnd (n + 1)).comp (atee bary (n + 1)) +
              (abnd (n + 1)).comp ((ateeIter bary k (n + 1)).comp (asub bary (n + 1)))) +
            ((atee bary n).comp (abnd n) +
              ((ateeIter bary k n).comp (abnd n)).comp (asub bary (n + 1)))
          = ((abnd (n + 1)).comp (atee bary (n + 1)) + (atee bary n).comp (abnd n)) +
            ((abnd (n + 1)).comp (ateeIter bary k (n + 1)) +
              (ateeIter bary k n).comp (abnd n)).comp (asub bary (n + 1)) := by
        rw [LinearMap.add_comp, ← LinearMap.comp_assoc]
        abel
      rw [hgroup, abnd_comp_atee, IH, LinearMap.sub_comp, LinearMap.id_comp,
        asubIter_comp_asub]
      abel

/-! ## Stage 5a: pushforward of affine chains and equivariance

Affine chains push forward along any map of point types `f : α → β`
(post-composition of vertex tuples).  The pushforward commutes with the
boundary and the cone, and, when `f` intertwines the two apex functions
(`baryβ (f ∘ w) = f (baryα w)`), with the subdivision operator `asub` and
the chain homotopy `atee` as well.  For the geometric stage the map `f`
will be an affine map of standard simplices, which sends barycenters to
barycenters. -/

/-- The pushforward of affine chains along a map of point types. -/
noncomputable def amap (f : α → β) (n : ℕ) : AC α n →ₗ[ℤ] AC β n :=
  Finsupp.lmapDomain ℤ ℤ (fun w : Fin (n + 1) → α => f ∘ w)

lemma amap_asimplex (f : α → β) (n : ℕ) (w : Fin (n + 1) → α) :
    amap f n (asimplex w) = asimplex (f ∘ w) := by
  rw [amap, asimplex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, asimplex]

/-- The pushforward commutes with the boundary. -/
lemma amap_comp_abnd (f : α → β) (n : ℕ) :
    (amap f n).comp (abnd n) = (abnd n).comp (amap f (n + 1)) := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, abnd_asimplex, map_sum,
    amap_asimplex, abnd_asimplex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, amap_asimplex]
  rfl

/-- The pushforward commutes with the cone (with pushed apex). -/
lemma amap_comp_acone (f : α → β) (b : α) (n : ℕ) :
    (amap f (n + 1)).comp (acone b : AC α n →ₗ[ℤ] AC α (n + 1)) =
      (acone (f b)).comp (amap f n) := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, acone_asimplex, amap_asimplex,
    amap_asimplex, acone_asimplex]
  congr 1
  funext k
  induction k using Fin.cases with
  | zero => simp only [Function.comp_apply, Fin.cons_zero]
  | succ k => simp only [Function.comp_apply, Fin.cons_succ]

/-- Equivariance of the subdivision operator: a map intertwining the apex
functions intertwines `asub`. -/
theorem amap_comp_asub (f : α → β)
    (baryα : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (baryβ : ∀ {m : ℕ}, (Fin (m + 1) → β) → β)
    (hf : ∀ (m : ℕ) (w : Fin (m + 1) → α), baryβ (f ∘ w) = f (baryα w)) :
    ∀ n, (amap f n).comp (asub baryα n) = (asub baryβ n).comp (amap f n)
  | 0 => by rw [asub_zero, asub_zero, LinearMap.comp_id, LinearMap.id_comp]
  | n + 1 => by
    have IH := amap_comp_asub f baryα baryβ hf n
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, asub_asimplex, amap_asimplex,
      asub_asimplex]
    have hcone := LinearMap.congr_fun (amap_comp_acone f (baryα w) n)
      (asub baryα n (abnd n (asimplex w)))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
    rw [hcone, hf]
    congr 1
    have hIH := LinearMap.congr_fun IH (abnd n (asimplex w))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hIH
    rw [hIH]
    congr 1
    have hbnd := LinearMap.congr_fun (amap_comp_abnd f n) (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hbnd
    rw [hbnd, amap_asimplex]

/-- Equivariance of the subdivision homotopy: a map intertwining the apex
functions intertwines `atee`. -/
theorem amap_comp_atee (f : α → β)
    (baryα : ∀ {m : ℕ}, (Fin (m + 1) → α) → α)
    (baryβ : ∀ {m : ℕ}, (Fin (m + 1) → β) → β)
    (hf : ∀ (m : ℕ) (w : Fin (m + 1) → α), baryβ (f ∘ w) = f (baryα w)) :
    ∀ n, (amap f (n + 1)).comp (atee baryα n) = (atee baryβ n).comp (amap f n)
  | 0 => by rw [atee_zero, atee_zero, LinearMap.comp_zero, LinearMap.zero_comp]
  | n + 1 => by
    have IH := amap_comp_atee f baryα baryβ hf n
    refine AC.hom_ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, atee_asimplex, amap_asimplex,
      atee_asimplex]
    have hcone := LinearMap.congr_fun (amap_comp_acone f (baryα w) (n + 1))
      (asimplex w - atee baryα n (abnd n (asimplex w)))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcone
    rw [hcone, hf]
    congr 1
    rw [map_sub, amap_asimplex]
    congr 1
    have hIH := LinearMap.congr_fun IH (abnd n (asimplex w))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hIH
    rw [hIH]
    congr 1
    have hbnd := LinearMap.congr_fun (amap_comp_abnd f n) (asimplex w)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hbnd
    rw [hbnd, amap_asimplex]

/-! ## Stage 5b: geometry on the standard simplex

The affine realization of a vertex tuple `v : Fin (n+1) → Δᵐ` as a
continuous map `Δⁿ → Δᵐ` (barycentric-coordinate weighted sum of the
vertices), its functoriality, and the honest barycenter `sbary`. -/

section Geometry

variable {d m k : ℕ}

/-- The underlying function of the affine map determined by a vertex tuple:
`x ↦ ∑ i, x i • v i` in barycentric coordinates. -/
def affineMapFun (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1)))
    (x : stdSimplex ℝ (Fin (n + 1))) : Fin (m + 1) → ℝ :=
  fun j => ∑ i, x i * v i j

lemma affineMapFun_mem (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1)))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    affineMapFun v x ∈ stdSimplex ℝ (Fin (m + 1)) := by
  constructor
  · intro j
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (stdSimplex.zero_le x i) (stdSimplex.zero_le (v i) j)
  · show ∑ j, ∑ i, x i * v i j = 1
    rw [Finset.sum_comm]
    calc ∑ i, ∑ j, x i * v i j = ∑ i : Fin (n + 1), x i * 1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, stdSimplex.sum_eq_one]
      _ = 1 := by
          simp only [mul_one]
          exact stdSimplex.sum_eq_one x

lemma continuous_affineMapFun (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1))) :
    Continuous (affineMapFun v) := by
  refine continuous_pi fun j => continuous_finset_sum _ fun i _ =>
    Continuous.mul ?_ continuous_const
  exact (continuous_apply i).comp continuous_subtype_val

/-- The affine map `Δⁿ → Δᵐ` determined by a vertex tuple
`v : Fin (n+1) → Δᵐ`, sending the `i`-th vertex of `Δⁿ` to `v i`. -/
noncomputable def affineMap (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (m + 1))) where
  toFun x := ⟨affineMapFun v x, affineMapFun_mem v x⟩
  continuous_toFun := (continuous_affineMapFun v).subtype_mk _

@[simp] lemma affineMap_apply_coe (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1)))
    (x : stdSimplex ℝ (Fin (n + 1))) (j : Fin (m + 1)) :
    affineMap v x j = ∑ i, x i * v i j := rfl

/-- The affine map sends vertices to the prescribed points. -/
lemma affineMap_vertex (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1)))
    (i : Fin (n + 1)) :
    affineMap v (stdSimplex.vertex i) = v i := by
  refine stdSimplex.ext ?_
  funext j
  rw [affineMap_apply_coe, Finset.sum_eq_single i]
  · show (Pi.single i 1 : Fin (n + 1) → ℝ) i * v i j = v i j
    rw [Pi.single_eq_same, one_mul]
  · intro b _ hb
    show (Pi.single i 1 : Fin (n + 1) → ℝ) b * v b j = 0
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Functoriality: the composite of affine maps is the affine map of the
pushed vertex tuple. -/
theorem affineMap_comp (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1)))
    (w : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (affineMap v).comp (affineMap w) = affineMap (fun i => affineMap v (w i)) := by
  refine ContinuousMap.ext fun x => stdSimplex.ext ?_
  funext j
  show affineMap v (affineMap w x) j = affineMap (fun i => affineMap v (w i)) x j
  simp only [affineMap_apply_coe, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

/-- The identity vertex tuple. -/
noncomputable def idTuple (n : ℕ) : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)) :=
  fun i => stdSimplex.vertex i

/-- The affine map of the identity tuple is the identity. -/
lemma affineMap_idTuple (n : ℕ) :
    affineMap (idTuple n) = ContinuousMap.id (stdSimplex ℝ (Fin (n + 1))) := by
  refine ContinuousMap.ext fun x => stdSimplex.ext ?_
  funext j
  show affineMap (idTuple n) x j = x j
  rw [affineMap_apply_coe, Finset.sum_eq_single j]
  · show x j * (Pi.single j 1 : Fin (n + 1) → ℝ) j = x j
    rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    show x b * (Pi.single b 1 : Fin (n + 1) → ℝ) j = 0
    rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Composing an affine map with the identity tuple recovers the tuple. -/
lemma affineMap_comp_idTuple (v : Fin (n + 1) → stdSimplex ℝ (Fin (m + 1))) :
    ⇑(affineMap v) ∘ idTuple n = v :=
  funext fun i => affineMap_vertex v i

/-- `stdSimplex.map` along a vertex map is the affine map of the
corresponding vertex tuple. -/
lemma stdSimplex_map_eq_affineMap (g : Fin (n + 1) → Fin (m + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map g x = affineMap (fun i => stdSimplex.vertex (g i)) x := by
  refine stdSimplex.ext ?_
  funext j
  have hL : (stdSimplex.map g x) j = ∑ i with g i = j, x i :=
    FunOnFinite.linearMap_apply_apply ℝ ℝ g (⇑x) j
  rw [hL]
  show ∑ i with g i = j, x i = ∑ i, x i * (Pi.single (g i) 1 : Fin (m + 1) → ℝ) j
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g i = j
  · rw [if_pos h, ← h, Pi.single_eq_same, mul_one]
  · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h), mul_zero]

/-- Composing an affine map with a topological face inclusion restricts the
vertex tuple along `Fin.succAbove`. -/
lemma affineMap_comp_face (v : Fin (n + 2) → stdSimplex ℝ (Fin (d + 1)))
    (j : Fin (n + 2)) :
    (affineMap v).comp (SingularPrism.face j) =
      affineMap (v ∘ j.succAbove) := by
  refine ContinuousMap.ext fun x => ?_
  rw [ContinuousMap.comp_apply]
  show affineMap v (stdSimplex.map j.succAbove x) = _
  rw [stdSimplex_map_eq_affineMap j.succAbove x, ← ContinuousMap.comp_apply,
    affineMap_comp]
  have h : (fun i => affineMap v (stdSimplex.vertex (j.succAbove i))) =
      v ∘ j.succAbove := funext fun i => affineMap_vertex v _
  rw [h]

/-- The barycenter of a vertex tuple in a standard simplex. -/
noncomputable def sbary {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))) :
    stdSimplex ℝ (Fin (d + 1)) :=
  ⟨fun j => ((m : ℝ) + 1)⁻¹ * ∑ i, w i j, by
    constructor
    · intro j
      refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
      exact Finset.sum_nonneg fun i _ => stdSimplex.zero_le (w i) j
    · rw [← Finset.mul_sum, Finset.sum_comm]
      have hsum : ∑ i, ∑ j, w i j = ((m : ℝ) + 1) := by
        calc ∑ i : Fin (m + 1), ∑ j, w i j = ∑ i : Fin (m + 1), (1 : ℝ) :=
              Finset.sum_congr rfl fun i _ => stdSimplex.sum_eq_one (w i)
          _ = ((m : ℝ) + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, mul_one]
              push_cast
              ring
      rw [hsum, inv_mul_cancel₀ (by positivity)]⟩

@[simp] lemma sbary_apply {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1)))
    (j : Fin (d + 1)) :
    sbary w j = ((m : ℝ) + 1)⁻¹ * ∑ i, w i j := rfl

/-- Affine maps send barycenters to barycenters (the intertwining property
required by the equivariance lemmas of stage 5a). -/
lemma sbary_affineMap (v : Fin (n + 1) → stdSimplex ℝ (Fin (d + 1))) {m : ℕ}
    (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) :
    sbary (⇑(affineMap v) ∘ w) = affineMap v (sbary w) := by
  refine stdSimplex.ext ?_
  funext j
  show ((m : ℝ) + 1)⁻¹ * ∑ i, (affineMap v (w i)) j = affineMap v (sbary w) j
  simp only [affineMap_apply_coe, sbary_apply, mul_assoc, Finset.sum_mul,
    ← Finset.mul_sum]
  rw [Finset.sum_comm]

end Geometry

/-! ## Stage 5c: the singular subdivision operator `sdOp` and homotopy `tOp`

Affine chains in `Δⁿ` are evaluated as singular chains of `X` along a
singular simplex `σ : Δⁿ → X` (`toChain`); pushing forward the subdivided
identity tuple defines the singular barycentric subdivision `sdOp` and its
chain homotopy `tOp` on Mathlib's singular chain complex.  All identities
transport from the affine layer through the equivariance lemmas of
stage 5a. -/

section Singular

open SingularPrism

variable {X Y : TopCat.{0}}

/-- Post-composition with a morphism of `ℤ`-modules, as a `ℤ`-linear map on
hom groups out of `ℤ`. -/
noncomputable def postComp {M N : ModuleCat.{0} ℤ} (g : M ⟶ N) :
    (ModuleCat.of ℤ ℤ ⟶ M) →ₗ[ℤ] (ModuleCat.of ℤ ℤ ⟶ N) where
  toFun f := f ≫ g
  map_add' f₁ f₂ := by rw [Preadditive.add_comp]
  map_smul' r f := by rw [RingHom.id_apply, Preadditive.zsmul_comp]

/-- `TopCat.toSSetObjEquiv`, retyped so that the domain of the continuous
map is literally `stdSimplex ℝ (Fin (m + 1))` (rather than the definitionally
equal `Fin ((unop (op ⦋m⦌)).len + 1)` normal form, which blocks rewriting). -/
noncomputable def simplexEquiv (X : TopCat.{0}) (m : ℕ) :
    Idx X m ≃ C(stdSimplex ℝ (Fin (m + 1)), X) :=
  X.toSSetObjEquiv (op ⦋m⦌)

/-- Retyped naturality of `simplexEquiv` with respect to face maps. -/
lemma simplexEquiv_δ {m : ℕ} (j : Fin (m + 2)) (a : Idx X (m + 1)) :
    simplexEquiv X m ((TopCat.toSSet.obj X).δ j a) =
      (simplexEquiv X (m + 1) a).comp (face j) :=
  toSSetObjEquiv_δ j a

/-- Retyped naturality of `simplexEquiv` with respect to continuous maps. -/
lemma simplexEquiv_map (f : X ⟶ Y) {m : ℕ} (a : Idx X m) :
    simplexEquiv Y m ((TopCat.toSSet.map f).app (op ⦋m⦌) a) =
      f.hom.comp (simplexEquiv X m a) :=
  toSSetObjEquiv_map f a

/-- The singular `m`-simplex obtained by precomposing `σ` with the affine
map of a vertex tuple `w` in `Δⁿ`. -/
noncomputable def pushSimplex {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) {m : ℕ}
    (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) : Idx X m :=
  (simplexEquiv X m).symm (σ.comp (affineMap w))

lemma simplexEquiv_pushSimplex {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) {m : ℕ}
    (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) :
    simplexEquiv X m (pushSimplex σ w) = σ.comp (affineMap w) :=
  Equiv.apply_symm_apply _ _

/-- Evaluation of affine chains in `Δⁿ` as singular chains of `X` along a
singular simplex `σ : Δⁿ → X`. -/
noncomputable def toChain {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (m : ℕ) :
    AC (stdSimplex ℝ (Fin (n + 1))) m →ₗ[ℤ] (ModuleCat.of ℤ ℤ ⟶ Cgrp X m) :=
  Finsupp.linearCombination ℤ (fun w => gen X m (pushSimplex σ w))

lemma toChain_asimplex {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (m : ℕ)
    (w : Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) :
    toChain σ m (asimplex w) = gen X m (pushSimplex σ w) :=
  lift_asimplex _ w

/-- Faces of pushed simplices restrict the vertex tuple. -/
lemma δ_pushSimplex {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) {m : ℕ}
    (w : Fin (m + 2) → stdSimplex ℝ (Fin (n + 1))) (k : Fin (m + 2)) :
    (TopCat.toSSet.obj X).δ k (pushSimplex σ w) =
      pushSimplex σ (w ∘ k.succAbove) := by
  apply (simplexEquiv X m).injective
  rw [simplexEquiv_δ, simplexEquiv_pushSimplex, simplexEquiv_pushSimplex,
    ContinuousMap.comp_assoc, affineMap_comp_face]

/-- The pushed simplex of the identity tuple is the simplex itself. -/
lemma pushSimplex_idTuple {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    pushSimplex σ (idTuple n) = (simplexEquiv X n).symm σ := by
  unfold pushSimplex
  rw [affineMap_idTuple, ContinuousMap.comp_id]

lemma toChain_asimplex_idTuple {n : ℕ} (s : Idx X n) :
    toChain (simplexEquiv X n s) n (asimplex (idTuple n)) = gen X n s := by
  rw [toChain_asimplex, pushSimplex_idTuple, Equiv.symm_apply_apply]

/-- Any face of a singular simplex is the pushed simplex of a face of the
identity tuple. -/
lemma δ_eq_pushSimplex {n : ℕ} (s : Idx X (n + 1)) (k : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ k s =
      pushSimplex (simplexEquiv X (n + 1) s) (idTuple (n + 1) ∘ k.succAbove) := by
  have h : pushSimplex (simplexEquiv X (n + 1) s) (idTuple (n + 1)) = s := by
    rw [pushSimplex_idTuple, Equiv.symm_apply_apply]
  conv_lhs => rw [← h]
  exact δ_pushSimplex _ _ k

/-- `toChain` intertwines the affine and the singular boundary. -/
lemma toChain_comp_abnd {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) (m : ℕ) :
    (postComp (bnd X m)).comp (toChain σ (m + 1)) = (toChain σ m).comp (abnd m) := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, toChain_asimplex]
  show gen X (m + 1) (pushSimplex σ w) ≫ bnd X m = toChain σ m (abnd m (asimplex w))
  rw [gen_d, abnd_asimplex, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, toChain_asimplex, δ_pushSimplex]

/-- `toChain` intertwines post-composition with the induced chain map. -/
lemma toChain_comp_chainMap {n : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (f : X ⟶ Y) (m : ℕ) :
    (postComp (chainMap f m)).comp (toChain σ m) = toChain (f.hom.comp σ) m := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, toChain_asimplex, toChain_asimplex]
  show gen X m (pushSimplex σ w) ≫ chainMap f m =
    gen Y m (pushSimplex (f.hom.comp σ) w)
  rw [gen_map]
  congr 1

/-- `toChain` turns the affine pushforward along an affine map into
precomposition of the singular simplex. -/
lemma toChain_amap {n n' : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (v : Fin (n' + 1) → stdSimplex ℝ (Fin (n + 1))) (m : ℕ) :
    (toChain σ m).comp (amap (⇑(affineMap v)) m) = toChain (σ.comp (affineMap v)) m := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, amap_asimplex, toChain_asimplex, toChain_asimplex]
  congr 1
  apply (simplexEquiv X m).injective
  rw [simplexEquiv_pushSimplex, simplexEquiv_pushSimplex, ContinuousMap.comp_assoc,
    affineMap_comp]
  rfl

/-- The barycentric apex function on `Δⁿ`, in the shape expected by
`asub`/`atee`. -/
noncomputable def baryFn (n : ℕ) :
    ∀ {m : ℕ}, (Fin (m + 1) → stdSimplex ℝ (Fin (n + 1))) → stdSimplex ℝ (Fin (n + 1)) :=
  fun {_} w => sbary w

/-- Generator value of the singular subdivision operator. -/
noncomputable def sdGen (X : TopCat.{0}) (n : ℕ) (s : Idx X n) :
    ModuleCat.of ℤ ℤ ⟶ Cgrp X n :=
  toChain (simplexEquiv X n s) n (asub (baryFn n) n (asimplex (idTuple n)))

/-- The singular barycentric subdivision operator `sdOp X : C_n(X) ⟶ C_n(X)`. -/
noncomputable def sdOp (X : TopCat.{0}) (n : ℕ) : Cgrp X n ⟶ Cgrp X n :=
  Sigma.desc (sdGen X n)

lemma gen_sdOp {n : ℕ} (s : Idx X n) : gen X n s ≫ sdOp X n = sdGen X n s :=
  Sigma.ι_desc _ _

/-- Generator value of the singular subdivision homotopy. -/
noncomputable def tGen (X : TopCat.{0}) (n : ℕ) (s : Idx X n) :
    ModuleCat.of ℤ ℤ ⟶ Cgrp X (n + 1) :=
  toChain (simplexEquiv X n s) (n + 1) (atee (baryFn n) n (asimplex (idTuple n)))

/-- The singular subdivision chain homotopy `tOp X : C_n(X) ⟶ C_{n+1}(X)`. -/
noncomputable def tOp (X : TopCat.{0}) (n : ℕ) : Cgrp X n ⟶ Cgrp X (n + 1) :=
  Sigma.desc (tGen X n)

lemma gen_tOp {n : ℕ} (s : Idx X n) : gen X n s ≫ tOp X n = tGen X n s :=
  Sigma.ι_desc _ _

/-- The heart of the transport: `sdOp` on a pushed generator computes the
subdivision of the pushed tuple. -/
lemma gen_pushSimplex_comp_sdOp {n n' : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (w : Fin (n' + 1) → stdSimplex ℝ (Fin (n + 1))) :
    gen X n' (pushSimplex σ w) ≫ sdOp X n' =
      toChain σ n' (asub (baryFn n) n' (asimplex w)) := by
  rw [gen_sdOp]
  show toChain (simplexEquiv X n' (pushSimplex σ w)) n'
      (asub (baryFn n') n' (asimplex (idTuple n'))) = _
  rw [simplexEquiv_pushSimplex]
  have hL := LinearMap.congr_fun (toChain_amap σ w n')
    (asub (baryFn n') n' (asimplex (idTuple n')))
  rw [LinearMap.comp_apply] at hL
  rw [← hL]
  have heq := LinearMap.congr_fun (amap_comp_asub (⇑(affineMap w)) (baryFn n')
    (baryFn n) (fun m u => sbary_affineMap w u) n') (asimplex (idTuple n'))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at heq
  rw [heq, amap_asimplex, affineMap_comp_idTuple]

/-- `tOp` on a pushed generator computes the homotopy of the pushed tuple. -/
lemma gen_pushSimplex_comp_tOp {n n' : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (w : Fin (n' + 1) → stdSimplex ℝ (Fin (n + 1))) :
    gen X n' (pushSimplex σ w) ≫ tOp X n' =
      toChain σ (n' + 1) (atee (baryFn n) n' (asimplex w)) := by
  rw [gen_tOp]
  show toChain (simplexEquiv X n' (pushSimplex σ w)) (n' + 1)
      (atee (baryFn n') n' (asimplex (idTuple n'))) = _
  rw [simplexEquiv_pushSimplex]
  have hL := LinearMap.congr_fun (toChain_amap σ w (n' + 1))
    (atee (baryFn n') n' (asimplex (idTuple n')))
  rw [LinearMap.comp_apply] at hL
  rw [← hL]
  have heq := LinearMap.congr_fun (amap_comp_atee (⇑(affineMap w)) (baryFn n')
    (baryFn n) (fun m u => sbary_affineMap w u) n') (asimplex (idTuple n'))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at heq
  rw [heq, amap_asimplex, affineMap_comp_idTuple]

/-- The singular subdivision operator is a chain map: `∂ ∘ S = S ∘ ∂`. -/
theorem sdOp_comp_bnd (X : TopCat.{0}) (n : ℕ) :
    sdOp X (n + 1) ≫ bnd X n = bnd X n ≫ sdOp X n := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, ← Category.assoc, gen_sdOp, gen_d]
  have hL : sdGen X (n + 1) s ≫ bnd X n =
      toChain (simplexEquiv X (n + 1) s) n
        (asub (baryFn (n + 1)) n (abnd n (asimplex (idTuple (n + 1))))) := by
    have h := LinearMap.congr_fun
      (toChain_comp_abnd (simplexEquiv X (n + 1) s) n)
      (asub (baryFn (n + 1)) (n + 1) (asimplex (idTuple (n + 1))))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    have hcomm := LinearMap.congr_fun (abnd_comp_asub (baryFn (n + 1)) n)
      (asimplex (idTuple (n + 1)))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [← hcomm]
    exact h
  rw [hL, abnd_asimplex, map_sum, map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, Preadditive.zsmul_comp]
  congr 1
  rw [δ_eq_pushSimplex, gen_pushSimplex_comp_sdOp]

/-- In degree `0` the singular subdivision operator is the identity. -/
theorem sdOp_zero (X : TopCat.{0}) : sdOp X 0 = 𝟙 (Cgrp X 0) := by
  apply Sigma.hom_ext
  intro s
  rw [Category.comp_id, gen_sdOp]
  show toChain (simplexEquiv X 0 s) 0
    (asub (baryFn 0) 0 (asimplex (idTuple 0))) = gen X 0 s
  rw [asub_zero, LinearMap.id_apply]
  exact toChain_asimplex_idTuple s

/-- In degree `0` the singular subdivision homotopy vanishes. -/
theorem tOp_zero (X : TopCat.{0}) : tOp X 0 = 0 := by
  apply Sigma.hom_ext
  intro s
  rw [Limits.comp_zero, gen_tOp]
  show toChain (simplexEquiv X 0 s) 1
    (atee (baryFn 0) 0 (asimplex (idTuple 0))) = 0
  rw [atee_zero, LinearMap.zero_apply, map_zero]

/-- The chain homotopy identity in positive degrees:
`∂ ∘ T + T ∘ ∂ = id − S` on the degree-`(n+1)` singular chain group. -/
theorem tOp_chain_homotopy_succ (X : TopCat.{0}) (n : ℕ) :
    bnd X n ≫ tOp X n + tOp X (n + 1) ≫ bnd X (n + 1) =
      𝟙 (Cgrp X (n + 1)) - sdOp X (n + 1) := by
  apply Sigma.hom_ext
  intro s
  rw [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id]
  -- second summand: `T ∘ ∂` transported to `toChain σ (T (∂ id))`
  have h2 : gen X (n + 1) s ≫ (bnd X n ≫ tOp X n) =
      toChain (simplexEquiv X (n + 1) s) (n + 1)
        (atee (baryFn (n + 1)) n (abnd n (asimplex (idTuple (n + 1))))) := by
    rw [← Category.assoc, gen_d, Preadditive.sum_comp, abnd_asimplex, map_sum,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Preadditive.zsmul_comp, map_smul, map_smul]
    congr 1
    rw [δ_eq_pushSimplex, gen_pushSimplex_comp_tOp]
  -- first summand: `∂ ∘ T` transported to `toChain σ (∂ (T id))`
  have h1 : gen X (n + 1) s ≫ (tOp X (n + 1) ≫ bnd X (n + 1)) =
      toChain (simplexEquiv X (n + 1) s) (n + 1)
        (abnd (n + 1) (atee (baryFn (n + 1)) (n + 1) (asimplex (idTuple (n + 1))))) := by
    rw [← Category.assoc, gen_tOp]
    have h := LinearMap.congr_fun
      (toChain_comp_abnd (simplexEquiv X (n + 1) s) (n + 1))
      (atee (baryFn (n + 1)) (n + 1) (asimplex (idTuple (n + 1))))
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact h
  rw [h2, h1, ← map_add, gen_sdOp]
  have hhom := LinearMap.congr_fun (abnd_comp_atee (baryFn (n + 1)) n)
    (asimplex (idTuple (n + 1)))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hhom
  have hsum : atee (baryFn (n + 1)) n (abnd n (asimplex (idTuple (n + 1)))) +
      abnd (n + 1) (atee (baryFn (n + 1)) (n + 1) (asimplex (idTuple (n + 1)))) =
      asimplex (idTuple (n + 1)) -
        asub (baryFn (n + 1)) (n + 1) (asimplex (idTuple (n + 1))) := by
    exact (add_comm _ _).trans hhom
  rw [hsum, map_sub, toChain_asimplex_idTuple]
  rfl

/-- In degree `0`: `∂ ∘ T = id − S` (both sides vanish). -/
theorem tOp_chain_homotopy_zero (X : TopCat.{0}) :
    tOp X 0 ≫ bnd X 0 = 𝟙 (Cgrp X 0) - sdOp X 0 := by
  rw [tOp_zero, sdOp_zero, Limits.zero_comp, sub_self]

/-- Naturality of the singular subdivision operator. -/
theorem sdOp_natural (f : X ⟶ Y) (n : ℕ) :
    chainMap f n ≫ sdOp Y n = sdOp X n ≫ chainMap f n := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, ← Category.assoc, gen_map, gen_sdOp, gen_sdOp]
  have hR := LinearMap.congr_fun
    (toChain_comp_chainMap (simplexEquiv X n s) f n)
    (asub (baryFn n) n (asimplex (idTuple n)))
  rw [LinearMap.comp_apply] at hR
  have hL : sdGen Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) =
      toChain (f.hom.comp (simplexEquiv X n s)) n
        (asub (baryFn n) n (asimplex (idTuple n))) := by
    show toChain (simplexEquiv Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s)) n
        (asub (baryFn n) n (asimplex (idTuple n))) = _
    rw [simplexEquiv_map]
  rw [hL, ← hR]
  rfl

/-- Naturality of the singular subdivision homotopy. -/
theorem tOp_natural (f : X ⟶ Y) (n : ℕ) :
    chainMap f n ≫ tOp Y n = tOp X n ≫ chainMap f (n + 1) := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, ← Category.assoc, gen_map, gen_tOp, gen_tOp]
  have hR := LinearMap.congr_fun
    (toChain_comp_chainMap (simplexEquiv X n s) f (n + 1))
    (atee (baryFn n) n (asimplex (idTuple n)))
  rw [LinearMap.comp_apply] at hR
  have hL : tGen Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) =
      toChain (f.hom.comp (simplexEquiv X n s)) (n + 1)
        (atee (baryFn n) n (asimplex (idTuple n))) := by
    show toChain (simplexEquiv Y n ((TopCat.toSSet.map f).app (op ⦋n⦌) s)) (n + 1)
        (atee (baryFn n) n (asimplex (idTuple n))) = _
    rw [simplexEquiv_map]
  rw [hL, ← hR]
  rfl

/-! ### Iterates of the singular subdivision operator -/

/-- The `k`-th iterate of the singular subdivision operator. -/
noncomputable def sdOpIter (X : TopCat.{0}) (n : ℕ) : ℕ → (Cgrp X n ⟶ Cgrp X n)
  | 0 => 𝟙 _
  | k + 1 => sdOpIter X n k ≫ sdOp X n

@[simp] lemma sdOpIter_zero (X : TopCat.{0}) (n : ℕ) :
    sdOpIter X n 0 = 𝟙 (Cgrp X n) := rfl

lemma sdOpIter_succ (X : TopCat.{0}) (n k : ℕ) :
    sdOpIter X n (k + 1) = sdOpIter X n k ≫ sdOp X n := rfl

/-- The telescoped homotopy for the iterate, `T_{k+1} = T + S ≫ T_k`. -/
noncomputable def tOpIter (X : TopCat.{0}) (n : ℕ) : ℕ → (Cgrp X n ⟶ Cgrp X (n + 1))
  | 0 => 0
  | k + 1 => tOp X n + sdOp X n ≫ tOpIter X n k

@[simp] lemma tOpIter_zero (X : TopCat.{0}) (n : ℕ) : tOpIter X n 0 = 0 := rfl

lemma tOpIter_succ (X : TopCat.{0}) (n k : ℕ) :
    tOpIter X n (k + 1) = tOp X n + sdOp X n ≫ tOpIter X n k := rfl

/-- The iterate commutes with `sdOp`. -/
lemma sdOpIter_comp_sdOp (X : TopCat.{0}) (n k : ℕ) :
    sdOpIter X n k ≫ sdOp X n = sdOp X n ≫ sdOpIter X n k := by
  induction k with
  | zero => rw [sdOpIter_zero, Category.id_comp, Category.comp_id]
  | succ k IH =>
      calc sdOpIter X n (k + 1) ≫ sdOp X n
          = sdOpIter X n k ≫ sdOp X n ≫ sdOp X n := by
            rw [sdOpIter_succ, Category.assoc]
        _ = (sdOp X n ≫ sdOpIter X n k) ≫ sdOp X n := by
            rw [← IH, Category.assoc]
        _ = sdOp X n ≫ sdOpIter X n (k + 1) := by
            rw [Category.assoc, sdOpIter_succ]

/-- The iterate is a chain map. -/
theorem sdOpIter_comp_bnd (X : TopCat.{0}) (n k : ℕ) :
    sdOpIter X (n + 1) k ≫ bnd X n = bnd X n ≫ sdOpIter X n k := by
  induction k with
  | zero => rw [sdOpIter_zero, sdOpIter_zero, Category.id_comp, Category.comp_id]
  | succ k IH =>
      rw [sdOpIter_succ, sdOpIter_succ, Category.assoc, sdOp_comp_bnd,
        ← Category.assoc, IH, Category.assoc]

/-- The telescoped chain homotopy identity in positive degrees:
`∂ ∘ T_k + T_k ∘ ∂ = id − S^k` on the degree-`(n+1)` singular chain group. -/
theorem tOpIter_chain_homotopy_succ (X : TopCat.{0}) (n k : ℕ) :
    bnd X n ≫ tOpIter X n k + tOpIter X (n + 1) k ≫ bnd X (n + 1) =
      𝟙 (Cgrp X (n + 1)) - sdOpIter X (n + 1) k := by
  induction k with
  | zero =>
      rw [tOpIter_zero, tOpIter_zero, sdOpIter_zero, Limits.comp_zero,
        Limits.zero_comp, add_zero, sub_self]
  | succ k IH =>
      rw [tOpIter_succ, tOpIter_succ, sdOpIter_succ]
      have key : bnd X n ≫ (tOp X n + sdOp X n ≫ tOpIter X n k) +
          (tOp X (n + 1) + sdOp X (n + 1) ≫ tOpIter X (n + 1) k) ≫ bnd X (n + 1) =
          (bnd X n ≫ tOp X n + tOp X (n + 1) ≫ bnd X (n + 1)) +
            sdOp X (n + 1) ≫
              (bnd X n ≫ tOpIter X n k + tOpIter X (n + 1) k ≫ bnd X (n + 1)) := by
        rw [Preadditive.comp_add, Preadditive.add_comp, Preadditive.comp_add,
          Category.assoc]
        have hmid : bnd X n ≫ sdOp X n ≫ tOpIter X n k =
            sdOp X (n + 1) ≫ bnd X n ≫ tOpIter X n k := by
          rw [← Category.assoc, ← sdOp_comp_bnd, Category.assoc]
        rw [hmid]
        abel
      rw [key, tOp_chain_homotopy_succ, IH, Preadditive.comp_sub,
        Category.comp_id, sdOpIter_comp_sdOp]
      abel

/-- The telescoped chain homotopy identity in degree `0`:
`∂ ∘ T_k = id − S^k` on the degree-`0` singular chain group. -/
theorem tOpIter_chain_homotopy_zero (X : TopCat.{0}) (k : ℕ) :
    tOpIter X 0 k ≫ bnd X 0 = 𝟙 (Cgrp X 0) - sdOpIter X 0 k := by
  induction k with
  | zero => rw [tOpIter_zero, sdOpIter_zero, Limits.zero_comp, sub_self]
  | succ k IH =>
      rw [tOpIter_succ, sdOpIter_succ, Preadditive.add_comp, Category.assoc,
        tOp_chain_homotopy_zero, IH, Preadditive.comp_sub, Category.comp_id,
        sdOpIter_comp_sdOp]
      abel

/-- `toChain` intertwines `sdOp` and the affine subdivision. -/
lemma toChain_comp_sdOp {n n' : ℕ} (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    (postComp (sdOp X n')).comp (toChain σ n') =
      (toChain σ n').comp (asub (baryFn n) n') := by
  refine AC.hom_ext fun w => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, toChain_asimplex]
  exact gen_pushSimplex_comp_sdOp σ w

/-- The iterated singular subdivision of a generator is the evaluation of the
iterated affine subdivision of the identity tuple.  This ties the singular
operator to the affine support geometry of stage 6. -/
theorem gen_comp_sdOpIter {n : ℕ} (s : Idx X n) (k : ℕ) :
    gen X n s ≫ sdOpIter X n k =
      toChain (simplexEquiv X n s) n
        (asubIter (baryFn n) k n (asimplex (idTuple n))) := by
  induction k with
  | zero =>
      rw [sdOpIter_zero, Category.comp_id, asubIter_zero, LinearMap.id_apply,
        toChain_asimplex_idTuple]
  | succ k IH =>
      rw [sdOpIter_succ, ← Category.assoc, IH, asubIter_succ, LinearMap.comp_apply]
      have h := LinearMap.congr_fun
        (toChain_comp_sdOp (X := X) (n' := n) (simplexEquiv X n s))
        (asubIter (baryFn n) k n (asimplex (idTuple n)))
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      exact h

end Singular

/-! ## Stage 6: the diameter estimate for barycentric subdivision

We track the `Finsupp` support of the affine subdivision operator through its
cone recursion.  The two invariants: every vertex of every piece lies in the
convex hull (in the ambient coordinate space) of the original vertex tuple,
and the pairwise vertex distances contract by the factor `n / (n + 1)`.
Iterating gives geometric decay of piece diameters.  The ambient metric is
the sup metric on `Fin (d + 1) → ℝ`, whose subtype metric induces the
topology of `SimplexCategory.toTop` on `stdSimplex ℝ (Fin (d + 1))`. -/

section SupportTracking

variable {α : Type}

/-- Transport of a support predicate through a linear operator on affine
chains: if `T` maps every generator satisfying `P` to a chain supported on
tuples satisfying `Q`, the same holds for arbitrary chains supported on `P`. -/
lemma support_transport {n m : ℕ} (T : AC α n →ₗ[ℤ] AC α m)
    {P : (Fin (n + 1) → α) → Prop} {Q : (Fin (m + 1) → α) → Prop}
    (hT : ∀ w, P w → ∀ u ∈ (T (asimplex w)).support, Q u)
    (c : AC α n) (hc : ∀ w ∈ c.support, P w) :
    ∀ u ∈ (T c).support, Q u := by
  intro u hu
  have hrep : T c = ∑ w ∈ c.support, T (Finsupp.single w (c w)) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
  rw [hrep] at hu
  obtain ⟨w, hw, hu'⟩ := Finsupp.mem_support_finset_sum u hu
  have hsingle : (Finsupp.single w (c w) : AC α n) = (c w) • asimplex w := by
    rw [asimplex, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_smul] at hu'
  exact hT w (hc w hw) u (Finsupp.support_smul hu')

/-- The support of the boundary of a generator consists of faces. -/
lemma support_abnd_asimplex {n : ℕ} (w : Fin (n + 2) → α) :
    ∀ v ∈ (abnd n (asimplex w)).support, ∃ j : Fin (n + 2), v = w ∘ j.succAbove := by
  intro v hv
  rw [abnd_asimplex] at hv
  obtain ⟨j, _, hv'⟩ := Finsupp.mem_support_finset_sum v hv
  have hmem := Finsupp.support_smul hv'
  rw [asimplex] at hmem
  have hsingle := Finsupp.support_single_subset hmem
  rw [Finset.mem_singleton] at hsingle
  exact ⟨j, hsingle⟩

/-- The support of a cone consists of cones over the original support. -/
lemma support_acone {n : ℕ} (b : α) (c : AC α n) :
    ∀ u ∈ (acone b c).support, ∃ v ∈ c.support, u = Fin.cons b v := by
  classical
  intro u hu
  rw [acone, Finsupp.lmapDomain_apply] at hu
  obtain ⟨v, hv, huv⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hu)
  exact ⟨v, hv, huv.symm⟩

end SupportTracking

section Diameter

variable {d : ℕ}

@[simp] lemma baryFn_apply {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))) :
    baryFn d w = sbary w := rfl

/-- The convex hull, in the ambient coordinate space, of a vertex tuple in
the standard simplex. -/
def hullOf {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))) :
    Set (Fin (d + 1) → ℝ) :=
  convexHull ℝ (Set.range fun i => ((w i : Fin (d + 1) → ℝ)))

lemma coe_mem_hullOf {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1)))
    (i : Fin (m + 1)) : ((w i : Fin (d + 1) → ℝ)) ∈ hullOf w :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

/-- Hull monotonicity from a coordinatewise membership hypothesis. -/
lemma hullOf_subset {m m' : ℕ} {w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))}
    {v : Fin (m' + 1) → stdSimplex ℝ (Fin (d + 1))}
    (h : ∀ i, ((v i : Fin (d + 1) → ℝ)) ∈ hullOf w) : hullOf v ⊆ hullOf w :=
  convexHull_min (by rintro x ⟨i, rfl⟩; exact h i) (convex_convexHull ℝ _)

/-- The barycenter as an explicit convex combination in the ambient space. -/
lemma coe_sbary {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))) :
    ((sbary w : Fin (d + 1) → ℝ)) =
      ∑ i, ((m : ℝ) + 1)⁻¹ • ((w i : Fin (d + 1) → ℝ)) := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  rfl

lemma sbary_mem_hullOf {m : ℕ} (w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))) :
    ((sbary w : Fin (d + 1) → ℝ)) ∈ hullOf w := by
  rw [coe_sbary]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => by positivity) ?_
    (fun i _ => coe_mem_hullOf w i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_inv_cancel₀ (by positivity)]

/-- Two points of the hull of a tuple with pairwise distances `≤ D` are
themselves at distance `≤ D` (maximum principle for the convex `dist`). -/
lemma dist_le_of_mem_hullOf {m : ℕ} {w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))}
    {D : ℝ} (hw : ∀ i j, dist (w i) (w j) ≤ D)
    {x y : Fin (d + 1) → ℝ} (hx : x ∈ hullOf w) (hy : y ∈ hullOf w) :
    dist x y ≤ D := by
  obtain ⟨x', ⟨i, rfl⟩, hx'⟩ := convexHull_exists_dist_ge hx y
  obtain ⟨y', ⟨j, rfl⟩, hy'⟩ := convexHull_exists_dist_ge hy ((w i : Fin (d + 1) → ℝ))
  calc dist x y ≤ dist ((w i : Fin (d + 1) → ℝ)) y := hx'
    _ = dist y ((w i : Fin (d + 1) → ℝ)) := dist_comm _ _
    _ ≤ dist ((w j : Fin (d + 1) → ℝ)) ((w i : Fin (d + 1) → ℝ)) := hy'
    _ = dist (w j) (w i) := (Subtype.dist_eq _ _).symm
    _ ≤ D := hw j i

/-- Key metric estimate: the barycenter of an `m`-tuple with pairwise
distances `≤ D` is within `m/(m+1) · D` of every point of the tuple's hull. -/
lemma dist_sbary_le {m : ℕ} {w : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))}
    {D : ℝ} (hw : ∀ i j, dist (w i) (w j) ≤ D)
    {x : Fin (d + 1) → ℝ} (hx : x ∈ hullOf w) :
    dist ((sbary w : Fin (d + 1) → ℝ)) x ≤ ((m : ℝ) / (m + 1)) * D := by
  obtain ⟨x', ⟨j, rfl⟩, hx'⟩ :=
    convexHull_exists_dist_ge hx ((sbary w : Fin (d + 1) → ℝ))
  rw [dist_comm] at hx'
  refine hx'.trans ?_
  show dist ((w j : Fin (d + 1) → ℝ)) ((sbary w : Fin (d + 1) → ℝ)) ≤ _
  rw [dist_comm, dist_eq_norm]
  have hrep : ((sbary w : Fin (d + 1) → ℝ)) - (w j : Fin (d + 1) → ℝ) =
      ∑ i, ((m : ℝ) + 1)⁻¹ •
        (((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ))) := by
    funext j'
    rw [Pi.sub_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin (m + 1), ((m : ℝ) + 1)⁻¹ * (w i) j' = sbary w j' := by
      rw [sbary_apply, Finset.mul_sum]
    have h2 : ∑ _i : Fin (m + 1), ((m : ℝ) + 1)⁻¹ * (w j) j' = (w j) j' := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [h1, h2]
  rw [hrep]
  calc ‖∑ i, ((m : ℝ) + 1)⁻¹ •
        (((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ)))‖
      ≤ ∑ i, ‖((m : ℝ) + 1)⁻¹ •
        (((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ)))‖ :=
        norm_sum_le _ _
    _ = ∑ i, ((m : ℝ) + 1)⁻¹ *
        ‖((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ))‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ ((m : ℝ) / (m + 1)) * D := ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), sub_self, norm_zero,
    mul_zero, zero_add]
  have hterm : ∀ i ∈ Finset.univ.erase j,
      ((m : ℝ) + 1)⁻¹ * ‖((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ))‖ ≤
        ((m : ℝ) + 1)⁻¹ * D := by
    intro i _
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← dist_eq_norm]
    exact hw i j
  calc ∑ i ∈ Finset.univ.erase j, ((m : ℝ) + 1)⁻¹ *
        ‖((w i : Fin (d + 1) → ℝ)) - ((w j : Fin (d + 1) → ℝ))‖
      ≤ (Finset.univ.erase j).card • (((m : ℝ) + 1)⁻¹ * D) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((m : ℝ) / (m + 1)) * D := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
        push_cast
        ring

/-- The contraction ratio is monotone in the degree. -/
lemma ratio_mono (n : ℕ) : ((n : ℝ) / (n + 1)) ≤ (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((n : ℝ))]

/-- **Stage 6 main estimate.** Every piece of the barycentric subdivision of
an affine simplex has vertices in the hull of the original tuple, with
pairwise distances contracted by the factor `n / (n + 1)`. -/
theorem asub_support_bound :
    ∀ (n : ℕ) (w : Fin (n + 1) → stdSimplex ℝ (Fin (d + 1))) (D : ℝ), 0 ≤ D →
      (∀ i j, dist (w i) (w j) ≤ D) →
      ∀ u ∈ ((asub (baryFn d) n) (asimplex w)).support,
        (∀ i j, dist (u i) (u j) ≤ ((n : ℝ) / (n + 1)) * D) ∧
          ∀ i, ((u i : Fin (d + 1) → ℝ)) ∈ hullOf w
  | 0, w, D, hD, hw => by
      intro u hu
      rw [asub_zero, LinearMap.id_apply, asimplex] at hu
      have hmem := Finsupp.support_single_subset hu
      rw [Finset.mem_singleton] at hmem
      subst hmem
      refine ⟨fun i j => ?_, fun i => coe_mem_hullOf u i⟩
      have hij : i = j := Fin.ext (by omega)
      subst hij
      rw [dist_self]
      positivity
  | n + 1, w, D, hD, hw => by
      intro u hu
      rw [asub_asimplex] at hu
      obtain ⟨v, hv, huv⟩ := support_acone _ _ u hu
      subst huv
      have hmid : ∀ v' ∈ ((asub (baryFn d) n) (abnd n (asimplex w))).support,
          (∀ i j, dist (v' i) (v' j) ≤ ((n : ℝ) / (n + 1)) * D) ∧
            ∀ i, ((v' i : Fin (d + 1) → ℝ)) ∈ hullOf w := by
        refine support_transport _
          (P := fun v' => ∃ j : Fin (n + 2), v' = w ∘ j.succAbove) ?_ _
          (support_abnd_asimplex w)
        rintro v' ⟨j, rfl⟩ u' hu'
        obtain ⟨h1, h2⟩ := asub_support_bound n (w ∘ j.succAbove) D hD
          (fun i i' => hw _ _) u' hu'
        exact ⟨h1, fun i => hullOf_subset
          (fun i' => coe_mem_hullOf w (j.succAbove i')) (h2 i)⟩
      obtain ⟨h1, h2⟩ := hmid v hv
      have hr : ((n : ℝ) / (n + 1)) * D ≤ (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1)) * D := by
        refine mul_le_mul_of_nonneg_right ?_ hD
        push_cast
        have h := ratio_mono n
        rwa [show ((n : ℝ) + 2) = ((n : ℝ) + 1 + 1) by ring] at h
      have happx : ∀ i' : Fin (n + 1),
          dist (baryFn d w) (v i') ≤ (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) + 1)) * D := by
        intro i'
        rw [baryFn_apply, Subtype.dist_eq]
        have hdist := dist_sbary_le (w := w) hw (h2 i')
        refine hdist.trans (le_of_eq ?_)
        push_cast
        ring
      refine ⟨fun i j => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases ?_ (fun j' => ?_) j
          · rw [Fin.cons_zero, dist_self]
            positivity
          · rw [Fin.cons_zero, Fin.cons_succ]
            exact happx j'
        · refine Fin.cases ?_ (fun j' => ?_) j
          · rw [Fin.cons_succ, Fin.cons_zero, dist_comm]
            exact happx i'
          · rw [Fin.cons_succ, Fin.cons_succ]
            exact (h1 i' j').trans hr
      · refine Fin.cases ?_ (fun i' => ?_) i
        · rw [Fin.cons_zero, baryFn_apply]
          exact sbary_mem_hullOf w
        · rw [Fin.cons_succ]
          exact h2 i'

/-- Iterated version: `k`-fold subdivision contracts pairwise distances by
`(n/(n+1))^k`, keeping all vertices in the hull of the original tuple. -/
theorem asubIter_support_bound (k : ℕ) :
    ∀ (n : ℕ) (w : Fin (n + 1) → stdSimplex ℝ (Fin (d + 1))) (D : ℝ), 0 ≤ D →
      (∀ i j, dist (w i) (w j) ≤ D) →
      ∀ u ∈ ((asubIter (baryFn d) k n) (asimplex w)).support,
        (∀ i j, dist (u i) (u j) ≤ ((n : ℝ) / (n + 1)) ^ k * D) ∧
          ∀ i, ((u i : Fin (d + 1) → ℝ)) ∈ hullOf w := by
  induction k with
  | zero =>
      intro n w D hD hw u hu
      rw [asubIter_zero, LinearMap.id_apply, asimplex] at hu
      have hmem := Finsupp.support_single_subset hu
      rw [Finset.mem_singleton] at hmem
      subst hmem
      exact ⟨fun i j => by rw [pow_zero, one_mul]; exact hw i j,
        fun i => coe_mem_hullOf u i⟩
  | succ k IH =>
      intro n w D hD hw u hu
      rw [asubIter_succ, LinearMap.comp_apply] at hu
      refine support_transport (asub (baryFn d) n)
        (P := fun v => (∀ i j, dist (v i) (v j) ≤ ((n : ℝ) / (n + 1)) ^ k * D) ∧
          ∀ i, ((v i : Fin (d + 1) → ℝ)) ∈ hullOf w)
        (Q := fun u => (∀ i j, dist (u i) (u j) ≤ ((n : ℝ) / (n + 1)) ^ (k + 1) * D) ∧
          ∀ i, ((u i : Fin (d + 1) → ℝ)) ∈ hullOf w) ?_ _
        (IH n w D hD hw) u hu
      rintro v ⟨hv1, hv2⟩ u' hu'
      obtain ⟨h1, h2⟩ := asub_support_bound n v (((n : ℝ) / (n + 1)) ^ k * D)
        (by positivity) hv1 u' hu'
      refine ⟨fun i j => ?_, fun i => hullOf_subset hv2 (h2 i)⟩
      calc dist (u' i) (u' j)
          ≤ ((n : ℝ) / (n + 1)) * (((n : ℝ) / (n + 1)) ^ k * D) := h1 i j
        _ = ((n : ℝ) / (n + 1)) ^ (k + 1) * D := by ring

/-- Any two points of the standard simplex are at sup-distance `≤ 1`. -/
lemma stdSimplex_dist_le_one (x y : stdSimplex ℝ (Fin (d + 1))) : dist x y ≤ 1 := by
  rw [Subtype.dist_eq, dist_pi_le_iff zero_le_one]
  intro j
  rw [Real.dist_eq, abs_sub_le_iff]
  have hx := mem_Icc_of_mem_stdSimplex x.2 j
  have hy := mem_Icc_of_mem_stdSimplex y.2 j
  constructor
  · linarith [hx.2, hy.1]
  · linarith [hy.2, hx.1]

/-- **Stage 6 payoff.** The pieces of the iterated barycentric subdivision of
any affine simplex in the standard simplex become uniformly small. -/
theorem exists_asubIter_small (n : ℕ) (w : Fin (n + 1) → stdSimplex ℝ (Fin (d + 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k, ∀ u ∈ ((asubIter (baryFn d) k n) (asimplex w)).support,
      ∀ i j, dist (u i) (u j) < ε := by
  have hlt : ((n : ℝ) / (n + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨k, fun u hu i j => ?_⟩
  have hbound := (asubIter_support_bound k n w 1 zero_le_one
    (fun i j => stdSimplex_dist_le_one _ _) u hu).1 i j
  calc dist (u i) (u j) ≤ ((n : ℝ) / (n + 1)) ^ k * 1 := hbound
    _ = ((n : ℝ) / (n + 1)) ^ k := mul_one _
    _ < ε := hk

end Diameter

/-! ## Stage 7: the small-simplices theorem

For an open cover `U ∪ V = X` and a singular simplex `σ`, the Lebesgue
number of the preimage cover `σ⁻¹U, σ⁻¹V` of the compact metric `Δⁿ`
together with the stage 6 decay yields an iterate `k` of the singular
subdivision all of whose pieces land in `U` or in `V`.  By
`gen_comp_sdOpIter`, the pieces of `sdOpIter X n k` on the generator of `σ`
are exactly the `pushSimplex σ u` for `u` in the support of the iterated
affine subdivision of the identity tuple, so smallness is stated over that
support.  The chain-homotopy witness relating `sdOpIter X n k` to the
identity is `tOpIter_chain_homotopy_succ` / `tOpIter_chain_homotopy_zero`. -/

section SmallSimplices

open SingularPrism

variable {X : TopCat.{0}}

/-- The affine map of a tuple lands in the tuple's hull. -/
lemma affineMap_mem_hullOf {d m : ℕ} (u : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1)))
    (x : stdSimplex ℝ (Fin (m + 1))) :
    ((affineMap u x : Fin (d + 1) → ℝ)) ∈ hullOf u := by
  have hrep : ((affineMap u x : Fin (d + 1) → ℝ)) =
      ∑ i, x i • ((u i : Fin (d + 1) → ℝ)) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact affineMap_apply_coe u x j
  rw [hrep]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => stdSimplex.zero_le x i)
    (stdSimplex.sum_eq_one x) (fun i _ => coe_mem_hullOf u i)

/-- Every point of an affine piece is within the piece's vertex spread of
its zeroth vertex. -/
lemma dist_affineMap_le {d m : ℕ} {u : Fin (m + 1) → stdSimplex ℝ (Fin (d + 1))}
    {D : ℝ} (hu : ∀ i j, dist (u i) (u j) ≤ D) (x : stdSimplex ℝ (Fin (m + 1))) :
    dist (affineMap u x) (u 0) ≤ D :=
  dist_le_of_mem_hullOf hu (affineMap_mem_hullOf u x) (coe_mem_hullOf u 0)

/-- **Stage 7: the small-simplices theorem.** For open sets `U, V` covering
`X` and any singular `n`-simplex `s`, there is an iterate `k` such that
every piece of `sdOpIter X n k` applied to the generator of `s` (i.e. every
`pushSimplex σ u` with `u` in the support of the iterated affine
subdivision, per `gen_comp_sdOpIter`) has range contained in `U` or in `V`. -/
theorem exists_sdOpIter_small {n : ℕ} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (s : Idx X n) :
    ∃ k, ∀ u ∈ ((asubIter (baryFn n) k n) (asimplex (idTuple n))).support,
      Set.range ⇑(simplexEquiv X n (pushSimplex (simplexEquiv X n s) u)) ⊆ U ∨
        Set.range ⇑(simplexEquiv X n (pushSimplex (simplexEquiv X n s) u)) ⊆ V := by
  set σ := simplexEquiv X n s with hσ
  haveI : CompactSpace (stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex _)
  have hcover : (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) ⊆
      ⋃ b : Bool, (if b then ⇑σ ⁻¹' U else ⇑σ ⁻¹' V) := by
    intro x _
    have hmem : σ x ∈ U ∪ V := by rw [hUV]; trivial
    rcases hmem with h | h
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
  have hopen : ∀ b : Bool, IsOpen (if b then ⇑σ ⁻¹' U else ⇑σ ⁻¹' V) := by
    intro b
    cases b
    · exact hV.preimage σ.continuous
    · exact hU.preimage σ.continuous
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  obtain ⟨k, hk⟩ := exists_asubIter_small n (idTuple n) (half_pos hδ)
  refine ⟨k, fun u hu => ?_⟩
  obtain ⟨b, hb⟩ := hball (u 0) (Set.mem_univ _)
  have himg : Set.range ⇑(σ.comp (affineMap u)) ⊆
      (if b then U else V) := by
    rintro y ⟨x, rfl⟩
    have hdist : dist (affineMap u x) (u 0) < δ := by
      have hle := dist_affineMap_le (fun i j => (hk u hu i j).le) x
      linarith
    have hxball : affineMap u x ∈ Metric.ball (u 0) δ := Metric.mem_ball.mpr hdist
    have hpre := hb hxball
    cases b
    · exact hpre
    · exact hpre
  rw [simplexEquiv_pushSimplex]
  cases b
  · exact Or.inr himg
  · exact Or.inl himg

end SmallSimplices

end SingularSubdivision
end Foundation
end IndisputableMonolith
