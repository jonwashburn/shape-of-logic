/-
Sphere homology `H_*(Sⁿ; ℤ)`: the geometric half of Stage C, and Stage D.

Layer 5b of the excision spine, continuing `SingularSphere.lean` (which
holds Stages A/B and the abstract Mayer-Vietoris consequences).

## Contents

* Step 1 (concrete cover): `Sph n` is the unit sphere in
  `EuclideanSpace ℝ (Fin (n+1))`; `coverU`/`coverV` remove the south/north
  pole; both are open, cover, and are contractible via Mathlib's
  stereographic projection (`contractibleSpace_compl_singleton_sphere`).
* Step 2 (equator, homotopy type of the intersection): rather than the
  hand-rolled normalization retraction sketched in the parent frontier
  note, we compose the stereographic homeomorphism (punctured sphere ≅
  orthogonal hyperplane, with the second pole going to `0`) with Mathlib's
  polar-coordinates homeomorphism `homeomorphUnitSphereProd`
  (`{0}ᶜ ≃ₜ sphere × (0,∞)`) and collapse the contractible factor:
  `coverU ∩ coverV ≃ₕ Sⁿ⁻¹` (`interHomotopyEquiv`).
* Step 3 (induction): the suspension isomorphism
  `H_{k+2}(Sⁿ⁺¹) ≅ H_{k+1}(Sⁿ)` (`suspensionIso`), the base case `S⁰`
  (finite, hence discrete and totally disconnected), `H₁(Sⁿ⁺²) = 0`
  (path-connected intersection), and the non-vanishing of `H₁(S¹)`
  (a point-difference class in the two-arc intersection is a nonzero
  kernel element of the Mayer-Vietoris pair map, hence lifts through the
  connecting map by exactness).
* Step 4 (Stage D exports; all `#print axioms`-clean, only `propext`,
  `Classical.choice`, `Quot.sound`):
  - `sphere_top_ne_zero : ¬ IsZero (H_n(Sⁿ))` for `1 ≤ n`;
  - `sphere_homology_vanish : IsZero (H_k(Sⁿ))` for `1 ≤ k`, `k ≠ n`;
  - `spheres_not_homotopyEquivalent :
      m ≠ n → IsEmpty (HomotopyEquiv Sᵐ Sⁿ)`;
  - `sphere_dim_eq_of_homotopyEquiv` (the `Nonempty → m = n` form).

## FRONTIER (for the next worker)

Stages A-D of the excision spine are COMPLETE: this file builds green,
0 sorry, 0 new axioms, on top of `SingularSphere.lean` (Stages A/B/C).
The sphere model is `Sph n := TopCat.of (Metric.sphere
(0 : EuclideanSpace ℝ (Fin (n+1))) 1)` with homology `Hgrp (Sph n) k`.

Next: the campaign consumers.
1. The `D = 2` and `D ≥ 4` linking-vanishing argument consuming Stage D:
   spheres `S¹`/`S^{D-2}` can be unlinked in dimension `D ≠ 3` because the
   relevant homology/homotopy obstruction vanishes there; the Stage D
   exports supply the dimension-detection facts
   (`sphere_dim_eq_of_homotopyEquiv`, `sphere_homology_vanish`,
   `sphere_top_ne_zero`).
2. `AlexanderLinkingBridge` assembly in `PublicSpine.lean`, replacing the
   S¹-cohomology axiom of `Foundation/DimensionForcing.lean`
   (`linking_requires_D3`).

Load-bearing tricks documented for reuse: the `amb` ambient-coordinate
abbrev (subtype-of-`TopCat.of` coercion bridge; plain `↑` coercions fail
to elaborate on `↥(Sph n)`), the `esp0_ext`/`esp1_ext` coordinatewise
extensionality helpers (raw `PiLp.ext` + `fin_cases` produces
un-rewritable `⟨0, ⋯⟩` indices), and the polar-coordinates route to the
equator homotopy equivalence (no hand-rolled normalization homotopy:
stereographic ∘ `homeomorphUnitSphereProd` ∘ collapse `Ioi 0`).

## Instance-diamond note (load-bearing, inherited from layers 4-5)

For `R = ℤ` every `ModuleCat ℤ` carrier has two `Module ℤ` instances
(`isModule` and `AddCommGroup.toIntModule`), propositionally but not
definitionally equal, and synthesis prefers the generic one.  This file
deprioritizes `AddCommGroup.toIntModule` and `SubNegMonoid.toZSMul`
locally, matching layers 1-5.
-/
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import IndisputableMonolith.Foundation.SingularSphere

namespace IndisputableMonolith
namespace Foundation
namespace SingularSphereGeometry

open CategoryTheory Category Limits AlgebraicTopology Simplicial Opposite
open SingularPrism SingularSubdivision SingularMayerVietoris SingularSphere
open Metric Set

attribute [local instance 10] Classical.decEq

/- See the instance-diamond note in the module header. -/
attribute [local instance 0] AddCommGroup.toIntModule
attribute [local instance 0] SubNegMonoid.toZSMul

/-! ## Step 1: the sphere model, poles, and the open cover -/

/-- The ambient Euclidean space of `Sⁿ`. -/
noncomputable abbrev Esp (n : ℕ) : Type := EuclideanSpace ℝ (Fin (n + 1))

/-- The `n`-sphere as a topological space: the unit sphere in
`EuclideanSpace ℝ (Fin (n+1))`. -/
noncomputable def Sph (n : ℕ) : TopCat.{0} :=
  TopCat.of (sphere (0 : Esp n) 1)

/-- The north-pole vector: the last standard basis vector. -/
noncomputable def northV (n : ℕ) : Esp n :=
  EuclideanSpace.single (Fin.last n) 1

lemma norm_northV (n : ℕ) : ‖northV n‖ = 1 := by
  rw [northV, EuclideanSpace.norm_single, norm_one]

/-- The north pole, as a point of the sphere. -/
noncomputable def northP (n : ℕ) : sphere (0 : Esp n) 1 :=
  ⟨northV n, by rw [mem_sphere_zero_iff_norm]; exact norm_northV n⟩

/-- The south pole, as a point of the sphere. -/
noncomputable def southP (n : ℕ) : sphere (0 : Esp n) 1 := -northP n

lemma northP_ne_southP (n : ℕ) : northP n ≠ southP n := by
  intro h
  have h1 : (northP n : Esp n) = -(northP n : Esp n) := by
    calc (northP n : Esp n) = (southP n : Esp n) := congrArg _ h
      _ = -(northP n : Esp n) := coe_neg_sphere (northP n)
  have h2 : (northP n : Esp n) = 0 := by
    have hsum : (northP n : Esp n) + (northP n : Esp n) = 0 := by
      nth_rewrite 2 [h1]
      exact add_neg_cancel _
    have h2' : (2 : ℝ) • (northP n : Esp n) = 0 := by
      rw [two_smul]
      exact hsum
    rcases smul_eq_zero.mp h2' with h | h
    · exact absurd h (by norm_num)
    · exact h
  have h3 : ‖(northP n : Esp n)‖ = 1 := norm_eq_of_mem_sphere (northP n)
  rw [h2, norm_zero] at h3
  exact zero_ne_one h3

/-- The subtype topology of `Sph n` is the metric sphere topology
(instance bridge across `TopCat.of`). -/
instance (n : ℕ) : T1Space ↥(Sph n) :=
  inferInstanceAs (T1Space (sphere (0 : Esp n) 1))

/-- The sphere minus the south pole. -/
noncomputable def coverU (n : ℕ) : Set ↥(Sph n) := {southP n}ᶜ

/-- The sphere minus the north pole. -/
noncomputable def coverV (n : ℕ) : Set ↥(Sph n) := {northP n}ᶜ

lemma isOpen_coverU (n : ℕ) : IsOpen (coverU n) := isOpen_compl_singleton

lemma isOpen_coverV (n : ℕ) : IsOpen (coverV n) := isOpen_compl_singleton

lemma coverU_union_coverV (n : ℕ) : coverU n ∪ coverV n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases h : x = southP n
  · right
    intro hx
    rw [Set.mem_singleton_iff] at hx
    exact northP_ne_southP n (hx.symm.trans h)
  · left
    exact h

/-! ## Step 1: contractibility of the punctured sphere -/

/-- **The punctured sphere is contractible** (any sphere, any removed
point): stereographic projection is a homeomorphism from the complement
of a point onto the orthogonal hyperplane, which is a real topological
vector space and hence contractible. -/
theorem contractibleSpace_compl_singleton_sphere {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : sphere (0 : E) 1) :
    ContractibleSpace ↥(({p}ᶜ : Set (sphere (0 : E) 1))) := by
  have hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hsrc : ({p}ᶜ : Set (sphere (0 : E) 1)) = (stereographic hp).source := rfl
  have e1 : ↥(({p}ᶜ : Set (sphere (0 : E) 1))) ≃ₜ ↥((stereographic hp).source) :=
    Homeomorph.setCongr hsrc
  have e2 : ↥((stereographic hp).source) ≃ₜ ↥((stereographic hp).target) :=
    (stereographic hp).toHomeomorphSourceTarget
  have e3 : ↥((stereographic hp).target) ≃ₜ (ℝ ∙ (p : E))ᗮ :=
    (Homeomorph.setCongr (stereographic_target hp)).trans
      (Homeomorph.Set.univ _)
  exact ((e1.trans e2).trans e3).contractibleSpace

instance contractible_coverU (n : ℕ) : ContractibleSpace ↥(coverU n) :=
  contractibleSpace_compl_singleton_sphere (southP n)

instance contractible_coverV (n : ℕ) : ContractibleSpace ↥(coverV n) :=
  contractibleSpace_compl_singleton_sphere (northP n)

/-! ## Step 2: the homotopy type of the intersection -/

/-- The orthogonal hyperplane at the north pole. -/
noncomputable abbrev Hyp (n : ℕ) : Type := ((ℝ ∙ (northV n))ᗮ : Submodule ℝ (Esp n))

lemma mem_inter_iff (n : ℕ) (x : ↥(Sph n)) :
    x ∈ coverU n ∩ coverV n ↔ x ≠ southP n ∧ x ≠ northP n := by
  constructor
  · rintro ⟨hU, hV⟩
    exact ⟨hU, hV⟩
  · rintro ⟨hS, hN⟩
    exact ⟨hS, hN⟩

/-- Stereographic projection at the north pole restricts to a homeomorphism
from the doubly punctured sphere onto the punctured hyperplane (the south
pole goes to the origin). -/
noncomputable def interHomeoPunctured (n : ℕ) :
    ↥(coverU n ∩ coverV n) ≃ₜ ↥(({0}ᶜ : Set (Hyp n))) := by
  have hnv : ‖northV n‖ = 1 := norm_northV n
  have hsource : ∀ y : ↥(Sph n), y ≠ northP n →
      y ∈ (stereographic hnv).source := by
    intro y hy
    show y ∈ ({(⟨northV n, _⟩ : sphere (0 : Esp n) 1)}ᶜ : Set _)
    exact hy
  have hst_south : stereographic hnv (southP n) = 0 :=
    stereographic_apply_neg (northP n)
  refine Homeomorph.mk (Equiv.mk ?_ ?_ ?_ ?_) ?_ ?_
  · -- forward map
    refine fun x => ⟨stereographic hnv x.1, ?_⟩
    obtain ⟨hS, hN⟩ := (mem_inter_iff n x.1).mp x.2
    intro h0
    apply hS
    refine (stereographic hnv).injOn (hsource x.1 hN)
      (hsource (southP n) (fun h => northP_ne_southP n h.symm)) ?_
    rw [hst_south]
    exact h0
  · -- inverse map
    refine fun y => ⟨(stereographic hnv).symm y.1, ?_⟩
    have hmem : (stereographic hnv).symm y.1 ∈ (stereographic hnv).source :=
      (stereographic hnv).map_target (by
        rw [stereographic_target]; exact Set.mem_univ _)
    refine (mem_inter_iff n _).mpr ⟨?_, hmem⟩
    intro hS
    apply y.2
    have := (stereographic hnv).right_inv (x := y.1) (by
      rw [stereographic_target]; exact Set.mem_univ _)
    rw [← this, hS, hst_south]
    rfl
  · -- left inverse
    intro x
    obtain ⟨_, hN⟩ := (mem_inter_iff n x.1).mp x.2
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val
      ((stereographic hnv).left_inv (hsource x.1 hN))))
  · -- right inverse
    intro y
    exact Subtype.ext ((stereographic hnv).right_inv (x := y.1) (by
      rw [stereographic_target]; exact Set.mem_univ _))
  · -- continuity, forward
    refine Continuous.subtype_mk ?_ _
    refine ContinuousOn.comp_continuous
      (stereographic hnv).continuousOn continuous_subtype_val ?_
    intro x
    exact hsource x.1 ((mem_inter_iff n x.1).mp x.2).2
  · -- continuity, inverse
    refine Continuous.subtype_mk ?_ _
    refine ContinuousOn.comp_continuous
      (stereographic hnv).continuousOn_symm continuous_subtype_val ?_
    intro y
    rw [stereographic_target]
    exact Set.mem_univ _

/-- The punctured hyperplane in polar coordinates:
`Hyp n \ {0} ≃ₜ sphere(Hyp n) × (0, ∞)`. -/
noncomputable def puncturedPolar (n : ℕ) :
    ↥(({0}ᶜ : Set (Hyp n))) ≃ₜ
      (↥(sphere (0 : Hyp n) 1) × ↥(Ioi (0 : ℝ))) :=
  homeomorphUnitSphereProd (Hyp n)

/-- A linear isometry equivalence restricts to a homeomorphism of unit
spheres. -/
noncomputable def sphereHomeoOfLinearIsometryEquiv {F G : Type}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ F] [NormedSpace ℝ G] (e : F ≃ₗᵢ[ℝ] G) :
    ↥(sphere (0 : F) 1) ≃ₜ ↥(sphere (0 : G) 1) :=
  e.toHomeomorph.subtype (fun x => by
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm]
    exact (congrArg (· = 1) (e.norm_map x)).symm.to_iff)

/-- The finrank fact for the ambient space, in the shape
`fromOrthogonalSpanSingleton` wants. -/
lemma fact_finrank_esp (n : ℕ) :
    Fact (Module.finrank ℝ (Esp (n + 1)) = n + 1 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The north-pole hyperplane of `Sⁿ⁺¹` is isometric to `EuclideanSpace ℝ
(Fin (n+1))`, the ambient space of `Sⁿ`. -/
noncomputable def hypIsometry (n : ℕ) : Hyp (n + 1) ≃ₗᵢ[ℝ] Esp n :=
  haveI : Fact (Module.finrank ℝ (Esp (n + 1)) = n + 1 + 1) :=
    fact_finrank_esp n
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
    (fun h => one_ne_zero (by rw [← norm_northV (n + 1), h, norm_zero]))).repr

instance : ContractibleSpace ↥(Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, Set.mem_Ioi.mpr one_pos⟩

/-- Collapsing a contractible factor is a homotopy equivalence. -/
noncomputable def hequivProdContractible (Z C : Type)
    [TopologicalSpace Z] [TopologicalSpace C] [ContractibleSpace C] :
    ContinuousMap.HomotopyEquiv (Z × C) Z :=
  ((ContinuousMap.HomotopyEquiv.refl Z).prodCongr
      (ContractibleSpace.hequiv_unit C).some).trans
    (Homeomorph.prodUnique Z Unit).toHomotopyEquiv

/-- **Step 2.** The intersection of the two punctured-sphere covers of
`Sⁿ⁺¹` is homotopy equivalent to `Sⁿ`. -/
noncomputable def interHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      ↥(coverU (n + 1) ∩ coverV (n + 1)) ↥(Sph n) :=
  (((interHomeoPunctured (n + 1)).trans
    ((puncturedPolar (n + 1)).trans
      ((sphereHomeoOfLinearIsometryEquiv (hypIsometry n)).prodCongr
        (Homeomorph.refl ↥(Ioi (0 : ℝ)))))).toHomotopyEquiv).trans
    (hequivProdContractible ↥(sphere (0 : Esp n) 1) ↥(Ioi (0 : ℝ)))

/-! ## Step 3: the suspension isomorphism -/

/-- Homotopy-equivalence isomorphism on `Hgrp` (retyped from layer 1). -/
noncomputable def hgrpIso {X Y : TopCat.{0}}
    (h : ContinuousMap.HomotopyEquiv X Y) (k : ℕ) : Hgrp X k ≅ Hgrp Y k :=
  homotopyEquiv_homology_iso h k

/-- **The suspension isomorphism** `H_{k+2}(Sⁿ⁺¹) ≅ H_{k+1}(Sⁿ)`: the
Mayer-Vietoris connecting map for the two-punctured-sphere cover, followed
by the homotopy equivalence of the intersection with the equator sphere. -/
noncomputable def suspensionIso (n k : ℕ) :
    Hgrp (Sph (n + 1)) (k + 2) ≅ Hgrp (Sph n) (k + 1) :=
  haveI : IsIso (mvδ (isOpen_coverU (n + 1)) (isOpen_coverV (n + 1))
      (coverU_union_coverV (n + 1)) (k + 1)) :=
    isIso_mvδ_of_contractible _ _ _ k
  asIso (mvδ (isOpen_coverU (n + 1)) (isOpen_coverV (n + 1))
      (coverU_union_coverV (n + 1)) (k + 1)) ≪≫
    hgrpIso (interHomotopyEquiv n) (k + 1)

/-! ## Step 3: the base case `S⁰` -/

/-- The ambient coordinates of a sphere point (coercion helper across
`TopCat.of`). -/
noncomputable abbrev amb {n : ℕ} (x : ↥(Sph n)) : Esp n := x.1

lemma norm_amb {n : ℕ} (x : ↥(Sph n)) : ‖amb x‖ = 1 :=
  norm_eq_of_mem_sphere x

lemma amb_injective {n : ℕ} : Function.Injective (amb (n := n)) :=
  fun _ _ h => Subtype.ext h

/-- Coordinatewise extensionality in `Esp 0`. -/
lemma esp0_ext {a b : Esp 0} (h0 : a 0 = b 0) : a = b := by
  apply PiLp.ext
  intro i
  have hi : i = 0 := Fin.ext (by omega)
  rw [hi]
  exact h0

/-- Coordinatewise extensionality in `Esp 1`. -/
lemma esp1_ext {a b : Esp 1} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  apply PiLp.ext
  intro i
  refine Fin.cases h0 (fun j => ?_) i
  have hj : j = 0 := Fin.ext (by omega)
  rw [hj, show (0 : Fin 1).succ = (1 : Fin 2) from by decide]
  exact h1

lemma northV_ne_zero (n : ℕ) : northV n ≠ 0 := fun h =>
  one_ne_zero (by rw [← norm_northV n, h, norm_zero])

lemma abs_eq_one_of_sq_eq_one {t : ℝ} (h : t ^ 2 = 1) : |t| = 1 := by
  have h3 : (|t| - 1) * (|t| + 1) = 0 := by
    have : |t| ^ 2 = 1 := by rw [sq_abs]; exact h
    nlinarith [this]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · have := abs_nonneg t
    linarith

lemma amb_southP (n : ℕ) : amb (southP n : sphere (0 : Esp n) 1) = -(northV n) :=
  coe_neg_sphere (northP n)

/-- A point of `S⁰` is one of the two poles. -/
lemma sph0_eq_pole (x : ↥(Sph 0)) : x = northP 0 ∨ x = southP 0 := by
  have hx : ‖amb x‖ = 1 := norm_amb x
  have hsq : amb x 0 ^ 2 = 1 := by
    have hs := EuclideanSpace.norm_sq_eq (amb x)
    rw [hx, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs] at hs
    linarith [hs]
  have habs : |amb x 0| = 1 := abs_eq_one_of_sq_eq_one hsq
  have hlast : (0 : Fin 1) = Fin.last 0 := by decide
  rcases (abs_eq zero_le_one).mp habs with h | h
  · left
    apply amb_injective
    apply esp0_ext
    rw [h]
    show (1 : ℝ) = northV 0 0
    rw [northV, EuclideanSpace.single_apply, if_pos hlast]
  · right
    apply amb_injective
    rw [amb_southP 0]
    apply esp0_ext
    rw [h]
    show (-1 : ℝ) = -(northV 0 0)
    rw [northV, EuclideanSpace.single_apply, if_pos hlast]

open Classical in
instance : Finite ↥(Sph 0) := by
  refine Finite.of_injective
    (fun x : ↥(Sph 0) => decide (x = northP 0)) ?_
  intro x y hxy
  dsimp only at hxy
  have hiff : (x = northP 0) ↔ (y = northP 0) := decide_eq_decide.mp hxy
  rcases sph0_eq_pole x with hx | hx <;> rcases sph0_eq_pole y with hy | hy
  · rw [hx, hy]
  · exact absurd ((hiff.mp hx).symm.trans hy) (northP_ne_southP 0)
  · exact absurd ((hiff.mpr hy).symm.trans hx) (northP_ne_southP 0)
  · rw [hx, hy]

instance : DiscreteTopology ↥(Sph 0) := Finite.instDiscreteTopology

/-- **Base case.** All positive-degree homology of `S⁰` vanishes. -/
lemma isZero_sph0 {k : ℕ} (hk : k ≠ 0) : IsZero (Hgrp (Sph 0) k) :=
  isZero_homology_of_totallyDisconnected (Sph 0) hk

/-! ## Step 3: path-connectedness of the intersection in dimension `≥ 2` -/

lemma finrank_hyp (n : ℕ) : Module.finrank ℝ (Hyp (n + 1)) = n + 1 :=
  haveI : Fact (Module.finrank ℝ (Esp (n + 1)) = n + 1 + 1) :=
    fact_finrank_esp n
  Submodule.finrank_orthogonal_span_singleton (northV_ne_zero (n + 1))

lemma one_lt_rank_hyp (n : ℕ) : 1 < Module.rank ℝ (Hyp (n + 2)) := by
  have hfr : Module.finrank ℝ (Hyp (n + 2)) = n + 2 := finrank_hyp (n + 1)
  rw [← Module.finrank_eq_rank, hfr]
  exact_mod_cast (by omega : 1 < n + 2)

instance pathConnected_inter (n : ℕ) :
    PathConnectedSpace ↥(coverU (n + 2) ∩ coverV (n + 2)) := by
  have h1 : IsPathConnected ({0}ᶜ : Set (Hyp (n + 2))) :=
    isPathConnected_compl_singleton_of_one_lt_rank (one_lt_rank_hyp n) 0
  haveI : PathConnectedSpace ↥(({0}ᶜ : Set (Hyp (n + 2)))) :=
    isPathConnected_iff_pathConnectedSpace.mp h1
  exact (interHomeoPunctured (n + 2)).symm.surjective.pathConnectedSpace
    (interHomeoPunctured (n + 2)).symm.continuous

/-! ## Step 3: the vanishing induction -/

/-- **Stage D vanishing.** `H_k(Sⁿ) = 0` for `1 ≤ k`, `k ≠ n`. -/
theorem sphere_homology_vanish :
    ∀ n k : ℕ, 1 ≤ k → k ≠ n → IsZero (Hgrp (Sph n) k) := by
  intro n
  induction n with
  | zero =>
      intro k hk _
      exact isZero_sph0 (by omega)
  | succ n ih =>
      intro k hk hkn
      match k, hk with
      | 1, _ =>
          have hn : n ≠ 0 := by omega
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          exact isZero_h1_of_contractible (isOpen_coverU (m + 2))
            (isOpen_coverV (m + 2)) (coverU_union_coverV (m + 2))
      | (k + 2), _ =>
          exact (ih (k + 1) (by omega) (by omega)).of_iso (suspensionIso n k)

/-! ## Step 3: non-vanishing of `H₁(S¹)` -/

section CircleTop

/-- The east point of the circle. -/
noncomputable def eastP : sphere (0 : Esp 1) 1 :=
  ⟨EuclideanSpace.single 0 1, by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single, norm_one]⟩

/-- The west point of the circle. -/
noncomputable def westP : sphere (0 : Esp 1) 1 := -eastP

lemma amb_eastP_zero : amb (eastP : ↥(Sph 1)) 0 = 1 := by
  show EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 0 = 1
  rw [EuclideanSpace.single_apply, if_pos rfl]

lemma amb_westP_zero : amb (westP : ↥(Sph 1)) 0 = -1 := by
  have hc : amb (westP : ↥(Sph 1)) =
      -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := coe_neg_sphere eastP
  rw [hc, show (-(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) 0 =
    -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 0) from rfl,
    EuclideanSpace.single_apply, if_pos rfl]

lemma northV_zero : northV 1 0 = 0 := by
  rw [northV, EuclideanSpace.single_apply, if_neg (by decide)]

lemma amb_northP_zero : amb (northP 1 : ↥(Sph 1)) 0 = 0 := northV_zero

lemma amb_southP_zero : amb (southP 1 : ↥(Sph 1)) 0 = 0 := by
  rw [show amb (southP 1 : ↥(Sph 1)) = -(northV 1) from amb_southP 1,
    show (-(northV 1)) 0 = -(northV 1 0) from rfl, northV_zero]
  exact neg_zero

/-- On the doubly punctured circle, the first coordinate never vanishes. -/
lemma coord_zero_ne_zero (x : ↥(Sph 1)) (hS : x ≠ southP 1)
    (hN : x ≠ northP 1) : amb x 0 ≠ 0 := by
  intro h0
  have hx : ‖amb x‖ = 1 := norm_amb x
  have hsq : amb x 1 ^ 2 = 1 := by
    have hs := EuclideanSpace.norm_sq_eq (amb x)
    rw [hx, Fin.sum_univ_two, h0] at hs
    simp only [Real.norm_eq_abs, sq_abs] at hs
    linarith [hs]
  have habs : |amb x 1| = 1 := abs_eq_one_of_sq_eq_one hsq
  have hlast : (1 : Fin 2) = Fin.last 1 := by decide
  rcases (abs_eq zero_le_one).mp habs with h | h
  · apply hN
    apply amb_injective
    apply esp1_ext
    · rw [h0]
      show (0 : ℝ) = northV 1 0
      rw [northV_zero]
    · rw [h]
      show (1 : ℝ) = northV 1 1
      rw [northV, EuclideanSpace.single_apply, if_pos hlast]
  · apply hS
    apply amb_injective
    rw [amb_southP 1]
    apply esp1_ext
    · rw [h0]
      show (0 : ℝ) = -(northV 1 0)
      rw [northV_zero, neg_zero]
    · rw [h]
      show (-1 : ℝ) = -(northV 1 1)
      rw [northV, EuclideanSpace.single_apply, if_pos hlast]

lemma eastP_mem_inter : (eastP : ↥(Sph 1)) ∈ coverU 1 ∩ coverV 1 := by
  refine (mem_inter_iff 1 eastP).mpr ⟨?_, ?_⟩
  · intro h
    have h2 := amb_eastP_zero
    rw [show amb (eastP : ↥(Sph 1)) = amb (southP 1 : ↥(Sph 1)) from
      congrArg amb h, amb_southP_zero] at h2
    exact one_ne_zero h2.symm
  · intro h
    have h2 := amb_eastP_zero
    rw [show amb (eastP : ↥(Sph 1)) = amb (northP 1 : ↥(Sph 1)) from
      congrArg amb h, amb_northP_zero] at h2
    exact one_ne_zero h2.symm

lemma westP_mem_inter : (westP : ↥(Sph 1)) ∈ coverU 1 ∩ coverV 1 := by
  refine (mem_inter_iff 1 westP).mpr ⟨?_, ?_⟩
  · intro h
    have h2 := amb_westP_zero
    rw [show amb (westP : ↥(Sph 1)) = amb (southP 1 : ↥(Sph 1)) from
      congrArg amb h, amb_southP_zero] at h2
    norm_num at h2
  · intro h
    have h2 := amb_westP_zero
    rw [show amb (westP : ↥(Sph 1)) = amb (northP 1 : ↥(Sph 1)) from
      congrArg amb h, amb_northP_zero] at h2
    norm_num at h2

/-- The doubly punctured circle, as a space. -/
noncomputable abbrev Wc : TopCat.{0} :=
  TopCat.of (coverU 1 ∩ coverV 1 : Set ↥(Sph 1))

/-- The east point in the intersection. -/
noncomputable def aW : ↥Wc := ⟨eastP, eastP_mem_inter⟩

/-- The west point in the intersection. -/
noncomputable def bW : ↥Wc := ⟨westP, westP_mem_inter⟩

/-- The coordinate function on the doubly punctured circle. -/
noncomputable def coordW (w : ↥Wc) : ℝ := amb (w.1 : ↥(Sph 1)) 0

/-- The right (east) arc of the doubly punctured circle. -/
noncomputable def arcA : Set ↥Wc := {w | 0 < coordW w}

lemma continuous_coordW : Continuous coordW :=
  (EuclideanSpace.proj (0 : Fin 2)).continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)

lemma isClopen_arcA : IsClopen arcA := by
  constructor
  · -- closed: on `Wc` the coordinate never vanishes, so `< 0`/`> 0` split
    have heq : arcA = coordW ⁻¹' (Ici (0 : ℝ)) := by
      apply Set.ext
      intro w
      obtain ⟨hS, hN⟩ := (mem_inter_iff 1 w.1).mp w.2
      constructor
      · intro hw
        have hw' : (0 : ℝ) < coordW w := hw
        exact le_of_lt hw'
      · intro hw
        have hw' : (0 : ℝ) ≤ coordW w := hw
        show (0 : ℝ) < coordW w
        exact lt_of_le_of_ne hw'
          (fun h => coord_zero_ne_zero w.1 hS hN h.symm)
    rw [heq]
    exact isClosed_Ici.preimage continuous_coordW
  · have heq : arcA = coordW ⁻¹' (Ioi (0 : ℝ)) := rfl
    rw [heq]
    exact isOpen_Ioi.preimage continuous_coordW

lemma aW_mem_arcA : aW ∈ arcA := by
  show (0 : ℝ) < coordW aW
  rw [show coordW aW = amb (eastP : ↥(Sph 1)) 0 from rfl, amb_eastP_zero]
  exact one_pos

lemma bW_notMem_arcA : bW ∉ arcA := by
  show ¬ (0 : ℝ) < coordW bW
  rw [show coordW bW = amb (westP : ↥(Sph 1)) 0 from rfl, amb_westP_zero]
  norm_num

/-- The point-difference class in `H₀` of the two-arc intersection. -/
noncomputable def diffClass : ModuleCat.of ℤ ℤ ⟶ Hgrp Wc 0 :=
  ptH Wc aW - ptH Wc bW

/-- The point-difference class pairs to `1` against the east-arc
augmentation (hence is nonzero). -/
lemma diffClass_pairing :
    diffClass ≫ augH Wc arcA isClopen_arcA = 𝟙 (ModuleCat.of ℤ ℤ) := by
  rw [diffClass, Preadditive.sub_comp, ptH_augH, ptH_augH,
    if_pos aW_mem_arcA, if_neg bW_notMem_arcA, sub_zero]

/-- The point-difference class dies in `H₀(U) ⊞ H₀(V)` (both points join
inside each punctured circle). -/
lemma diffClass_mvPair :
    diffClass ≫ mvPair (coverU 1) (coverV 1) 0 = 0 := by
  have hjU : ptH (TopCat.of (coverU 1))
      ((mvInclU (coverU 1) (coverV 1)).hom aW) =
      ptH (TopCat.of (coverU 1))
        ((mvInclU (coverU 1) (coverV 1)).hom bW) :=
    ptH_eq_of_joined (PathConnectedSpace.joined _ _)
  have hjV : ptH (TopCat.of (coverV 1))
      ((mvInclV (coverU 1) (coverV 1)).hom aW) =
      ptH (TopCat.of (coverV 1))
        ((mvInclV (coverU 1) (coverV 1)).hom bW) :=
    ptH_eq_of_joined (PathConnectedSpace.joined _ _)
  apply biprod.hom_ext
  · rw [assoc, zero_comp, mvPair, biprod.lift_fst, diffClass,
      Preadditive.sub_comp, ptH_natural, ptH_natural, hjU, sub_self]
  · rw [assoc, zero_comp, mvPair, biprod.lift_snd, Preadditive.comp_neg,
      diffClass, Preadditive.sub_comp, ptH_natural, ptH_natural, hjV,
      sub_self, neg_zero]

/-- **`H₁(S¹) ≠ 0`.** If it vanished, the Mayer-Vietoris connecting map
out of it would be zero, and exactness would kill the point-difference
class, contradicting its nonzero pairing. -/
theorem h1_s1_ne_zero : ¬ IsZero (Hgrp (Sph 1) 1) := by
  intro hZ
  have hδ : mvδ (isOpen_coverU 1) (isOpen_coverV 1)
      (coverU_union_coverV 1) 0 = 0 :=
    hZ.eq_of_src _ _
  have hex := mv_exact₁ (isOpen_coverU 1) (isOpen_coverV 1)
    (coverU_union_coverV 1) 0
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hker : mvPair (coverU 1) (coverV 1) 0 (diffClass (1 : ℤ)) = 0 := by
    rw [← ModuleCat.comp_apply, diffClass_mvPair, zeroApp]
  obtain ⟨w, hw⟩ := hex (diffClass (1 : ℤ)) hker
  have hw' : mvδ (isOpen_coverU 1) (isOpen_coverV 1)
      (coverU_union_coverV 1) 0 w = diffClass (1 : ℤ) := hw
  rw [hδ, zeroApp] at hw'
  have h1 : augH Wc arcA isClopen_arcA (diffClass (1 : ℤ)) = (1 : ℤ) := by
    rw [← ModuleCat.comp_apply, diffClass_pairing, ModuleCat.id_apply]
  rw [← hw', map_zero] at h1
  exact one_ne_zero h1.symm

end CircleTop

/-! ## Step 4: Stage D exports -/

/-- **Stage D.** The top homology of `Sⁿ` does not vanish (`1 ≤ n`). -/
theorem sphere_top_ne_zero : ∀ n : ℕ, 1 ≤ n → ¬ IsZero (Hgrp (Sph n) n) := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      intro _
      match n, ih with
      | 0, _ => exact h1_s1_ne_zero
      | (m + 1), ih =>
          intro hZ
          exact (ih (by omega)) (hZ.of_iso (suspensionIso (m + 1) m).symm)

/-- **Stage D.** Spheres of different dimension are not homotopy
equivalent. -/
theorem spheres_not_homotopyEquivalent {m n : ℕ} (hmn : m ≠ n) :
    IsEmpty (ContinuousMap.HomotopyEquiv ↥(Sph m) ↥(Sph n)) := by
  constructor
  intro e
  rcases Nat.lt_or_ge m n with h | h
  · exact sphere_top_ne_zero n (by omega)
      ((sphere_homology_vanish m n (by omega) (by omega)).of_iso
        (hgrpIso e n).symm)
  · have h' : n < m := lt_of_le_of_ne h (fun hh => hmn hh.symm)
    exact sphere_top_ne_zero m (by omega)
      ((sphere_homology_vanish n m (by omega) (by omega)).of_iso
        (hgrpIso e.symm m).symm)

/-- Stage D, `Nonempty` form: homotopy-equivalent spheres have equal
dimension. -/
theorem sphere_dim_eq_of_homotopyEquiv {m n : ℕ}
    (h : Nonempty (ContinuousMap.HomotopyEquiv ↥(Sph m) ↥(Sph n))) :
    m = n := by
  by_contra hmn
  exact (spheres_not_homotopyEquivalent hmn).false h.some

end SingularSphereGeometry
end Foundation
end IndisputableMonolith
