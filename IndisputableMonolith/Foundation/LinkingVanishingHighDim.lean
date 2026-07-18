/-
Linking vanishing in high dimension (D = 2 and D ≥ 4): the Mayer-Vietoris
reduction to the arc-complement acyclicity frontier.

## What this file proves (0 sorry, 0 new axioms)

Campaign P-d3link, final phase.  The binder predicate
(`PublicSpine.DetectsNontrivialLinking D`, restated verbatim below) asks for
an embedded circle in `S^D` whose complement has nonvanishing first singular
homology.  The full refutation for `D ≠ 3` is Alexander duality for
arbitrary (possibly wild) embedded circles.  This file carries out the
classical Mayer-Vietoris reduction (Hatcher 2B.1, circle case):

* **Two-point complement** (`twoPointComplHEquiv`, `isZero_h2_twoPointCompl`):
  for any two distinct points `p ≠ q` of `Sⁿ` (`n ≥ 1`), the complement
  `Sⁿ \ {p, q}` is homotopy equivalent to `Sⁿ⁻¹` (stereographic projection at
  `p`, a translation, and polar coordinates); hence `H₂(Sⁿ \ {p,q}) = 0`
  whenever `n ≠ 3`.
* **Semicircle arcs** (`arcMap`, `range_arcPlus/Minus`, …): the closed upper
  and lower semicircles of `S¹` are ranges of explicit embeddings of the
  unit interval meeting exactly in the east and west points.
* **The Mayer-Vietoris step** (`isZero_h1_inter`): if `U, V` are open, cover,
  `H₂(X) = 0` and `H₁(U) = H₁(V) = 0`, then `H₁(U ∩ V) = 0` (exactness of
  the banked MV sequence at `H₁(U ∩ V)`).
* **The reduction** (`isZero_h1_complement_of_embedding`,
  `not_detects_of_arcAcyclic`, `forces_D3_of_arcAcyclic`): granting the
  single remaining frontier `ArcComplementsAcyclic D` (every embedded arc in
  `S^D` has `H₁`-acyclic complement — true for every `D`, classically by the
  compact-support bisection argument), every embedded circle in `S^D`
  (`D ≠ 3`) has `H₁`-acyclic complement, so the binder's `forces_D3` holds.

## The precise remaining frontier

`ArcComplementsAcyclic D` (below): for every topological embedding
`a : [0,1] → S^D`, `H₁(S^D \ range a; ℤ) = 0`.  This is NOT an axiom and NOT
a sorry: it is a hypothesis parameter, to be discharged by the
compact-support bisection argument (Hatcher 2B.1, arc case) on top of the
banked Mayer-Vietoris layer.  Everything else in the `forces_D3` chain is
proved unconditionally here.

## Instance-diamond note (load-bearing, inherited from layers 4-5b)

For `R = ℤ` every `ModuleCat ℤ` carrier has two `Module ℤ` instances,
propositionally but not definitionally equal, and synthesis prefers the
generic one.  This file deprioritizes `AddCommGroup.toIntModule` and
`SubNegMonoid.toZSMul` locally, matching layers 1-5b.
-/
import IndisputableMonolith.Foundation.SingularSphereGeometry
import IndisputableMonolith.Foundation.LinkingVanishingLowDim

namespace IndisputableMonolith
namespace Foundation
namespace LinkingVanishingHighDim

open CategoryTheory Category Limits AlgebraicTopology Simplicial
open SingularPrism SingularSubdivision SingularMayerVietoris SingularSphere
open SingularSphereGeometry
open Metric Set

attribute [local instance 10] Classical.decEq

/- See the instance-diamond note in the module header. -/
attribute [local instance 0] AddCommGroup.toIntModule
attribute [local instance 0] SubNegMonoid.toZSMul

/-! ## The binder predicate, restated verbatim -/

/-- Verbatim restatement of `PublicSpine.linkingComplementH1`. -/
noncomputable def linkingComplementH1 (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)) : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of {x : TopCat.sphere.{0} D // x ∉ Set.range f})

/-- Verbatim restatement of `PublicSpine.DetectsNontrivialLinking`. -/
def DetectsNontrivialLinking (D : ℕ) : Prop :=
  ∃ f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D),
    Topology.IsEmbedding f ∧
      ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)

/-! ## The frontier: arc complements are `H₁`-acyclic -/

/-- **The precisely-stated remaining frontier** (Hatcher 2B.1, arc case):
every topological embedding of the unit interval into `S^D` has
`H₁`-acyclic complement.  Classically true for every `D` (compact-support
bisection); this file consumes it as a hypothesis parameter and reduces
`forces_D3` to it. -/
def ArcComplementsAcyclic (D : ℕ) : Prop :=
  ∀ a : C(unitInterval, ↥(Sph D)), Topology.IsEmbedding a →
    CategoryTheory.Limits.IsZero
      (Hgrp (TopCat.of {y : ↥(Sph D) // y ∉ Set.range a}) 1)

/-! ## Semicircle arcs of the circle -/

/-- The point of the plane with coordinates `(a, b)`. -/
noncomputable def pt2 (a b : ℝ) : Esp 1 :=
  WithLp.toLp 2 ![a, b]

@[simp] lemma pt2_zero (a b : ℝ) : pt2 a b 0 = a := rfl

@[simp] lemma pt2_one (a b : ℝ) : pt2 a b 1 = b := rfl

lemma pt2_norm (a b : ℝ) : ‖pt2 a b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  show Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) = Real.sqrt (a ^ 2 + b ^ 2)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

/-- Membership of `(a, b)` in the unit circle from `a² + b² = 1`. -/
lemma pt2_mem_sphere {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    pt2 a b ∈ sphere (0 : Esp 1) 1 := by
  rw [mem_sphere_zero_iff_norm, pt2_norm, h, Real.sqrt_one]

/-- Coordinates of a circle point satisfy the circle equation. -/
lemma coord_sq_add_sq (z : ↥(Sph 1)) : amb z 0 ^ 2 + amb z 1 ^ 2 = 1 := by
  have hs := EuclideanSpace.norm_sq_eq (amb z)
  rw [norm_amb, one_pow, Fin.sum_univ_two] at hs
  simpa only [Real.norm_eq_abs, sq_abs] using hs.symm

/-- The first coordinate of a circle point lies in `[-1, 1]` (squared form). -/
lemma sq_coord0_le_one (z : ↥(Sph 1)) : amb z 0 ^ 2 ≤ 1 := by
  nlinarith [coord_sq_add_sq z, sq_nonneg (amb z 1)]

/-- The semicircle arc: `t ↦ (1 - 2t, s·√(1 - (1-2t)²))`, where `s = ±1`
selects the upper or lower semicircle. -/
noncomputable def arcFun (s : ℝ) (hs : s ^ 2 = 1) (t : unitInterval) :
    ↥(Sph 1) :=
  ⟨pt2 (1 - 2 * (t : ℝ)) (s * Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2)), by
    apply pt2_mem_sphere
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hle : (1 - 2 * (t : ℝ)) ^ 2 ≤ 1 := by nlinarith
    rw [mul_pow, hs, one_mul, Real.sq_sqrt (by linarith)]
    ring⟩

lemma arcFun_coord0 (s : ℝ) (hs : s ^ 2 = 1) (t : unitInterval) :
    amb (arcFun s hs t) 0 = 1 - 2 * (t : ℝ) := rfl

lemma arcFun_coord1 (s : ℝ) (hs : s ^ 2 = 1) (t : unitInterval) :
    amb (arcFun s hs t) 1 = s * Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2) := rfl

lemma continuous_arcFun (s : ℝ) (hs : s ^ 2 = 1) :
    Continuous (arcFun s hs) := by
  apply Continuous.subtype_mk
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi ?_
  intro i
  fin_cases i
  · show Continuous fun t : unitInterval => (1 - 2 * (t : ℝ))
    fun_prop
  · show Continuous fun t : unitInterval =>
      s * Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2)
    fun_prop

/-- The semicircle arc as a continuous map. -/
noncomputable def arcMap (s : ℝ) (hs : s ^ 2 = 1) :
    C(unitInterval, ↥(Sph 1)) :=
  ⟨arcFun s hs, continuous_arcFun s hs⟩

lemma arcMap_injective (s : ℝ) (hs : s ^ 2 = 1) :
    Function.Injective (arcMap s hs) := by
  intro t t' h
  have h0 : amb (arcFun s hs t) 0 = amb (arcFun s hs t') 0 := by
    rw [show arcFun s hs t = arcFun s hs t' from h]
  rw [arcFun_coord0, arcFun_coord0] at h0
  exact Subtype.ext (by linarith)

lemma isEmbedding_arcMap (s : ℝ) (hs : s ^ 2 = 1) :
    Topology.IsEmbedding (arcMap s hs) := by
  haveI : T2Space ↥(Sph 1) :=
    inferInstanceAs (T2Space ↥(sphere (0 : Esp 1) 1))
  exact ((continuous_arcFun s hs).isClosedEmbedding
    (arcMap_injective s hs)).isEmbedding

/-- The upper semicircle arc. -/
noncomputable def arcPlus : C(unitInterval, ↥(Sph 1)) :=
  arcMap 1 (one_pow 2)

/-- The lower semicircle arc. -/
noncomputable def arcMinus : C(unitInterval, ↥(Sph 1)) :=
  arcMap (-1) (neg_one_sq)

lemma isEmbedding_arcPlus : Topology.IsEmbedding arcPlus :=
  isEmbedding_arcMap 1 (one_pow 2)

lemma isEmbedding_arcMinus : Topology.IsEmbedding arcMinus :=
  isEmbedding_arcMap (-1) (neg_one_sq)

/-- Preimage parameter for a point of the circle: `t = (1 - z₀)/2 ∈ [0,1]`. -/
noncomputable def arcParam (z : ↥(Sph 1)) : unitInterval :=
  ⟨(1 - amb z 0) / 2, by
    constructor
    · have h := sq_coord0_le_one z
      have : amb z 0 ≤ 1 := by nlinarith
      linarith
    · have h := sq_coord0_le_one z
      have : -1 ≤ amb z 0 := by nlinarith
      linarith⟩

lemma arcFun_arcParam (s : ℝ) (hs : s ^ 2 = 1) (z : ↥(Sph 1))
    (hz : s * amb z 1 = |amb z 1|) :
    arcFun s hs (arcParam z) = z := by
  apply amb_injective
  apply esp1_ext
  · rw [arcFun_coord0]
    show 1 - 2 * ((1 - amb z 0) / 2) = amb z 0
    ring
  · rw [arcFun_coord1]
    have hcoord : 1 - (1 - 2 * ((arcParam z : ℝ))) ^ 2 = amb z 1 ^ 2 := by
      show 1 - (1 - 2 * ((1 - amb z 0) / 2)) ^ 2 = amb z 1 ^ 2
      have := coord_sq_add_sq z
      nlinarith [coord_sq_add_sq z]
    rw [hcoord, Real.sqrt_sq_eq_abs, ← hz]
    have hs' : s * s = 1 := by nlinarith [hs]
    calc s * (s * amb z 1) = (s * s) * amb z 1 := by ring
      _ = amb z 1 := by rw [hs', one_mul]

/-- The upper semicircle is the range of `arcPlus`. -/
lemma range_arcPlus :
    Set.range arcPlus = {z : ↥(Sph 1) | 0 ≤ amb z 1} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    show (0 : ℝ) ≤ amb (arcFun 1 (one_pow 2) t) 1
    rw [arcFun_coord1, one_mul]
    exact Real.sqrt_nonneg _
  · intro hz
    exact ⟨arcParam z, arcFun_arcParam 1 (one_pow 2) z
      (by rw [one_mul, abs_of_nonneg hz])⟩

/-- The lower semicircle is the range of `arcMinus`. -/
lemma range_arcMinus :
    Set.range arcMinus = {z : ↥(Sph 1) | amb z 1 ≤ 0} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    show amb (arcFun (-1) neg_one_sq t) 1 ≤ 0
    rw [arcFun_coord1]
    have := Real.sqrt_nonneg (1 - (1 - 2 * (t : ℝ)) ^ 2)
    nlinarith
  · intro hz
    exact ⟨arcParam z, arcFun_arcParam (-1) neg_one_sq z
      (by rw [abs_of_nonpos hz]; ring)⟩

/-- The two semicircles cover the circle. -/
lemma range_arcPlus_union_arcMinus :
    Set.range arcPlus ∪ Set.range arcMinus = Set.univ := by
  rw [range_arcPlus, range_arcMinus]
  ext z
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact le_total 0 (amb z 1)

/-- The two semicircles meet exactly in the east and west points. -/
lemma range_arcPlus_inter_arcMinus :
    Set.range arcPlus ∩ Set.range arcMinus =
      {(eastP : ↥(Sph 1)), (westP : ↥(Sph 1))} := by
  rw [range_arcPlus, range_arcMinus]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hz1 : amb z 1 = 0 := le_antisymm h2 h1
    have hz0 : amb z 0 ^ 2 = 1 := by
      have := coord_sq_add_sq z
      nlinarith
    have habs : |amb z 0| = 1 := abs_eq_one_of_sq_eq_one hz0
    rcases (abs_eq zero_le_one).mp habs with h | h
    · left
      apply amb_injective
      apply esp1_ext
      · rw [h, amb_eastP_zero]
      · rw [hz1]
        show (0 : ℝ) = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1
        rw [EuclideanSpace.single_apply, if_neg (by decide)]
    · right
      apply amb_injective
      apply esp1_ext
      · rw [h, amb_westP_zero]
      · rw [hz1]
        have hc : amb (westP : ↥(Sph 1)) =
            -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := coe_neg_sphere eastP
        rw [hc, show (-(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) 1 =
          -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1) from rfl,
          EuclideanSpace.single_apply, if_neg (by decide), neg_zero]
  · rintro (rfl | rfl)
    · constructor
      · rw [show amb (eastP : ↥(Sph 1)) 1 =
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1 from rfl,
          EuclideanSpace.single_apply, if_neg (by decide)]
      · rw [show amb (eastP : ↥(Sph 1)) 1 =
          EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1 from rfl,
          EuclideanSpace.single_apply, if_neg (by decide)]
    · have hw : amb (westP : ↥(Sph 1)) 1 = 0 := by
        have hc : amb (westP : ↥(Sph 1)) =
            -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := coe_neg_sphere eastP
        rw [hc, show (-(EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) 1 =
          -(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) 1) from rfl,
          EuclideanSpace.single_apply, if_neg (by decide), neg_zero]
      exact ⟨le_of_eq hw.symm, le_of_eq hw⟩

lemma eastP_ne_westP : (eastP : ↥(Sph 1)) ≠ westP := by
  intro h
  have := congrArg (fun z : ↥(Sph 1) => amb z 0) h
  simp only [amb_eastP_zero, amb_westP_zero] at this
  norm_num at this

/-! ## The two-point complement: `Sⁿ \ {p, q} ≃ₕ Sⁿ⁻¹` for arbitrary points -/

/-- The orthogonal hyperplane at an arbitrary sphere point `p` is isometric
to the ambient space one dimension down (generalizing `hypIsometry`, which
is the `p = northP` case). -/
noncomputable def perpIsometry (n : ℕ) (p : ↥(Sph (n + 1))) :
    ((ℝ ∙ (amb p))ᗮ : Submodule ℝ (Esp (n + 1))) ≃ₗᵢ[ℝ] Esp n :=
  haveI : Fact (Module.finrank ℝ (Esp (n + 1)) = n + 1 + 1) :=
    fact_finrank_esp n
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
    (fun h => one_ne_zero (by rw [← norm_amb p, h, norm_zero]))).repr

/-- `p` as the base point of its own stereographic chart. -/
lemma stereographic_source_pt (n : ℕ) (p : ↥(Sph n)) (x : ↥(Sph n))
    (hx : x ≠ p) : x ∈ (stereographic (norm_amb p)).source := by
  rw [stereographic_source]
  intro hmem
  exact hx (hmem.trans (Subtype.ext rfl))

/-- Stereographic projection at `p` restricts to a homeomorphism from the
doubly punctured sphere `Sⁿ \ {p, q}` onto the hyperplane minus the image
of `q` (generalizing `interHomeoPunctured` to arbitrary points). -/
noncomputable def twoPunctHomeo (n : ℕ) (p q : ↥(Sph n)) (hqp : q ≠ p) :
    ↥(({p, q} : Set ↥(Sph n))ᶜ) ≃ₜ
      ↥(({stereographic (norm_amb p) q}ᶜ :
        Set ((ℝ ∙ (amb p))ᗮ : Submodule ℝ (Esp n)))) := by
  set φ := stereographic (norm_amb p) with hφ
  have hsrc : ∀ x : ↥(Sph n), x ≠ p → x ∈ φ.source :=
    fun x hx => stereographic_source_pt n p x hx
  have htgt : ∀ z : ((ℝ ∙ (amb p))ᗮ : Submodule ℝ (Esp n)), z ∈ φ.target :=
    fun z => by rw [hφ, stereographic_target]; exact Set.mem_univ z
  have hmem_compl : ∀ x : ↥(Sph n), x ∈ ({p, q} : Set ↥(Sph n))ᶜ ↔
      x ≠ p ∧ x ≠ q := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    push_neg
    exact Iff.rfl
  refine Homeomorph.mk (Equiv.mk ?_ ?_ ?_ ?_) ?_ ?_
  · -- forward map
    refine fun x => ⟨φ x.1, ?_⟩
    obtain ⟨hxp, hxq⟩ := (hmem_compl x.1).mp x.2
    intro h0
    exact hxq (φ.injOn (hsrc x.1 hxp) (hsrc q hqp) h0)
  · -- inverse map
    refine fun y => ⟨φ.symm y.1, ?_⟩
    have hmem : φ.symm y.1 ∈ φ.source := φ.map_target (htgt y.1)
    refine (hmem_compl _).mpr ⟨?_, ?_⟩
    · intro hp0
      have : φ.symm y.1 ∈ ({⟨amb p, by
          rw [mem_sphere_zero_iff_norm]; exact norm_amb p⟩}ᶜ :
            Set (sphere (0 : Esp n) 1)) := by
        rw [← stereographic_source (norm_amb p)]
        exact hmem
      exact this (by rw [hp0]; exact Set.mem_singleton_iff.mpr (Subtype.ext rfl))
    · intro hq0
      apply y.2
      have hri := φ.right_inv (x := y.1) (htgt y.1)
      rw [Set.mem_singleton_iff, ← hri, hq0]
  · -- left inverse
    intro x
    obtain ⟨hxp, _⟩ := (hmem_compl x.1).mp x.2
    exact Subtype.ext (φ.left_inv (hsrc x.1 hxp))
  · -- right inverse
    intro y
    exact Subtype.ext (φ.right_inv (x := y.1) (htgt y.1))
  · -- continuity, forward
    refine Continuous.subtype_mk ?_ _
    refine ContinuousOn.comp_continuous φ.continuousOn continuous_subtype_val ?_
    intro x
    exact hsrc x.1 ((hmem_compl x.1).mp x.2).1
  · -- continuity, inverse
    refine Continuous.subtype_mk ?_ _
    refine ContinuousOn.comp_continuous φ.continuousOn_symm
      continuous_subtype_val ?_
    intro y
    exact htgt y.1

/-- Translating a puncture to the origin: `F \ {y₀} ≃ₜ F \ {0}`. -/
noncomputable def punctTranslateHomeo {F : Type} [NormedAddCommGroup F]
    (y₀ : F) : ↥(({y₀}ᶜ : Set F)) ≃ₜ ↥(({0}ᶜ : Set F)) :=
  (Homeomorph.subRight y₀).subtype (fun x => by
    rw [Set.mem_compl_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_singleton_iff]
    exact (not_congr sub_eq_zero).symm.trans Iff.rfl)

/-- **The two-point complement is homotopy equivalent to the equator
sphere**: `Sⁿ⁺¹ \ {p, q} ≃ₕ Sⁿ` for any distinct `p, q` (stereographic
projection at `p`, translation of the image of `q` to the origin, polar
coordinates, and collapse of the ray factor). -/
noncomputable def twoPointComplHEquiv (n : ℕ) (p q : ↥(Sph (n + 1)))
    (hqp : q ≠ p) :
    ContinuousMap.HomotopyEquiv
      ↥(({p, q} : Set ↥(Sph (n + 1)))ᶜ) ↥(Sph n) :=
  (((twoPunctHomeo (n + 1) p q hqp).trans
    ((punctTranslateHomeo (stereographic (norm_amb p) q)).trans
      ((homeomorphUnitSphereProd _).trans
        ((sphereHomeoOfLinearIsometryEquiv (perpIsometry n p)).prodCongr
          (Homeomorph.refl ↥(Ioi (0 : ℝ))))))).toHomotopyEquiv).trans
    (hequivProdContractible ↥(sphere (0 : Esp n) 1) ↥(Ioi (0 : ℝ)))

/-- `H₂(Sⁿ \ {p, q}) = 0` for `n ≥ 1`, `n ≠ 3`, and any distinct points. -/
theorem isZero_h2_twoPointCompl {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≠ 3)
    (p q : ↥(Sph n)) (hqp : q ≠ p) :
    IsZero (Hgrp (TopCat.of ↥(({p, q} : Set ↥(Sph n))ᶜ)) 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact (sphere_homology_vanish m 2 one_le_two (by omega)).of_iso
    (hgrpIso (twoPointComplHEquiv m p q hqp) 2)

/-! ## The Mayer-Vietoris step -/

/-- **MV middle vanishing**: open cover `U ∪ V = X` with `H₂(X) = 0` and
`H₁(U) = H₁(V) = 0` forces `H₁(U ∩ V) = 0` (exactness of the banked
Mayer-Vietoris sequence at `H₁(U ∩ V)`). -/
theorem isZero_h1_inter {X : TopCat.{0}} {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (hX2 : IsZero (Hgrp X 2))
    (hU1 : IsZero (Hgrp (TopCat.of U) 1))
    (hV1 : IsZero (Hgrp (TopCat.of V) 1)) :
    IsZero (Hgrp (TopCat.of (U ∩ V : Set X)) 1) :=
  (mv_exact₁ hU hV hUV 1).isZero_X₂
    (hX2.eq_of_src _ _)
    (((biprod_isZero_iff _ _).mpr ⟨hU1, hV1⟩).eq_of_tgt _ _)

/-! ## Subtype flattening -/

/-- Inside `W \ E`, the locus avoiding `K ⊇ E` is homeomorphic to the locus
of `W` avoiding `K` (flattening a subtype of a subtype). -/
noncomputable def flattenComplHomeo {W : TopCat.{0}} (E K : Set ↥W)
    (hEK : E ⊆ K) :
    ↥({x : ↥(TopCat.of (Eᶜ : Set ↥W)) | x.1 ∉ K}) ≃ₜ
      {y : ↥W // y ∉ K} where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, fun hE => y.2 (hEK hE)⟩, y.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-! ## The reduction: circle complements from arc complements -/

/-- **Abstract two-arc Mayer-Vietoris**: two closed sets `KP, KM` in a space
`W`, with `H₂(W \ (KP ∩ KM)) = 0` and `H₁`-acyclic complements, have
`H₁`-acyclic union complement. -/
theorem isZero_h1_unionCompl {W : TopCat.{0}} (KP KM : Set ↥W)
    (hKPc : IsClosed KP) (hKMc : IsClosed KM)
    (hX2 : IsZero (Hgrp (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) 2))
    (hP1 : IsZero (Hgrp (TopCat.of {y : ↥W // y ∉ KP}) 1))
    (hM1 : IsZero (Hgrp (TopCat.of {y : ↥W // y ∉ KM}) 1)) :
    IsZero (Hgrp (TopCat.of {y : ↥W // y ∉ KP ∪ KM}) 1) := by
  -- the MV cover of `W \ (KP ∩ KM)` by the complements of the two arcs
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
  -- H₁ of the pieces, flattened to the arc complements
  have hU1 : IsZero (Hgrp (TopCat.of
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)))) 1) :=
    hP1.of_iso (hgrpIso
      (flattenComplHomeo (KP ∩ KM) KP Set.inter_subset_left).toHomotopyEquiv 1)
  have hV1 : IsZero (Hgrp (TopCat.of
      ({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)))) 1) :=
    hM1.of_iso (hgrpIso
      (flattenComplHomeo (KP ∩ KM) KM Set.inter_subset_right).toHomotopyEquiv 1)
  -- MV middle vanishing, then flatten the intersection
  have hmid := isZero_h1_inter hUopen hVopen hUVcover hX2 hU1 hV1
  have hUVeq :
      (({x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP} :
        Set (TopCat.of ((KP ∩ KM)ᶜ : Set ↥W))) ∩
      {x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KM}) =
      {x : ↥(TopCat.of ((KP ∩ KM)ᶜ : Set ↥W)) | x.1 ∉ KP ∪ KM} := by
    ext x
    rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_setOf_eq,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ (h | h)
      · exact h1 h
      · exact h2 h
    · intro h
      exact ⟨fun hP => h (Set.mem_union_left _ hP),
        fun hM => h (Set.mem_union_right _ hM)⟩
  rw [hUVeq] at hmid
  exact hmid.of_iso (hgrpIso
    (flattenComplHomeo (KP ∩ KM) (KP ∪ KM)
      (Set.inter_subset_left.trans
        Set.subset_union_left)).symm.toHomotopyEquiv 1)

/-- **The circle-complement reduction** (Hatcher 2B.1, circle case): if arc
complements in `S^D` are `H₁`-acyclic, then for `D ≥ 1`, `D ≠ 3`, every
embedded circle in `S^D` has `H₁`-acyclic complement.  Mayer-Vietoris over
the complements of the two semicircle images inside the complement of the
two endpoint images. -/
theorem isZero_h1_complement_of_embedding (D : ℕ) (hD : 1 ≤ D) (hD3 : D ≠ 3)
    (harc : ArcComplementsAcyclic D)
    (g : C(↥(Sph 1), ↥(Sph D))) (hg : Topology.IsEmbedding g) :
    IsZero (Hgrp (TopCat.of {y : ↥(Sph D) // y ∉ Set.range g}) 1) := by
  haveI : T2Space ↥(Sph D) :=
    inferInstanceAs (T2Space ↥(sphere (0 : Esp D) 1))
  -- the two semicircle images
  have hgP : Topology.IsEmbedding (g.comp arcPlus) := by
    rw [ContinuousMap.coe_comp]
    exact hg.comp isEmbedding_arcPlus
  have hgM : Topology.IsEmbedding (g.comp arcMinus) := by
    rw [ContinuousMap.coe_comp]
    exact hg.comp isEmbedding_arcMinus
  have hKPg : Set.range (g.comp arcPlus) = ⇑g '' Set.range arcPlus := by
    rw [ContinuousMap.coe_comp, Set.range_comp]
  have hKMg : Set.range (g.comp arcMinus) = ⇑g '' Set.range arcMinus := by
    rw [ContinuousMap.coe_comp, Set.range_comp]
  -- the two endpoint images
  have hinter : Set.range (g.comp arcPlus) ∩ Set.range (g.comp arcMinus) =
      ({g eastP, g westP} : Set ↥(Sph D)) := by
    rw [hKPg, hKMg, ← Set.image_inter hg.injective,
      range_arcPlus_inter_arcMinus, Set.image_pair]
  have hcover : Set.range (g.comp arcPlus) ∪ Set.range (g.comp arcMinus) =
      Set.range g := by
    rw [hKPg, hKMg, ← Set.image_union, range_arcPlus_union_arcMinus,
      Set.image_univ]
  -- H₂ of the two-point complement vanishes
  have hgqp : g westP ≠ g eastP := fun h =>
    eastP_ne_westP (hg.injective h).symm
  have hX2 : IsZero (Hgrp (TopCat.of
      ((Set.range (g.comp arcPlus) ∩ Set.range (g.comp arcMinus))ᶜ :
        Set ↥(Sph D))) 2) := by
    rw [hinter]
    exact isZero_h2_twoPointCompl hD hD3 (g eastP) (g westP) hgqp
  -- assemble
  have hbig := isZero_h1_unionCompl
    (Set.range (g.comp arcPlus)) (Set.range (g.comp arcMinus))
    (isCompact_range (g.comp arcPlus).continuous).isClosed
    (isCompact_range (g.comp arcMinus).continuous).isClosed
    hX2 (harc _ hgP) (harc _ hgM)
  rw [hcover] at hbig
  exact hbig

/-! ## Transport to the `TopCat.sphere` model of the binder -/

/-- The `Sph`-model map underlying a circle map in the `TopCat.sphere`
(`ULift`) model. -/
noncomputable def toSphMap (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)) :
    C(↥(Sph 1), ↥(Sph D)) :=
  ⟨fun x =>
      (show ULift.{0} ↥(sphere (0 : Esp D) 1) from
        f (show ↥(TopCat.sphere.{0} 1) from ULift.up x)).down,
    continuous_uliftDown.comp (f.continuous.comp continuous_uliftUp)⟩

lemma isEmbedding_toSphMap (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D))
    (hf : Topology.IsEmbedding f) :
    Topology.IsEmbedding (toSphMap D f) :=
  (Homeomorph.ulift.isEmbedding.comp hf).comp
    Homeomorph.ulift.symm.isEmbedding

/-- The complement of an embedded circle in the `TopCat.sphere` model is
homeomorphic to its complement in the `Sph` model. -/
noncomputable def complDownHomeo (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)) :
    {x : ↥(TopCat.sphere.{0} D) // x ∉ Set.range f} ≃ₜ
      {y : ↥(Sph D) // y ∉ Set.range (toSphMap D f)} where
  toFun x := ⟨(show ULift.{0} ↥(sphere (0 : Esp D) 1) from x.1).down,
    fun ⟨z, hz⟩ => x.2 ⟨show ↥(TopCat.sphere.{0} 1) from ULift.up z,
      congrArg ULift.up hz⟩⟩
  invFun y := ⟨show ↥(TopCat.sphere.{0} D) from ULift.up y.1,
    fun ⟨w, hw⟩ => y.2
      ⟨(show ULift.{0} ↥(sphere (0 : Esp 1) 1) from w).down,
        congrArg ULift.down hw⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_uliftDown.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (continuous_uliftUp.comp continuous_subtype_val) _

/-- **The high-dimensional (and `D = 2`) vanishing, conditional on the arc
frontier**: granting `ArcComplementsAcyclic D`, no embedded circle in `S^D`
(`D ≥ 1`, `D ≠ 3`) has homologically nontrivial complement. -/
theorem not_detects_of_arcAcyclic (D : ℕ) (hD : 1 ≤ D) (hD3 : D ≠ 3)
    (harc : ArcComplementsAcyclic D) : ¬ DetectsNontrivialLinking D := by
  rintro ⟨f, hemb, hH⟩
  apply hH
  have hz := isZero_h1_complement_of_embedding D hD hD3 harc
    (toSphMap D f) (isEmbedding_toSphMap D f hemb)
  exact hz.of_iso (hgrpIso (complDownHomeo D f).toHomotopyEquiv 1)

/-- **The bridge's uniqueness half, conditional on the arc frontier**:
granting arc-complement acyclicity in every dimension `D ≥ 2`, `D ≠ 3`,
nontrivial linking forces `D = 3`.  Dimensions `0` and `1` are the banked
unconditional results (`LinkingVanishingLowDim`). -/
theorem forces_D3_of_arcAcyclic
    (harc : ∀ D, 2 ≤ D → D ≠ 3 → ArcComplementsAcyclic D) :
    ∀ D, DetectsNontrivialLinking D → D = 3 := by
  intro D hdet
  by_contra hne
  match D, hne with
  | 0, _ => exact LinkingVanishingLowDim.not_detects_zero hdet
  | 1, _ => exact LinkingVanishingLowDim.not_detects_one hdet
  | (n + 2), hne =>
      exact not_detects_of_arcAcyclic (n + 2) (by omega) hne
        (harc (n + 2) (by omega) hne) hdet

end LinkingVanishingHighDim
end Foundation
end IndisputableMonolith
