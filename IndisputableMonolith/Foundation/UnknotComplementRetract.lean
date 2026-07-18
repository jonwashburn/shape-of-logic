import Mathlib

/-!
# Unknot complement retract: geometric core of `DetectsNontrivialLinking 3`

Standalone module (imports only Mathlib) proving:

1. `unknot : C(𝕊 1, 𝕊 3)` — the flat unknot `(x₀,x₁) ↦ (x₀,x₁,0,0)`.
2. `unknot_isEmbedding` — it is a topological embedding.
3. `core` — the "dual" circle `z ↦ (0,0,z₀,z₁)` valued in the complement of
   the unknot.
4. `retractToCore` — the retraction of the complement onto that circle,
   `y ↦ (y₂,y₃)/‖(y₂,y₃)‖`.
5. `retract_core` — the retraction restricted along `core` is the identity.
6. `unknotComplementH1_ne_zero` — given `H₁(S¹;ℤ) ≅ ℤ` (singular homology,
   Mathlib's `singularHomologyFunctor`), the first singular homology of the
   unknot complement in S³ is not the zero object.

Everything is at universe 0 and matches the shapes used by
`IndisputableMonolith.Foundation.PublicSpine.linkingComplementH1` (not
imported here; the gluing happens elsewhere).
-/

noncomputable section

namespace IndisputableMonolith
namespace Foundation
namespace UnknotComplementRetract

open scoped RealInnerProductSpace
open CategoryTheory CategoryTheory.Limits

/-! ## Linear algebra: coordinate inclusions and projection -/

/-- Inclusion `(x₀,x₁) ↦ (x₀,x₁,0,0)` as a linear isometry. -/
def incl01 : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 ![x 0, x 1, 0, 0]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;>
          simp [PiLp.add_apply]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;>
          simp [PiLp.smul_apply] }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_four, Fin.sum_univ_two]
    simp [PiLp.toLp_apply]

/-- Inclusion `(x₀,x₁) ↦ (0,0,x₀,x₁)` as a linear isometry. -/
def incl23 : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 ![0, 0, x 0, x 1]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;>
          simp [PiLp.add_apply]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;>
          simp [PiLp.smul_apply] }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_four, Fin.sum_univ_two]
    simp [PiLp.toLp_apply]

/-- Projection `y ↦ (y₂,y₃)` as a linear map (continuous by finite dimension). -/
def proj23 : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := fun y => WithLp.toLp 2 ![y 2, y 3]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;>
      simp [PiLp.add_apply]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;>
      simp [PiLp.smul_apply]

lemma proj23_continuous : Continuous proj23 :=
  proj23.continuous_of_finiteDimensional

@[simp] lemma incl01_apply_coord (x : EuclideanSpace ℝ (Fin 2)) :
    (incl01 x : Fin 4 → ℝ) = ![x 0, x 1, 0, 0] := rfl

@[simp] lemma incl23_apply_coord (x : EuclideanSpace ℝ (Fin 2)) :
    (incl23 x : Fin 4 → ℝ) = ![0, 0, x 0, x 1] := rfl

@[simp] lemma proj23_apply_coord (y : EuclideanSpace ℝ (Fin 4)) :
    (proj23 y : Fin 2 → ℝ) = ![y 2, y 3] := rfl

/-! ## The unknot -/

/-- Underlying point-level unknot: `S¹ → S³`, `(x₀,x₁) ↦ (x₀,x₁,0,0)`. -/
def unknotFun (z : ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :
    ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  ULift.up ⟨incl01 z.down.1, by
    rw [mem_sphere_zero_iff_norm, incl01.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.down.2⟩

/-- The standard flat unknot `S¹ ↪ S³` as a continuous map between the
`TopCat` spheres. -/
def unknot : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 3) where
  toFun := unknotFun
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact incl01.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)

lemma unknot_injective : Function.Injective unknot := by
  intro a b hab
  have h4 : incl01 a.down.1 = incl01 b.down.1 :=
    congrArg (fun w => (ULift.down w).1) hab
  have h2 : a.down.1 = b.down.1 := incl01.injective h4
  exact ULift.ext a b (Subtype.ext h2)

instance : CompactSpace (TopCat.sphere.{0} 1) := by
  show CompactSpace (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  infer_instance

instance : T2Space (TopCat.sphere.{0} 3) := by
  show T2Space (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
  infer_instance

/-- The unknot is a topological embedding (continuous injective map from a
compact space to a Hausdorff space). -/
theorem unknot_isEmbedding : Topology.IsEmbedding unknot :=
  (unknot.continuous.isClosedEmbedding unknot_injective).isEmbedding

/-! ## The complement and the core circle -/

/-- The complement of the unknot in S³, as a `TopCat` object (exact shape of
`linkingComplementH1`'s argument). -/
def Cpl : TopCat.{0} :=
  TopCat.of {x : TopCat.sphere.{0} 3 // x ∉ Set.range unknot}

/-- Coordinate extraction: a point in the range of the unknot has vanishing
coordinates 2 and 3. -/
lemma coord23_eq_zero_of_mem_range {y : TopCat.sphere.{0} 3}
    (hy : y ∈ Set.range unknot) :
    (ULift.down y).1 2 = 0 ∧ (ULift.down y).1 3 = 0 := by
  obtain ⟨w, hw⟩ := hy
  have h4 : incl01 w.down.1 = (ULift.down y).1 :=
    congrArg (fun v => (ULift.down v).1) hw
  constructor
  · have := congrFun (congrArg WithLp.ofLp h4) 2
    simpa using this.symm
  · have := congrFun (congrArg WithLp.ofLp h4) 3
    simpa using this.symm

/-- Point-level core circle `z ↦ (0,0,z₀,z₁)`, landing in the complement. -/
def coreFun (z : TopCat.sphere.{0} 1) : Cpl := by
  refine ⟨ULift.up ⟨incl23 (ULift.down (α := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) z).1, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, incl23.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.down.2
  · intro hmem
    obtain ⟨h2, h3⟩ := coord23_eq_zero_of_mem_range hmem
    have hz0 : z.down.1 0 = 0 := by simpa using h2
    have hz1 : z.down.1 1 = 0 := by simpa using h3
    have hz : z.down.1 = 0 := by
      ext i
      fin_cases i
      · simpa using hz0
      · simpa using hz1
    have hnorm : ‖z.down.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.down.2
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm

/-- The core circle as a continuous map into the complement. -/
def core : C(TopCat.sphere.{0} 1, Cpl) where
  toFun := coreFun
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact incl23.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)

/-! ## The retraction -/

/-- The `(y₂,y₃)`-part of a point of the complement. -/
def part23 (y : Cpl) : EuclideanSpace ℝ (Fin 2) :=
  proj23 (ULift.down y.1).1

lemma part23_continuous : Continuous part23 :=
  proj23_continuous.comp
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val))

/-- Well-definedness: on the complement of the unknot, `(y₂,y₃) ≠ 0`. -/
lemma part23_ne_zero (y : Cpl) : part23 y ≠ 0 := by
  intro h0
  set x : EuclideanSpace ℝ (Fin 4) := (ULift.down y.1).1 with hx
  have h2 : x 2 = 0 := by
    have := congrFun (congrArg WithLp.ofLp h0) 0
    simpa [part23, hx] using this
  have h3 : x 3 = 0 := by
    have := congrFun (congrArg WithLp.ofLp h0) 1
    simpa [part23, hx] using this
  -- the head part (x₀,x₁) then has norm 1
  set z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x 0, x 1] with hzdef
  have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 (ULift.down y.1).2
  have hznorm : ‖z‖ = 1 := by
    rw [EuclideanSpace.norm_eq] at hxnorm ⊢
    rw [Fin.sum_univ_four] at hxnorm
    rw [Fin.sum_univ_two]
    rw [h2, h3] at hxnorm
    simpa [hzdef, PiLp.toLp_apply] using hxnorm
  -- hence y is in the range of the unknot: contradiction
  apply y.2
  refine ⟨ULift.up ⟨z, mem_sphere_zero_iff_norm.2 hznorm⟩, ?_⟩
  apply ULift.ext
  apply Subtype.ext
  show incl01 z = x
  ext i
  fin_cases i
  · simp [hzdef]
  · simp [hzdef]
  · simpa using h2.symm
  · simpa using h3.symm

/-- Point-level retraction `y ↦ (y₂,y₃)/‖(y₂,y₃)‖`. -/
def retractFun (y : Cpl) : TopCat.sphere.{0} 1 :=
  ULift.up ⟨‖part23 y‖⁻¹ • part23 y, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (part23_ne_zero y))]⟩

/-- The retraction of the unknot complement onto the core circle. -/
def retractToCore : C(Cpl, TopCat.sphere.{0} 1) where
  toFun := retractFun
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact ((part23_continuous.norm.inv₀
      fun y => norm_ne_zero_iff.2 (part23_ne_zero y)).smul part23_continuous)

/-! ## Retraction identity on the core -/

/-- Composite identity: the retraction restricted along the core circle is the
identity of S¹. -/
theorem retract_core (z : TopCat.sphere.{0} 1) : retractToCore (core z) = z := by
  have hpart : part23 (core z) = z.down.1 := by
    ext i
    fin_cases i <;>
      simp [part23, core, coreFun]
  have hnorm : ‖z.down.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.down.2
  apply ULift.ext
  apply Subtype.ext
  show ‖part23 (core z)‖⁻¹ • part23 (core z) = z.down.1
  rw [hpart, hnorm, inv_one, one_smul]

theorem retract_comp_core :
    (retractToCore.comp core) = ContinuousMap.id (TopCat.sphere.{0} 1) := by
  ext z
  exact retract_core z

/-! ## Capstone: nontrivial H₁ of the complement -/

/-- **Capstone.** Given that first singular homology of S¹ with ℤ coefficients
is ℤ (as an iso in `ModuleCat ℤ`), the first singular homology of the unknot
complement in S³ is not the zero object. Pure retraction argument: `core` and
`retractToCore` exhibit H₁(S¹) as a retract of H₁(complement). -/
theorem unknotComplementH1_ne_zero
    (h1 : Nonempty ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere.{0} 1)) ≅ ModuleCat.of ℤ ℤ)) :
    ¬ CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of {x : TopCat.sphere.{0} 3 // x ∉ Set.range unknot})) := by
  intro hz
  obtain ⟨e⟩ := h1
  set H : TopCat.{0} ⥤ ModuleCat ℤ :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ ℤ) with hH
  let g : TopCat.sphere.{0} 1 ⟶ Cpl := TopCat.ofHom core
  let r : Cpl ⟶ TopCat.sphere.{0} 1 := TopCat.ofHom retractToCore
  have hgr : g ≫ r = 𝟙 (TopCat.sphere.{0} 1) := by
    ext z
    exact retract_core z
  have hmap : H.map g ≫ H.map r = 𝟙 (H.obj (TopCat.sphere.{0} 1)) := by
    rw [← H.map_comp, hgr, H.map_id]
  have hzC : IsZero (H.obj Cpl) := hz
  have hg0 : H.map g = 0 := hzC.eq_zero_of_tgt _
  have hid0 : 𝟙 (H.obj (TopCat.sphere.{0} 1)) = 0 := by
    rw [← hmap, hg0, zero_comp]
  have hzS1 : IsZero (H.obj (TopCat.sphere.{0} 1)) :=
    (IsZero.iff_id_eq_zero _).mpr hid0
  have hzZ : IsZero (ModuleCat.of ℤ ℤ) := hzS1.of_iso e.symm
  have hsub : Subsingleton ℤ := ModuleCat.isZero_of_iff_subsingleton.mp hzZ
  exact one_ne_zero (hsub.elim (1 : ℤ) 0)

/- Axioms audit (2026-07-17, `#print axioms` on the built module):
`unknotComplementH1_ne_zero`, `unknot_isEmbedding`, `retract_comp_core` each
depend only on `[propext, Classical.choice, Quot.sound]`. No `sorry`, no new
axioms, no `native_decide`. -/

end UnknotComplementRetract
end Foundation
end IndisputableMonolith
