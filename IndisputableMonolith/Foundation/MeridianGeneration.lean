import IndisputableMonolith.Foundation.UnknotComplementRetract
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.SingularPrism

/-!
# The meridian generates the first homology of the unknot complement

The standard unknot complement deformation retracts onto its core circle.
Consequently its first singular homology with integer coefficients is
isomorphic to `ℤ`.  The meridian class is the image under the core inclusion
of a generator of the circle's first homology.

Status: 0 sorry, 0 new axiom.
-/

noncomputable section

namespace IndisputableMonolith
namespace Foundation
namespace MeridianGeneration

open scoped RealInnerProductSpace
open CategoryTheory
open UnknotComplementRetract

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev S1 := TopCat.sphere.{0} 1
abbrev H1 (X : TopCat.{0}) : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj X

/-! ## The geometric deformation retract -/

/-- Projection onto the first two ambient coordinates. -/
def proj01 : E4 →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := fun y => WithLp.toLp 2 ![y 0, y 1]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [PiLp.add_apply]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [PiLp.smul_apply]

lemma proj01_continuous : Continuous proj01 :=
  proj01.continuous_of_finiteDimensional

/-- The first two coordinates of a complement point. -/
def part01 (y : Cpl) : EuclideanSpace ℝ (Fin 2) :=
  proj01 (ULift.down y.1).1

lemma part01_continuous : Continuous part01 :=
  proj01_continuous.comp
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val))

/-- Scale the first two coordinates of a complement point by `1 - t`, leaving
the last two coordinates fixed. -/
def rawDeformation (p : Set.Icc (0 : ℝ) 1 × Cpl) : E4 :=
  (1 - (p.1 : ℝ)) • incl01 (part01 p.2) + incl23 (part23 p.2)

lemma rawDeformation_continuous : Continuous rawDeformation := by
  unfold rawDeformation
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (incl01.continuous.comp (part01_continuous.comp continuous_snd))).add
      (incl23.continuous.comp (part23_continuous.comp continuous_snd))

/-- The unnormalized deformation vector never vanishes because its last two
coordinates are the nonzero `part23` of the complement point. -/
lemma rawDeformation_ne_zero (p : Set.Icc (0 : ℝ) 1 × Cpl) :
    rawDeformation p ≠ 0 := by
  intro hzero
  apply part23_ne_zero p.2
  ext i
  fin_cases i
  · have h := congrFun (congrArg WithLp.ofLp hzero) 2
    simpa [rawDeformation, part23] using h
  · have h := congrFun (congrArg WithLp.ofLp hzero) 3
    simpa [rawDeformation, part23] using h

/-- Normalize the scaled vector back to the unit sphere. -/
def normalizedDeformationSphere (p : Set.Icc (0 : ℝ) 1 × Cpl) :
    TopCat.sphere.{0} 3 :=
  ULift.up ⟨‖rawDeformation p‖⁻¹ • rawDeformation p, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (rawDeformation_ne_zero p))]⟩

/-- Normalization does not enter the unknot: the last two coordinates remain
a common nonzero scalar multiple of `part23`. -/
lemma normalizedDeformationSphere_not_mem_unknot
    (p : Set.Icc (0 : ℝ) 1 × Cpl) :
    normalizedDeformationSphere p ∉ Set.range unknot := by
  intro hmem
  obtain ⟨h2, h3⟩ := coord23_eq_zero_of_mem_range hmem
  have hn : ‖rawDeformation p‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.2 (rawDeformation_ne_zero p))
  have hx2 : (ULift.down p.2.1).1 2 = 0 := by
    have hs :
        ‖rawDeformation p‖⁻¹ * (ULift.down p.2.1).1 2 = 0 := by
      simpa [normalizedDeformationSphere, rawDeformation, PiLp.smul_apply] using h2
    exact (mul_eq_zero.mp hs).resolve_left hn
  have hx3 : (ULift.down p.2.1).1 3 = 0 := by
    have hs :
        ‖rawDeformation p‖⁻¹ * (ULift.down p.2.1).1 3 = 0 := by
      simpa [normalizedDeformationSphere, rawDeformation, PiLp.smul_apply] using h3
    exact (mul_eq_zero.mp hs).resolve_left hn
  apply part23_ne_zero p.2
  ext i
  fin_cases i
  · simpa [part23] using hx2
  · simpa [part23] using hx3

/-- The normalized straight-line deformation, valued in the unknot
complement. -/
def deformationMap : C(Set.Icc (0 : ℝ) 1 × Cpl, Cpl) where
  toFun := fun p =>
    ⟨normalizedDeformationSphere p, normalizedDeformationSphere_not_mem_unknot p⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact ((rawDeformation_continuous.norm.inv₀
      fun p => norm_ne_zero_iff.2 (rawDeformation_ne_zero p)).smul
        rawDeformation_continuous)

lemma deformation_zero (y : Cpl) : deformationMap ⟨0, y⟩ = y := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  have hyNorm : ‖(ULift.down y.1).1‖ = 1 :=
    mem_sphere_zero_iff_norm.1 (ULift.down y.1).2
  show ‖rawDeformation (0, y)‖⁻¹ • rawDeformation (0, y) =
    (ULift.down y.1).1
  have hraw : rawDeformation (0, y) = (ULift.down y.1).1 := by
    ext i
    fin_cases i <;>
      simp [rawDeformation, part01, proj01, part23, proj23]
  rw [hraw, hyNorm, inv_one, one_smul]

lemma rawDeformation_one (y : Cpl) :
    rawDeformation (1, y) = incl23 (part23 y) := by
  ext i
  fin_cases i <;>
    simp [rawDeformation, incl23, part01, proj01, part23, proj23]

lemma deformation_one (y : Cpl) :
    deformationMap ⟨1, y⟩ = core (retractToCore y) := by
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  show ‖rawDeformation (1, y)‖⁻¹ • rawDeformation (1, y) =
    incl23 (‖part23 y‖⁻¹ • part23 y)
  rw [rawDeformation_one, incl23.norm_map]
  exact (incl23.map_smulₛₗ _ _).symm

/-- The identity of the unknot complement is homotopic to projection onto the
core circle. -/
def deformationHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id Cpl)
      (core.comp retractToCore) :=
  ContinuousMap.Homotopy.mk deformationMap deformation_zero deformation_one

/-- The exact retraction identity on the core, packaged as a constant
homotopy. -/
def coreRetractionHomotopy :
    ContinuousMap.Homotopy (retractToCore.comp core) (ContinuousMap.id S1) := by
  let K : C(Set.Icc (0 : ℝ) 1 × S1, S1) :=
    ⟨fun p => p.2, continuous_snd⟩
  exact ContinuousMap.Homotopy.mk K
    (fun z => (retract_core z).symm) (fun _ => rfl)

/-- The unknot complement and its core circle are homotopy equivalent. -/
def complementHomotopyEquiv : ContinuousMap.HomotopyEquiv Cpl S1 where
  toFun := retractToCore
  invFun := core
  left_inv := ⟨deformationHomotopy.symm⟩
  right_inv := ⟨coreRetractionHomotopy⟩

/-! ## First homology and the meridian -/

/-- The deformation retract induces an isomorphism from the first homology of
the unknot complement to the first homology of the circle. -/
noncomputable def unknotComplementH1IsoCircle : H1 Cpl ≅ H1 S1 :=
  SingularPrism.homotopyEquiv_homology_iso complementHomotopyEquiv 1

/-- The first singular homology of the standard unknot complement is `ℤ`. -/
noncomputable def unknotComplementH1IsoInt :
    H1 Cpl ≅ ModuleCat.of ℤ ℤ :=
  unknotComplementH1IsoCircle ≪≫
    Classical.choice CircleWindingChain.circleH1ZIsoInt_holds

/-- A distinguished generator of the circle's first homology, chosen by the
proved isomorphism `H₁(S¹;ℤ) ≅ ℤ`. -/
noncomputable def circleH1Generator : H1 S1 :=
  (Classical.choice CircleWindingChain.circleH1ZIsoInt_holds).inv (1 : ℤ)

/-- The meridian class: the image of the circle generator under the core
inclusion. -/
noncomputable def meridianClass : H1 Cpl :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom core) circleH1Generator

/-- The chosen circle generator maps to `1` under the circle homology
isomorphism. -/
theorem circleH1Generator_maps_to_one :
    (Classical.choice CircleWindingChain.circleH1ZIsoInt_holds).hom
      circleH1Generator = (1 : ℤ) := by
  simp [circleH1Generator]

/-- The circle homology generator is nonzero. -/
theorem circleH1Generator_ne_zero : circleH1Generator ≠ 0 := by
  intro hzero
  have := circleH1Generator_maps_to_one
  rw [hzero, map_zero] at this
  exact one_ne_zero this.symm

/-- The meridian is literally the core-induced image of a generator. -/
theorem meridianClass_eq_core_map_generator :
    meridianClass =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom core) circleH1Generator :=
  rfl

/-- The core meridian class is nonzero in the complement's first homology. -/
theorem meridianClass_ne_zero : meridianClass ≠ 0 := by
  intro hzero
  let H : TopCat.{0} ⥤ ModuleCat ℤ :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
  have hcomp :
      H.map (TopCat.ofHom core) ≫ H.map (TopCat.ofHom retractToCore) =
        𝟙 (H.obj S1) := by
    rw [← H.map_comp]
    have hcr :
        TopCat.ofHom core ≫ TopCat.ofHom retractToCore = 𝟙 S1 := by
      ext z
      exact retract_core z
    rw [hcr, H.map_id]
  have happ := congrArg
    (fun f : H.obj S1 ⟶ H.obj S1 => f circleH1Generator) hcomp
  change H.map (TopCat.ofHom retractToCore)
      (H.map (TopCat.ofHom core) circleH1Generator) = circleH1Generator at happ
  rw [← meridianClass_eq_core_map_generator, hzero, map_zero] at happ
  exact circleH1Generator_ne_zero happ.symm

/-- Under the proved isomorphism `H₁(S³ \ unknot;ℤ) ≅ ℤ`, the core meridian
maps to `1`; in particular it is a generator. -/
theorem unknotComplementH1IsoInt_maps_meridian_to_one :
    unknotComplementH1IsoInt.hom meridianClass = (1 : ℤ) := by
  let H : TopCat.{0} ⥤ ModuleCat ℤ :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
  change (Classical.choice CircleWindingChain.circleH1ZIsoInt_holds).hom
    (H.map (TopCat.ofHom retractToCore)
      (H.map (TopCat.ofHom core) circleH1Generator)) = (1 : ℤ)
  have hcr :
      TopCat.ofHom core ≫ TopCat.ofHom retractToCore = 𝟙 S1 := by
    ext z
    exact retract_core z
  have hmap :
      H.map (TopCat.ofHom core) ≫ H.map (TopCat.ofHom retractToCore) =
        𝟙 (H.obj S1) := by
    rw [← H.map_comp, hcr, H.map_id]
  have happ := congrArg
    (fun f : H.obj S1 ⟶ H.obj S1 => f circleH1Generator) hmap
  change H.map (TopCat.ofHom retractToCore)
      (H.map (TopCat.ofHom core) circleH1Generator) = circleH1Generator at happ
  rw [happ]
  exact circleH1Generator_maps_to_one

end MeridianGeneration
end Foundation
end IndisputableMonolith
