import Mathlib
import IndisputableMonolith.Foundation.UnknotComplementRetract

/-!
# Sharpness of compactness and of 1-acyclicity

Without compactness the recognition requirement holds at `D = 2`:
the plane is 1-acyclic and the unit circle's exterior retracts onto a
circle of radius 2, so complement first homology is nontrivial.

Without 1-acyclicity it holds at `D = 4`: `S¹ × S³` retracts onto `S¹`,
so its own first homology is already nontrivial.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SharpnessCountermodels

noncomputable section

open scoped RealInnerProductSpace
open CategoryTheory CategoryTheory.Limits
open UnknotComplementRetract

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev S1 := TopCat.sphere.{0} 1
abbrev S3 := TopCat.sphere.{0} 3

/-- The open exterior of the unit circle in the plane. -/
abbrev Exterior : Type := {x : E2 // 1 < ‖x‖}

instance : TopologicalSpace Exterior := inferInstance

/-- Radius-2 circle, as a metric sphere. -/
abbrev RadiusTwo : Type := Metric.sphere (0 : E2) 2

/-- A point of norm 2 lies in the exterior. -/
theorem radiusTwo_mem_exterior (z : RadiusTwo) : 1 < ‖(z : E2)‖ := by
  have hz : ‖(z : E2)‖ = 2 := mem_sphere_zero_iff_norm.1 z.property
  have : (1 : ℝ) < 2 := by norm_num
  simpa [hz] using this

/-- Inclusion of the radius-2 circle into the exterior. -/
def includeRadiusTwo : C(RadiusTwo, Exterior) where
  toFun := fun z => ⟨z, radiusTwo_mem_exterior z⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

/-- Radial retraction of the exterior onto the radius-2 circle. -/
noncomputable def retractExterior : C(Exterior, RadiusTwo) where
  toFun := fun x =>
    ⟨((2 : ℝ) / ‖(x : E2)‖) • (x : E2), by
      have hxpos : 0 < ‖(x : E2)‖ :=
        lt_trans (by norm_num : (0 : ℝ) < 1) x.property
      have hx : ‖(x : E2)‖ ≠ 0 := ne_of_gt hxpos
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_div, Real.norm_eq_abs, norm_norm]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [hx]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.div₀
        (continuous_subtype_val.norm) (fun x =>
          ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) x.property))).smul
      continuous_subtype_val)

theorem retractExterior_comp_include (z : RadiusTwo) :
    retractExterior (includeRadiusTwo z) = z := by
  apply Subtype.ext
  have hz : ‖(z : E2)‖ = 2 := mem_sphere_zero_iff_norm.1 z.property
  simp [retractExterior, includeRadiusTwo, hz]

/-- The plane is contractible, hence 1-acyclic. Compactness is the
missing clause. -/
theorem plane_contractible : ContractibleSpace E2 :=
  inferInstance

/-- North pole of `S³`. -/
def s3Base : S3 :=
  ULift.up ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by
    change dist (EuclideanSpace.single (0 : Fin 4) (1 : ℝ)
        : EuclideanSpace ℝ (Fin 4)) 0 = 1
    simp⟩

/-- `S¹ × S³` retracts onto `S¹` by projection. -/
def includeS1 : C(S1, S1 × S3) where
  toFun := fun z => (z, s3Base)
  continuous_toFun := continuous_id.prodMk continuous_const

def projectS1 : C(S1 × S3, S1) where
  toFun := fun p => p.1
  continuous_toFun := continuous_fst

theorem projectS1_comp_include :
    (projectS1.comp includeS1) = ContinuousMap.id S1 := by
  ext z
  rfl

/-- First homology of `S¹` is a retract of first homology of `S¹ × S³`,
so the product is not 1-acyclic. -/
theorem s1_times_s3_not_one_acyclic
    (h1 : Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj S1) ≅ ModuleCat.of ℤ ℤ)) :
    ¬ IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of (S1 × S3))) := by
  intro hz
  obtain ⟨e⟩ := h1
  set H : TopCat.{0} ⥤ ModuleCat ℤ :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)
  let g : S1 ⟶ TopCat.of (S1 × S3) := TopCat.ofHom includeS1
  let r : TopCat.of (S1 × S3) ⟶ S1 := TopCat.ofHom projectS1
  have hgr : g ≫ r = 𝟙 S1 := by
    ext z
    rfl
  have hmap : H.map g ≫ H.map r = 𝟙 (H.obj S1) := by
    rw [← H.map_comp, hgr, H.map_id]
  have hg0 : H.map g = 0 := hz.eq_zero_of_tgt _
  have hid0 : 𝟙 (H.obj S1) = 0 := by
    rw [← hmap, hg0, zero_comp]
  have hzS1 : IsZero (H.obj S1) := (IsZero.iff_id_eq_zero _).mpr hid0
  have hzZ : IsZero (ModuleCat.of ℤ ℤ) := hzS1.of_iso e.symm
  have hsub : Subsingleton ℤ := ModuleCat.isZero_of_iff_subsingleton.mp hzZ
  exact one_ne_zero (hsub.elim (1 : ℤ) 0)

/-- Compactness is sharp: the plane is 1-acyclic and not compact, and
its unit-circle complement contains a retracting circle. -/
theorem compactness_is_sharp :
    ContractibleSpace E2 ∧
      (∀ z : RadiusTwo, 1 < ‖(z : E2)‖) ∧
        (retractExterior.comp includeRadiusTwo =
          ContinuousMap.id RadiusTwo) := by
  refine ⟨plane_contractible, radiusTwo_mem_exterior, ?_⟩
  exact ContinuousMap.ext retractExterior_comp_include

/-- Acyclicity is sharp: dropping 1-acyclicity lets a 4-manifold
retract onto a circle, so first homology is already nontrivial
once `H₁(S¹;ℤ) ≅ ℤ`. -/
theorem acyclicity_is_sharp
    (h1 : Nonempty
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj S1) ≅ ModuleCat.of ℤ ℤ)) :
    (projectS1.comp includeS1) = ContinuousMap.id S1 ∧
      ¬ IsZero
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of (S1 × S3))) :=
  ⟨projectS1_comp_include, s1_times_s3_not_one_acyclic h1⟩

end

end SharpnessCountermodels
end Foundation
end IndisputableMonolith
