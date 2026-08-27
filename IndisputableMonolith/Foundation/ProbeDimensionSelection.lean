import Mathlib
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.UnknotComplementRetract
import IndisputableMonolith.Foundation.CircleWindingChain

/-!
# Probe-dimension selection

Recognition trajectories are paths, so the runnable probe is q = 1.
That circle detector is `PublicSpine.DetectsNontrivialLinking`: it fires at
D = 3 and only there.

The Alexander dual sphere q = D−2 fires at more than one D. Concrete
witnesses: equatorial S⁰ ⊂ S² (this module) and the flat unknot S¹ ⊂ S³
(already proved). Two hits with different D means the dual-sphere probe
selects no unique dimension.

Status: 0 sorry, 0 new axiom.
-/

noncomputable section

namespace IndisputableMonolith
namespace Foundation
namespace ProbeDimensionSelection

open scoped RealInnerProductSpace
open CategoryTheory CategoryTheory.Limits
open UnknotComplementRetract

/-- First singular homology of the complement of an embedded q-sphere in S^D. -/
def sphereProbeComplementH1 (q D : ℕ)
    (f : C(TopCat.sphere.{0} q, TopCat.sphere.{0} D)) : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of {x : TopCat.sphere.{0} D // x ∉ Set.range f})

/-- Content-typed S^q detector. -/
def DetectsNontrivialSphereProbe (q D : ℕ) : Prop :=
  ∃ f : C(TopCat.sphere.{0} q, TopCat.sphere.{0} D),
    Topology.IsEmbedding f ∧
      ¬ CategoryTheory.Limits.IsZero (sphereProbeComplementH1 q D f)

theorem detectsSphereProbe_one_iff_linking (D : ℕ) :
    DetectsNontrivialSphereProbe 1 D ↔ PublicSpine.DetectsNontrivialLinking D := by
  unfold DetectsNontrivialSphereProbe PublicSpine.DetectsNontrivialLinking
    sphereProbeComplementH1 PublicSpine.linkingComplementH1
  rfl

/-! ## Equatorial S⁰ ⊂ S² -/

def polesIncl : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 ![x 0, 0, 0]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [PiLp.add_apply]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [PiLp.smul_apply] }
  norm_map' := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_one]
    simp [PiLp.toLp_apply]

def polesCoreIncl : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearMap :=
    { toFun := fun z => WithLp.toLp 2 ![0, z 0, z 1]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [PiLp.add_apply]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [PiLp.smul_apply] }
  norm_map' := by
    intro z
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_two]
    simp [PiLp.toLp_apply]

def polesProj : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := fun y => WithLp.toLp 2 ![y 1, y 2]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [PiLp.add_apply]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [PiLp.smul_apply]

lemma polesProj_continuous : Continuous polesProj :=
  polesProj.continuous_of_finiteDimensional

def polesFun (z : ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) :
    ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ULift.up ⟨polesIncl z.down.1, by
    rw [mem_sphere_zero_iff_norm, polesIncl.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.down.2⟩

def poles : C(TopCat.sphere.{0} 0, TopCat.sphere.{0} 2) where
  toFun := polesFun
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact polesIncl.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)

lemma poles_injective : Function.Injective poles := by
  intro a b hab
  have h3 : polesIncl a.down.1 = polesIncl b.down.1 :=
    congrArg (fun w => (ULift.down w).1) hab
  have h1 : a.down.1 = b.down.1 := polesIncl.injective h3
  exact ULift.ext a b (Subtype.ext h1)

instance : CompactSpace (TopCat.sphere.{0} 0) := by
  show CompactSpace (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))
  infer_instance

instance : T2Space (TopCat.sphere.{0} 2) := by
  show T2Space (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
  infer_instance

theorem poles_isEmbedding : Topology.IsEmbedding poles :=
  (poles.continuous.isClosedEmbedding poles_injective).isEmbedding

def PolesCpl : TopCat.{0} :=
  TopCat.of {x : TopCat.sphere.{0} 2 // x ∉ Set.range poles}

lemma poles_coord0_eq {y : TopCat.sphere.{0} 2}
    (hy : y ∈ Set.range poles) :
    (ULift.down y).1 1 = 0 ∧ (ULift.down y).1 2 = 0 := by
  obtain ⟨w, hw⟩ := hy
  have h3 : polesIncl w.down.1 = (ULift.down y).1 :=
    congrArg (fun v => (ULift.down v).1) hw
  constructor
  · have := congrFun (congrArg WithLp.ofLp h3) 1
    simpa using this.symm
  · have := congrFun (congrArg WithLp.ofLp h3) 2
    simpa using this.symm

def polesCoreFun (z : TopCat.sphere.{0} 1) : PolesCpl := by
  refine ⟨ULift.up ⟨polesCoreIncl
      (ULift.down (α := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) z).1, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, polesCoreIncl.norm_map]
    exact mem_sphere_zero_iff_norm.1 z.down.2
  · intro hmem
    obtain ⟨h1, h2⟩ := poles_coord0_eq hmem
    have hz0 : z.down.1 0 = 0 := by simpa using h1
    have hz1 : z.down.1 1 = 0 := by simpa using h2
    have hz : z.down.1 = 0 := by
      ext i
      fin_cases i
      · simpa using hz0
      · simpa using hz1
    have hnorm : ‖z.down.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.down.2
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm

def polesCore : C(TopCat.sphere.{0} 1, PolesCpl) where
  toFun := polesCoreFun
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact polesCoreIncl.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)

def polesPart (y : PolesCpl) : EuclideanSpace ℝ (Fin 2) :=
  polesProj (ULift.down y.1).1

lemma polesPart_continuous : Continuous polesPart :=
  polesProj_continuous.comp
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val))

lemma polesPart_ne_zero (y : PolesCpl) : polesPart y ≠ 0 := by
  intro h0
  set x : EuclideanSpace ℝ (Fin 3) := (ULift.down y.1).1
  have hx1 : x 1 = 0 := by
    have := congrFun (congrArg WithLp.ofLp h0) 0
    simpa [polesPart, polesProj] using this
  have hx2 : x 2 = 0 := by
    have := congrFun (congrArg WithLp.ofLp h0) 1
    simpa [polesPart, polesProj] using this
  set z : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 ![x 0]
  have hxnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 (ULift.down y.1).2
  have hznorm : ‖z‖ = 1 := by
    rw [EuclideanSpace.norm_eq] at hxnorm ⊢
    rw [Fin.sum_univ_three] at hxnorm
    rw [Fin.sum_univ_one]
    rw [hx1, hx2] at hxnorm
    simpa [z, PiLp.toLp_apply] using hxnorm
  apply y.2
  refine ⟨ULift.up ⟨z, mem_sphere_zero_iff_norm.2 hznorm⟩, ?_⟩
  apply ULift.ext
  apply Subtype.ext
  show polesIncl z = x
  ext i
  fin_cases i
  · change (polesIncl z) 0 = x 0
    simp [polesIncl, z, PiLp.toLp_apply]
  · change (polesIncl z) 1 = x 1
    simpa [polesIncl, z, PiLp.toLp_apply] using hx1.symm
  · change (polesIncl z) 2 = x 2
    simpa [polesIncl, z, PiLp.toLp_apply] using hx2.symm

def polesRetractFun (y : PolesCpl) : TopCat.sphere.{0} 1 :=
  ULift.up ⟨‖polesPart y‖⁻¹ • polesPart y, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (polesPart_ne_zero y))]⟩

def polesRetract : C(PolesCpl, TopCat.sphere.{0} 1) where
  toFun := polesRetractFun
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact ((polesPart_continuous.norm.inv₀
      fun y => norm_ne_zero_iff.2 (polesPart_ne_zero y)).smul polesPart_continuous)

theorem poles_retract_core (z : TopCat.sphere.{0} 1) :
    polesRetract (polesCore z) = z := by
  have hpart : polesPart (polesCore z) = z.down.1 := by
    ext i
    fin_cases i <;> simp [polesPart, polesCore, polesCoreFun, polesProj, polesCoreIncl]
  have hnorm : ‖z.down.1‖ = 1 := mem_sphere_zero_iff_norm.1 z.down.2
  apply ULift.ext
  apply Subtype.ext
  show ‖polesPart (polesCore z)‖⁻¹ • polesPart (polesCore z) = z.down.1
  rw [hpart, hnorm, inv_one, one_smul]

theorem polesComplementH1_ne_zero
    (h1 : Nonempty ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.sphere.{0} 1)) ≅ ModuleCat.of ℤ ℤ)) :
    ¬ CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of {x : TopCat.sphere.{0} 2 // x ∉ Set.range poles})) := by
  intro hz
  obtain ⟨e⟩ := h1
  set H : TopCat.{0} ⥤ ModuleCat ℤ :=
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ) with hH
  let g : TopCat.sphere.{0} 1 ⟶ PolesCpl := TopCat.ofHom polesCore
  let r : PolesCpl ⟶ TopCat.sphere.{0} 1 := TopCat.ofHom polesRetract
  have hgr : g ≫ r = 𝟙 (TopCat.sphere.{0} 1) := by
    ext z
    exact poles_retract_core z
  have hmap : H.map g ≫ H.map r = 𝟙 (H.obj (TopCat.sphere.{0} 1)) := by
    rw [← H.map_comp, hgr, H.map_id]
  have hzC : IsZero (H.obj PolesCpl) := hz
  have hg0 : H.map g = 0 := hzC.eq_zero_of_tgt _
  have hid0 : 𝟙 (H.obj (TopCat.sphere.{0} 1)) = 0 := by
    rw [← hmap, hg0, zero_comp]
  have hzS1 : IsZero (H.obj (TopCat.sphere.{0} 1)) :=
    (IsZero.iff_id_eq_zero _).mpr hid0
  have hzZ : IsZero (ModuleCat.of ℤ ℤ) := hzS1.of_iso e.symm
  have hsub : Subsingleton ℤ := ModuleCat.isZero_of_iff_subsingleton.mp hzZ
  exact one_ne_zero (hsub.elim (1 : ℤ) 0)

/-- THEOREM: the dual-sphere probe fires at D = 2. -/
theorem dual_sphere_detector_fires_two :
    DetectsNontrivialSphereProbe 0 2 :=
  ⟨poles, poles_isEmbedding,
    polesComplementH1_ne_zero CircleWindingChain.circleH1ZIsoInt_holds⟩

/-- THEOREM: the dual-sphere probe fires at D = 3, because it is the circle
probe (the flat unknot). -/
theorem dual_sphere_detector_fires_three :
    DetectsNontrivialSphereProbe 1 3 :=
  (detectsSphereProbe_one_iff_linking 3).2 PublicSpine.detectsNontrivialLinking_three

/-- THEOREM: the circle probe fires at D = 3. -/
theorem circle_probe_fires_three : DetectsNontrivialSphereProbe 1 3 :=
  dual_sphere_detector_fires_three

/-- THEOREM: the circle probe selects D = 3. -/
theorem circle_probe_selects_D3 :
    ∀ D, DetectsNontrivialSphereProbe 1 D → D = 3 :=
  fun D h =>
    PublicSpineLinkingClosure.forces_D3 D
      ((detectsSphereProbe_one_iff_linking D).1 h)

/-- Recognition-runnable probes are paths. -/
def recognitionRunnableSphereProbe : ℕ := 1

theorem recognitionRunnableSphereProbe_eq_one :
    recognitionRunnableSphereProbe = 1 :=
  rfl

def IsRecognitionRunnableSphereProbe (q : ℕ) : Prop :=
  q = recognitionRunnableSphereProbe

/-- THEOREM: the Alexander dual sphere is not a unique-dimension selector:
it fires at both D = 2 and D = 3. -/
theorem dual_sphere_selects_no_unique_D :
    ¬ ∃ D₀ : ℕ, ∀ D, 2 ≤ D → DetectsNontrivialSphereProbe (D - 2) D → D = D₀ := by
  rintro ⟨D₀, h⟩
  have h2 := h 2 (by decide) dual_sphere_detector_fires_two
  have h3 := h 3 (by decide) dual_sphere_detector_fires_three
  exact (by decide : 2 ≠ 3) (h2.trans h3.symm)

/-- THEOREM: among sphere probes, the recognition-runnable path-type is the
unique discriminating probe. It forces D = 3. The dual sphere fires at both
2 and 3, so it does not select a unique D. -/
theorem path_type_unique_discriminating_sphere_probe :
    (∀ D, DetectsNontrivialSphereProbe 1 D → D = 3) ∧
      DetectsNontrivialSphereProbe 0 2 ∧
      DetectsNontrivialSphereProbe 1 3 ∧
      ¬ ∃ D₀ : ℕ, ∀ D, 2 ≤ D → DetectsNontrivialSphereProbe (D - 2) D → D = D₀ :=
  ⟨circle_probe_selects_D3, dual_sphere_detector_fires_two,
    dual_sphere_detector_fires_three, dual_sphere_selects_no_unique_D⟩

/-- Named residual: a general-D equatorial retract. Inhabited at 2 and 3. -/
structure EquatorialRetract (D : ℕ) : Prop where
  two_le : 2 ≤ D
  detects : DetectsNontrivialSphereProbe (D - 2) D

theorem equatorialRetract_two : EquatorialRetract 2 where
  two_le := by decide
  detects := dual_sphere_detector_fires_two

theorem equatorialRetract_three : EquatorialRetract 3 where
  two_le := by decide
  detects := dual_sphere_detector_fires_three

end ProbeDimensionSelection
end Foundation
end IndisputableMonolith
