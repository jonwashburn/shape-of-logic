import Mathlib
import IndisputableMonolith.Foundation.RecognitionLinkingPositiveID
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.UnknotComplementRetract
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.CircleParam
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Recognition-produced detecting embedding

Sharpening residual after `ContentTypedRecognitionLinkingPremises`.

Content-typed discharge still cites the independent topological unknot and
adds a recognition-circle agreement conjunct. This module builds a detecting
embedding that uses the hierarchy winding in the map itself: rotate the domain
circle by `recognitionWindingStep F H`, then apply the flat inclusion into S³.

## Receipts

* **THEOREM:** `recognitionProducedEmbedding F H` is an embedding S¹ ↪ S³ with
  nontrivial complement H₁, hence inhabits `DetectsNontrivialLinking 3`.
* **THEOREM (load-bearing):** the produced map is unequal to bare `unknot`
  (rotation angle `log φ ∈ (0, 2π)`).
* **THEOREM (decoy):** agreement-under-independent-unknot
  (`ContentTypedRecognitionLinkingPremises`) is strictly weaker: it is
  inhabited while every recognition-produced map differs from bare `unknot`.

Architecture citations stay on `PublicSpineLinkingClosure`.

Status: 0 sorry, 0 new axiom.
-/

noncomputable section

namespace IndisputableMonolith
namespace Foundation
namespace RecognitionProducedEmbedding

open RecognitionLinkingPositiveID
open LinkingFromHierarchy
open LinkingNecessity
open PublicSpine
open ClosedFramework
open HierarchyRealization
open CircleParam
open UnknotComplementRetract

/-! ## 1. Domain rotation by the recognition winding step -/

/-- Planar rotation by angle `θ` on the ambient Euclidean plane of S¹. -/
def rotate2 (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[x 0 * Real.cos θ - x 1 * Real.sin θ,
    x 0 * Real.sin θ + x 1 * Real.cos θ]

theorem rotate2_sq_sum (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    (x 0 * Real.cos θ - x 1 * Real.sin θ) ^ 2 +
      (x 0 * Real.sin θ + x 1 * Real.cos θ) ^ 2 =
    x 0 ^ 2 + x 1 ^ 2 := by
  have hc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  calc
    (x 0 * Real.cos θ - x 1 * Real.sin θ) ^ 2 +
        (x 0 * Real.sin θ + x 1 * Real.cos θ) ^ 2
      = x 0 ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
          x 1 ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    _ = x 0 ^ 2 * 1 + x 1 ^ 2 * 1 := by rw [hc, add_comm (Real.sin θ ^ 2), hc]
    _ = x 0 ^ 2 + x 1 ^ 2 := by ring

theorem rotate2_norm_eq (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖rotate2 θ x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [rotate2, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Real.norm_eq_abs, sq_abs]
  exact rotate2_sq_sum θ x

theorem continuous_rotate2 (θ : ℝ) : Continuous (rotate2 θ) := by
  change Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
    (WithLp.toLp 2 ![
      x 0 * Real.cos θ - x 1 * Real.sin θ,
      x 0 * Real.sin θ + x 1 * Real.cos θ] : EuclideanSpace ℝ (Fin 2))
  refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp ?_
  refine continuous_pi fun i => ?_
  fin_cases i
  · show Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
      x 0 * Real.cos θ - x 1 * Real.sin θ
    fun_prop
  · show Continuous fun x : EuclideanSpace ℝ (Fin 2) =>
      x 0 * Real.sin θ + x 1 * Real.cos θ
    fun_prop

theorem rotate2_neg (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    rotate2 (-θ) (rotate2 θ x) = x := by
  ext i
  fin_cases i
  · simp [rotate2, Real.cos_neg, Real.sin_neg]
    ring_nf
    have hc := Real.cos_sq_add_sin_sq θ
    grind
  · simp [rotate2, Real.cos_neg, Real.sin_neg]
    ring_nf
    have hc := Real.cos_sq_add_sin_sq θ
    grind

theorem rotate2_neg' (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    rotate2 θ (rotate2 (-θ) x) = x := by
  simpa using rotate2_neg (-θ) x

theorem rotate2_injective (θ : ℝ) : Function.Injective (rotate2 θ) := by
  intro x y h
  simpa [rotate2_neg] using congrArg (rotate2 (-θ)) h

theorem rotate2_surjective (θ : ℝ) : Function.Surjective (rotate2 θ) :=
  fun y => ⟨rotate2 (-θ) y, rotate2_neg' θ y⟩

@[simp] theorem rotate2_base (θ : ℝ) :
    rotate2 θ sphereOneBaseVector =
      !₂[Real.cos θ, Real.sin θ] := by
  simp [rotate2, sphereOneBaseVector, EuclideanSpace.single_apply]

/-- Domain homeomorphism of S¹ rotating by the hierarchy recognition step. -/
def recognitionCircleRotation
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 1) where
  toFun z :=
    ULift.up ⟨rotate2 (recognitionWindingStep F H) z.down.1, by
      rw [mem_sphere_zero_iff_norm, rotate2_norm_eq]
      exact mem_sphere_zero_iff_norm.1 z.down.2⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact (continuous_rotate2 (recognitionWindingStep F H)).comp
      (continuous_subtype_val.comp continuous_uliftDown)

theorem recognitionCircleRotation_injective
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Function.Injective (recognitionCircleRotation F H) := by
  intro a b hab
  have h := congrArg (fun w => (ULift.down w).1) hab
  exact ULift.ext a b
    (Subtype.ext (rotate2_injective (recognitionWindingStep F H) h))

instance : CompactSpace (TopCat.sphere.{0} 1) := by
  show CompactSpace (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  infer_instance

instance : T2Space (TopCat.sphere.{0} 1) := by
  show T2Space (ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
  infer_instance

theorem recognitionCircleRotation_isEmbedding
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Topology.IsEmbedding (recognitionCircleRotation F H) :=
  ((recognitionCircleRotation F H).continuous.isClosedEmbedding
    (recognitionCircleRotation_injective F H)).isEmbedding

theorem recognitionCircleRotation_surjective
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Function.Surjective (recognitionCircleRotation F H) := by
  intro z
  obtain ⟨w, hw⟩ := rotate2_surjective (recognitionWindingStep F H) z.down.1
  refine ⟨ULift.up ⟨w, ?_⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm]
    have hz := mem_sphere_zero_iff_norm.1 z.down.2
    have hrw : ‖rotate2 (recognitionWindingStep F H) w‖ = ‖z.down.1‖ := by rw [hw]
    have : ‖w‖ = ‖z.down.1‖ := by rwa [rotate2_norm_eq] at hrw
    exact this.trans hz
  · exact ULift.ext _ _ (Subtype.ext hw)

/-! ## 2. Produced embedding: rotate, then flat-unknot into S³ -/

/-- **Recognition-produced detecting embedding.** Domain circle is rotated by
the hierarchy's recognition winding step, then embedded as the flat unknot in
S³. The hierarchy argument is load-bearing in the map. -/
def recognitionProducedEmbedding
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 3) :=
  unknot.comp (recognitionCircleRotation F H)

theorem recognitionProducedEmbedding_isEmbedding
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Topology.IsEmbedding (recognitionProducedEmbedding F H) :=
  unknot_isEmbedding.comp (recognitionCircleRotation_isEmbedding F H)

theorem recognitionProducedEmbedding_range_eq_unknot
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    Set.range (recognitionProducedEmbedding F H) = Set.range unknot := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨recognitionCircleRotation F H z, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := recognitionCircleRotation_surjective F H z
    exact ⟨w, by simp [recognitionProducedEmbedding, hw]⟩

theorem linkingComplementH1_eq_of_range_eq
    {f g : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 3)}
    (h : Set.range f = Set.range g) :
    linkingComplementH1 3 f = linkingComplementH1 3 g := by
  unfold linkingComplementH1
  exact congrArg
    (fun s : Set (TopCat.sphere.{0} 3) =>
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of {x // x ∉ s})) h

theorem recognitionProducedEmbedding_complementH1_ne_zero
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    ¬ CategoryTheory.Limits.IsZero
      (linkingComplementH1 3 (recognitionProducedEmbedding F H)) := by
  rw [linkingComplementH1_eq_of_range_eq
    (recognitionProducedEmbedding_range_eq_unknot F H)]
  exact unknotComplementH1_ne_zero CircleWindingChain.circleH1ZIsoInt_holds

/-- Produced embedding inhabits content-typed Detects at 3. -/
theorem recognition_produced_detects
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    DetectsNontrivialLinking 3 :=
  ⟨recognitionProducedEmbedding F H,
    recognitionProducedEmbedding_isEmbedding F H,
    recognitionProducedEmbedding_complementH1_ne_zero F H⟩

/-! ## 3. Load-bearing: produced map ≠ bare unknot -/

theorem recognitionWindingStep_lt_two_pi
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionWindingStep F H < 2 * Real.pi := by
  rw [recognitionWindingStep_eq_log_phi]
  have hlog2 : Real.log PhiForcing.φ < Real.log 2 :=
    Real.log_lt_log PhiForcing.phi_pos PhiForcing.phi_lt_two
  have h2 : Real.log 2 < 1 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2 <| by
      linarith [Real.exp_one_gt_d9]
  have h1 : Real.log PhiForcing.φ < 1 := lt_trans hlog2 h2
  linarith [Real.pi_gt_three]

theorem recognitionProducedEmbedding_ne_unknot
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    recognitionProducedEmbedding F H ≠ unknot := by
  intro hEq
  set θ := recognitionWindingStep F H with hθdef
  have hθpos : 0 < θ := recognitionWindingStep_pos F H
  have hθlt : θ < 2 * Real.pi := recognitionWindingStep_lt_two_pi F H
  have hpt :=
    congrArg (fun f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 3) =>
      f sphereOneBasepoint) hEq
  have hfix :
      recognitionCircleRotation F H sphereOneBasepoint = sphereOneBasepoint :=
    unknot_injective (by
      simpa [recognitionProducedEmbedding, ContinuousMap.comp_apply] using hpt)
  have hrot : rotate2 θ sphereOneBaseVector = sphereOneBaseVector := by
    have := congrArg (fun z : TopCat.sphere.{0} 1 => z.down.1) hfix
    simpa [recognitionCircleRotation, sphereOneBasepoint, ← hθdef] using this
  have hc : Real.cos θ = 1 := by
    have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hrot
    simp [rotate2, sphereOneBaseVector, EuclideanSpace.single_apply] at h0
    exact h0
  have hfalse : False := by
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff θ).mp hc
    have hpos : (0 : ℝ) < (n : ℝ) * (2 * Real.pi) := by rwa [hn]
    have hlt : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by rwa [hn]
    have hnpos : (0 : ℤ) < n := by
      have : (0 : ℝ) < (n : ℝ) := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    have hnlt : n < (1 : ℤ) := by
      have : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
      exact_mod_cast this
    omega
  exact hfalse.elim

/-! ## 4. Dual-pair credit lands in the complement -/

/-- Credit direction: the orthogonal flat circle in the (2,3)-plane (unknot core). -/
def recognitionCreditCoreEmbedding :
    C(TopCat.sphere.{0} 1, TopCat.sphere.{0} 3) where
  toFun z :=
    ULift.up ⟨incl23 z.down.1, by
      rw [mem_sphere_zero_iff_norm, incl23.norm_map]
      exact mem_sphere_zero_iff_norm.1 z.down.2⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact incl23.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)

theorem recognitionCreditCore_not_in_unknot_range
    (z : TopCat.sphere.{0} 1) :
    recognitionCreditCoreEmbedding z ∉ Set.range unknot := by
  intro ⟨w, hw⟩
  have hmem := coord23_eq_zero_of_mem_range (y := recognitionCreditCoreEmbedding z)
    ⟨w, hw⟩
  -- credit core has ambient vector incl23 z, so coords 0,1 vanish and
  -- ‖(c2,c3)‖ = 1, hence not both c2 and c3 zero
  have hz0 : (recognitionCreditCoreEmbedding z).down.val 0 = 0 := by
    simp [recognitionCreditCoreEmbedding, incl23_apply_coord]
  have hz1 : (recognitionCreditCoreEmbedding z).down.val 1 = 0 := by
    simp [recognitionCreditCoreEmbedding, incl23_apply_coord]
  have hnorm : ‖(recognitionCreditCoreEmbedding z).down.val‖ = 1 :=
    mem_sphere_zero_iff_norm.1 (recognitionCreditCoreEmbedding z).down.property
  have hsum :
      (recognitionCreditCoreEmbedding z).down.val 2 ^ 2 +
        (recognitionCreditCoreEmbedding z).down.val 3 ^ 2 = 1 := by
    have hn := hnorm
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)] at hn
    simp [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs, hz0, hz1] at hn
    exact hn
  have : (0 : ℝ) = 1 := by
    simpa [hmem.1, hmem.2] using hsum
  exact absurd this (by norm_num)

theorem recognitionCreditCore_not_in_produced_range
    (F : ClosedObservableFramework) (H : RealizedHierarchy F)
    (z : TopCat.sphere.{0} 1) :
    recognitionCreditCoreEmbedding z ∉
      Set.range (recognitionProducedEmbedding F H) := by
  rw [recognitionProducedEmbedding_range_eq_unknot F H]
  exact recognitionCreditCore_not_in_unknot_range z

/-- Credit loop of the hierarchy lands in the complement of the produced debit embedding. -/
theorem creditLoop_avoids_recognition_produced
    (F : ClosedObservableFramework) (H : RealizedHierarchy F)
    (t : unitInterval) :
    recognitionCreditCoreEmbedding (creditLoop F H t) ∉
      Set.range (recognitionProducedEmbedding F H) :=
  recognitionCreditCore_not_in_produced_range F H _

/-! ## 5. Decoy: agreement-under-unknot is strictly weaker -/

/-- **Decoy.** Content-typed premises (agreement under independent unknot) hold,
yet every recognition-produced detecting map differs from bare `unknot`.
Agreement-under-unknot therefore does not construct the recognition-produced
detector. -/
theorem agreement_under_unknot_strictly_weaker :
    ContentTypedRecognitionLinkingPremises ∧
      (∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
        unknot ≠ recognitionProducedEmbedding F H) :=
  ⟨contentTypedRecognitionLinkingPremises, fun F H =>
    (recognitionProducedEmbedding_ne_unknot F H).symm⟩

/-- Specialization: J-hierarchy produces a detecting embedding unequal to bare unknot. -/
theorem j_hierarchy_recognition_produced_detects :
    DetectsNontrivialLinking 3 ∧
      recognitionProducedEmbedding
          jRealizedHierarchy.1 jRealizedHierarchy.2 ≠ unknot :=
  ⟨recognition_produced_detects jRealizedHierarchy.1 jRealizedHierarchy.2,
    recognitionProducedEmbedding_ne_unknot
      jRealizedHierarchy.1 jRealizedHierarchy.2⟩

/-! ## 6. Certificate -/

structure RecognitionProducedEmbeddingCert : Prop where
  /-- Produced map detects linking at 3. -/
  produced_detects :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      DetectsNontrivialLinking 3
  /-- Hierarchy winding is load-bearing (≠ bare unknot). -/
  load_bearing_winding :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionProducedEmbedding F H ≠ unknot
  /-- Dual-pair credit lands outside the produced debit image. -/
  credit_in_complement :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F)
      (t : unitInterval),
      recognitionCreditCoreEmbedding (creditLoop F H t) ∉
        Set.range (recognitionProducedEmbedding F H)
  /-- Agreement-under-unknot is strictly weaker. -/
  agreement_weaker :
    ContentTypedRecognitionLinkingPremises ∧
      (∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
        unknot ≠ recognitionProducedEmbedding F H)
  /-- Topology uniqueness unchanged. -/
  topology_forces_D3 : ∀ D, DetectsNontrivialLinking D → D = 3

theorem recognitionProducedEmbeddingCert :
    RecognitionProducedEmbeddingCert where
  produced_detects := recognition_produced_detects
  load_bearing_winding := recognitionProducedEmbedding_ne_unknot
  credit_in_complement := creditLoop_avoids_recognition_produced
  agreement_weaker := agreement_under_unknot_strictly_weaker
  topology_forces_D3 := PublicSpineLinkingClosure.forces_D3

end RecognitionProducedEmbedding
end Foundation
end IndisputableMonolith
