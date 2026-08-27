import Mathlib
import IndisputableMonolith.Foundation.PublicSpine

/-!
# Foliation independence of the linking detector

A 3+1 split is a product `ℝ × S³`. Time translation is a homeomorphism
of spacetime and is the identity on the spatial factor.

The linking detector is a property of an embedding `S¹ ↪ S³`. It does
not mention a time coordinate, so it is the same in every constant-time
slice.

Status: 0 sorry, 0 new axiom.
-/

noncomputable section

namespace IndisputableMonolith
namespace Foundation
namespace FoliationIndependence

open PublicSpine

abbrev SpatialSlice := TopCat.sphere.{0} 3
abbrev SpaceTime := ℝ × SpatialSlice
abbrev Circle := TopCat.sphere.{0} 1

/-- Time translation on spacetime. -/
def timeTranslate (s : ℝ) : SpaceTime ≃ₜ SpaceTime :=
  (Homeomorph.addLeft s).prodCongr (Homeomorph.refl SpatialSlice)

theorem timeTranslate_prod (s : ℝ) (q : SpaceTime) :
    timeTranslate s q = (s + q.1, q.2) := by
  cases q
  simp [timeTranslate, Homeomorph.prodCongr, Homeomorph.addLeft, Prod.map]

theorem timeTranslate_spatial_id (s : ℝ) (p : SpaceTime) :
    (timeTranslate s p).2 = p.2 := by
  rw [timeTranslate_prod]

/-- The slice at time t. -/
def slice (t : ℝ) : Set SpaceTime :=
  {p | p.1 = t}

theorem timeTranslate_maps_slice (s t : ℝ) :
    timeTranslate s '' slice t = slice (s + t) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [timeTranslate_prod]
    exact congrArg (fun u => s + u) hq
  · intro hp
    refine ⟨(t, p.2), rfl, ?_⟩
    rw [timeTranslate_prod]
    apply Prod.ext
    · exact hp.symm
    · rfl

/-- Place a spatial circle into the slice at time t. -/
def embedAtTime (t : ℝ)
    (f : C(Circle, SpatialSlice)) : C(Circle, SpaceTime) :=
  ContinuousMap.prodMk (ContinuousMap.const Circle t) f

theorem embedAtTime_time (t : ℝ) (f : C(Circle, SpatialSlice)) (θ : Circle) :
    (embedAtTime t f θ).1 = t :=
  rfl

theorem embedAtTime_space (t : ℝ) (f : C(Circle, SpatialSlice)) (θ : Circle) :
    (embedAtTime t f θ).2 = f θ :=
  rfl

/-- Changing the slice time does not change the spatial embedding. -/
theorem spatial_embedding_independent_of_time
    (t s : ℝ) (f : C(Circle, SpatialSlice)) :
    (fun θ => (embedAtTime t f θ).2) = (fun θ => (embedAtTime s f θ).2) :=
  rfl

/-- Equal spatial maps give the same detector verdict. -/
theorem detector_depends_only_on_spatial
    {f g : C(Circle, SpatialSlice)} (h : f = g) :
    (Topology.IsEmbedding f ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 3 f)) ↔
      (Topology.IsEmbedding g ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 3 g)) := by
  subst h
  rfl

/-- The detector is a fact about S³. It does not mention a time coordinate. -/
theorem detector_at_any_slice_time (_t : ℝ) :
    DetectsNontrivialLinking 3 :=
  detectsNontrivialLinking_three

/-- Foliation independence: time translation leaves the spatial factor
fixed, and the detector is a property of that factor. -/
theorem linking_independent_of_foliation
    (s : ℝ) (p : SpaceTime) :
    (timeTranslate s p).2 = p.2 ∧ DetectsNontrivialLinking 3 :=
  ⟨timeTranslate_spatial_id s p, detectsNontrivialLinking_three⟩

end FoliationIndependence
end Foundation
end IndisputableMonolith

end
