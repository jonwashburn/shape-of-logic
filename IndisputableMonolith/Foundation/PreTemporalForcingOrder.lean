import Mathlib

/-!
# Pre-Temporal Forcing Order

This module records the dependency order that exists "before time" in
Recognition Science. Since physical time is itself a forced object, the
ordering here is not chronological. It is a forcing order: `A` is before `B`
when `B` requires `A` as prior structure.

The central distinction is between:

* **recognition-light**: the primitive revealing act of distinction, prior to
  time and spacetime;
* **physical light**: the null-cone / photon / electromagnetic carrier,
  downstream of J-cost, ticks, and spacetime.

So light is fundamental in two senses, but only the first sense is pre-temporal.
Physical light is the first boundary of spacetime, not the first item in the
forcing chain.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PreTemporalForcingOrder

/-! ## Stages -/

/-- The dependency stages in the pre-temporal forcing chain. -/
inductive Stage where
  | distinction
  | recognitionInterface
  | singleValuedPredicate
  | symmetricComparison
  | compositionConsistency
  | rcl
  | jCost
  | arithmeticObject
  | timeTick
  | spacetime
  | lightCone
  | photonEM
  | embodiedObserver
  deriving DecidableEq, Repr

/-- A numerical rank for the forcing order. Lower rank means prior structure. -/
def rank : Stage → ℕ
  | .distinction => 0
  | .recognitionInterface => 1
  | .singleValuedPredicate => 2
  | .symmetricComparison => 3
  | .compositionConsistency => 4
  | .rcl => 5
  | .jCost => 6
  | .arithmeticObject => 7
  | .timeTick => 8
  | .spacetime => 9
  | .lightCone => 10
  | .photonEM => 11
  | .embodiedObserver => 12

/-- Forcing priority: `a` is before `b` iff its dependency rank is smaller. -/
def Before (a b : Stage) : Prop := rank a < rank b

instance (a b : Stage) : Decidable (Before a b) := Nat.decLt _ _

/-! ## Main order theorems -/

theorem distinction_first (s : Stage) (h : s ≠ Stage.distinction) :
    Before Stage.distinction s := by
  cases s <;> simp [Before, rank] at h ⊢

theorem recognition_before_predicate :
    Before Stage.recognitionInterface Stage.singleValuedPredicate := by
  decide

theorem predicate_before_symmetry :
    Before Stage.singleValuedPredicate Stage.symmetricComparison := by
  decide

theorem symmetry_before_composition :
    Before Stage.symmetricComparison Stage.compositionConsistency := by
  decide

theorem composition_before_rcl :
    Before Stage.compositionConsistency Stage.rcl := by
  decide

theorem rcl_before_jCost :
    Before Stage.rcl Stage.jCost := by
  decide

theorem jCost_before_arithmetic :
    Before Stage.jCost Stage.arithmeticObject := by
  decide

theorem arithmetic_before_time :
    Before Stage.arithmeticObject Stage.timeTick := by
  decide

theorem time_before_spacetime :
    Before Stage.timeTick Stage.spacetime := by
  decide

theorem spacetime_before_lightCone :
    Before Stage.spacetime Stage.lightCone := by
  decide

theorem lightCone_before_photonEM :
    Before Stage.lightCone Stage.photonEM := by
  decide

theorem photonEM_before_embodiedObserver :
    Before Stage.photonEM Stage.embodiedObserver := by
  decide

/-! ## Light: two senses -/

/-- Recognition-light: the revealing act of an interface making distinction
available. This is pre-temporal. -/
def RecognitionLight : Stage := Stage.recognitionInterface

/-- Physical light: the null boundary / electromagnetic carrier of spacetime. -/
def PhysicalLight : Stage := Stage.lightCone

theorem recognition_light_before_time :
    Before RecognitionLight Stage.timeTick := by
  decide

theorem recognition_light_before_spacetime :
    Before RecognitionLight Stage.spacetime := by
  decide

theorem recognition_light_before_physical_light :
    Before RecognitionLight PhysicalLight := by
  decide

theorem physical_light_after_spacetime :
    Before Stage.spacetime PhysicalLight := by
  decide

/-- Physical light is not first in the forcing order. It requires spacetime. -/
theorem physical_light_not_first :
    ¬∀ s : Stage, s ≠ PhysicalLight → Before PhysicalLight s := by
  intro h
  have hbad := h Stage.distinction (by decide)
  norm_num [Before, PhysicalLight, rank] at hbad

/-! ## Observer: two senses -/

/-- Primitive observer-like structure: a recognizer/interface. This is forced
as soon as recognition, not merely bare abstract distinction, is in play. -/
def PrimitiveObserver : Stage := Stage.recognitionInterface

/-- Embodied observer: a physical subsystem with finite resolution, downstream
of spacetime and physical light. -/
def PhysicalObserver : Stage := Stage.embodiedObserver

theorem primitive_observer_before_time :
    Before PrimitiveObserver Stage.timeTick := by
  decide

theorem primitive_observer_before_physical_light :
    Before PrimitiveObserver PhysicalLight := by
  decide

theorem physical_observer_after_physical_light :
    Before PhysicalLight PhysicalObserver := by
  decide

/-! ## Certificate -/

structure PreTemporalOrderCert where
  recognition_light_pre_time : Before RecognitionLight Stage.timeTick
  recognition_light_pre_spacetime : Before RecognitionLight Stage.spacetime
  physical_light_post_spacetime : Before Stage.spacetime PhysicalLight
  light_cone_pre_photon : Before Stage.lightCone Stage.photonEM
  primitive_observer_pre_time : Before PrimitiveObserver Stage.timeTick
  physical_observer_post_light : Before PhysicalLight PhysicalObserver

def cert : PreTemporalOrderCert where
  recognition_light_pre_time := recognition_light_before_time
  recognition_light_pre_spacetime := recognition_light_before_spacetime
  physical_light_post_spacetime := physical_light_after_spacetime
  light_cone_pre_photon := lightCone_before_photonEM
  primitive_observer_pre_time := primitive_observer_before_time
  physical_observer_post_light := physical_observer_after_physical_light

theorem cert_inhabited : Nonempty PreTemporalOrderCert := ⟨cert⟩

end PreTemporalForcingOrder
end Foundation
end IndisputableMonolith
