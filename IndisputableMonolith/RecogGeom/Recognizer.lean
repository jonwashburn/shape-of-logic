import Mathlib
import IndisputableMonolith.RecogGeom.Core
import IndisputableMonolith.RecogGeom.Locality

/-!
# Recognition Geometry: Recognition Maps (RG2)

This module defines recognition maps—the fundamental objects that connect
configurations to events. A recognizer is a function R : C → E that maps
configurations to observable events.

## Axiom RG2: Recognizers and Events

There exists at least one recognizer: a map R : C → E for some nontrivial
event space E (meaning |Im(R)| ≥ 2).

## Key Insight

Configurations are what the world does; events are what recognizers see.
The recognition map R encodes how the world presents itself to observation.

-/

namespace IndisputableMonolith
namespace RecogGeom

/-! ## Recognition Map (RG2) -/

/-- A recognition map from configurations to events.
    This is the basic object connecting the configuration world
    to the observable event world.

    RG2: There exists at least one nontrivial recognizer. -/
structure Recognizer (C : Type*) (E : Type*) where
  /-- The recognition function mapping configurations to events -/
  R : C → E
  /-- The recognizer is nontrivial: at least two distinct events are produced -/
  nontrivial : ∃ c₁ c₂ : C, R c₁ ≠ R c₂

/-- A local recognizer is a recognizer on a local configuration space -/
structure LocalRecognizer (C : Type*) (E : Type*) extends
    LocalConfigSpace C, Recognizer C E

/-! ## Basic Properties -/

variable {C E : Type*}

/-- The image of a recognizer has at least 2 elements -/
theorem Recognizer.image_nontrivial (r : Recognizer C E) :
    ∃ e₁ e₂ : E, e₁ ∈ Set.range r.R ∧ e₂ ∈ Set.range r.R ∧ e₁ ≠ e₂ := by
  obtain ⟨c₁, c₂, hne⟩ := r.nontrivial
  exact ⟨r.R c₁, r.R c₂, ⟨c₁, rfl⟩, ⟨c₂, rfl⟩, hne⟩

/-- A trivial recognizer maps everything to the same event -/
def Recognizer.isTrivial (r : Recognizer C E) : Prop :=
  ∀ c₁ c₂ : C, r.R c₁ = r.R c₂

/-- No recognizer is trivial (by definition) -/
theorem Recognizer.not_trivial (r : Recognizer C E) : ¬r.isTrivial := by
  intro h
  obtain ⟨c₁, c₂, hne⟩ := r.nontrivial
  exact hne (h c₁ c₂)

/-! ## Local Image -/

/-- The local image of a recognizer on a neighborhood -/
def Recognizer.localImage (r : Recognizer C E) (U : Set C) : Set E :=
  r.R '' U

/-- Local image is subset of full image -/
theorem Recognizer.localImage_subset_range (r : Recognizer C E) (U : Set C) :
    r.localImage U ⊆ Set.range r.R :=
  Set.image_subset_range r.R U

/-! ## Preimage Structure -/

/-- The preimage (fiber) of an event under a recognizer -/
def Recognizer.fiber (r : Recognizer C E) (e : E) : Set C :=
  r.R ⁻¹' {e}

/-- A configuration is in the fiber of its event -/
theorem Recognizer.mem_fiber_self (r : Recognizer C E) (c : C) :
    c ∈ r.fiber (r.R c) := by
  simp [fiber]

/-- Fibers partition the configuration space -/
theorem Recognizer.fibers_partition (r : Recognizer C E) :
    ∀ c : C, ∃! e : E, c ∈ r.fiber e := by
  intro c
  use r.R c
  constructor
  · exact r.mem_fiber_self c
  · intro e he
    simp [fiber] at he
    exact he.symm

/-! ## Event Lifting -/

/-- An event is realized by some configuration if it's in the image -/
def Recognizer.isRealized (r : Recognizer C E) (e : E) : Prop :=
  e ∈ Set.range r.R

/-- Every event in the image has a witness configuration -/
noncomputable def Recognizer.witness (r : Recognizer C E) (e : E)
    (he : r.isRealized e) : C :=
  he.choose

theorem Recognizer.witness_spec (r : Recognizer C E) (e : E)
    (he : r.isRealized e) : r.R (r.witness e he) = e :=
  he.choose_spec

/-! ## Constant Recognizer (Trivial Event Space) -/

/-- A constant function is NOT a valid recognizer (it's trivial) -/
theorem constant_not_recognizer (C : Type*) [Nonempty C] (e : E) :
    ¬∃ c₁ c₂ : C, (fun _ : C => e) c₁ ≠ (fun _ : C => e) c₂ := by
  push_neg
  intros
  rfl

/-! ## Module Status -/

def recognizer_status : String :=
  "✓ Recognizer structure defined (RG2)\n" ++
  "✓ LocalRecognizer combining locality and recognition\n" ++
  "✓ Nontriviality enforced by definition\n" ++
  "✓ Local image and fiber definitions\n" ++
  "✓ Fiber partition theorem\n" ++
  "✓ Event realization and witness\n" ++
  "\n" ++
  "RECOGNITION MAPS (RG2) COMPLETE"

#eval recognizer_status

end RecogGeom
end IndisputableMonolith
