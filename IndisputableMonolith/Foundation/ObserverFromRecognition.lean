import Mathlib
import IndisputableMonolith.Foundation.PrimitiveDistinction

/-!
# Observer From Recognition

This module proves the next foundational step:

> non-trivial recognition forces an interface, and an interface is the
> primitive observer.

The word "observer" here is not yet a biological observer, a conscious
subject, or a physical measuring device. It is the minimal interface through
which a distinction becomes an event. The theorem says that once a carrier has
even one non-trivial distinction, there exists a finite-valued recognizer that
separates the distinguished pair. That finite-valued recognizer is the
primitive observer-like structure.

In the later physical theory, `ObserverFormalization.lean` upgrades this
primitive interface into a finite-resolution recognizer over ledger
configurations. This module supplies the pre-physical floor.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ObserverFromRecognition

open Classical
open PrimitiveDistinction

/-! ## Primitive Interface -/

/-- A primitive interface on a carrier `K`: a finite-valued recognizer.

The codomain is `Fin n`, so the interface has finite resolution. This is the
pre-physical form of an observer: not a mind, but the map through which
configurations become distinguishable events. -/
structure PrimitiveInterface (K : Type*) where
  n : ℕ
  hpos : 0 < n
  observe : K → Fin n

/-- The kernel of an interface: two configurations are indistinguishable
relative to the interface iff they produce the same observed outcome. -/
def PrimitiveInterface.kernel {K : Type*} (I : PrimitiveInterface K)
    (x y : K) : Prop :=
  I.observe x = I.observe y

/-- A primitive observer is exactly a primitive interface. This is a naming
choice, but it is important: the observer is not external to recognition; it is
the interface structure recognition forces. -/
abbrev PrimitiveObserver (K : Type*) := PrimitiveInterface K

/-- The observer kernel is reflexive. -/
theorem kernel_refl {K : Type*} (I : PrimitiveInterface K) (x : K) :
    I.kernel x x := rfl

/-- The observer kernel is symmetric. -/
theorem kernel_symm {K : Type*} (I : PrimitiveInterface K) {x y : K}
    (h : I.kernel x y) : I.kernel y x := h.symm

/-- The observer kernel is transitive. -/
theorem kernel_trans {K : Type*} (I : PrimitiveInterface K) {x y z : K}
    (hxy : I.kernel x y) (hyz : I.kernel y z) : I.kernel x z :=
  hxy.trans hyz

/-- Every primitive interface partitions its carrier into observational
equivalence classes. -/
theorem kernel_is_equivalence {K : Type*} (I : PrimitiveInterface K) :
    Equivalence (I.kernel) :=
  ⟨kernel_refl I,
   fun {x y} h => kernel_symm I (x := x) (y := y) h,
   fun {x y z} h₁ h₂ => kernel_trans I (x := x) (y := y) (z := z) h₁ h₂⟩

/-! ## Non-Trivial Recognition -/

/-- A carrier has non-trivial recognition when at least two configurations are
distinguishable. At the primitive floor this is simply the existence of a
non-equality. -/
def NontrivialRecognition (K : Type*) : Prop :=
  ∃ x y : K, equalityDistinction K x y

/-- An interface separates a pair if the pair lands in distinct observed
outcomes. -/
def Separates {K : Type*} (I : PrimitiveInterface K) (x y : K) : Prop :=
  I.observe x ≠ I.observe y

/-- The canonical two-outcome interface that asks whether the input is the
chosen reference point `x₀`. This is the minimal finite recognizer induced by
one named distinction. -/
noncomputable def pointInterface {K : Type*} (x₀ : K) :
    PrimitiveInterface K where
  n := 2
  hpos := by norm_num
  observe := fun x =>
    if x = x₀ then (1 : Fin 2) else (0 : Fin 2)

/-- The point interface recognizes its reference point as outcome `1`. -/
theorem pointInterface_at_ref {K : Type*} (x₀ : K) :
    (pointInterface x₀).observe x₀ = (1 : Fin 2) := by
  unfold pointInterface
  simp

/-- Any point distinct from the reference is recognized as outcome `0`. -/
theorem pointInterface_away {K : Type*} {x₀ y : K} (h : y ≠ x₀) :
    (pointInterface x₀).observe y = (0 : Fin 2) := by
  unfold pointInterface
  simp [h]

/-- The point interface separates any point from any distinct point. -/
theorem pointInterface_separates {K : Type*} {x₀ y : K} (h : x₀ ≠ y) :
    Separates (pointInterface x₀) x₀ y := by
  unfold Separates
  rw [pointInterface_at_ref x₀]
  have hy : y ≠ x₀ := fun h' => h h'.symm
  rw [pointInterface_away hy]
  norm_num

/-! ## Main Theorem -/

/-- **Observer from recognition.**

If a carrier admits any non-trivial recognition, then there exists a finite
interface, hence a primitive observer, that separates a distinguished pair.

This is the pre-physical observer theorem: observer-dependence is not added
at the quantum-measurement layer. It is forced at the first moment a
distinction becomes an event. -/
theorem nontrivial_recognition_forces_interface (K : Type*) :
    NontrivialRecognition K →
    ∃ (I : PrimitiveInterface K) (x y : K),
      equalityDistinction K x y ∧ Separates I x y := by
  intro h
  rcases h with ⟨x, y, hxy⟩
  exact ⟨pointInterface x, x, y, hxy, pointInterface_separates hxy⟩

/-- Same theorem under the observer name: non-trivial recognition forces a
primitive observer. -/
theorem nontrivial_recognition_forces_observer (K : Type*) :
    NontrivialRecognition K →
    ∃ (O : PrimitiveObserver K) (x y : K),
      equalityDistinction K x y ∧ Separates O x y :=
  nontrivial_recognition_forces_interface K

/-- The primitive observer theorem in compact certificate form. -/
structure ObserverFromRecognitionCert where
  forced :
    ∀ K : Type*, NontrivialRecognition K →
      ∃ (O : PrimitiveObserver K) (x y : K),
        equalityDistinction K x y ∧ Separates O x y
  kernel_equiv :
    ∀ {K : Type*} (O : PrimitiveObserver K), Equivalence (O.kernel)

/-- Certificate: the primitive observer is forced by non-trivial recognition. -/
def observerFromRecognitionCert : ObserverFromRecognitionCert where
  forced := nontrivial_recognition_forces_observer
  kernel_equiv := kernel_is_equivalence

theorem observerFromRecognitionCert_inhabited :
    Nonempty ObserverFromRecognitionCert :=
  ⟨observerFromRecognitionCert⟩

/-! ## Relation to the pre-temporal order

`PreTemporalForcingOrder.lean` records that the primitive observer, in this
sense, precedes time and physical light. The embodied observer of
`ObserverFormalization.lean` is downstream: a physical finite-resolution
interface living inside the ledger and spacetime structure.
-/

end ObserverFromRecognition
end Foundation
end IndisputableMonolith
