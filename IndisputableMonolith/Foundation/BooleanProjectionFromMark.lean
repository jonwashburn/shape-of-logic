import Mathlib

/-!
# Boolean Projection from a Marked Pair

The T-1 Boolean floor is canonical only after a distinguishing mark has been
chosen. A non-singleton carrier supplies at least one two-point shadow, but a
larger carrier does not choose that shadow uniquely.
-/

namespace IndisputableMonolith
namespace Foundation
namespace BooleanProjectionFromMark

/-- A named two-point mark inside a carrier. -/
structure MarkedPair (K : Type*) where
  base : K
  alt : K
  distinct : base ≠ alt

/-- The Boolean projection determined by a marked pair: the base point maps to
`false`, and every non-base point maps to `true`. -/
noncomputable def boolProjection {K : Type*} (m : MarkedPair K) : K → Bool := by
  classical
  exact fun z => if z = m.base then false else true

/-- Given a marked pair, the induced Boolean projection sends the marked base
to `false` and the marked alternative to `true`. -/
theorem boolProjection_canonical_given_mark {K : Type*} (m : MarkedPair K) :
    boolProjection m m.base = false ∧ boolProjection m m.alt = true := by
  classical
  constructor
  · simp [boolProjection]
  · have halt_ne_base : m.alt ≠ m.base := fun h => m.distinct h.symm
    simp [boolProjection, halt_ne_base]

/-- Without a mark, a three-point carrier has multiple inequivalent Boolean
shadows. This witnesses that non-singletonness alone does not canonically
select a Boolean floor projection. -/
theorem bool_projection_not_canonical_without_mark :
    ∃ (K : Type) (m1 m2 : MarkedPair K),
      boolProjection m1 ≠ boolProjection m2 := by
  classical
  let m1 : MarkedPair (Fin 3) :=
    { base := 0
      alt := 1
      distinct := by decide }
  let m2 : MarkedPair (Fin 3) :=
    { base := 1
      alt := 0
      distinct := by decide }
  refine ⟨Fin 3, m1, m2, ?_⟩
  intro h
  have h0 := congrArg (fun f : Fin 3 → Bool => f 0) h
  simp [boolProjection, m1, m2] at h0

/-- Certificate packaging the marked-pair Boolean projection facts. -/
structure BooleanProjectionFromMarkCert : Prop where
  /-- Every marked pair canonically determines a two-valued shadow. -/
  marked_pair_projection :
    ∀ {K : Type*} (m : MarkedPair K),
      boolProjection m m.base = false ∧ boolProjection m m.alt = true
  /-- Non-singletonness alone does not choose a unique two-valued shadow. -/
  no_canonical_projection_without_mark :
    ∃ (K : Type) (m1 m2 : MarkedPair K),
      boolProjection m1 ≠ boolProjection m2

/-- The Boolean-projection certificate is theorem-backed. -/
theorem booleanProjectionFromMarkCert : BooleanProjectionFromMarkCert where
  marked_pair_projection := boolProjection_canonical_given_mark
  no_canonical_projection_without_mark :=
    bool_projection_not_canonical_without_mark

end BooleanProjectionFromMark
end Foundation
end IndisputableMonolith
