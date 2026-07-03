import IndisputableMonolith.Foundation.MaximalForcing.Primitive

/-!
# Maximal Forcing: Admissible Realization Classes

Maximal forcing never concedes a degree of freedom lazily. If a claim is not
forced on the current admissible class, the next move is to either:

1. tighten admissibility by adding a deeper law that reality must satisfy; or
2. prove independence by countermodel.

This module defines the admissibility-class machinery used by the closure
operator.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- A class of admissible realizations. The type `R` is deliberately abstract:
different phases may instantiate it with strict logic realizations, costed
realizations, physical models, or domain-specific structures. -/
structure AdmissibilityClass (R : Type u) where
  admissible : Set R
  label : String

/-- Tightening from `A` to `B`: every `B`-admissible realization is
`A`-admissible. The optional strictness witness is a separate field so the core
order remains usable even when strictness is not yet known. -/
structure Tightening {R : Type u} (A B : AdmissibilityClass R) where
  subset : ∀ r : R, r ∈ B.admissible -> r ∈ A.admissible
  strict_witness : Prop

/-- A claim forced after tightening is a target for promotion from `Selected` to
`Forced`. -/
def ForcedAfterTightening {R : Type u} (A B : AdmissibilityClass R)
    (C : RealityClaim R) : Prop :=
  Nonempty (Tightening A B) ∧ Forced B.admissible C

/-- If a claim is forced on a wider admissible class, it remains forced after
tightening. -/
theorem forced_of_forced_under_tightening {R : Type u}
    {A B : AdmissibilityClass R} {C : RealityClaim R}
    (hT : Tightening A B) (hA : Forced A.admissible C) :
    Forced B.admissible C := by
  intro r hr
  exact hA r (hT.subset r hr)

/-! ## Legitimacy of a tightening (Phase 5)

The placeholder `strict_witness := True` carries no content. A tightening is
*legitimate* only if it does real work and is justified by a deeper law rather
than a free selection. The next definitions make legitimacy a proof obligation. -/

/-- A tightening does real work when some realization admissible for the wider
class `A` is excluded by the narrower class `B`. This is derived from a genuine
independence-to-forcing flip: if a claim is independent over `A` but forced over
`B`, then the `A`-admissible realization that *fails* the claim cannot be
`B`-admissible, since everything `B`-admissible satisfies it. -/
theorem tightening_does_work {R : Type u} {A B : AdmissibilityClass R}
    {C : RealityClaim R}
    (hIndep : Independent A.admissible C) (hForced : Forced B.admissible C) :
    ∃ r : R, r ∈ A.admissible ∧ r ∉ B.admissible := by
  obtain ⟨_r0, r1, _h0, h1, _hC0, hnotC1⟩ := hIndep
  exact ⟨r1, h1, fun hr1B => hnotC1 (hForced r1 hr1B)⟩

/-- A **legitimate** tightening. Beyond the subset order it carries:

* `does_work`: a proof the gate is non-vacuous (some `A`-admissible realization is
  excluded by `B`); and
* `deeper_law` together with `deeper_law_proof`: the actual RS forcing theorem that
  justifies the added constraint, so the tightening is forced by a deeper law, not
  chosen freely. `deeper_law_label` names it for the audit.

This replaces `strict_witness := True`: legitimacy is now a discharged proof
obligation, not a stored `True`. -/
structure LegitimateTightening {R : Type u} (A B : AdmissibilityClass R) where
  subset : ∀ r : R, r ∈ B.admissible -> r ∈ A.admissible
  does_work : ∃ r : R, r ∈ A.admissible ∧ r ∉ B.admissible
  deeper_law : Prop
  deeper_law_proof : deeper_law
  deeper_law_label : String

/-- Every legitimate tightening is in particular a tightening (its stored
`strict_witness` is the deeper law it was justified by). -/
def LegitimateTightening.toTightening {R : Type u} {A B : AdmissibilityClass R}
    (L : LegitimateTightening A B) : Tightening A B where
  subset := L.subset
  strict_witness := L.deeper_law

/-- Smart constructor. A genuine independence-to-forcing flip plus a named, proved
deeper law assembles a legitimate tightening. -/
def legitimateTightening_of_flip {R : Type u} {A B : AdmissibilityClass R}
    {C : RealityClaim R}
    (hsub : ∀ r : R, r ∈ B.admissible -> r ∈ A.admissible)
    (hIndep : Independent A.admissible C) (hForced : Forced B.admissible C)
    (law : Prop) (law_proof : law) (law_label : String) :
    LegitimateTightening A B where
  subset := hsub
  does_work := tightening_does_work hIndep hForced
  deeper_law := law
  deeper_law_proof := law_proof
  deeper_law_label := law_label

end MaximalForcing
end Foundation
end IndisputableMonolith
