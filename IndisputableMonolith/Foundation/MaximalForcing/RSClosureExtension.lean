import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure

/-!
# Maximal Forcing: closure stability under carrier extension

The original carrier-completeness worry is "the curated claim set might omit a
physically real invariant." This module answers the *forced* half of that worry at
the framework level: the maximal-forcing classification is **stable under extension
by a forced invariant**. Concretely, given a complete classifier certificate for a
claim universe `U` and any claim `C₀` forced over `U`'s admissibility class, the
universe extended with `C₀` again has a complete classifier, and `C₀` is classified
`Forced`.

The consequence is structural, not cosmetic. No forced invariant can ever be
"missing" in a way that breaks the closure: any forced fact, once named, is absorbed
into the `Forced` bucket while every prior classification is preserved verbatim
(`ClaimClassification` depends on the universe only through its admissibility class
and realization type, both untouched by enlarging the claim set). Therefore the only
way a genuinely new claim adds content beyond `Forced` is by carrying its own
independence witness (`Independent`) or named selection principle (`Selected`) — each
a real proof obligation. The register's incompleteness, if any, can only ever be an
*undiscovered independence or selection*, never an undiscovered forced invariant.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- Extend a claim universe with one additional claim, keeping the same realization
type and admissibility class. -/
def ClaimUniverse.extend (U : ClaimUniverse.{u}) (C0 : RealityClaim U.Realization) :
    ClaimUniverse.{u} where
  Realization := U.Realization
  admissibility := U.admissibility
  claims := insert C0 U.claims

@[simp] theorem extend_realization (U : ClaimUniverse.{u}) (C0 : RealityClaim U.Realization) :
    (U.extend C0).Realization = U.Realization := rfl

@[simp] theorem extend_admissibility (U : ClaimUniverse.{u}) (C0 : RealityClaim U.Realization) :
    (U.extend C0).admissibility = U.admissibility := rfl

@[simp] theorem extend_claims (U : ClaimUniverse.{u}) (C0 : RealityClaim U.Realization) :
    (U.extend C0).claims = insert C0 U.claims := rfl

/-- The new claim is in the extended closure. -/
theorem mem_extend_self {P : Primitive} (U : ClaimUniverse.{u})
    (C0 : RealityClaim U.Realization) : InClosure P (U.extend C0) C0 :=
  Set.mem_insert _ _

/-- Old claims remain in the extended closure. -/
theorem mem_extend_of_mem {P : Primitive} {U : ClaimUniverse.{u}}
    {C0 C : RealityClaim U.Realization} (h : InClosure P U C) :
    InClosure P (U.extend C0) C :=
  Set.mem_insert_of_mem _ h

/-- **Transport a classification along an extension.** `ClaimClassification` and
`IndependenceWitness` are indexed by the universe, so a classification over `U` must be
rebuilt constructor-by-constructor to land over `U.extend C₀`. Every field is defeq
because `extend` changes only the claim set, leaving the realization type and
admissibility class fixed. -/
def ClaimClassification.toExtend {U : ClaimUniverse.{u}}
    {C0 C : RealityClaim U.Realization}
    (h : ClaimClassification U C) : ClaimClassification (U.extend C0) C := by
  rcases h with hf | hw | hs
  · exact ClaimClassification.forced hf
  · refine ClaimClassification.independent
      { yes_model := hw.yes_model, no_model := hw.no_model,
        yes_admissible := hw.yes_admissible, no_admissible := hw.no_admissible,
        yes_holds := hw.yes_holds, no_fails := hw.no_fails }
  · exact ClaimClassification.selected hs

/-- **UNIFIED EXTENSION STABILITY (THEOREM).** A complete classifier for `U`, together
with *any* classification of a new claim `C₀` over `U`'s gate (forced, independent, or
selected), yields a complete classifier for the extended universe. Old claims keep
their classification verbatim; the new claim keeps the classification you supplied.

This is the full structural answer to carrier-completeness: the classifier is closed
under adjoining any claim you can classify. The only barrier to extending the register
is producing the classification certificate itself — which is exactly the
maximal-forcing proof obligation. A new claim never "breaks" the closure; it only adds
work if it is genuinely `Independent` or `Selected`, and even then it slots in cleanly. -/
def MaximalClosureCert.extendClassified {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (h0 : ClaimClassification U C0) :
    MaximalClosureCert P (U.extend C0) where
  classifies := by
    intro C hC
    rcases Set.mem_insert_iff.mp hC with h | h
    · rw [h]; exact h0.toExtend
    · exact (cert.classifies C h).toExtend

/-- **EXTENSION STABILITY, FORCED CASE (THEOREM).** Specialization of
`extendClassified` to a forced new claim: the new claim is classified `Forced`. -/
def MaximalClosureCert.extendForced {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (hC0 : Forced U.admissibility.admissible C0) :
    MaximalClosureCert P (U.extend C0) :=
  cert.extendClassified (ClaimClassification.forced hC0)

/-- **EXTENSION STABILITY, INDEPENDENT CASE (THEOREM).** Specialization to a new claim
carrying an explicit countermodel witness: the new claim is classified `Independent`. -/
def MaximalClosureCert.extendIndependent {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (W : IndependenceWitness U C0) :
    MaximalClosureCert P (U.extend C0) :=
  cert.extendClassified (ClaimClassification.independent W)

/-- **EXTENSION STABILITY, SELECTED CASE (THEOREM).** Specialization to a new claim
governed by a named selection principle: the new claim is classified `Selected`. -/
def MaximalClosureCert.extendSelected {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (hS : Selected U.admissibility.admissible C0) :
    MaximalClosureCert P (U.extend C0) :=
  cert.extendClassified (ClaimClassification.selected hS)

/-- **EXTENSION PRESERVES THE TRICHOTOMY (THEOREM).** Every claim in a universe
extended by a forced invariant is `Forced`, `Independent`, or `Selected`. The new
forced claim lands in `Forced`; everything else keeps its prior classification. -/
theorem extend_preserves_trichotomy {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (hC0 : Forced U.admissibility.admissible C0)
    (C : RealityClaim U.Realization) (hC : InClosure P (U.extend C0) C) :
    Forced (U.extend C0).admissibility.admissible C ∨
    Independent (U.extend C0).admissibility.admissible C ∨
    Selected (U.extend C0).admissibility.admissible C :=
  maximal_forcing_closure_trichotomy (cert.extendForced hC0) C hC

/-- **No forced invariant can be missing (THEOREM).** For any claim `C₀` forced over
`U`'s admissibility, the extended universe still admits a complete classifier and
`C₀` itself is `Forced` there. This is the precise structural answer to the
carrier-completeness worry on the forced side: the closure absorbs any forced fact
without disruption. -/
theorem forced_invariant_absorbed {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (hC0 : Forced U.admissibility.admissible C0) :
    (Nonempty (MaximalClosureCert P (U.extend C0))) ∧
    Forced (U.extend C0).admissibility.admissible C0 :=
  ⟨⟨cert.extendForced hC0⟩, hC0⟩

/-- **THE REGISTER IS SATURATED UNDER CLASSIFIED EXTENSION (THEOREM).** This is the
complete structural statement of carrier-completeness, covering all three buckets at
once. A complete classifier survives adjoining any claim `C₀` for which a
classification certificate (`ClaimClassification U C₀`) exists. Equivalently: the
predicate "this universe has a complete classifier" is closed under extension by any
classifiable claim.

The honest reading: the curated carrier cannot be "incomplete" in any way the framework
fails to absorb. If a new physically-real invariant is proposed, exactly one of three
things happens, and all three are handled — it is `Forced` (absorbed automatically, the
yard/eos-style derivations), `Independent` (absorbed once you exhibit a countermodel),
or `Selected` (absorbed once you name a selection principle). The residual content of
the maximal-forcing program is never "find the missing slot in the register"; it is
always "produce the classification certificate for a specific proposed claim." -/
theorem register_saturated_under_classification {P : Primitive} {U : ClaimUniverse.{u}}
    (cert : MaximalClosureCert P U) {C0 : RealityClaim U.Realization}
    (h0 : ClaimClassification U C0) :
    Nonempty (MaximalClosureCert P (U.extend C0)) :=
  ⟨cert.extendClassified h0⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
