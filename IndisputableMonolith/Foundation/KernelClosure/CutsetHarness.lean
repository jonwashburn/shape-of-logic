import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.ClockFromCompletion
import IndisputableMonolith.Foundation.OctaveFloorStep

/-!
# The cutset harness: closing a kernel sentence by exclusion

Every kernel sentence above the forced floor has a kernel-checked countermodel:
a structure consistent with the rungs below in which the sentence fails. So no
sentence can be forced by consistency alone. A cutset closure forces it the
other way round: exhibit the class of structures that violate the sentence, name
a *blade* `Φ` that the real ledger passes, and prove that every violator fails
`Φ`. The sentence is then a theorem of `Φ` together with the floor.

## The blade rule

Where the premise hides in a negative argument is in `Φ`. The harness therefore
records the blade's provenance, and only two provenances are admissible:

* `floorTheorem`: `Φ` is a property the forced floor (T-2 through T4, the octave
  floor step) already has, proved, not assumed; or
* `definition`: `Φ` is the reading of a word the floor already uses (tick,
  record, completed, unit).

A blade of any other kind is a seventh sentence, and the row is relabelled, not
closed. The provenance field is a declaration; the check that it is honest is
made by reading the blade's definition, which must mention neither the sentence
nor a numeral.

## The meter contract, as fields

The three earlier exclusion certificates in this library that turned out to be
vacuous (an exclusivity claim quantifying over an empty class, a model-
independence claim with a two-state counterexample, eight sites assuming a one-
state ledger) are the reason the row carries witnesses, not just the universal:

* `real`, `blade_real`: the planted positive. The real object passes `Φ`.
* `violator`, `violator_violates`, `blade_kills_violator`: the planted negative.
  The census countermodel is in the violating class and fails `Φ`.
* `exclusion`: the universal. Every floor-consistent violator fails `Φ`.

From these the harness derives: the violating class is non-empty
(`class_nonempty`), the blade varies across the population (`blade_varies`),
the vacuous row cannot be built (`vacuous_rejected`), the trivial blade cannot be
built (`trivial_blade_rejected`), and the sentence holds on the real object
without being assumed there (`real_sentence`).

## The cheapest degenerate output

The harness cannot exclude `Blade := Sentence`. A row whose blade restates its
sentence inhabits `CutsetRow` and proves nothing; that is the blade rule's job
and it is checked by reading. Reported here so no later row claims the harness
caught it.

## The blades, stated once

* `B1` statability: the structure steps, `S ≃ (Fin D → Bool) × S`. The forced
  floor has it (`OctaveFloorStep.stepEquivD`); a finite non-empty state space
  cannot (`finite_does_not_step`).
* `B2` least count: among positive counts the least is one. The schema that
  fixed the unit at T2 (`BooleanUnitForced.unit_forced_of_least`).
* `B3` record persistence: a record is a configuration that deformation cannot
  move. A definition; `HasRecords` is the property a ledger needs.

## The planted good row

The clock row of `ClockFromCompletion` in harness form: candidates are closed
passes, the sentence is the Gray cover, the blade is the completion clock
(a definition), the real object is the eight-tick Gray cycle, the violator is
the period-two bounce. `clockRow` inhabits `CutsetRow`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset

universe u

/-! ## Provenance and the row -/

/-- Where a blade comes from. Only these two are admissible. -/
inductive BladeProvenance
  | floorTheorem (name : String)
  | definition (word : String)
  deriving Repr

/-- A cutset row over a type `X` of candidate structures. -/
structure CutsetRow (X : Type u) where
  /-- What the rungs below already impose on a candidate. -/
  Floor : X → Prop
  /-- The kernel sentence being closed. -/
  Sentence : X → Prop
  /-- The blade. -/
  Blade : X → Prop
  provenance : BladeProvenance
  /-- Planted positive. -/
  real : X
  real_floor : Floor real
  blade_real : Blade real
  /-- Planted negative: the census countermodel. -/
  violator : X
  violator_floor : Floor violator
  violator_violates : ¬ Sentence violator
  blade_kills_violator : ¬ Blade violator
  /-- The universal exclusion. -/
  exclusion : ∀ x, Floor x → ¬ Sentence x → ¬ Blade x

namespace CutsetRow

variable {X : Type u} (R : CutsetRow X)

/-- The cutset theorem read forwards: floor plus blade forces the sentence. -/
theorem forces : ∀ x, R.Floor x → R.Blade x → R.Sentence x := by
  intro x hf hb
  by_contra hs
  exact R.exclusion x hf hs hb

/-- The sentence holds on the real object, derived, not assumed. -/
theorem real_sentence : R.Sentence R.real :=
  R.forces R.real R.real_floor R.blade_real

/-- The violating class is non-empty. -/
theorem class_nonempty : ∃ x, R.Floor x ∧ ¬ R.Sentence x :=
  ⟨R.violator, R.violator_floor, R.violator_violates⟩

/-- The blade varies across the population: true somewhere, false somewhere. -/
theorem blade_varies : ∃ x y, R.Blade x ∧ ¬ R.Blade y :=
  ⟨R.real, R.violator, R.blade_real, R.blade_kills_violator⟩

/-- **Vacuity rejected.** No inhabitant has a sentence true on all of its floor. -/
theorem vacuous_rejected : ¬ ∀ x, R.Floor x → R.Sentence x := by
  intro h
  exact R.violator_violates (h R.violator R.violator_floor)

/-- **Trivial blade rejected.** No inhabitant has a blade true everywhere. -/
theorem trivial_blade_rejected : ¬ ∀ x, R.Blade x := by
  intro h
  exact R.blade_kills_violator (h R.violator)

/-- The real object and the violator are distinct. -/
theorem real_ne_violator : R.real ≠ R.violator := by
  intro h
  exact R.blade_kills_violator (h ▸ R.blade_real)

end CutsetRow

/-- **Decoy.** A row whose sentence is trivially true cannot be built: the type
of such rows is empty. -/
theorem vacuous_decoy_rejected {X : Type u} :
    IsEmpty {R : CutsetRow X // ∀ x, R.Sentence x} :=
  ⟨fun ⟨R, h⟩ => R.violator_violates (h R.violator)⟩

/-- **Decoy.** A row whose blade is trivially true cannot be built. -/
theorem trivial_blade_decoy_rejected {X : Type u} :
    IsEmpty {R : CutsetRow X // ∀ x, R.Blade x} :=
  ⟨fun ⟨R, h⟩ => R.blade_kills_violator (h R.violator)⟩

/-! ## The blades -/

/-- **B1, statability.** A state space steps when it factors as a pattern times
itself: the recognizer has a floor above. -/
def Steps (S : Type u) (D : ℕ) : Prop :=
  Nonempty (S ≃ (Fin D → Bool) × S)

/-- The forced floor steps, in every dimension. -/
theorem floor_steps (D : ℕ) : Steps (Fin D → ℤ) D :=
  ⟨OctaveFloorStep.stepEquivD⟩

/-- **A finite non-empty state space does not step** once there is at least one
distinction per floor: its cardinality would have to be `2^D` times itself. -/
theorem finite_does_not_step (S : Type u) [Fintype S] [Nonempty S] {D : ℕ} (hD : 0 < D) :
    ¬ Steps S D := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  have hpos : 0 < Fintype.card S := Fintype.card_pos
  have h2 : (1 : ℕ) < 2 ^ D := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hD)
  have hlt : Fintype.card S < 2 ^ D * Fintype.card S := by
    calc Fintype.card S = 1 * Fintype.card S := (one_mul _).symm
      _ < 2 ^ D * Fintype.card S := Nat.mul_lt_mul_of_pos_right h2 hpos
  exact (ne_of_lt hlt) h

/-- **B2, least count.** Among positive counts the least is one. This is the
schema that fixed the unit at T2. -/
theorem least_positive_count : IsLeast {n : ℕ | 0 < n} 1 :=
  ⟨Nat.one_pos, fun _ hn => hn⟩

/-- **B3, record persistence.** Given a deformation relation on configurations,
a record is a configuration that deformation cannot move off itself. -/
def IsRecord {C : Type u} (Deform : C → C → Prop) (c : C) : Prop :=
  ∀ c', Deform c c' → c' = c

/-- A structure has records when some configuration is one. A structure in which
every configuration deforms to some other has none, hence no ledger. -/
def HasRecords {C : Type u} (Deform : C → C → Prop) : Prop :=
  ∃ c, IsRecord Deform c

/-- If deformation moves every configuration somewhere else, there are no records. -/
theorem no_records_of_everything_moves {C : Type u} (Deform : C → C → Prop)
    (h : ∀ c, ∃ c', Deform c c' ∧ c' ≠ c) : ¬ HasRecords Deform := by
  rintro ⟨c, hc⟩
  obtain ⟨c', hd, hne⟩ := h c
  exact hne (hc c' hd)

/-! ## The planted good row: the clock row in harness form -/

open Patterns PublicSpine.PartINamedAxiomClosure PublicSpine.ClockDischargeProbe
open ClockFromCompletion

/-- A closed pass of any length in any dimension. -/
abbrev Pass := (d : ℕ) × (T : ℕ) × (Fin T → Pattern d)

/-- The eight-tick Gray cycle as a candidate. -/
def gray8 : Pass := ⟨3, 8, grayCycle3Path⟩

/-- The period-two bounce as a candidate. -/
def bounce : Pass := ⟨3, 2, bouncePass⟩

/-- The clock row: candidates are non-empty closed passes; the sentence is the
Gray cover (complete, one bit per tick); the blade is the completion clock, a
definition (completed = one item of the floor above); the violator is the bounce. -/
def clockRow : CutsetRow Pass where
  Floor := fun x => 0 < x.2.1
  Sentence := fun x => GrayCoverSemanticModel x.2.2
  Blade := fun x => CompletionClock x.2.2
  provenance := .definition "completed = legible as one item of the floor above"
  real := gray8
  real_floor := by decide
  blade_real := completionClock_gray8
  violator := bounce
  violator_floor := by decide
  violator_violates := fun h => completionClock_rejects_bounce ((completionClock_iff_grayCover _).2 h)
  blade_kills_violator := completionClock_rejects_bounce
  exclusion := fun x _ hs hb => hs ((completionClock_iff_grayCover x.2.2).1 hb)

/-- The harness returns the clock theorem: any closed pass that is a completion
clock is a Gray cover. -/
theorem clockRow_forces : ∀ x : Pass, 0 < x.2.1 → CompletionClock x.2.2 → GrayCoverSemanticModel x.2.2 :=
  clockRow.forces

/-! ## Certificate -/

/-- The harness certificate: the decoys are rejected, the blades are stated with
their floor witnesses, and the clock row inhabits the harness. -/
structure Cert : Prop where
  vacuous_rejected : ∀ {X : Type} , IsEmpty {R : CutsetRow X // ∀ x, R.Sentence x}
  trivial_blade_rejected : ∀ {X : Type}, IsEmpty {R : CutsetRow X // ∀ x, R.Blade x}
  floor_steps : ∀ D, Steps (Fin D → ℤ) D
  finite_does_not_step : ∀ {D : ℕ}, 0 < D → ¬ Steps Bool D
  least_count : IsLeast {n : ℕ | 0 < n} 1
  clock_row_forces :
    ∀ x : Pass, 0 < x.2.1 → CompletionClock x.2.2 → GrayCoverSemanticModel x.2.2
  clock_row_class_nonempty : ∃ x : Pass, 0 < x.2.1 ∧ ¬ GrayCoverSemanticModel x.2.2

theorem cert : Cert where
  vacuous_rejected := vacuous_decoy_rejected
  trivial_blade_rejected := trivial_blade_decoy_rejected
  floor_steps := floor_steps
  finite_does_not_step := fun hD => finite_does_not_step Bool hD
  least_count := least_positive_count
  clock_row_forces := clockRow_forces
  clock_row_class_nonempty := clockRow.class_nonempty

end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
