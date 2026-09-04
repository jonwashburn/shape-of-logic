import Mathlib
import IndisputableMonolith.Foundation.NothingToDistinction
import IndisputableMonolith.Foundation.PublicSpine.PartINamedAxiomClosure

/-!
# Kernel closure census: the floor (T-2) and the clock

Two rows sit outside the kernel structure and belong on the ledger.

## The floor: which fragment of the ambient theory T-2 consumes

`Empty ≠ Unit` (`NothingToDistinction.nothing_ne_something`) has no lower
stratum inside the library; its terminal state is a statement of what it uses.
The census measures that fragment down to its floor:

* **One universe.** Both types live in `Type 0`; no universe hierarchy is used.
* **One inductive suffices.** `single_inductive_suffices` proves
  `Empty ≠ (Empty → Empty)`: the empty inductive together with function types
  already yields a distinction between two types. `Unit` is a convenience, not
  a requirement.
* **The empty inductive cannot be removed.** `ne_is_arrow_to_false` records
  that `α ≠ β` *is* `α = β → False` by definition. Any theory in which a
  distinction can be *stated* as an inequality contains the empty proposition.
  So there is no countermodel "one step below": a step below the empty type
  is a theory with no inequality in it, in which T-2 is not false but
  unstatable. That is the sense in which "there is no rung below the floor".
* **The Prop half** (`false_ne_true`) is the same fragment one universe down.

The exact fragment is therefore: one universe, the empty inductive, function
types, equality with transport. `#print axioms` on every row is empty. This
does not license "from nothing"; it names precisely what the nothing is.

## The clock: identification of the recognition clock with the cube pass

The public target `RecognitionClockIdentificationOpen` asks for a predicate on
passes `Fin T → Pattern d` that Gray-8 satisfies, that forces surjection, and
that is not surjection in disguise. The tree's terminal is the named-axiom class
`SemanticClockLaw` (`PartINamedAxiomClosure`): any member is a complete-pass
predicate that accepts Gray-8, forces surjection, rejects the six-post
reciprocal pass and rejects a surjective non-Gray cover. The class is inhabited
(`GrayCoverSemanticModel`), so the row is consistent, and its identification is
a MODEL choice.

This module records:

* **Decoys rejected by the class itself.** `decoy_false_rejected`: no member is
  the always-false predicate. `decoy_surjective_rejected`: no member is
  extensionally surjection.
* **A new obstruction on where the predicate can live.**
  `translation_invariant_step_rules_accept_bounce`: any step rule
  (a condition on consecutive states) that is invariant under the cube's
  translation symmetry and accepts Gray-8 also accepts the period-2 one-bit
  bounce, which is not surjective. Hence
  `no_step_rule_is_a_complete_pass_law`: no `SemanticClockLaw` member is a
  translation-invariant step rule. The complete-pass predicate must see more
  than one step at a time, or must break the cube's translation symmetry.
  This generalizes the killed posting-class route into a theorem and tells the
  next attack where not to look.

**Verdict.** Floor: statement, exact fragment named, axiom-free. Clock: the
residual named here (a recognition-native member) is supplied by
`KernelClosure.ClockFromCompletion` (2026-09-02): completion is occupying one
item of the floor above, the step is one post per tick, and coverage is a
theorem of the floor step. The row is MODEL under those two named readings, no
longer OPEN; the obstructions below still bind (local symmetric step laws are
excluded, and the member is not a step rule).
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace FloorAndClock

open Patterns
open PublicSpine
open PublicSpine.PartINamedAxiomClosure
open PublicSpine.ClockDischargeProbe

/-! ## The floor -/

/-- T-2 re-exported: initial and terminal objects of `Type` are distinct. -/
theorem t2_floor : NothingToDistinction.Nothing ≠ NothingToDistinction.Something :=
  NothingToDistinction.nothing_ne_something

/-- **One inductive suffices.** The empty type and the type of its
self-maps are distinct: the latter is inhabited by the identity. -/
theorem single_inductive_suffices : Empty ≠ (Empty → Empty) := by
  intro h
  have hn : Nonempty Empty := by
    rw [h]; exact ⟨id⟩
  obtain ⟨e⟩ := hn
  exact Empty.elim e

/-- **The empty inductive cannot be removed.** Inequality is, by definition, an
arrow into `False`. A theory without the empty proposition cannot state T-2. -/
theorem ne_is_arrow_to_false (α β : Type) : (α ≠ β) = (α = β → False) := rfl

/-- The Prop half of the floor, in the same fragment one universe down. -/
theorem false_ne_true : (False : Prop) ≠ True := by
  intro h
  exact h ▸ trivial

/-- The fragment T-2 consumes, as data: one universe (`Type 0`), the empty
inductive, function types, equality. Each field is inhabited by a proof in
that fragment alone. -/
structure T2Fragment : Prop where
  one_universe : (Empty : Type) ≠ (Unit : Type)
  one_inductive : Empty ≠ (Empty → Empty)
  inequality_is_arrow_to_false : ∀ α β : Type, (α ≠ β) = (α = β → False)
  prop_half : (False : Prop) ≠ True

theorem t2Fragment_holds : T2Fragment where
  one_universe := NothingToDistinction.nothing_ne_something
  one_inductive := single_inductive_suffices
  inequality_is_arrow_to_false := ne_is_arrow_to_false
  prop_half := false_ne_true

/-! ## The clock: the terminal class and its decoys -/

/-- The named-axiom class is inhabited, so the clock row is consistent. -/
theorem clock_class_inhabited : Nonempty SemanticClockLaw :=
  semanticClockLaw_nonempty

/-- Decoy `P := False` is rejected: every member accepts Gray-8. -/
theorem decoy_false_rejected :
    ¬ ∃ K : SemanticClockLaw,
      ∀ {d T : ℕ} (pass : Fin T → Pattern d), K.completePass pass ↔ False := by
  rintro ⟨K, hK⟩
  exact (hK grayCycle3Path).mp K.gray8_complete

/-- Decoy `P := Surjective` is rejected: every member refuses a surjective
non-Gray cover. -/
theorem decoy_surjective_rejected :
    ¬ ∃ K : SemanticClockLaw,
      ∀ {d T : ℕ} (pass : Fin T → Pattern d),
        K.completePass pass ↔ Function.Surjective pass := by
  rintro ⟨K, hK⟩
  obtain ⟨hsurj, _, hnot⟩ := K.nonGray_surjection_rejected
  exact hnot ((hK jumpCover).mpr hsurj)

/-! ## The clock: local symmetric step rules are excluded -/

/-- Translation of a pattern by `v` (coordinatewise exclusive or). -/
def xorPat {d : ℕ} (v p : Pattern d) : Pattern d := fun i => xor (v i) (p i)

/-- A relation on patterns is translation-invariant when it is preserved by
every translation of the cube. -/
def TranslationInvariant {d : ℕ} (R : Pattern d → Pattern d → Prop) : Prop :=
  ∀ (v a b : Pattern d), R a b → R (xorPat v a) (xorPat v b)

/-- A step rule: a pass is accepted iff every consecutive pair of states
satisfies `R`. -/
def StepRule {d T : ℕ} [NeZero T] (R : Pattern d → Pattern d → Prop)
    (pass : Fin T → Pattern d) : Prop :=
  ∀ t : Fin T, R (pass t) (pass (t + 1))

theorem gray_step_zero : grayCycle3Path 0 = bounceA ∧ grayCycle3Path 1 = bounceB := by
  constructor
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

theorem xorPat_bounceB_bounceA : xorPat bounceB bounceA = bounceB := by
  funext i; fin_cases i <;> rfl

theorem xorPat_bounceB_bounceB : xorPat bounceB bounceB = bounceA := by
  funext i; fin_cases i <;> rfl

/-- **Obstruction.** A translation-invariant step rule that accepts Gray-8
accepts the period-2 one-bit bounce. -/
theorem translation_invariant_step_rules_accept_bounce
    (R : Pattern 3 → Pattern 3 → Prop) (hR : TranslationInvariant R)
    (hgray : StepRule R grayCycle3Path) : StepRule R bouncePass := by
  obtain ⟨h0, h1⟩ := gray_step_zero
  have hAB : R bounceA bounceB := by
    have := hgray 0
    rwa [h0, show (0 : Fin 8) + 1 = 1 from rfl, h1] at this
  have hBA : R bounceB bounceA := by
    have := hR bounceB _ _ hAB
    rwa [xorPat_bounceB_bounceA, xorPat_bounceB_bounceB] at this
  intro t
  fin_cases t
  · exact hAB
  · exact hBA

/-- **No step rule is a complete-pass law.** No member of the clock class is
extensionally a translation-invariant step rule on `Pattern 3`: such a rule
would accept the bounce, and the law forces surjection. -/
theorem no_step_rule_is_a_complete_pass_law :
    ¬ ∃ (K : SemanticClockLaw) (R : Pattern 3 → Pattern 3 → Prop),
      TranslationInvariant R ∧
        ∀ {T : ℕ} [NeZero T] (pass : Fin T → Pattern 3),
          K.completePass pass ↔ StepRule R pass := by
  rintro ⟨K, R, hR, hK⟩
  have hgray : StepRule R grayCycle3Path := (hK grayCycle3Path).mp K.gray8_complete
  have hbounce : K.completePass bouncePass :=
    (hK bouncePass).mpr (translation_invariant_step_rules_accept_bounce R hR hgray)
  exact bouncePass_not_surjective (K.forces_surjective bouncePass hbounce)

/-- The obstruction is not vacuous: the one-bit adjacency rule is a
translation-invariant step rule that Gray-8 satisfies. -/
theorem oneBit_rule_is_translation_invariant :
    TranslationInvariant (fun p q : Pattern 3 => OneBitDiff p q) ∧
      StepRule (fun p q : Pattern 3 => OneBitDiff p q) grayCycle3Path := by
  refine ⟨?_, grayCycle3_oneBit_step⟩
  intro v a b hab
  obtain ⟨k, hk, huniq⟩ := hab
  refine ⟨k, ?_, ?_⟩
  · simp only [xorPat]
    intro h
    apply hk
    cases hv : v k <;> cases ha : a k <;> cases hb : b k <;> simp_all
  · intro j hj
    apply huniq
    simp only [xorPat] at hj
    intro h
    apply hj
    rw [h]

/-! ## Row certificate -/

structure FloorAndClockCert : Prop where
  floor : T2Fragment
  clock_inhabited : Nonempty SemanticClockLaw
  clock_not_false :
    ¬ ∃ K : SemanticClockLaw,
      ∀ {d T : ℕ} (pass : Fin T → Pattern d), K.completePass pass ↔ False
  clock_not_surjective :
    ¬ ∃ K : SemanticClockLaw,
      ∀ {d T : ℕ} (pass : Fin T → Pattern d),
        K.completePass pass ↔ Function.Surjective pass
  clock_not_step_rule :
    ¬ ∃ (K : SemanticClockLaw) (R : Pattern 3 → Pattern 3 → Prop),
      TranslationInvariant R ∧
        ∀ {T : ℕ} [NeZero T] (pass : Fin T → Pattern 3),
          K.completePass pass ↔ StepRule R pass
  obstruction_nonvacuous :
    TranslationInvariant (fun p q : Pattern 3 => OneBitDiff p q) ∧
      StepRule (fun p q : Pattern 3 => OneBitDiff p q) grayCycle3Path

theorem FloorAndClockCert_holds : FloorAndClockCert where
  floor := t2Fragment_holds
  clock_inhabited := clock_class_inhabited
  clock_not_false := decoy_false_rejected
  clock_not_surjective := decoy_surjective_rejected
  clock_not_step_rule := no_step_rule_is_a_complete_pass_law
  obstruction_nonvacuous := oneBit_rule_is_translation_invariant

end FloorAndClock
end KernelClosure
end Foundation
end IndisputableMonolith
