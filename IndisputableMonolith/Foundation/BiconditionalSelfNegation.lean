import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.OntologyPredicates

/-!
# Biconditional Self-Negation: No Real Configuration Satisfies `P ↔ ¬P`

This module proves the classical-logic fact that no real-valued configuration can
satisfy a biconditional of the form `(defect c = 0) ↔ ¬(defect c = 0)`, together
with a few corollaries about stabilization status and the unique zero-defect
existent at `x = 1`.

## What this module actually proves

For any real `c`, the proposition `(defect c = 0) ↔ ¬(defect c = 0)` is
inhabited iff `False`. The proof is a two-line case split on excluded middle.

The same fact holds for any predicate `P`: classical logic has no fixed point
for negation. The phenomenon is propositional-logic content, not anything
specific to Recognition Science.

## What this module does NOT prove

**It does not address Gödel's first incompleteness theorem.**

Gödel sentences do not satisfy `P ↔ ¬P`. They satisfy `G ↔ ¬Prov_F(⌜G⌝)`, where
`Prov_F(⌜G⌝)` is a syntactic predicate over Gödel numbers and `G` is a sentence
in the language of `F`. These are distinct propositions; the biconditional is
consistent; that is the entire point of Gödel I.

A logic-trained reader who sees the structure here labeled as a "Gödel
dissolution" will reject the framing immediately. The historical filename
`GodelDissolution.lean` was misleading. The canonical home is this module;
the old file remains as a backward-compatibility shim with the same theorem
content under deprecated names.

The categorical argument for why Gödel I has no target inside the Recognition
Science forcing chain (T-1 → T0 → ... → T8 → constants) lives at the
meta-level and is not a Lean theorem. See
`papers/Godel_And_RS_Closure_Honest_Assessment_20260520.html` for the
honest accounting.

## Cross-references

- `LawOfExistence.defect_at_one`, `LawOfExistence.defect_pos_of_ne_one`:
  the substantive content about the cost functional.
- `OntologyPredicates.rs_exists_unique`: the unique zero-defect existent.
- `papers/godel_dissolution.tex`: the philosophical paper. The Lean module
  here proves only the propositional logic; the categorical argument is in
  the paper.
-/

namespace IndisputableMonolith
namespace Foundation
namespace BiconditionalSelfNegation

open Real
open LawOfExistence
open OntologyPredicates

/-! ## Stabilization predicates (preserved from earlier API)

These predicates are about real-valued configurations and are correctly named.
They are re-exported by the legacy `GodelDissolution` namespace.
-/

/-- A real configuration "stabilizes" iff its defect vanishes. -/
def RSStab (c : ℝ) : Prop := defect c = 0

/-- A real configuration "diverges" iff its defect exceeds every bound. -/
def RSDiverge (c : ℝ) : Prop := ∀ C : ℝ, defect c > C

/-- A real configuration is "outside the stabilization classification" iff it
neither stabilizes nor diverges. By `diverge_impossible` below, this reduces
to "non-stabilizing" for real-valued configurations. -/
def RSOutside (c : ℝ) : Prop := ¬RSStab c ∧ ¬RSDiverge c

/-- Decidability of stabilization status for real configurations. Classical. -/
theorem stab_decidable (c : ℝ) : RSStab c ∨ ¬RSStab c :=
  em (RSStab c)

/-- Divergence in the sense of "exceeds every real bound" is vacuous for any
real-valued defect: take the bound equal to the defect itself. -/
theorem diverge_impossible (c : ℝ) : ¬RSDiverge c := by
  intro h
  have : defect c > defect c := h (defect c)
  linarith

/-- Every real configuration either stabilizes or fails to stabilize. The
extra `RSOutside` clause is included for compatibility with the legacy API;
by `diverge_impossible` it adds no content. -/
theorem config_classification (c : ℝ) : RSStab c ∨ RSOutside c := by
  by_cases hs : RSStab c
  · exact Or.inl hs
  · exact Or.inr ⟨hs, diverge_impossible c⟩

/-! ## The biconditional-self-negation structures

The first structure encodes a real configuration claiming
`(defect c = 0) ↔ ¬(defect c = 0)`. The classical-logic fact below shows
no such configuration can exist.

The second structure encodes a more general predicate-level biconditional
self-negation. The same classical fact applies.

Neither structure corresponds to a Gödel sentence in any technical sense.
Both are propositional-logic content.
-/

/-- A real configuration claiming the biconditional self-negation
`(defect c = 0) ↔ ¬(defect c = 0)`.

By classical logic this structure has no inhabitants. Despite the historical
naming (`SelfRefQuery`), this is not a model of Gödel-style self-reference.
A Gödel sentence is not `P ↔ ¬P`; it is `P ↔ ¬Q(⌜P⌝)` with `Q` a syntactic
provability predicate, and that biconditional is consistent. -/
structure SelfNegatingConfig where
  /-- The underlying real configuration. -/
  config : ℝ
  /-- The biconditional self-negation. This field is inhabited iff `False`. -/
  self_negation : (defect config = 0) ↔ ¬(defect config = 0)

/-- A general predicate-level biconditional self-negation. The fields together
encode `RSStab c ↔ asserts ↔ ¬RSStab c`, which collapses to `RSStab c ↔ ¬RSStab c`,
which is `P ↔ ¬P` and has no inhabitant. -/
structure GeneralSelfNegatingPredicate where
  /-- The underlying real configuration. -/
  config : ℝ
  /-- An associated proposition. -/
  asserts : Prop
  /-- That proposition is the negation of the stabilization status. -/
  encodes_negation : asserts ↔ ¬RSStab config
  /-- The configuration's stabilization status agrees with the proposition. -/
  correctness : RSStab config ↔ asserts

/-! ## The main theorems

These are classical-logic facts. They are correctly proved; they should not
be cited as resolutions of Gödel's incompleteness theorem.
-/

/-- **Classical-logic fact.** No real configuration satisfies
`(defect c = 0) ↔ ¬(defect c = 0)`. Two-line proof by excluded middle. -/
theorem no_self_negating_config : ¬∃ q : SelfNegatingConfig, True := by
  intro ⟨q, _⟩
  have h := q.self_negation
  by_cases hd : defect q.config = 0
  · exact (h.mp hd) hd
  · exact hd (h.mpr hd)

/-- **Classical-logic fact.** No real configuration carries a general
predicate-level biconditional self-negation. -/
theorem no_general_self_negating_predicate :
    ¬∃ q : GeneralSelfNegatingPredicate, True := by
  intro ⟨q, _⟩
  have h1 := q.correctness
  have h2 := q.encodes_negation
  have h : RSStab q.config ↔ ¬RSStab q.config := h1.trans h2
  by_cases hs : RSStab q.config
  · exact (h.mp hs) hs
  · exact hs (h.mpr hs)

/-- Pointwise classical version. For every real `c`,
`(defect c = 0) ↔ ¬(defect c = 0)` is uninhabited. -/
theorem no_self_negation_at_point (c : ℝ) :
    ¬((defect c = 0) ↔ ¬(defect c = 0)) := by
  intro h
  by_cases hd : defect c = 0
  · exact (h.mp hd) hd
  · exact hd (h.mpr hd)

/-- A redundant compatibility statement: if a real `c` admitted a
biconditional self-negation, then `False`. Equivalent to
`no_self_negation_at_point`; kept for legacy API. -/
theorem self_negation_implies_false
    (c : ℝ)
    (_h_encodes : ∀ P : Prop, (P ↔ RSStab c) → (P ↔ ¬RSStab c) → False)
    (h_correct : RSStab c ↔ ¬RSStab c) :
    False := by
  by_cases hs : RSStab c
  · exact (h_correct.mp hs) hs
  · exact hs (h_correct.mpr hs)

/-! ## Bundled theorem (formerly `GodelDissolutionTheorem`)

The bundle collects four genuine facts:

1. No `SelfNegatingConfig` exists (classical logic).
2. No `GeneralSelfNegatingPredicate` exists (classical logic).
3. Every real configuration has definite stabilization status (classical
   excluded middle).
4. There exists a unique real `x > 0` with zero defect, namely `x = 1`
   (substantive cost-uniqueness content).

Item 4 is the only substantive RS content. The other three are propositional
logic. The bundle was historically called `GodelDissolutionTheorem`; that
name overstates what items 1-3 do.
-/

/-- Bundled classical-logic-and-unique-minimizer theorem. -/
structure ClassicalLogicAndUniqueMinimizerTheorem where
  /-- Classical: no real configuration satisfies `(defect = 0) ↔ ¬(defect = 0)`. -/
  no_self_negating_config : ¬∃ q : SelfNegatingConfig, True
  /-- Classical: no real configuration carries a general biconditional self-negation. -/
  no_general_self_negating_predicate : ¬∃ q : GeneralSelfNegatingPredicate, True
  /-- Classical: every real configuration has definite stabilization status. -/
  definite_status : ∀ c : ℝ, RSStab c ∨ ¬RSStab c
  /-- Substantive: the RS closure picks out a unique positive existent. -/
  rs_closure_meaning : ∃! x : ℝ, RSExists x

/-- The bundled theorem holds. -/
theorem classical_logic_and_unique_minimizer_theorem :
    ClassicalLogicAndUniqueMinimizerTheorem := {
  no_self_negating_config := no_self_negating_config
  no_general_self_negating_predicate := no_general_self_negating_predicate
  definite_status := stab_decidable
  rs_closure_meaning := rs_exists_unique
}

/-- The complete bundle: classical-logic facts plus the unique-existent value
`x = 1`. Was historically called `complete_godel_dissolution`. The Gödel
framing was wrong; the content is correct. -/
theorem complete_classical_logic_and_closure :
    -- Self-negating configurations impossible
    (¬∃ q : SelfNegatingConfig, True) ∧
    -- Unique RS-existent
    (∃! x : ℝ, RSExists x) ∧
    -- That existent is unity
    (∀ x : ℝ, RSExists x ↔ x = 1) ∧
    -- Every config has definite status
    (∀ c : ℝ, RSStab c ∨ ¬RSStab c) :=
  ⟨no_self_negating_config, rs_exists_unique, rs_exists_unique_one, stab_decidable⟩

/-! ## Documentation-only structures (formerly `GodelRequirements`, `RSDoesNotSatisfyGodel`)

The structures below carry no theorem content. Each field is `Prop`; the
canonical inhabitant has every field set to `True`. They are Lean records of
philosophical / categorical claims, not theorems. Reviewers reading the
older naming may have mistaken them for proved propositions; they are
not.

If you want the genuine categorical argument (RS does not separately
maintain `Prov` and `True` predicates, so the gap exploited by Gödel I
does not arise), it lives in the prose of the companion paper, not here.
-/

/-- Documentation-only record of the standard prerequisites Gödel's first
incompleteness theorem requires of a target system. Each field is a `Prop`
placeholder; this structure carries no theorem content. -/
structure GodelTargetClassPrerequisites where
  /-- The target is a formal system. -/
  formal_system : Type
  /-- The target is consistent. -/
  consistent : Prop
  /-- The target's axiom set is computably enumerable. -/
  axiom_enumerable : Prop
  /-- The target expresses sufficient arithmetic. -/
  expresses_arithmetic : Prop
  /-- The target internally expresses its own provability predicate. -/
  expresses_provability : Prop

/-- Documentation-only record of the structural differences between
Recognition Science and Gödel-I's target class. Each field is `Prop`;
the canonical inhabitant has every field set to `True`. This carries no
theorem content. -/
structure RsCategoricalDifferenceFromGodel where
  /-- RS is selection dynamics, not a proof system. -/
  not_proof_system : Prop
  /-- RS truth is stabilization, not Tarskian satisfaction. -/
  not_tarskian : Prop
  /-- RS truth is internal, no external model required. -/
  no_external_model : Prop

/-- Canonical inhabitant of `RsCategoricalDifferenceFromGodel` with every
philosophical field set to `True`. The structure is documentation, not a
theorem. -/
def rs_categorical_difference_from_godel : RsCategoricalDifferenceFromGodel := {
  not_proof_system := True
  not_tarskian := True
  no_external_model := True
}

end BiconditionalSelfNegation
end Foundation
end IndisputableMonolith
