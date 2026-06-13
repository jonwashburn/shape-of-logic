import IndisputableMonolith.Foundation.BiconditionalSelfNegation

/-!
# `GodelDissolution.lean` — Deprecated Backward-Compatibility Shim

**This file is a deprecated alias.** The canonical content has moved to
`IndisputableMonolith.Foundation.BiconditionalSelfNegation`, with theorem
names that honestly describe what is proved.

## Why the rename

The Lean theorems formerly named `self_ref_query_impossible`,
`general_self_ref_impossible`, `godel_dissolution_holds`, and
`complete_godel_dissolution` prove a classical-logic triviality: no real
configuration `c` can satisfy `(defect c = 0) ↔ ¬(defect c = 0)`, because
that is `P ↔ ¬P` and has no model in any classical system. This fact is
correct, but it is unrelated to Gödel's first incompleteness theorem.

A Gödel sentence is not `P ↔ ¬P`. It is `G ↔ ¬Prov_F(⌜G⌝)`, where `Prov_F`
is a syntactic provability predicate over Gödel numbers and `G` is a
sentence in the language of `F`. These are distinct propositions; the
biconditional is consistent (that is the whole point of Gödel I).
Treating a Gödel sentence as if it were `P ↔ ¬P` is a category error.

The historical labeling was therefore misleading. The substantive
categorical argument that Gödel I has no target inside the RS forcing
chain (it targets recursively axiomatized proof systems for arithmetic
that maintain a syntactic `Prov` predicate separately from semantic
`True`; RS does not maintain that separation) is a meta-level argument,
not a Lean theorem. See `papers/Godel_And_RS_Closure_Honest_Assessment_20260520.html`
for the honest accounting.

## Migration

Replace imports of `IndisputableMonolith.Foundation.GodelDissolution`
with `IndisputableMonolith.Foundation.BiconditionalSelfNegation` at your
convenience. The old names below are preserved as aliases so existing
code continues to build.

| Old name                            | New canonical name                                   |
|-------------------------------------|------------------------------------------------------|
| `GodelDissolution`                  | `BiconditionalSelfNegation`                          |
| `SelfRefQuery`                      | `SelfNegatingConfig`                                 |
| `GeneralSelfRefQuery`               | `GeneralSelfNegatingPredicate`                       |
| `self_ref_query_impossible`         | `no_self_negating_config`                            |
| `general_self_ref_impossible`       | `no_general_self_negating_predicate`                 |
| `self_ref_not_configuration`        | `no_self_negation_at_point`                          |
| `self_ref_not_rs_true`              | `self_negation_implies_false`                        |
| `GodelDissolutionTheorem`           | `ClassicalLogicAndUniqueMinimizerTheorem`            |
| `godel_dissolution_holds`           | `classical_logic_and_unique_minimizer_theorem`       |
| `complete_godel_dissolution`        | `complete_classical_logic_and_closure`               |
| `GodelRequirements`                 | `GodelTargetClassPrerequisites` (documentation only) |
| `RSDoesNotSatisfyGodel`             | `RsCategoricalDifferenceFromGodel` (documentation)   |
| `rs_avoids_godel`                   | `rs_categorical_difference_from_godel` (documentation)|

The names `RSStab`, `RSDiverge`, `RSOutside`, `stab_decidable`,
`diverge_impossible`, `config_classification` are unchanged; they
accurately describe what they are.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GodelDissolution

open Real
open LawOfExistence
open OntologyPredicates

/-! Re-export the canonical new names from `BiconditionalSelfNegation`
into the legacy `GodelDissolution` namespace, so existing files that do
`open Foundation.GodelDissolution` can use the new honest names without
changing their `open` statements. -/

export BiconditionalSelfNegation
  (SelfNegatingConfig GeneralSelfNegatingPredicate
   no_self_negating_config no_general_self_negating_predicate
   no_self_negation_at_point self_negation_implies_false
   ClassicalLogicAndUniqueMinimizerTheorem
   classical_logic_and_unique_minimizer_theorem
   complete_classical_logic_and_closure
   GodelTargetClassPrerequisites RsCategoricalDifferenceFromGodel
   rs_categorical_difference_from_godel)

/-! ## Re-exported stabilization predicates -/

/-- Re-export of `BiconditionalSelfNegation.RSStab`. -/
abbrev RSStab := BiconditionalSelfNegation.RSStab

/-- Re-export of `BiconditionalSelfNegation.RSDiverge`. -/
abbrev RSDiverge := BiconditionalSelfNegation.RSDiverge

/-- Re-export of `BiconditionalSelfNegation.RSOutside`. -/
abbrev RSOutside := BiconditionalSelfNegation.RSOutside

/-- Re-export of `BiconditionalSelfNegation.stab_decidable`. -/
theorem stab_decidable (c : ℝ) : RSStab c ∨ ¬RSStab c :=
  BiconditionalSelfNegation.stab_decidable c

/-- Re-export of `BiconditionalSelfNegation.diverge_impossible`. -/
theorem diverge_impossible (c : ℝ) : ¬RSDiverge c :=
  BiconditionalSelfNegation.diverge_impossible c

/-- Re-export of `BiconditionalSelfNegation.config_classification`. -/
theorem config_classification (c : ℝ) : RSStab c ∨ RSOutside c :=
  BiconditionalSelfNegation.config_classification c

/-! ## Re-exported structures (under deprecated names) -/

/-- **Deprecated.** Renamed to `BiconditionalSelfNegation.SelfNegatingConfig`.
Despite the historical name, this is not a model of a Gödel sentence.
A Gödel sentence is `G ↔ ¬Prov(⌜G⌝)`, which is consistent. This structure
encodes `P ↔ ¬P`, which is uninhabited. -/
@[deprecated "Renamed to BiconditionalSelfNegation.SelfNegatingConfig" (since := "2026-05-20")]
abbrev SelfRefQuery := BiconditionalSelfNegation.SelfNegatingConfig

/-- **Deprecated.** Renamed to `BiconditionalSelfNegation.GeneralSelfNegatingPredicate`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.GeneralSelfNegatingPredicate"
  (since := "2026-05-20")]
abbrev GeneralSelfRefQuery := BiconditionalSelfNegation.GeneralSelfNegatingPredicate

/-! ## Re-exported theorems (under deprecated names) -/

set_option linter.deprecated false in
/-- **Deprecated.** Renamed to `BiconditionalSelfNegation.no_self_negating_config`.
Proves that no real configuration satisfies `(defect c = 0) ↔ ¬(defect c = 0)`.
This is a classical-logic triviality; it does not address Gödel sentences. -/
@[deprecated "Renamed to BiconditionalSelfNegation.no_self_negating_config"
  (since := "2026-05-20")]
theorem self_ref_query_impossible : ¬∃ q : SelfRefQuery, True :=
  BiconditionalSelfNegation.no_self_negating_config

set_option linter.deprecated false in
/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.no_general_self_negating_predicate`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.no_general_self_negating_predicate"
  (since := "2026-05-20")]
theorem general_self_ref_impossible : ¬∃ q : GeneralSelfRefQuery, True :=
  BiconditionalSelfNegation.no_general_self_negating_predicate

/-- **Deprecated.** Renamed to `BiconditionalSelfNegation.no_self_negation_at_point`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.no_self_negation_at_point"
  (since := "2026-05-20")]
theorem self_ref_not_configuration (c : ℝ) :
    ¬((defect c = 0) ↔ ¬(defect c = 0)) :=
  BiconditionalSelfNegation.no_self_negation_at_point c

/-- **Deprecated.** Renamed to `BiconditionalSelfNegation.self_negation_implies_false`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.self_negation_implies_false"
  (since := "2026-05-20")]
theorem self_ref_not_rs_true
    (c : ℝ)
    (h_encodes : ∀ P : Prop, (P ↔ RSStab c) → (P ↔ ¬RSStab c) → False)
    (h_correct : RSStab c ↔ ¬RSStab c) :
    False :=
  BiconditionalSelfNegation.self_negation_implies_false c h_encodes h_correct

/-! ## Re-exported bundled theorem -/

/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.ClassicalLogicAndUniqueMinimizerTheorem`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.ClassicalLogicAndUniqueMinimizerTheorem"
  (since := "2026-05-20")]
abbrev GodelDissolutionTheorem :=
  BiconditionalSelfNegation.ClassicalLogicAndUniqueMinimizerTheorem

set_option linter.deprecated false in
/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.classical_logic_and_unique_minimizer_theorem`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.classical_logic_and_unique_minimizer_theorem"
  (since := "2026-05-20")]
theorem godel_dissolution_holds : GodelDissolutionTheorem :=
  BiconditionalSelfNegation.classical_logic_and_unique_minimizer_theorem

set_option linter.deprecated false in
/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.complete_classical_logic_and_closure`. -/
@[deprecated "Renamed to BiconditionalSelfNegation.complete_classical_logic_and_closure"
  (since := "2026-05-20")]
theorem complete_godel_dissolution :
    (¬∃ q : SelfRefQuery, True) ∧
    (∃! x : ℝ, RSExists x) ∧
    (∀ x : ℝ, RSExists x ↔ x = 1) ∧
    (∀ c : ℝ, RSStab c ∨ ¬RSStab c) :=
  BiconditionalSelfNegation.complete_classical_logic_and_closure

/-! ## Re-exported documentation-only structures -/

/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.GodelTargetClassPrerequisites`.
Documentation record, not a theorem. -/
@[deprecated "Renamed to BiconditionalSelfNegation.GodelTargetClassPrerequisites"
  (since := "2026-05-20")]
abbrev GodelRequirements :=
  BiconditionalSelfNegation.GodelTargetClassPrerequisites

/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.RsCategoricalDifferenceFromGodel`.
Documentation record, not a theorem. -/
@[deprecated "Renamed to BiconditionalSelfNegation.RsCategoricalDifferenceFromGodel"
  (since := "2026-05-20")]
abbrev RSDoesNotSatisfyGodel :=
  BiconditionalSelfNegation.RsCategoricalDifferenceFromGodel

set_option linter.deprecated false in
/-- **Deprecated.** Renamed to
`BiconditionalSelfNegation.rs_categorical_difference_from_godel`.
Documentation-only `def`, not a theorem. -/
@[deprecated "Renamed to BiconditionalSelfNegation.rs_categorical_difference_from_godel"
  (since := "2026-05-20")]
def rs_avoids_godel : RSDoesNotSatisfyGodel :=
  BiconditionalSelfNegation.rs_categorical_difference_from_godel

end GodelDissolution
end Foundation
end IndisputableMonolith
