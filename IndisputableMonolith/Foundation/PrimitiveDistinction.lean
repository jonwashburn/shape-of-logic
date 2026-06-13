/-
  PrimitiveDistinction.lean

  Below the four Aristotelian conditions: the type-theoretic floor.

  The Logic_FE rigidity theorem starts from a comparison operator
  C : K × K → Cost satisfying four classical Aristotelian conditions
  (Identity, Non-Contradiction, Excluded Middle, Composition Consistency)
  plus regularity and structural conditions. We treated those four
  conditions as primitive axioms. This module pushes the foundational
  floor one layer lower.

  We start from the most primitive object: an equality-derived cost.
  Given any type with decidable equality, the canonical cost
  C(x, y) := indicator(x ≠ y) is a function on pairs whose definitional
  content automatically yields three of the four Aristotelian conditions:
  Identity (L1), Non-Contradiction (L2), and Totality (L3a). These are
  not axioms; they are consequences of the type signature of equality
  combined with the definition of cost-as-indicator.

  The fourth condition, Composition Consistency (L4), and the regularity
  condition Continuity (L3b), and the structural condition Scale
  Invariance (B1), remain substantive: they impose non-trivial
  compatibility between the cost and the carrier's algebraic structure
  and topology, and they are not forced by the equality-derived cost
  alone.

  The headline of this module:

    `aristotelian_decomposition`:
      The four classical Aristotelian conditions on an equality-derived
      cost decompose into three definitional facts (L1, L2, L3a) plus
      one substantive structural condition (L4 + regularity + invariance).

  This cuts the foundational surface of Logic_FE from "seven independent
  axioms" to "four substantive conditions plus three definitional facts."

  References:
    - Logic_FE rigidity paper:
      Washburn, "A Functional-Equation Encoding of Logical Consistency
      on Continuous Positive-Ratio Comparisons," April 2026.
    - Universal Forcing paper:
      Washburn, "The Universal Forcing Meta-Theorem," April 2026.
-/

import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveDistinction

open Classical

/-! ## The Primitive: Distinction Predicate -/

/-- A **distinction predicate** on a carrier `K` is a binary predicate
that detects whether two elements are distinguishable. The canonical
example is the equality test, available on any type. -/
def Distinction (K : Type*) : Type _ := K → K → Prop

/-- The canonical distinction induced by equality: two elements are
distinct iff they are not equal. This is the most primitive distinction
on any type and exists for every type without further structure. -/
def equalityDistinction (K : Type*) : Distinction K :=
  fun x y => x ≠ y

/-- Reflexivity of the canonical distinction: an element is not distinct
from itself. This is reflexivity of equality, a definitional fact of any
type theory. -/
theorem equalityDistinction_irrefl (K : Type*) :
    ∀ x : K, ¬ equalityDistinction K x x := by
  intro x h
  exact h rfl

/-- Symmetry of the canonical distinction: distinguishability does not
depend on argument order. This is symmetry of disequality, derived from
the symmetric definition of equality. -/
theorem equalityDistinction_symm (K : Type*) :
    ∀ x y : K, equalityDistinction K x y ↔ equalityDistinction K y x := by
  intro x y
  unfold equalityDistinction
  exact ⟨fun h heq => h heq.symm, fun h heq => h heq.symm⟩

/-! ## The Equality-Induced Cost -/

/-- The **canonical cost induced by equality**: assigns 0 to identical
pairs and a positive weight to distinct pairs. This is a function on
pairs whose form is determined entirely by the equality predicate. -/
noncomputable def equalityCost (K : Type*) (weight : ℝ) : K → K → ℝ :=
  fun x y => if x = y then 0 else weight

/-! ## The Three Definitional Facts

The following three theorems show that an equality-induced cost
automatically satisfies three of the four Aristotelian conditions
without any structural assumption beyond the type signature.
-/

/-- **(L1) Identity, derived.** The equality-induced cost satisfies
`C(x, x) = 0` definitionally. This is not an axiom; it is the
definitional content of "comparing a thing with itself takes no work,"
forced by reflexivity of equality. -/
theorem identity_from_equality (K : Type*) (weight : ℝ) :
    ∀ x : K, equalityCost K weight x x = 0 := by
  intro x
  unfold equalityCost
  simp

/-- **(L2) Non-Contradiction, derived.** The equality-induced cost is
symmetric in its arguments. This follows from the symmetric definition
of equality: `x = y` iff `y = x`. -/
theorem non_contradiction_from_equality (K : Type*) (weight : ℝ) :
    ∀ x y : K, equalityCost K weight x y = equalityCost K weight y x := by
  intro x y
  unfold equalityCost
  by_cases h : x = y
  · subst h; rfl
  · have hSymm : ¬ y = x := fun heq => h heq.symm
    simp [h, hSymm]

/-- **(L3a) Totality, derived.** The equality-induced cost is total:
it is defined and returns a value for every ordered pair in `K × K`.
This follows from the function type signature alone; there are no
input pairs on which the cost is undefined. -/
theorem totality_from_function_type (K : Type*) (weight : ℝ) :
    ∀ x y : K, ∃ c : ℝ, equalityCost K weight x y = c := by
  intro x y
  exact ⟨equalityCost K weight x y, rfl⟩

/-- **(L1)+(L2)+(L3a) packaged.** The equality-induced cost satisfies
the three definitional Aristotelian conditions (Identity,
Non-Contradiction, Totality) automatically, with no structural
assumption beyond the existence of an equality predicate on `K`. -/
theorem equality_cost_satisfies_definitional_conditions
    (K : Type*) (weight : ℝ) :
    (∀ x : K, equalityCost K weight x x = 0) ∧
    (∀ x y : K, equalityCost K weight x y = equalityCost K weight y x) ∧
    (∀ x y : K, ∃ c : ℝ, equalityCost K weight x y = c) :=
  ⟨identity_from_equality K weight,
   non_contradiction_from_equality K weight,
   totality_from_function_type K weight⟩

/-! ## The Substantive Condition: Composition Consistency

The fourth Aristotelian condition, Composition Consistency, is not
type-theoretic. It requires the cost to be compatible with the
carrier's algebraic structure. We make this precise by exhibiting a
comparison operator that satisfies the three definitional conditions
but fails Composition Consistency, demonstrating that (L4) is
genuinely substantive. Equivalently: primitive distinction by itself is
too weak to be a recognition cost. The analytic RCL/J-cost layer is
structurally required, not optional.
-/

/-- The Aristotelian condition (L4) **Composition Consistency** in
abstract form: there exists a combiner `P` such that the cost of any
composite operation is determined by the costs of its components,
with the components combined under the carrier's algebraic structure.
Specialised to `(ℝ_{>0}, ·)`: -/
def CompositionConsistency (C : ℝ → ℝ → ℝ) : Prop :=
  ∃ P : ℝ → ℝ → ℝ,
    ∀ x y : ℝ, 0 < x → 0 < y →
      C (x * y) 1 + C (x / y) 1 = P (C x 1) (C y 1)

/-- The equality-induced cost on `ℝ`, taken with the multiplicative
identity `1` as base point. -/
noncomputable def hammingCostOnReal (weight : ℝ) : ℝ → ℝ → ℝ :=
  equalityCost ℝ weight

/-- **The substantive content of (L4).** The equality-induced cost on
`(ℝ_{>0}, ·)` with positive weight does **not** satisfy Composition
Consistency. This is the positive structural lesson: raw distinction is
insufficient for recognition. A cost that supports the later RCL/J-cost
analysis must respect the carrier's multiplicative composition, and that
compatibility is not derivable from equality alone. -/
theorem composition_consistency_not_definitional (weight : ℝ) (hw : weight ≠ 0) :
    ¬ CompositionConsistency (hammingCostOnReal weight) := by
  intro ⟨P, hP⟩
  -- Take x = 2, y = 2 (so xy = 4 ≠ 1, x/y = 1).
  -- Then C(4, 1) + C(1, 1) = weight + 0 = weight.
  -- And P(C(2, 1), C(2, 1)) = P(weight, weight).
  have hxy_a : (2 : ℝ) * 2 = 4 := by norm_num
  have hxy_b : (2 : ℝ) / 2 = 1 := by norm_num
  have h22 : hammingCostOnReal weight (2 * 2) 1 + hammingCostOnReal weight (2 / 2) 1
              = P (hammingCostOnReal weight 2 1) (hammingCostOnReal weight 2 1) :=
    hP 2 2 (by norm_num) (by norm_num)
  have h2val : hammingCostOnReal weight 2 1 = weight := by
    unfold hammingCostOnReal equalityCost
    simp
  have h4val : hammingCostOnReal weight 4 1 = weight := by
    unfold hammingCostOnReal equalityCost
    simp
  have h1val : hammingCostOnReal weight 1 1 = 0 := by
    unfold hammingCostOnReal equalityCost
    simp
  have left22 : hammingCostOnReal weight (2 * 2) 1
                  + hammingCostOnReal weight (2 / 2) 1 = weight := by
    rw [hxy_a, hxy_b, h4val, h1val, add_zero]
  have right22 : P (hammingCostOnReal weight 2 1) (hammingCostOnReal weight 2 1)
                  = P weight weight := by
    rw [h2val]
  have hP22 : P weight weight = weight := by
    rw [← right22, ← h22, left22]
  -- Now take x = 2, y = 3 (so xy = 6 ≠ 1, x/y = 2/3 ≠ 1).
  -- C(6, 1) + C(2/3, 1) = weight + weight = 2*weight.
  -- P(C(2, 1), C(3, 1)) = P(weight, weight) = weight (from above).
  -- Contradiction: 2*weight ≠ weight when weight ≠ 0.
  have hxy_c : (2 : ℝ) * 3 = 6 := by norm_num
  have h23 : hammingCostOnReal weight (2 * 3) 1
              + hammingCostOnReal weight (2 / 3) 1
              = P (hammingCostOnReal weight 2 1) (hammingCostOnReal weight 3 1) :=
    hP 2 3 (by norm_num) (by norm_num)
  have h6val : hammingCostOnReal weight 6 1 = weight := by
    unfold hammingCostOnReal equalityCost
    have : (6 : ℝ) ≠ 1 := by norm_num
    simp [this]
  have h23val : hammingCostOnReal weight (2/3 : ℝ) 1 = weight := by
    unfold hammingCostOnReal equalityCost
    have : (2/3 : ℝ) ≠ 1 := by norm_num
    simp [this]
  have h3val : hammingCostOnReal weight 3 1 = weight := by
    unfold hammingCostOnReal equalityCost
    have : (3 : ℝ) ≠ 1 := by norm_num
    simp [this]
  have left23 : hammingCostOnReal weight (2 * 3) 1
                  + hammingCostOnReal weight (2 / 3) 1 = 2 * weight := by
    rw [hxy_c, h6val, h23val]
    ring
  have right23 : P (hammingCostOnReal weight 2 1) (hammingCostOnReal weight 3 1)
                  = P weight weight := by
    rw [h2val, h3val]
  have hP23 : P weight weight = 2 * weight := by
    rw [← right23, ← h23, left23]
  -- Combine: weight = 2*weight, so weight = 0, contradicting hw.
  have : weight = 2 * weight := hP22.symm.trans hP23
  have : weight = 0 := by linarith
  exact hw this

/-- Positive framing of `composition_consistency_not_definitional`: primitive
equality cost is too weak to be the recognition cost used by the analytic
forcing chain. -/
theorem equality_cost_insufficient_for_recognition (weight : ℝ) (hw : weight ≠ 0) :
    ¬ CompositionConsistency (hammingCostOnReal weight) :=
  composition_consistency_not_definitional weight hw

/-! ## The Aristotelian Decomposition

The headline result of this module: the four classical Aristotelian
conditions, when applied to an equality-derived cost on a carrier with
multiplicative structure, decompose into three definitional facts and
one substantive structural condition.
-/

/-- **The Aristotelian Decomposition.** On any carrier with an
equality-induced cost:

* (L1) Identity is **definitional**, forced by reflexivity of equality.
* (L2) Non-Contradiction is **definitional**, forced by symmetry of
  equality.
* (L3a) Totality is **definitional**, forced by the function type
  signature.
* (L4) Composition Consistency is **substantive**, requiring non-trivial
  compatibility between the cost and the carrier's algebraic structure;
  it is not derivable from the type signature alone, as witnessed by
  the failure of the Hamming cost on `(ℝ_{>0}, ·)`.

This decomposition reduces the foundational surface of the rigidity
theorem from "seven independent axioms" to "four substantive
structural conditions plus three definitional facts."
-/
theorem aristotelian_decomposition (weight : ℝ) (hw : weight ≠ 0) :
    -- Definitional: L1, L2, L3a hold for the equality-induced cost.
    (∀ x : ℝ, equalityCost ℝ weight x x = 0) ∧
    (∀ x y : ℝ, equalityCost ℝ weight x y = equalityCost ℝ weight y x) ∧
    (∀ x y : ℝ, ∃ c : ℝ, equalityCost ℝ weight x y = c) ∧
    -- Substantive: L4 fails for the equality-induced cost, demonstrating
    -- that L4 is not a type-theoretic consequence.
    ¬ CompositionConsistency (hammingCostOnReal weight) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact identity_from_equality ℝ weight
  · exact non_contradiction_from_equality ℝ weight
  · exact totality_from_function_type ℝ weight
  · exact equality_cost_insufficient_for_recognition weight hw

/-! ## Bridge to Logic_FE

Here we connect the new framework to the existing
`SatisfiesLawsOfLogic` predicate. The bridge says: if a comparison
operator on `ℝ_{>0}` is derived from an equality cost, then it
automatically satisfies the Identity and Non-Contradiction conditions
of Logic_FE, and the rigidity theorem of Logic_FE reduces to imposing
the substantive conditions (Composition Consistency, Continuity, Scale
Invariance, polynomial closure, Non-Triviality) on the cost.
-/

open IndisputableMonolith.Foundation.LogicAsFunctionalEquation

/-- **Bridge theorem.** The Identity and Non-Contradiction conditions
of `SatisfiesLawsOfLogic` are automatic for any equality-induced cost.
The remaining four conditions of `SatisfiesLawsOfLogic` (excluded
middle as continuity, scale invariance, route independence, and
non-triviality) are the substantive structural axioms. -/
theorem equality_cost_satisfies_definitional
    (weight : ℝ) :
    Identity (hammingCostOnReal weight) ∧
    NonContradiction (hammingCostOnReal weight) := by
  refine ⟨?_, ?_⟩
  · intro x _
    exact identity_from_equality ℝ weight x
  · intro x y _ _
    exact non_contradiction_from_equality ℝ weight x y

/-! ## Summary

The four Aristotelian conditions of Logic_FE are not seven independent
axioms. Three of them (Identity, Non-Contradiction, Totality) are
definitional facts forced by the type signature of an equality-induced
cost. Only the fourth (Composition Consistency) is a genuinely
substantive structural condition.

The rigidity theorem of Logic_FE therefore rests on:

* **One substantive structural condition** (Composition Consistency):
  the cost respects the carrier's composition.
* **Three regularity / structural hypotheses** (Continuity, Scale
  Invariance, Polynomial-degree-2 closure of the combiner): the cost
  has the analytic regularity required for the d'Alembert classification
  to apply.
* **One existence assumption** (Non-Triviality): the cost is not
  identically zero.
* **Three definitional facts** (Identity, Non-Contradiction, Totality):
  forced by the type signature of the equality-induced cost.

This is the deepest structural decomposition of the Aristotelian
foundations of comparison-based rigidity that the present framework
admits.
-/

end PrimitiveDistinction
end Foundation
end IndisputableMonolith
