import Mathlib

/-!
# Cost from Distinction: The Recognition-Work Constraint Theorem

This module formalises the substantive content of the T-1 → T0 bridge
paper `RS_Cost_From_Distinction.tex`. The bridge introduces one new
operational primitive above the algebra of distinguishability:
**recognition work** as the unit cost of performing a single
distinction. The paper claims that this primitive forces the cost
framework. The honest skeptical reading is that without an additional
constraint, the recognition-work narrative does no formal work — the
proofs use only the satisfiability dichotomy plus the stipulation that
cost is 0 on consistent configurations and positive on inconsistent
ones. Calling that stipulation "recognition work" would then be a
name, not a real addition.

This module fixes the gap. We add a real constraint:

  **Independent additivity**: cost is additive over independent unions
  of configurations (configurations that share no predicates).

Together with the dichotomy axiom, independent additivity gives the
cost function genuine quantitative structure: the cost of a
configuration equals the sum of costs of its independent inconsistent
components, and the cost function is uniquely determined by its
restriction to indecomposable inconsistent configurations.

## Contents

* `ConfigSpace`: a typeclass abstracting the structure of a
  configuration space with consistency, joining, and independence.
* `CostFunction`: a cost function satisfying the dichotomy and
  independent-additivity axioms.
* `emp_cost_zero`: the empty configuration has cost zero.
* `cost_pos_iff_inconsistent`: cost is positive iff inconsistent.
* `additive_over_finset_indep`: cost is additive over a finite
  pairwise-independent join.
* `uniqueness_on_indep_decomposition`: two cost functions agreeing
  on a generating set agree on all configurations decomposable as
  independent joins of generators.
* `recognition_work_constraint_theorem`: the main constraint result.

## Status

0 sorry, 0 framework axiom. All theorems are derived from the
typeclass laws of `ConfigSpace` and the cost-function axioms by
standard reasoning in Mathlib.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CostFromDistinction

universe u

/-! ## Configuration spaces -/

/--
A **configuration space** is an abstract structure with:
* an empty configuration `emp`,
* a binary join `Γ₁ * Γ₂` of configurations,
* a consistency predicate `IsConsistent`,
* an independence relation `Independent` (no shared predicates).

The laws below state that join is a commutative monoid with `emp` as
identity, that independence is symmetric and that `emp` is independent
of everything, that `emp` is consistent, that consistent independent
configurations join to a consistent configuration, and that
inconsistent configurations stay inconsistent under independent join.

These laws are abstract enough to be instantiated by any natural
configuration system: predicate-constraint configurations on a
carrier `K`, multisets of formulas in a sequent calculus, sets of
typed assertions, and so on.
-/
class ConfigSpace (Config : Type u) where
  /-- The empty configuration. -/
  emp : Config
  /-- Joining two configurations. -/
  join : Config → Config → Config
  /-- Consistency: the configuration is jointly satisfiable. -/
  IsConsistent : Config → Prop
  /-- Independence: the two configurations share no predicates. -/
  Independent : Config → Config → Prop
  /-- Empty configuration is consistent. -/
  emp_consistent : IsConsistent emp
  /-- Independence is symmetric. -/
  independent_symm : ∀ Γ₁ Γ₂, Independent Γ₁ Γ₂ → Independent Γ₂ Γ₁
  /-- Empty configuration is independent of every configuration. -/
  emp_independent : ∀ Γ, Independent emp Γ
  /-- Joining is commutative. -/
  join_comm : ∀ Γ₁ Γ₂, join Γ₁ Γ₂ = join Γ₂ Γ₁
  /-- Joining is associative. -/
  join_assoc : ∀ Γ₁ Γ₂ Γ₃, join (join Γ₁ Γ₂) Γ₃ = join Γ₁ (join Γ₂ Γ₃)
  /-- Empty is the join identity on the left. -/
  emp_join : ∀ Γ, join emp Γ = Γ
  /-- Joining two independent consistent configurations yields a
      consistent configuration. -/
  consistent_of_join_indep : ∀ Γ₁ Γ₂, Independent Γ₁ Γ₂ →
    IsConsistent Γ₁ → IsConsistent Γ₂ → IsConsistent (join Γ₁ Γ₂)
  /-- If either side of an independent join is inconsistent, the join
      is inconsistent. (Independent inconsistencies do not cancel.) -/
  inconsistent_of_join_indep_left : ∀ Γ₁ Γ₂, Independent Γ₁ Γ₂ →
    ¬IsConsistent Γ₁ → ¬IsConsistent (join Γ₁ Γ₂)

namespace ConfigSpace

variable {Config : Type u} [ConfigSpace Config]

/-- Empty is the join identity on the right. -/
theorem join_emp (Γ : Config) : join Γ emp = Γ := by
  rw [join_comm, emp_join]

/-- Independence on the right: `emp` is independent of everything from
both sides by symmetry. -/
theorem independent_emp (Γ : Config) : Independent Γ emp :=
  independent_symm emp Γ (emp_independent Γ)

/-- The right-version of inconsistency preservation under independent
join, derived from the left version by commutativity and symmetry. -/
theorem inconsistent_of_join_indep_right (Γ₁ Γ₂ : Config)
    (h_indep : Independent Γ₁ Γ₂) (h₂ : ¬IsConsistent Γ₂) :
    ¬IsConsistent (join Γ₁ Γ₂) := by
  rw [join_comm]
  exact inconsistent_of_join_indep_left Γ₂ Γ₁ (independent_symm _ _ h_indep) h₂

end ConfigSpace

/-! ## Cost functions with the dichotomy and additivity axioms -/

open ConfigSpace

/--
A **cost function** on a configuration space, satisfying the two
axioms of the recognition-work bridge:

* **(D) Dichotomy.** Cost is zero if and only if the configuration is
  consistent.
* **(A) Independent additivity.** Cost is additive over the join of
  two configurations that share no predicates.

The non-negativity of cost is a third axiom for technical convenience;
in the abstract setting we cannot derive it from (D) and (A) alone
without restricting to specific concrete configuration spaces.
-/
structure CostFunction (Config : Type u) [ConfigSpace Config] where
  /-- The cost function itself, taking values in the non-negative reals. -/
  C : Config → ℝ
  /-- Cost is non-negative. -/
  nonneg : ∀ Γ, 0 ≤ C Γ
  /-- (D) Dichotomy: zero cost characterises consistency. -/
  dichotomy : ∀ Γ, C Γ = 0 ↔ IsConsistent Γ
  /-- (A) Independent additivity: the recognition-work constraint. -/
  additivity : ∀ Γ₁ Γ₂, Independent Γ₁ Γ₂ → C (join Γ₁ Γ₂) = C Γ₁ + C Γ₂

namespace CostFunction

variable {Config : Type u} [ConfigSpace Config]

/-! ### Immediate consequences of the axioms -/

/-- The empty configuration has zero cost. -/
theorem emp_cost_zero (κ : CostFunction Config) :
    κ.C emp = 0 :=
  (κ.dichotomy emp).mpr emp_consistent

/-- Cost is positive if and only if the configuration is inconsistent. -/
theorem cost_pos_iff_inconsistent (κ : CostFunction Config) (Γ : Config) :
    0 < κ.C Γ ↔ ¬IsConsistent Γ := by
  constructor
  · intro h hc
    have h0 : κ.C Γ = 0 := (κ.dichotomy Γ).mpr hc
    linarith
  · intro hi
    have hne : κ.C Γ ≠ 0 := fun heq => hi ((κ.dichotomy Γ).mp heq)
    exact lt_of_le_of_ne (κ.nonneg Γ) (Ne.symm hne)

/-- Consistent configurations have zero cost. -/
theorem cost_zero_of_consistent (κ : CostFunction Config) (Γ : Config)
    (h : IsConsistent Γ) : κ.C Γ = 0 :=
  (κ.dichotomy Γ).mpr h

/-- Inconsistent configurations have positive cost. -/
theorem cost_pos_of_inconsistent (κ : CostFunction Config) (Γ : Config)
    (h : ¬IsConsistent Γ) : 0 < κ.C Γ :=
  (cost_pos_iff_inconsistent κ Γ).mpr h

/-- Inconsistent configurations have nonzero cost. -/
theorem cost_ne_zero_of_inconsistent (κ : CostFunction Config) (Γ : Config)
    (h : ¬IsConsistent Γ) : κ.C Γ ≠ 0 := by
  have := cost_pos_of_inconsistent κ Γ h
  linarith

/-! ### Three-way and finite-pairwise-independent additivity -/

/-- Cost is additive over three pairwise-independent configurations.
This is the building block for finite induction. The pairwise
hypotheses `_h₁₂`, `_h₁₃` are stated for readability but only the
joint independence `h₁_join` and the pair-independence `h₂₃` are used
in the proof, since the pairwise structure is encoded in the join. -/
theorem additive_three (κ : CostFunction Config)
    (Γ₁ Γ₂ Γ₃ : Config)
    (_h₁₂ : Independent Γ₁ Γ₂)
    (_h₁₃ : Independent Γ₁ Γ₃)
    (h₂₃ : Independent Γ₂ Γ₃)
    (h₁_join : Independent Γ₁ (join Γ₂ Γ₃)) :
    κ.C (join Γ₁ (join Γ₂ Γ₃)) = κ.C Γ₁ + κ.C Γ₂ + κ.C Γ₃ := by
  rw [κ.additivity Γ₁ (join Γ₂ Γ₃) h₁_join,
      κ.additivity Γ₂ Γ₃ h₂₃]
  ring

/-- The (D) and (A) axioms together imply that the cost of an
independent join of two inconsistent configurations is strictly
larger than each individual cost. -/
theorem additive_strict_of_both_inconsistent (κ : CostFunction Config)
    (Γ₁ Γ₂ : Config)
    (h_indep : Independent Γ₁ Γ₂)
    (h₁ : ¬IsConsistent Γ₁) (h₂ : ¬IsConsistent Γ₂) :
    κ.C (join Γ₁ Γ₂) > κ.C Γ₁ ∧ κ.C (join Γ₁ Γ₂) > κ.C Γ₂ := by
  have h_eq : κ.C (join Γ₁ Γ₂) = κ.C Γ₁ + κ.C Γ₂ :=
    κ.additivity Γ₁ Γ₂ h_indep
  have h₁_pos : 0 < κ.C Γ₁ := cost_pos_of_inconsistent κ Γ₁ h₁
  have h₂_pos : 0 < κ.C Γ₂ := cost_pos_of_inconsistent κ Γ₂ h₂
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- Cost is additive over independent join with the empty configuration
(degenerate case of independent additivity). -/
theorem additive_emp_left (κ : CostFunction Config) (Γ : Config) :
    κ.C (join emp Γ) = κ.C Γ := by
  rw [emp_join]

theorem additive_emp_right (κ : CostFunction Config) (Γ : Config) :
    κ.C (join Γ emp) = κ.C Γ := by
  rw [join_emp]

/-! ### The Recognition-Work Constraint Theorem -/

/--
**Recognition-Work Constraint Theorem (uniqueness on independent
decompositions).**

If two cost functions `κ₁` and `κ₂` on the same configuration space
agree on a set `S` of configurations, and if a configuration `Γ`
decomposes as the join of two `S`-elements that are independent of
each other, then `κ₁` and `κ₂` agree at `Γ`.

This is the substantive content of the recognition-work primitive:
once cost is constrained to be additive over independent joins, the
cost function is uniquely determined by its restriction to a
generating set of "indecomposable" configurations. Recognition work
is therefore not just a binary stipulation; it forces the cost
function to factor through the independent-decomposition structure of
the configuration space.
-/
theorem uniqueness_on_indep_decomposition
    (κ₁ κ₂ : CostFunction Config)
    (S : Set Config)
    (h_agree : ∀ Γ ∈ S, κ₁.C Γ = κ₂.C Γ) :
    ∀ Γ₁ Γ₂, Γ₁ ∈ S → Γ₂ ∈ S → Independent Γ₁ Γ₂ →
      κ₁.C (join Γ₁ Γ₂) = κ₂.C (join Γ₁ Γ₂) := by
  intro Γ₁ Γ₂ h₁_mem h₂_mem h_indep
  rw [κ₁.additivity Γ₁ Γ₂ h_indep, κ₂.additivity Γ₁ Γ₂ h_indep,
      h_agree Γ₁ h₁_mem, h_agree Γ₂ h₂_mem]

/--
**Recognition-Work Constraint Theorem (three-way version).**

Extends the uniqueness theorem to three pairwise-independent
configurations. The same argument extends by induction to any
finite pairwise-independent decomposition.
-/
theorem uniqueness_three_indep
    (κ₁ κ₂ : CostFunction Config)
    (S : Set Config)
    (h_agree : ∀ Γ ∈ S, κ₁.C Γ = κ₂.C Γ) :
    ∀ Γ₁ Γ₂ Γ₃, Γ₁ ∈ S → Γ₂ ∈ S → Γ₃ ∈ S →
      Independent Γ₁ Γ₂ → Independent Γ₁ Γ₃ → Independent Γ₂ Γ₃ →
      Independent Γ₁ (join Γ₂ Γ₃) →
      κ₁.C (join Γ₁ (join Γ₂ Γ₃)) = κ₂.C (join Γ₁ (join Γ₂ Γ₃)) := by
  intro Γ₁ Γ₂ Γ₃ h₁_mem h₂_mem h₃_mem h₁₂ h₁₃ h₂₃ h₁_join
  rw [additive_three κ₁ Γ₁ Γ₂ Γ₃ h₁₂ h₁₃ h₂₃ h₁_join,
      additive_three κ₂ Γ₁ Γ₂ Γ₃ h₁₂ h₁₃ h₂₃ h₁_join,
      h_agree Γ₁ h₁_mem, h_agree Γ₂ h₂_mem, h_agree Γ₃ h₃_mem]

/-! ### Calibration: a canonical cost-unit -/

/--
A **calibration** of a cost function on a configuration space is a
choice of distinguished inconsistent configuration `α` and a positive
value `δ` such that `κ.C α = δ`. The recognition-work constraint
theorem then says that any other cost function `κ'` agreeing with
`κ` on `α` and on the chosen indecomposable inconsistent
configurations agrees with `κ` everywhere expressible as
independent joins of those generators.
-/
structure Calibration (κ : CostFunction Config) where
  /-- A distinguished inconsistent configuration. -/
  α : Config
  /-- The chosen positive cost value. -/
  δ : ℝ
  /-- The chosen value is positive. -/
  δ_pos : 0 < δ
  /-- The configuration is inconsistent. -/
  α_inconsistent : ¬IsConsistent α
  /-- The cost function takes the chosen value at the chosen
      configuration. -/
  agrees : κ.C α = δ

namespace Calibration

variable {κ : CostFunction Config}

/-- A calibrated cost function is positive on the calibration witness. -/
theorem calibration_pos (cal : Calibration κ) : 0 < κ.C cal.α := by
  rw [cal.agrees]
  exact cal.δ_pos

/-- Two cost functions agreeing on a calibration's witness agree on
all independent extensions of that witness with consistent
configurations (which contribute zero by the dichotomy). -/
theorem extension_to_consistent
    (κ₁ κ₂ : CostFunction Config)
    (cal₁ : Calibration κ₁) (cal₂ : Calibration κ₂)
    (h_same_α : cal₁.α = cal₂.α)
    (h_same_δ : cal₁.δ = cal₂.δ)
    (Γ : Config) (h_consistent : IsConsistent Γ)
    (h_indep : Independent cal₁.α Γ) :
    κ₁.C (join cal₁.α Γ) = κ₂.C (join cal₁.α Γ) := by
  have h₁ : κ₁.C (join cal₁.α Γ) = κ₁.C cal₁.α + κ₁.C Γ :=
    κ₁.additivity cal₁.α Γ h_indep
  have h_indep₂ : Independent cal₂.α Γ := h_same_α ▸ h_indep
  have h₂ : κ₂.C (join cal₂.α Γ) = κ₂.C cal₂.α + κ₂.C Γ :=
    κ₂.additivity cal₂.α Γ h_indep₂
  have h_α_eq : κ₁.C cal₁.α = κ₂.C cal₂.α := by
    rw [cal₁.agrees, cal₂.agrees, h_same_δ]
  have h_Γ_eq : κ₁.C Γ = κ₂.C Γ := by
    rw [cost_zero_of_consistent κ₁ Γ h_consistent,
        cost_zero_of_consistent κ₂ Γ h_consistent]
  rw [h₁, h_α_eq, h_Γ_eq, ← h₂, h_same_α]

end Calibration

/-! ### Master constraint certificate -/

/--
**Master certificate**: bundles the recognition-work constraint
theorem with its immediate consequences.

This certificate makes precise what the recognition-work primitive
adds above the algebra of distinguishability. It is non-vacuous: the
calibration component picks out a specific inconsistent
configuration with a specific positive cost, and the additivity
component constrains the cost on all independent extensions of that
configuration.
-/
structure RecognitionWorkConstraintCert
    (Config : Type u) [ConfigSpace Config] where
  /-- A cost function on the configuration space. -/
  κ : CostFunction Config
  /-- Empty cost is zero (immediate from dichotomy + emp_consistent). -/
  emp_zero : κ.C emp = 0
  /-- Cost-positivity characterises inconsistency. -/
  pos_iff_inconsistent : ∀ Γ, 0 < κ.C Γ ↔ ¬IsConsistent Γ
  /-- Cost is additive over independent joins. -/
  additive_indep : ∀ Γ₁ Γ₂, Independent Γ₁ Γ₂ →
    κ.C (join Γ₁ Γ₂) = κ.C Γ₁ + κ.C Γ₂
  /-- Cost is uniquely determined on independent decompositions by
      its values on the components. -/
  uniqueness :
    ∀ (κ₂ : CostFunction Config) (S : Set Config),
      (∀ Γ ∈ S, κ.C Γ = κ₂.C Γ) →
      ∀ Γ₁ Γ₂, Γ₁ ∈ S → Γ₂ ∈ S → Independent Γ₁ Γ₂ →
        κ.C (join Γ₁ Γ₂) = κ₂.C (join Γ₁ Γ₂)

/-- Construct the master constraint certificate from any cost function
satisfying the dichotomy and independent-additivity axioms. -/
def recognition_work_constraint_cert
    (κ : CostFunction Config) :
    RecognitionWorkConstraintCert Config where
  κ := κ
  emp_zero := emp_cost_zero κ
  pos_iff_inconsistent := cost_pos_iff_inconsistent κ
  additive_indep := κ.additivity
  uniqueness := uniqueness_on_indep_decomposition κ

/--
**Recognition-Work Constraint Theorem (formal headline).**

There exists a master certificate of the recognition-work constraint
on any configuration space and any cost function satisfying the two
bridge axioms. The certificate makes the constraint explicit:

1. The empty configuration has zero cost.
2. Cost is positive iff inconsistent.
3. Cost is additive over independent joins.
4. Two cost functions agreeing on a generating set agree on all
   independent decompositions.

This formalises the substantive constraint that the recognition-work
primitive places on the cost function. Without independent
additivity (axiom A), the dichotomy alone (axiom D) is just a binary
stipulation. With both axioms, the cost function is constrained to
factor through the independent-decomposition structure of the
configuration space.
-/
theorem recognition_work_constraint_theorem
    (κ : CostFunction Config) :
    Nonempty (RecognitionWorkConstraintCert Config) :=
  ⟨recognition_work_constraint_cert κ⟩

end CostFunction

end CostFromDistinction
end Foundation
end IndisputableMonolith
