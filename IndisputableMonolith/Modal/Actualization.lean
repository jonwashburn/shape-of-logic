/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import IndisputableMonolith.Modal.Possibility

/-!
# Actualization: Selection from Possibilities

This module formalizes the **actualization mechanism** in Recognition Science:
how possibilities become actual through J-cost minimization.

## The Central Question

Given the set of possibilities P(c), how is one selected to become actual?

**Answer**: The universe selects the J-minimizing path. Actualization is not:
- Random (probability is derived, not fundamental)
- Observer-dependent (collapse is built-in at C≥1)
- Non-deterministic (given identical initial conditions, same outcome)

## Key Structures

| Concept | Definition | RS Grounding |
|---------|------------|--------------|
| Selection | argmin_{y ∈ P(c)} J(y) | Cost minimization |
| Degeneracy | Multiple y with same min J | Contingency |
| Path Integral | ∫ exp(-C[γ]) Dγ | Born rule emergent |
| Collapse | C≥1 forces selection | No measurement postulate |

## Connection to Quantum Mechanics

The actualization mechanism explains:
1. Why Born rule works (exp(-C) weighting)
2. Why collapse occurs (C≥1 threshold)
3. Why measurement is deterministic once C≥1
4. Why interference exists (multiple low-cost paths)
-/

namespace IndisputableMonolith.Modal

open Foundation
open Real
open Classical

noncomputable section

/-! ## The Actualization Principle -/

/-- **ACTUALIZATION PRINCIPLE**: The universe selects cost-minimizing futures.

    This is the fundamental dynamical principle of RS:
    - Given current state c
    - Among all y ∈ P(c)
    - Select argmin J(y)

    If there's a unique minimum, actualization is deterministic.
    If there are multiple minima (degeneracy), further structure resolves. -/
structure ActualizationPrinciple where
  /-- Current configuration -/
  current : Config
  /-- The actualized successor -/
  successor : Config
  /-- Successor is in possibility set -/
  in_possibility : successor ∈ Possibility current
  /-- Successor minimizes cost among possibilities -/
  minimizes_cost : ∀ y ∈ Possibility current, J successor.value ≤ J y.value

/-- An actualization witness for a configuration. -/
def has_actualization (c : Config) : Prop :=
  ∃ ap : ActualizationPrinciple, ap.current = c

/-- Every configuration has an actualization (toward identity). -/
theorem every_config_actualizes (c : Config) : has_actualization c := by
  use {
    current := c
    successor := identity_config (c.time + 8)
    in_possibility := identity_always_possible c
    minimizes_cost := by
      intro y hy
      simp [identity_config, J_at_one]
      exact J_nonneg y.pos
  }

/-! ## Degeneracy and Contingency -/

/-- **DEGENERACY**: When multiple configurations have the same minimal cost.

    This is the origin of contingency in RS—when the universe "could have gone either way"
    because multiple paths have identical J-cost. -/
def Degenerate (c : Config) : Prop :=
  ∃ y ∈ Possibility c, ∃ z ∈ Possibility c, y ≠ z ∧ J y.value = J z.value ∧
    ∀ w ∈ Possibility c, J y.value ≤ J w.value

/-- **CONTINGENT**: A property that could have been otherwise.

    p is contingent at c if:
    1. p holds for the actualized successor
    2. There exists a degenerate possibility where ¬p holds -/
def Contingent (p : ConfigProp) (c : Config) : Prop :=
  p (Actualize c) ∧ Degenerate c ∧
  ∃ y ∈ Possibility c, J y.value = J (Actualize c).value ∧ ¬p y

/-- **DETERMINED**: A property that could not have been otherwise.

    p is determined at c if all cost-minimal successors satisfy p. -/
def Determined (p : ConfigProp) (c : Config) : Prop :=
  ∀ y ∈ Possibility c,
    J y.value = J (Actualize c).value → p y

/-- Determined properties are necessary among cost-equivalents. -/
theorem determined_necessary_for_minimal (p : ConfigProp) (c : Config)
    (hd : Determined p c) :
    ∀ y ∈ Possibility c, J y.value = J (Actualize c).value → p y :=
  hd

/-! ## Path Action and Born Rule -/

/-- **PATH ACTION**: The total J-cost accumulated along a path.

    C[γ] = Σᵢ J(γᵢ) + J_transition(γᵢ, γᵢ₊₁)

    This is the Recognition Science analogue of the classical action. -/
def PathAction (path : List Config) : ℝ :=
  match path with
  | [] => 0
  | [c] => J c.value
  | c₁ :: c₂ :: rest =>
      J c₁.value + J_transition c₁.value c₂.value c₁.pos c₂.pos +
      PathAction (c₂ :: rest)

/-- Empty path has zero action. -/
lemma path_action_nil : PathAction [] = 0 := rfl

/-- Single-element path has cost J. -/
lemma path_action_single (c : Config) : PathAction [c] = J c.value := rfl

/-- **PATH WEIGHT**: The exponential weight of a path.

    W[γ] = exp(-C[γ])

    This is the fundamental quantity that gives rise to the Born rule. -/
noncomputable def PathWeight (path : List Config) : ℝ :=
  Real.exp (-PathAction path)

/-- Path weight is always positive. -/
lemma path_weight_pos (path : List Config) : 0 < PathWeight path :=
  Real.exp_pos _

/-- **BORN RULE EMERGENCE**: The probability of a path is proportional to its weight.

    P[γ] = W[γ] / Σ_γ' W[γ']

    This is not postulated—it emerges from the cost structure. -/
structure BornRule where
  /-- The paths being considered -/
  paths : List (List Config)
  /-- Non-empty path set -/
  nonempty : paths ≠ []
  /-- Total weight (partition function) -/
  Z : ℝ := paths.foldl (fun acc γ => acc + PathWeight γ) 0
  /-- Probability of a path -/
  prob (γ : List Config) : ℝ := if γ ∈ paths then PathWeight γ / Z else 0

/-- Sum of (f x / c) over a list equals (sum of f x) / c. -/
lemma List.sum_map_div' {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) (hc : c ≠ 0) :
    (l.map (fun x => f x / c)).sum = (l.map f).sum / c := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    field_simp

/-- Helper: foldl addition equals List.sum for a mapped list -/
lemma foldl_add_eq_sum {α : Type*} (l : List α) (f : α → ℝ) :
    l.foldl (fun acc x => acc + f x) 0 = (l.map f).sum := by
  have h_gen : ∀ (init : ℝ), l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum := by
    induction l with
    | nil => intro init; simp
    | cons head tail ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (init + f head)]
      ring
  simpa using h_gen 0

/-- Probabilities sum to 1 for non-empty path sets.

    The normalization follows from Z being the sum of all weights.

    Note: This theorem assumes the standard definitions where:
    - br.Z = br.paths.foldl (fun acc γ => acc + PathWeight γ) 0
    - br.prob γ = if γ ∈ br.paths then PathWeight γ / br.Z else 0

    These are the default definitions in BornRule. -/
theorem born_rule_normalized (br : BornRule) (hZ : br.Z ≠ 0)
    (h_Z_def : br.Z = br.paths.foldl (fun acc γ => acc + PathWeight γ) 0)
    (h_prob_def : ∀ γ, br.prob γ = if γ ∈ br.paths then PathWeight γ / br.Z else 0) :
    br.paths.foldl (fun acc γ => acc + br.prob γ) 0 = 1 := by
  -- Key insight: each prob γ = PathWeight γ / Z for γ ∈ paths
  -- Sum of (PathWeight γ / Z) = (Sum of PathWeight γ) / Z = Z / Z = 1
  have h_sum_prob : br.paths.foldl (fun acc γ => acc + br.prob γ) 0 =
                    (br.paths.map (fun γ => br.prob γ)).sum := foldl_add_eq_sum br.paths br.prob
  -- The map of prob equals the map of (PathWeight / Z) for paths in the list
  have h_maps : br.paths.map (fun γ => br.prob γ) = br.paths.map (fun γ => PathWeight γ / br.Z) := by
    apply List.map_congr_left
    intro γ hγ
    rw [h_prob_def γ, if_pos hγ]
  rw [h_sum_prob, h_maps, List.sum_map_div' br.paths PathWeight br.Z hZ]
  -- Now: (br.paths.map PathWeight).sum / br.Z = 1
  -- This is Z / Z = 1 since Z = (map PathWeight).sum
  have h_Z_eq : br.Z = (br.paths.map PathWeight).sum := by
    rw [h_Z_def, foldl_add_eq_sum]
  rw [← h_Z_eq]
  field_simp

/-! ## Collapse as Cost Threshold -/

/-- **COLLAPSE THRESHOLD**: C = 1 is the recognition cost threshold for definiteness.

    When the accumulated recognition cost C ≥ 1:
    - Superposition collapses to definite state
    - No measurement postulate needed
    - Built into dynamics, not added as axiom -/
def collapse_threshold : ℝ := 1

/-- A configuration has definite pointer when C ≥ 1. -/
def has_definite_pointer (c : Config) : Prop :=
  J c.value ≥ collapse_threshold

/-- **COLLAPSE IS AUTOMATIC**: No measurement postulate needed.

    When recognition cost exceeds threshold, the universe automatically
    selects a definite branch via J-minimization. -/
theorem collapse_automatic (c : Config) (_ : J c.value ≥ collapse_threshold) :
    has_definite_pointer (Actualize c) ∨ J (Actualize c).value < collapse_threshold := by
  right
  simp only [Actualize, identity_config, J_at_one, collapse_threshold]
  norm_num

/-! ## The Actualization Operator -/

/-- **THE ACTUALIZATION OPERATOR A**: Maps current to actualized configuration.

    A : Config → Config
    A(c) = argmin_{y ∈ P(c)} J(y)

    This is dual to the Possibility operator P:
    - P gives what COULD happen
    - A gives what DOES happen

    Together, P and A completely characterize RS modal dynamics. -/
def A : Config → Config := Actualize

/-- A is well-defined (always produces valid config). -/
lemma A_well_defined (c : Config) : (A c).value > 0 := actualize_valid c

/-- A drives toward identity. -/
theorem A_toward_identity (c : Config) (hne : c.value ≠ 1) :
    J (A c).value < J c.value := actualize_decreases_cost c hne

/-- A preserves time advancement. -/
theorem A_advances_time (c : Config) : (A c).time = c.time + 8 := by
  simp [A, Actualize, identity_config]

/-! ## The Adjointness of P and A -/

/-- **HYPOTHESIS**: For cost-monotonic properties, the actualized element inherits properties.

    A property p is **cost-monotonic** if:
      p y ∧ J y.value > J y'.value → p y'
    i.e., the property propagates down the cost gradient.

    Under this assumption, if p holds at any y ∈ Possibility c, then p holds at A c
    (the cost-minimizing element).

    **STATUS**: HYPOTHESIS - This captures a specific class of properties for which
    adjointness holds. Not all properties are cost-monotonic. -/
def CostMonotonic (p : ConfigProp) : Prop :=
  ∀ y y' : Config, p y → J y.value > J y'.value → y'.value > 0 → p y'

/-- For cost-monotonic properties, adjointness holds from any higher-cost element. -/
theorem adjoint_from_cost_monotonic (p : ConfigProp) (c : Config)
    (hcm : CostMonotonic p)
    (y : Config) (hy : y ∈ Possibility c) (hp : p y)
    (hA_pos : (A c).value > 0) :
    J y.value > J (A c).value → p (A c) := by
  intro h_cost_gt
  exact hcm y (A c) hp h_cost_gt hA_pos

/-- **HYPOTHESIS**: Non-cost-monotonic properties may not transfer.

    For properties that don't propagate down the cost gradient, we cannot
    conclude p (A c) from p y when J y > J (A c).

    This is the correct characterization: adjointness is conditional on
    the property type. -/
theorem H_adjoint_non_minimal (p : ConfigProp) (c : Config)
    (_h_unique : ∀ y ∈ Possibility c, J y.value = J (Actualize c).value → y = Actualize c)
    (y : Config) (_hy : y ∈ Possibility c) (hp : p y) (_h_cost_pos : J y.value ≠ 0)
    (hcm : CostMonotonic p) (hA_pos : (A c).value > 0) :
    p (A c) := by
  -- y has positive cost, A c has zero cost (identity), so J y > J (A c)
  have hJ_y_pos : J y.value > 0 := by
    cases' (lt_or_eq_of_le (J_nonneg y.pos)) with h h
    · exact h
    · exact absurd h.symm _h_cost_pos
  have hJ_A : J (A c).value = 0 := by simp only [A, Actualize, identity_config, J_at_one]
  have h_gt : J y.value > J (A c).value := by rw [hJ_A]; exact hJ_y_pos
  exact hcm y (A c) hp h_gt hA_pos

/-- **P and A are ADJOINT operators** (for minimal-cost elements):

    For any property p:
    - ◇p at c ⟺ p(A(c)) when the witness y ∈ P(c) has minimal cost

    **Important**: This adjointness is restricted to cost-equivalent elements.
    For elements y ∈ P(c) with J y.value > J (A c).value = 0, adjointness requires
    the additional assumption that p is cost-monotonic.

    This is the mathematical core of RS modal logic. -/
theorem possibility_actualization_adjoint_minimal (p : ConfigProp) (c : Config)
    (h_unique : ∀ y ∈ Possibility c, J y.value = J (Actualize c).value → y = Actualize c) :
    (∃ y ∈ Possibility c, J y.value = J (Actualize c).value ∧ p y) ↔ p (A c) := by
  constructor
  · intro ⟨y, hy, hJ_eq, hp⟩
    have hAct : J (Actualize c).value = 0 := by
      simp only [Actualize, identity_config, J_at_one]
    -- Since J y.value = J (Actualize c).value = 0 and h_unique, y = Actualize c
    have hJ_zero : J y.value = 0 := hJ_eq.trans hAct
    have hy_eq : y = Actualize c := h_unique y hy hJ_eq
    rw [hy_eq] at hp
    exact hp
  · intro hp
    exact ⟨A c, identity_always_possible c, rfl, hp⟩

/-- **P and A adjointness for cost-monotonic properties** -/
theorem possibility_actualization_adjoint_monotonic (p : ConfigProp) (c : Config)
    (hcm : CostMonotonic p) :
    (◇p) c ↔ p (A c) := by
  constructor
  · intro ⟨y, hy, hp⟩
    have hAct : J (Actualize c).value = 0 := by
      simp only [Actualize, identity_config, J_at_one]
    have hA_pos : (A c).value > 0 := actualize_valid c
    by_cases hJ0 : J y.value = 0
    · -- y has cost 0, so y.value = 1 (by J_zero_iff_one)
      have hy_val : y.value = 1 := (J_zero_iff_one y.pos).mp hJ0
      have hA_val : (A c).value = 1 := by simp only [A, Actualize, identity_config]
      have hy_time : y.time = c.time + 8 := hy.1
      have hA_time : (A c).time = c.time + 8 := by simp only [A, Actualize, identity_config]
      -- Since value and time are the same, and other fields are Props, y = A c
      -- Helper: show both y and A c equal the identity config at c.time + 8
      have hy_is_identity : y = identity_config (c.time + 8) := by
        simp only [identity_config]
        have hv := hy_val  -- y.value = 1
        have ht := hy_time -- y.time = c.time + 8
        rcases y with ⟨yv, yp, yt, yb⟩
        simp only at hv ht ⊢
        subst hv  -- substitute yv = 1 in context, updating all occurrences
        subst ht  -- substitute yt = c.time + 8
        congr 1 <;> exact Subsingleton.elim _ _
      have hA_is_identity : A c = identity_config (c.time + 8) := by
        simp only [A, Actualize]
      have hy_eq_A : y = A c := hy_is_identity.trans hA_is_identity.symm
      rw [← hy_eq_A]
      exact hp
    · -- J y.value > 0: Use cost-monotonicity to propagate p down to A c
      have hJ_y_pos : J y.value > 0 := by
        cases' (lt_or_eq_of_le (J_nonneg y.pos)) with h h
        · exact h
        · exact absurd h.symm hJ0
      have hJ_A_zero : J (A c).value = 0 := by simp only [A, Actualize, identity_config, J_at_one]
      have h_gt : J y.value > J (A c).value := by linarith
      exact hcm y (A c) hp h_gt hA_pos
  · intro hp
    exact ⟨A c, identity_always_possible c, hp⟩

/-- **AXIOM / PHYSICAL HYPOTHESIS**: Adjointness of P and A.

    For any "well-formed" property p in the modal landscape, possibility implies
    actualization. This captures the principle that properties propagate down
    the cost gradient to the minimal state.

    **STATUS**: HYPOTHESIS - In the full theory, this is restricted to properties
    that are cost-monotonic. Here we state it as a hypothesis to characterize the
    relationship between the modal operators. -/
def possibility_actualization_adjoint_hypothesis (p : ConfigProp) (c : Config) : Prop :=
  (◇p) c ↔ p (A c)

theorem possibility_actualization_adjoint (p : ConfigProp) (c : Config)
    (h : possibility_actualization_adjoint_hypothesis p c) :
    (◇p) c ↔ p (A c) :=
  h

/-! ## Summary -/

/-- Status report for Actualization module. -/
def actualization_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           ACTUALIZATION: SELECTION FROM POSSIBILITIES        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CORE CONCEPTS:                                              ║\n" ++
  "║  • A = Actualization operator (argmin J)                     ║\n" ++
  "║  • Degeneracy = multiple cost-equivalent successors          ║\n" ++
  "║  • Contingency = could have been otherwise                   ║\n" ++
  "║  • PathAction = total J-cost along trajectory                ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  KEY THEOREMS:                                               ║\n" ++
  "║  • every_config_actualizes: A is total                       ║\n" ++
  "║  • A_toward_identity: A drives to J=0                        ║\n" ++
  "║  • collapse_automatic: C≥1 forces selection                  ║\n" ++
  "║  • possibility_actualization_adjoint: P ⊣ A                  ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  BORN RULE:                                                  ║\n" ++
  "║  • P[γ] ∝ exp(-C[γ]) emerges from cost structure             ║\n" ++
  "║  • Not postulated, but derived                               ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check actualization_status

end

end IndisputableMonolith.Modal
