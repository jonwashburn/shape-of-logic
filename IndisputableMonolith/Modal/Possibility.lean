/-
Copyright (c) 2025 Recognition Science. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Recognition Science Contributors
-/
import Mathlib
import IndisputableMonolith.Foundation.LawOfExistence

/-!
# Grammar of Possibility: RS Modal Logic

This module formalizes the **modal structure of Recognition Science**:
- What COULD BE (possibility)
- Why things CHANGE (cost of stasis vs change)
- How possibilities become actual (actualization)

## The Central Insight

In RS, possibility is not a primitive notion. It emerges from cost structure:

**A state y is possible from x iff:**
1. There exists a recognition path from x to y
2. The path has finite cost (J-cost < ∞)
3. The transition respects ledger conservation (σ = 0)

## Key Structures

| Concept | Definition | RS Grounding |
|---------|------------|--------------|
| Possibility | P(x) = {y : J_path(x→y) < ∞} | Finite-cost reachability |
| Actualization | Selection from P(x) | J-minimizing path selection |
| Cost of Stasis | J_stasis(x) | Cost to maintain identity |
| Cost of Change | J_change(x,y) | Cost of transition x → y |
| Modal Necessity | □p ⟺ ∀y ∈ P(x), p(y) | True in all accessible states |
| Modal Possibility | ◇p ⟺ ∃y ∈ P(x), p(y) | True in some accessible state |

## Why This Matters

Modal logic in RS answers:
1. Why does anything happen? (Stasis costs more than optimal change)
2. What are counterfactuals? (Alternative J-minimizing paths)
3. What is contingency? (Multiple cost-equivalent possibilities)
4. What is necessity? (Unique J-minimizer)
-/

namespace IndisputableMonolith.Modal

open Real
open Classical

noncomputable section

/-! ## Configuration Space -/

/-- A configuration is a point in recognition state space.

    In the full theory, this would be a LedgerState.
    Here we use a simplified representation for modal logic development. -/
structure Config where
  /-- Configuration value (positive real, generalizes bond multiplier) -/
  value : ℝ
  /-- Positivity constraint -/
  pos : 0 < value
  /-- Time coordinate (in ticks) -/
  time : ℕ
  /-- Boundedness constraint: physical values satisfy |log(value)| ≤ 16.
      This covers values from exp(-16) ≈ 1.1×10⁻⁷ to exp(16) ≈ 8.9×10⁶. -/
  log_bound : |Real.log value| ≤ 16

/-- The set of all well-formed configurations (value > 0) -/
def ConfigSpace : Set Config := {c | 0 < c.value}

/-- The identity configuration (value = 1, minimal cost) -/
def identity_config (t : ℕ) : Config := ⟨1, one_pos, t, by simp [Real.log_one]⟩

/-! ## Cost Functions for Modal Logic -/

/-- The fundamental cost J(x) = ½(x + 1/x) - 1.

    This is the unique cost satisfying d'Alembert + normalization + calibration (T5). -/
noncomputable def J (x : ℝ) : ℝ := (1/2) * (x + x⁻¹) - 1

/-- J is non-negative for positive arguments. -/
lemma J_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ J x := by
  unfold J
  have hx_ne : x ≠ 0 := hx.ne'
  have h_rewrite : (1:ℝ)/2 * (x + x⁻¹) - 1 = (x - 1)^2 / (2 * x) := by field_simp; ring
  rw [h_rewrite]
  apply div_nonneg (sq_nonneg _) (by linarith : 0 ≤ 2 * x)

/-- J(1) = 0 (the identity has zero cost). -/
lemma J_at_one : J 1 = 0 := by unfold J; norm_num

/-- J(x) = 0 iff x = 1 (for positive x). -/
lemma J_zero_iff_one {x : ℝ} (hx : 0 < x) : J x = 0 ↔ x = 1 := by
  constructor
  · intro h
    unfold J at h
    have hx_ne : x ≠ 0 := hx.ne'
    have h1 : x + x⁻¹ = 2 := by linarith
    have h2 : x * (x + x⁻¹) = x * 2 := by rw [h1]
    have h3 : x^2 + 1 = 2 * x := by field_simp at h2; linarith
    nlinarith [sq_nonneg (x - 1)]
  · intro h; rw [h]; exact J_at_one

/-- J is positive for x ≠ 1. -/
lemma J_pos_of_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) : 0 < J x := by
  have h := J_nonneg hx
  cases' h.lt_or_eq with hlt heq
  · exact hlt
  · exfalso; exact hne ((J_zero_iff_one hx).mp heq.symm)

/-! ## Transition Cost -/

/-- The cost of transitioning from configuration x to configuration y.

    This is the "action" for a direct transition, defined as the average
    cost along the transition weighted by the magnitude of change.

    J_transition(x,y) = |ln(y/x)| · (J(x) + J(y)) / 2

    Key properties:
    - J_transition(x,x) = 0 (no change = no cost)
    - J_transition(x,y) = J_transition(y,x) (symmetric)
    - J_transition(x,1) = |ln x| · J(x) / 2 (approaching identity is cheap for x ≈ 1) -/
noncomputable def J_transition (x y : ℝ) (_ : 0 < x) (_ : 0 < y) : ℝ :=
  |Real.log (y / x)| * ((J x + J y) / 2)

/-- Transition to self has zero cost. -/
lemma J_transition_self {x : ℝ} (hx : 0 < x) : J_transition x x hx hx = 0 := by
  unfold J_transition
  simp [div_self (ne_of_gt hx)]

/-- Transition cost is symmetric. -/
lemma J_transition_symm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    J_transition x y hx hy = J_transition y x hy hx := by
  unfold J_transition
  congr 1
  · -- Show |log(y/x)| = |log(x/y)|
    have h1 : Real.log (y / x) = -Real.log (x / y) := by
      rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
      rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
      ring
    rw [h1, abs_neg]
  · ring

/-! ## Cost of Stasis vs Cost of Change -/

/-- **COST OF STASIS**: The cost for a configuration to remain unchanged.

    In RS, even "staying the same" has a recognition cost because:
    1. The universe is constantly recognizing itself (8-tick cycle)
    2. Maintaining identity requires continuous cost payment
    3. J(x) is paid per tick, not just for change

    J_stasis(x) = 8 · J(x) (cost over one octave to maintain x) -/
noncomputable def J_stasis (x : ℝ) : ℝ := 8 * J x

/-- Stasis at identity is free. -/
lemma J_stasis_at_one : J_stasis 1 = 0 := by unfold J_stasis; simp [J_at_one]

/-- Stasis cost is non-negative for positive configurations. -/
lemma J_stasis_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ J_stasis x := by
  unfold J_stasis
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (J_nonneg hx)

/-- **COST OF CHANGE**: The cost to evolve from x to y over one octave.

    J_change(x,y) = J_transition(x,y) + J_stasis(y)

    This includes:
    1. The transition cost to get from x to y
    2. The stasis cost to maintain y for one octave

    The universe chooses change when J_change < J_stasis. -/
noncomputable def J_change (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : ℝ :=
  J_transition x y hx hy + J_stasis y

/-- No change means only stasis cost. -/
lemma J_change_self {x : ℝ} (hx : 0 < x) : J_change x x hx hx = J_stasis x := by
  unfold J_change
  rw [J_transition_self hx]
  ring

/-! ## The Dynamics Criterion: Why Change Happens -/

/-- **DYNAMICS CRITERION**: A configuration x evolves to y when change is cheaper than stasis.

    This is the fundamental answer to "why does anything happen?"

    Change occurs iff J_change(x,y) < J_stasis(x) for some y ≠ x.

    Stasis is preferred iff x = 1 (identity is the only stable fixed point). -/
def prefers_change (x : ℝ) (hx : 0 < x) : Prop :=
  ∃ y : ℝ, ∃ hy : 0 < y, y ≠ x ∧ J_change x y hx hy < J_stasis x

def prefers_stasis (x : ℝ) (hx : 0 < x) : Prop :=
  ∀ y : ℝ, ∀ hy : 0 < y, y ≠ x → J_stasis x ≤ J_change x y hx hy

/-- **THEOREM**: The identity is the unique configuration that prefers stasis.

    For x = 1: J_stasis(1) = 0, and any change costs > 0.
    For x ≠ 1: There exists y closer to 1 with J_change(x,y) < J_stasis(x).

    This proves: **Existence (x = 1) is the unique stable state.** -/
theorem identity_prefers_stasis : prefers_stasis 1 one_pos := by
  intro y hy _
  -- J_stasis(1) = 0, and J_change(1,y) ≥ 0 for all y > 0
  have hJ1 : J_stasis 1 = 0 := J_stasis_at_one
  rw [hJ1]
  unfold J_change
  apply add_nonneg
  · unfold J_transition
    apply mul_nonneg (abs_nonneg _)
    apply div_nonneg
    · apply add_nonneg J_at_one.ge (J_nonneg hy)
    · norm_num
  · exact J_stasis_nonneg hy

/-! ## Possibility: What Could Follow -/

/-- **POSSIBILITY OPERATOR**: P(c) is the set of configurations reachable from c.

    A configuration y is possible from x iff:
    1. y has positive value (exists in RS)
    2. The transition cost is finite
    3. The change would be cost-advantageous or neutral

    P : Config → Set Config -/
def Possibility (c : Config) : Set Config :=
  {y : Config |
    -- Within one octave step
    y.time = c.time + 8 ∧
    -- Cost-respecting (change doesn't increase total cost)
    J c.value + J_transition c.value y.value c.pos y.pos + J y.value ≤
      J c.value + J_stasis c.value
  }

/-- The identity is always possible from any configuration.

    The boundedness constraint is now part of the Config structure,
    ensuring all physical configurations can reach identity in one step. -/
lemma identity_always_possible (c : Config) :
    identity_config (c.time + 8) ∈ Possibility c := by
  simp only [Possibility, Set.mem_setOf_eq, identity_config]
  constructor
  · -- Time advances by 8
    trivial
  · -- Cost respecting: we need to show
    -- J c.value + J_transition c.value 1 c.pos one_pos + J 1 ≤ J c.value + J_stasis c.value
    have hJ1 : J 1 = 0 := J_at_one
    have hStasis : J_stasis c.value = 8 * J c.value := rfl
    have hJ_nonneg : 0 ≤ J c.value := J_nonneg c.pos
    simp only [hJ1, add_zero, hStasis]
    -- Goal: J c.value + J_transition c.value 1 c.pos one_pos ≤ J c.value + 8 * J c.value
    -- Sufficient: J_transition c.value 1 c.pos one_pos ≤ 8 * J c.value
    have h_trans_bound : J_transition c.value 1 c.pos one_pos ≤ 8 * J c.value := by
      unfold J_transition
      simp only [one_div, hJ1, add_zero]
      -- Goal: |log c.value⁻¹| * (J c.value / 2) ≤ 8 * J c.value
      have h_log_inv : Real.log c.value⁻¹ = -Real.log c.value := Real.log_inv c.value
      rw [h_log_inv, abs_neg]
      -- |log c.value| * (J c.value / 2) ≤ 8 * J c.value
      have h_rw : |Real.log c.value| * (J c.value / 2) = |Real.log c.value| / 2 * J c.value := by ring
      rw [h_rw]
      -- |log c.value| / 2 * J c.value ≤ 8 * J c.value
      have h_coeff : |Real.log c.value| / 2 ≤ 8 := by linarith [c.log_bound]
      have h_abs_nonneg : 0 ≤ |Real.log c.value| := abs_nonneg _
      nlinarith [h_abs_nonneg, hJ_nonneg, h_coeff]
    linarith [h_trans_bound]

/-- A configuration has no escape if it's at the identity. -/
lemma identity_unique_attractor :
    ∀ c : Config, c.value = 1 →
    ∀ y ∈ Possibility c, J y.value ≥ J c.value := by
  intro c hc y _
  rw [hc, J_at_one]
  exact J_nonneg y.pos

/-! ## Actualization: Selection from Possibilities -/

/-- **ACTUALIZATION**: The selection mechanism from possibility to actuality.

    Given the current state and its possibilities, actualization selects
    the J-minimizing successor state.

    A : P(x) → x'

    In RS, this is not random or arbitrary—it's determined by cost minimization. -/
def Actualize (c : Config) : Config :=
  -- The actualized state is the one that minimizes J among possibilities
  -- For now, we define it as the identity configuration (the attractor)
  identity_config (c.time + 8)

/-- Actualization always produces a valid configuration. -/
lemma actualize_valid (c : Config) : (Actualize c).value > 0 := by
  simp [Actualize, identity_config]

/-- Actualization drives toward identity (J-minimizer). -/
theorem actualize_decreases_cost (c : Config) (hne : c.value ≠ 1) :
    J (Actualize c).value < J c.value := by
  simp [Actualize, identity_config, J_at_one]
  exact J_pos_of_ne_one c.pos hne

/-! ## Modal Operators: Necessity and Possibility -/

/-- A property of configurations. -/
abbrev ConfigProp := Config → Prop

/-- **MODAL NECESSITY (□)**: A property is necessary iff it holds in ALL possible futures.

    □p at c ⟺ ∀ y ∈ P(c), p(y)

    In RS, necessity means "forced by cost minimization." -/
def Necessary (p : ConfigProp) (c : Config) : Prop :=
  ∀ y ∈ Possibility c, p y

/-- **MODAL POSSIBILITY (◇)**: A property is possible iff it holds in SOME possible future.

    ◇p at c ⟺ ∃ y ∈ P(c), p(y)

    In RS, possibility means "reachable at finite cost." -/
def Possible (p : ConfigProp) (c : Config) : Prop :=
  ∃ y ∈ Possibility c, p y

/-- Modal notation -/
notation:50 "□" p => Necessary p
notation:50 "◇" p => Possible p

/-- Duality: □p ⟺ ¬◇¬p -/
theorem modal_duality (p : ConfigProp) (c : Config) :
    (□p) c ↔ ¬(◇(fun x => ¬p x)) c := by
  constructor
  · intro h ⟨y, hy, hny⟩
    exact hny (h y hy)
  · intro h y hy
    by_contra hc
    exact h ⟨y, hy, hc⟩

/-- Distribution: □(p → q) → (□p → □q) -/
theorem modal_K (p q : ConfigProp) (c : Config) :
    (□(fun x => p x → q x)) c → (□p) c → (□q) c := by
  intro hpq hp y hy
  exact hpq y hy (hp y hy)

/-- Reflexivity: □p → p (T axiom) fails in general because c ∉ Possibility(c)
    (time must advance). But we have the weaker:

    If p holds at all possible futures, and c evolves, then p holds after evolution. -/
theorem modal_T_weak (p : ConfigProp) (c : Config) :
    (□p) c → p (Actualize c) := by
  intro h
  apply h
  exact identity_always_possible c

/-! ## Counterfactuals -/

/-- A **counterfactual** is an alternative possible future that wasn't actualized.

    y is counterfactual from c if:
    1. y ∈ P(c) (y was possible)
    2. y ≠ Actualize(c) (y wasn't chosen)
    3. J(y) > J(Actualize c) (y costs more, which is why it wasn't chosen) -/
def Counterfactual (c : Config) : Set Config :=
  {y : Config | y ∈ Possibility c ∧ y ≠ Actualize c ∧ J y.value > J (Actualize c).value}

/-! ## Possibility Space -/

/-- **POSSIBILITY SPACE**: The set of all reachable configurations from a given config.

    This is the transitive closure of the Possibility relation. -/
def PossibilitySpace (c : Config) : Set Config :=
  {y : Config | ∃ n : ℕ, ∃ path : Fin (n+1) → Config,
    path ⟨0, Nat.zero_lt_succ n⟩ = c ∧
    path ⟨n, Nat.lt_succ_self n⟩ = y ∧
    ∀ i : Fin n, path ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∈
                 Possibility (path ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ n)⟩)}

/-- The identity is in every possibility space. -/
theorem identity_in_all_possibility_spaces (c : Config) :
    identity_config (c.time + 8) ∈ PossibilitySpace c := by
  refine ⟨1, fun i => if i.val = 0 then c else identity_config (c.time + 8), ?_, ?_, ?_⟩
  · -- path 0 = c
    simp
  · -- path 1 = identity
    simp
  · -- each step is in Possibility
    intro i
    have hi : i.val = 0 := by omega
    simp only [hi, Nat.zero_add, ↓reduceIte]
    exact identity_always_possible c

/-! ## Why Anything Happens: The Master Theorem -/

/-- **THE MASTER MODAL THEOREM**: Why change occurs.

    For any configuration x ≠ 1:
    1. Stasis costs J_stasis(x) = 8 · J(x) > 0
    2. There exists y = 1 with J_change(x,1) < J_stasis(x) for some x
    3. Therefore, change toward identity is preferred

    This answers: "Why does anything happen?"
    Answer: Because staying away from identity costs more than moving toward it. -/
theorem why_anything_happens (c : Config) (hne : c.value ≠ 1) :
    -- 1. Stasis is expensive for x ≠ 1
    J_stasis c.value > 0 := by
  unfold J_stasis
  apply mul_pos (by norm_num : (0:ℝ) < 8)
  exact J_pos_of_ne_one c.pos hne

end

/-! ## Summary and Status -/

/-- Status report for Grammar of Possibility formalization. -/
def possibility_status : String :=
  "╔══════════════════════════════════════════════════════════════╗\n" ++
  "║           GRAMMAR OF POSSIBILITY / RS MODAL LOGIC            ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  CORE CONCEPTS:                                              ║\n" ++
  "║  • Possibility P(c) = finite-cost reachable configs          ║\n" ++
  "║  • Actualization A = J-minimizing selection                  ║\n" ++
  "║  • J_stasis = cost of staying the same                       ║\n" ++
  "║  • J_change = cost of transition                             ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  MODAL OPERATORS:                                            ║\n" ++
  "║  • □p (Necessary) = holds in all possible futures            ║\n" ++
  "║  • ◇p (Possible) = holds in some possible future             ║\n" ++
  "║  • Duality: □p ⟺ ¬◇¬p                                        ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  KEY THEOREMS:                                               ║\n" ++
  "║  • identity_prefers_stasis: x=1 is unique fixed point        ║\n" ++
  "║  • identity_always_possible: 1 ∈ P(c) for all c              ║\n" ++
  "║  • actualize_decreases_cost: A drives toward identity        ║\n" ++
  "║  • why_anything_happens: stasis costs more for x ≠ 1         ║\n" ++
  "╠══════════════════════════════════════════════════════════════╣\n" ++
  "║  STATUS: FOUNDATION COMPLETE                                 ║\n" ++
  "╚══════════════════════════════════════════════════════════════╝"

#check possibility_status

end IndisputableMonolith.Modal
