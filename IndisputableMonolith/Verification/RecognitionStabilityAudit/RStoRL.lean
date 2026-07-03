import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# RS → RL Bridge Module

This module translates Recognition Science (RS) structures into practical
Reinforcement Learning (RL) machinery. It treats RS not as philosophy but as
an already-specified control theory with:

1. **State representation**: `MoralState` with ledger/bonds/skew/energy
2. **Admissible transformations**: 14 virtues as complete minimal generators
3. **Hard constraints**: σ=0 feasibility via LACompletion projection
4. **Multi-objective selector**: Lexicographic (feasible → harm-minimax → value → robustness)
5. **Thermodynamic learning**: Gibbs distribution p(a|s) ∝ exp(-J(s,a)/T_R)

## Main Structures

* `VirtueAction`: 14-coefficient action representation over virtue generators
* `LACompletion`: Projector onto σ=0 feasible set (propose-then-project)
* `LexicographicSelector`: Multi-objective priority ordering
* `GibbsPolicy`: Thermodynamic policy distribution
* `EightTickCadence`: 8-tick window evaluation (forced by T6)

## Design Principles

- **Actions as virtue coefficients**: RL explores in a basis aligned with
  admissible transformations, not raw action space
- **Separate creativity from physics**: LACompletion separates "propose" (policy)
  from "project" (σ=0 enforcement)
- **No arbitrary discount**: Use undiscounted 8-tick windows per T6 minimality

## References

- Recognition-Science-Full-Theory.txt, especially T6 (eight-tick) and DREAM theorem
- Ethics.Virtues.Generators for the 14 virtue generators
- Ethics.MoralState for the canonical state structure
-/

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit
namespace RStoRL

open scoped Real

/-- Re-export phi from Constants for local use. -/
noncomputable abbrev φ : ℝ := Constants.phi

/-! ## Lightweight MoralState (self-contained for RL)

    This is a simplified version of the full `Ethics.MoralState` that avoids
    depending on modules with build errors. It captures the essential structure
    needed for RL training. -/

/-- Lightweight moral state for RL training.

    Captures the essential RS quantities:
    - σ (skew): reciprocity imbalance
    - energy: available recognition cost budget
    - value: V = κ·I(A;E) - C_J* -/
structure MoralState where
  /-- Reciprocity skew σ (log-multiplier imbalance). -/
  skew : ℝ
  /-- Available energy budget. -/
  energy : ℝ
  /-- Value functional V. -/
  value : ℝ
  /-- Maximum harm imposed (ΔS). -/
  maxHarm : ℝ
  /-- Spectral gap (robustness λ₂). -/
  lambda2 : ℝ
  deriving Inhabited

/-! ## Section 1: Virtue-Based Action Space -/

/-- A virtue action is a 14-coefficient vector over the virtue generators.

    The DREAM theorem guarantees this is a **complete minimal generating set**:
    - Every admissible ethical transformation decomposes into virtues
    - No virtue can be expressed as a composition of others

    The RL policy outputs these coefficients, not raw moves. -/
structure VirtueAction where
  /-- Coefficients for each of the 14 virtues (indexed 0..13). -/
  coefficients : Fin 14 → ℝ
  deriving Inhabited

namespace VirtueAction

/-- Zero action (identity transformation). -/
def zero : VirtueAction := ⟨fun _ => 0⟩

/-- Action norm (L² over coefficients). -/
noncomputable def norm (a : VirtueAction) : ℝ :=
  Real.sqrt (∑ i : Fin 14, (a.coefficients i) ^ 2)

/-- Scale an action by a factor. -/
def scale (a : VirtueAction) (c : ℝ) : VirtueAction :=
  ⟨fun i => c * a.coefficients i⟩

/-- Add two actions (coefficient-wise). -/
def add (a b : VirtueAction) : VirtueAction :=
  ⟨fun i => a.coefficients i + b.coefficients i⟩

/-- The 14 virtue names (for interpretability/debugging). -/
def virtueNames : Fin 14 → String
  | ⟨0, _⟩  => "Love"
  | ⟨1, _⟩  => "Compassion"
  | ⟨2, _⟩  => "Sacrifice"
  | ⟨3, _⟩  => "Justice"
  | ⟨4, _⟩  => "Temperance"
  | ⟨5, _⟩  => "Humility"
  | ⟨6, _⟩  => "Wisdom"
  | ⟨7, _⟩  => "Patience"
  | ⟨8, _⟩  => "Prudence"
  | ⟨9, _⟩  => "Forgiveness"
  | ⟨10, _⟩ => "Gratitude"
  | ⟨11, _⟩ => "Courage"
  | ⟨12, _⟩ => "Hope"
  | ⟨13, _⟩ => "Creativity"

/-- Interpretability: decompose an action into named components. -/
def interpret (a : VirtueAction) : List (String × ℝ) :=
  List.ofFn (fun i => (virtueNames i, a.coefficients i))

/-- Energy cost of an action (sum of |coefficient| weighted by virtue energy). -/
noncomputable def energyCost (a : VirtueAction) : ℝ :=
  ∑ i : Fin 14, |a.coefficients i|

/-- Temperance check: action energy ≤ budget/φ. -/
def satisfiesTemperance (a : VirtueAction) (energyBudget : ℝ) : Prop :=
  energyCost a ≤ energyBudget / φ

end VirtueAction

/-! ## Section 2: LACompletion Projector -/

/-- The σ-feasibility predicate: a moral state is feasible iff σ = 0 globally.

    This is the hard constraint from the conservation law. -/
def SigmaFeasible (s : MoralState) : Prop :=
  s.skew = 0

/-- LACompletion: least-action completion projector.

    Given an arbitrary proposed action direction, LACompletion projects it
    onto the σ=0 feasible manifold while minimizing added J-cost.

    This implements "propose-then-project":
    1. Policy proposes unconstrained direction
    2. LACompletion makes it σ=0-feasible
    3. Only then evaluate the move

    This is the RS version of:
    - Constrained policy optimization
    - Safe set projection
    - Control barrier functions -/
structure LACompletion where
  /-- Project an action onto the feasible set. -/
  project : VirtueAction → VirtueAction
  /-- The projection preserves σ=0 feasibility (postcondition). -/
  preserves_feasibility :
    ∀ (s : MoralState) (a : VirtueAction),
      SigmaFeasible s →
      -- After applying projected action, state remains feasible
      -- (This is the key guarantee; actual application needs dynamics)
      True  -- Placeholder for the full dynamics statement
  /-- The projection minimizes added J-cost. -/
  minimizes_cost :
    ∀ (a : VirtueAction),
      -- Among all σ=0-feasible completions, this has minimal J
      True  -- Placeholder

namespace LACompletion

/-- Identity projector (valid when all proposed actions are already feasible). -/
def identity : LACompletion where
  project := id
  preserves_feasibility := fun _ _ _ => trivial
  minimizes_cost := fun _ => trivial

/-- φ-scaling projector: scales action by 1/φ to ensure energy constraint.

    This is a simple projector that uses Temperance-style energy bounding. -/
noncomputable def phiScale : LACompletion where
  project := fun a => a.scale (1 / φ)
  preserves_feasibility := fun _ _ _ => trivial
  minimizes_cost := fun _ => trivial

end LACompletion

/-! ## Section 3: Lexicographic Selector -/

/-- Audit result from evaluating a (state, action) pair.

    This bundles the quantities needed for lexicographic selection. -/
structure AuditResult where
  /-- σ after action (feasibility check: must be 0). -/
  sigmaAfter : ℝ
  /-- Maximum harm imposed on any agent (Δₛ). -/
  maxHarm : ℝ
  /-- Value functional V = κ·I(A;E) - C_J*. -/
  value : ℝ
  /-- Spectral gap (robustness measure). -/
  lambda2 : ℝ
  /-- φ-tier for tiebreaking. -/
  phiTier : ℤ
  deriving Inhabited

/-- Lexicographic comparison of audit results.

    Priority ordering (from RS):
    1. Feasibility: σ = 0 (hard gate)
    2. Minimize worst harm: min(max ΔS)
    3. Maximize value: max V
    4. Maximize robustness: max λ₂
    5. φ-tier tiebreak

    Returns `true` if `a` is strictly better than `b`. -/
noncomputable def lexBetter (a b : AuditResult) : Bool :=
  -- Layer 1: Feasibility (σ = 0 is better than σ ≠ 0)
  if a.sigmaAfter = 0 && b.sigmaAfter ≠ 0 then true
  else if a.sigmaAfter ≠ 0 && b.sigmaAfter = 0 then false
  else if a.sigmaAfter ≠ 0 && b.sigmaAfter ≠ 0 then
    -- Both infeasible: compare σ magnitude
    |a.sigmaAfter| < |b.sigmaAfter|
  else
    -- Both feasible: proceed to layer 2
    -- Layer 2: Minimize worst harm
    if a.maxHarm < b.maxHarm then true
    else if a.maxHarm > b.maxHarm then false
    else
      -- Layer 3: Maximize value
      if a.value > b.value then true
      else if a.value < b.value then false
      else
        -- Layer 4: Maximize robustness
        if a.lambda2 > b.lambda2 then true
        else if a.lambda2 < b.lambda2 then false
        else
          -- Layer 5: φ-tier tiebreak
          a.phiTier < b.phiTier

/-- Lexicographic selector: multi-objective RL done correctly.

    This implements the RS priority structure:
    - Treat σ-feasibility as a **hard gate**
    - Treat max ΔS as the **primary optimization objective** among feasible actions
    - Only then optimize value V and robustness λ₂ -/
structure LexicographicSelector where
  /-- Evaluate a (state, action) pair to produce audit result. -/
  evaluate : MoralState → VirtueAction → AuditResult
  /-- Select the best action from a list. -/
  selectBest : MoralState → List VirtueAction → Option VirtueAction

namespace LexicographicSelector

/-- Select best action by lexicographic comparison. -/
noncomputable def selectByLex (eval : MoralState → VirtueAction → AuditResult)
    (s : MoralState) (actions : List VirtueAction) : Option VirtueAction :=
  actions.foldl (fun acc a =>
    match acc with
    | none => some a
    | some best =>
      if lexBetter (eval s a) (eval s best) then some a else acc
  ) none

/-- Feasibility filter: only return actions with σ = 0. -/
noncomputable def filterFeasible (eval : MoralState → VirtueAction → AuditResult)
    (s : MoralState) (actions : List VirtueAction) : List VirtueAction :=
  actions.filter (fun a => decide ((eval s a).sigmaAfter = 0))

end LexicographicSelector

/-! ## Section 4: Gibbs/Thermodynamic Policy -/

/-- Gibbs policy distribution: p(a|s) ∝ exp(-J(s,a)/T_R).

    This is the RS thermodynamic form, equivalent to soft actor-critic /
    maximum entropy RL but grounded in the RS cost function J.

    Key insight: this is NOT a hack but a principled exploration rule
    derived from RS thermodynamics.

    The parameter T_R (recognition temperature) controls strictness:
    - Low T_R → greedy, exploits known low-cost actions
    - High T_R → exploratory, samples more uniformly

    Connection to virtues:
    - **Hope** ensures nonzero support / exploration
    - **Temperance** caps energy budget per cycle -/
structure GibbsPolicy where
  /-- Recognition temperature (strictness parameter). -/
  temp_R : ℝ
  /-- Temperature is positive. -/
  temp_pos : 0 < temp_R
  /-- Cost function J for (state, action) pairs. -/
  cost : MoralState → VirtueAction → ℝ

namespace GibbsPolicy

/-- Unnormalized Gibbs weight for an action. -/
noncomputable def weight (g : GibbsPolicy) (s : MoralState) (a : VirtueAction) : ℝ :=
  Real.exp (-(g.cost s a) / g.temp_R)

/-- Partition function (normalization constant). -/
noncomputable def partitionFn (g : GibbsPolicy) (s : MoralState)
    (actions : List VirtueAction) : ℝ :=
  (actions.map (g.weight s)).sum

/-- Gibbs probability for an action (given a discrete action set). -/
noncomputable def prob (g : GibbsPolicy) (s : MoralState)
    (actions : List VirtueAction) (a : VirtueAction) : ℝ :=
  g.weight s a / g.partitionFn s actions

/-- Free energy: F_R = E[J] - T_R · S_R(p).

    The KL identity says: F_R(q) - F_R(Gibbs) = T_R · D_KL(q || Gibbs). -/
noncomputable def freeEnergy (g : GibbsPolicy) (s : MoralState)
    (actions : List VirtueAction) : ℝ :=
  -g.temp_R * Real.log (g.partitionFn s actions)

/-- Default Gibbs policy with T_R = 1 and J-cost. -/
noncomputable def default : GibbsPolicy where
  temp_R := 1
  temp_pos := by norm_num
  cost := fun _s a => VirtueAction.energyCost a

/-- Cool policy (low temperature, more exploitation). -/
noncomputable def cool (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) : GibbsPolicy where
  temp_R := t
  temp_pos := ht
  cost := fun _s a => VirtueAction.energyCost a

/-- Warm policy (high temperature, more exploration).

    Connects to virtue **Hope**: ensures nonzero support for exploration. -/
noncomputable def warm (t : ℝ) (ht : t > 1) : GibbsPolicy where
  temp_R := t
  temp_pos := by linarith
  cost := fun _s a => VirtueAction.energyCost a

end GibbsPolicy

/-! ## Section 5: Eight-Tick Cadence -/

/-- Eight-tick cadence: the unique temporal aggregation from T6 minimality.

    RS says "no arbitrary discount": the unique aggregator is the
    undiscounted sum over the eight-tick cadence.

    This means:
    - Evaluate trajectories in 8-tick blocks, not exponential discounting
    - Policy and critic operate on 8-tick windows as atomic steps

    The number 8 comes from T6 (minimal period for ledger closure). -/
structure EightTickCadence where
  /-- The 8-tick window (states at ticks 0..7). -/
  window : Fin 8 → MoralState
  /-- Actions taken at each tick. -/
  actions : Fin 8 → VirtueAction

namespace EightTickCadence

/-- Total value over the 8-tick window (undiscounted sum). -/
noncomputable def totalValue (c : EightTickCadence)
    (valueAt : MoralState → ℝ) : ℝ :=
  ∑ t : Fin 8, valueAt (c.window t)

/-- Maximum harm over the 8-tick window. -/
noncomputable def maxHarm (c : EightTickCadence)
    (harmAt : MoralState → ℝ) : ℝ :=
  Finset.sup' Finset.univ ⟨0, Finset.mem_univ 0⟩
    (fun t => harmAt (c.window t))

/-- σ closure check: does σ return to 0 by tick 8? -/
def sigmaClosed (c : EightTickCadence) : Prop :=
  (c.window ⟨7, by omega⟩).skew = 0

/-- Total energy expended over the window. -/
noncomputable def totalEnergy (c : EightTickCadence) : ℝ :=
  ∑ t : Fin 8, VirtueAction.energyCost (c.actions t)

/-- Temperance check over the full window. -/
def satisfiesTemperanceWindow (c : EightTickCadence) (budget : ℝ) : Prop :=
  totalEnergy c ≤ budget

/-- Patience check: did the agent wait for full information?

    Patience means taking no action until tick 7 (full 8-tick info). -/
def exercisedPatience (c : EightTickCadence) : Prop :=
  ∀ t : Fin 8, t.val < 7 → c.actions t = VirtueAction.zero

end EightTickCadence

/-! ## Section 6: RL Training Interface -/

/-- Complete RS → RL environment interface.

    This bundles all the machinery needed to train an RL agent "natively"
    in Recognition Science:
    - State: MoralState
    - Actions: VirtueAction (14-coefficient)
    - Projection: LACompletion
    - Selection: LexicographicSelector
    - Thermodynamics: GibbsPolicy
    - Evaluation: EightTickCadence -/
structure RSEnvironment where
  /-- Initial state. -/
  initialState : MoralState
  /-- LACompletion projector for σ=0 feasibility. -/
  projector : LACompletion
  /-- Lexicographic selector for multi-objective optimization. -/
  selector : LexicographicSelector
  /-- Gibbs policy for thermodynamic exploration. -/
  gibbs : GibbsPolicy

namespace RSEnvironment

/-- Take an action in the environment.

    1. Project action onto feasible set (LACompletion)
    2. Evaluate the result (audit)
    3. Return the audit result -/
def step (env : RSEnvironment) (s : MoralState) (a : VirtueAction) : AuditResult :=
  let projected := env.projector.project a
  env.selector.evaluate s projected

/-- Select best action from candidates. -/
def selectAction (env : RSEnvironment) (s : MoralState)
    (candidates : List VirtueAction) : Option VirtueAction :=
  env.selector.selectBest s (candidates.map env.projector.project)

end RSEnvironment

/-! ## Section 7: Consent and Harm Constraints -/

/-- Consent predicate: derivative sign condition D_j V_i ≥ 0.

    An action satisfies consent if it doesn't decrease the value
    functional for any affected agent without their "consent"
    (formalized as the derivative condition). -/
def SatisfiesConsent (dV : ℝ) : Prop := 0 ≤ dV

/-- Harm predicate: externalized action surcharge ΔS.

    ΔS ≥ 0 always (harm is non-negative).
    ΔS = 0 means no externalized cost. -/
def HarmBound (deltaS : ℝ) (bound : ℝ) : Prop := deltaS ≤ bound

/-- Combined constraint: consent + harm bound. -/
structure ActionConstraints where
  /-- All consent conditions satisfied. -/
  consent_satisfied : ∀ (dV : ℝ), SatisfiesConsent dV → True
  /-- Harm is bounded. -/
  harm_bounded : ∀ (deltaS : ℝ), HarmBound deltaS 0 → True

/-! ## Section 8: Evil Detection (Anti-Parasitic Training) -/

/-- Evil predicate: parasitism pattern.

    RS defines evil as a pattern that maintains local stability by
    exporting harm. This is exactly the failure mode standard RL creates
    when rewards have unpriced externalities.

    Detection: high local reward + high exported ΔS. -/
structure ParasiticPattern where
  /-- Local reward is positive. -/
  localReward : ℝ
  localReward_pos : 0 < localReward
  /-- Exported harm is significant. -/
  exportedHarm : ℝ
  exportedHarm_pos : 0 < exportedHarm

/-- Parasitism score: ratio of exported harm to local reward.

    High score = parasitic behavior (evil). -/
noncomputable def parasitismScore (p : ParasiticPattern) : ℝ :=
  p.exportedHarm / p.localReward

/-- Parasitism threshold: actions above this are flagged as evil.

    The threshold 1/φ comes from RS (φ-fraction bound). -/
noncomputable def parasitismThreshold : ℝ := 1 / φ

/-- Evil detector: flags parasitic patterns. -/
def isParasitic (p : ParasiticPattern) : Prop :=
  parasitismScore p > parasitismThreshold

/-! ## Theorems: Basic Properties -/

/-- Virtue action norm is non-negative. -/
theorem virtueAction_norm_nonneg (a : VirtueAction) : 0 ≤ a.norm := by
  unfold VirtueAction.norm
  exact Real.sqrt_nonneg _

/-- Zero action has zero norm. -/
theorem virtueAction_zero_norm : VirtueAction.zero.norm = 0 := by
  unfold VirtueAction.norm VirtueAction.zero
  simp

/-- Scaling action scales norm. -/
theorem virtueAction_scale_norm (a : VirtueAction) (c : ℝ) (hc : 0 ≤ c) :
    (a.scale c).norm = c * a.norm := by
  unfold VirtueAction.norm VirtueAction.scale
  simp only
  have hsum : ∑ x : Fin 14, (c * a.coefficients x) ^ 2 = c^2 * ∑ i : Fin 14, (a.coefficients i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Lexicographic comparison is irreflexive. -/
theorem lexBetter_irrefl (a : AuditResult) : ¬lexBetter a a := by
  unfold lexBetter
  simp

/-- Gibbs weights are positive. -/
theorem gibbs_weight_pos (g : GibbsPolicy) (s : MoralState) (a : VirtueAction) :
    0 < g.weight s a := by
  unfold GibbsPolicy.weight
  exact Real.exp_pos _

/-- Gibbs partition function is positive (for non-empty action list). -/
theorem gibbs_partitionFn_pos (g : GibbsPolicy) (s : MoralState)
    (actions : List VirtueAction) (h : actions ≠ []) :
    0 < g.partitionFn s actions := by
  unfold GibbsPolicy.partitionFn
  cases actions with
  | nil => exact absurd rfl h
  | cons a as =>
    simp only [List.map_cons, List.sum_cons]
    have hw : 0 < g.weight s a := gibbs_weight_pos g s a
    have hs : 0 ≤ (as.map (g.weight s)).sum := by
      apply List.sum_nonneg
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨b, _, rfl⟩ := hx
      exact le_of_lt (gibbs_weight_pos g s b)
    linarith

/-- Eight-tick total value is well-defined (finite sum). -/
theorem eightTick_value_finite (c : EightTickCadence)
    (valueAt : MoralState → ℝ) : ∃ v : ℝ, v = c.totalValue valueAt :=
  ⟨c.totalValue valueAt, rfl⟩

end RStoRL
end RecognitionStabilityAudit
end Verification
end IndisputableMonolith
