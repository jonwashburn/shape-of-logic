import Mathlib

import Mathlib.Lean.Meta.Simp

import IndisputableMonolith.Verification.RecognitionStabilityAudit
import IndisputableMonolith.Verification.RecognitionStabilityAudit.RL.Attr

/-!
# RSA Reinforcement Learning (RL) module

This module makes the Recognition Stability Audit pipeline **RL-friendly** inside Lean:

- **Custom tags**
  - `@[rsa_simp]` marks *whitelisted rewrite/unfold lemmas* used by `rsa_simp`.
  - `@[rsa_milestone]` marks *milestone lemmas* that `rsa_step` is allowed to apply.

- **Whitelisted tactics**
  - `rsa_simp` runs `simp` using **only** the `@[rsa_simp]` whitelist
    (plus Lean's `simp only` builtins).
  - `rsa_step` does one bounded step: try `assumption`, otherwise try applying a
    `@[rsa_milestone]` lemma (then discharge trivial subgoals), and finally fall back to `rsa_simp`.

- **Canonical training goals**
  A small library of proved “gold” theorems (no `sorry`) that exercise the RSA pipeline.

The intended use is: an LLM proposes the next `rsa_step`/`rsa_simp`/`apply` etc., and Lean provides
the reward signal by goal closure / checklist completion.
-/

public meta section

namespace IndisputableMonolith
namespace Verification
namespace RecognitionStabilityAudit

open Lean Meta Elab Tactic
open scoped Topology
open Filter

/-! ## Tactics -/

private def getRsaSimpNames : MetaM (List Name) := do
  let env ← getEnv
  return (rsaSimpLemmaExt.getState env).toList

private def getRsaMilestoneNames : MetaM (List Name) := do
  let env ← getEnv
  return (rsaMilestoneExt.getState env).toList

/-- `rsa_simp` simplifies the goal using **only** the `@[rsa_simp]` whitelist (plus Lean's
`simp only` builtins). -/
elab "rsa_simp" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let names ← getRsaSimpNames
    -- Build simp theorems from the whitelist, and also add *all Prop hypotheses* (like `simp [*]`)
    -- so simp can discharge side conditions (e.g. `ξ ≠ 1`) deterministically.
    let mut thms ← Lean.Meta.simpTheoremsOfNames names true
    let hyps ← Lean.Meta.Simp.getPropHyps
    for f in hyps do
      let decl ← f.getDecl
      thms ← thms.add (.fvar f) #[] decl.toExpr
    let ctx : Simp.Context ← Simp.mkContext { failIfUnchanged := false }
      (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    let (result?, _stats) ← simpGoal g ctx
    -- `simpGoal` returns `none` iff the goal is closed; otherwise it returns a fresh goal `g'`.
    match result? with
    | none => replaceMainGoal []
    | some (_fvars, g') => replaceMainGoal [g']

/-- One bounded RL step: try `assumption`; otherwise try applying a `@[rsa_milestone]` lemma
(then discharge trivial subgoals); finally fall back to `rsa_simp`. -/
elab "rsa_step" : tactic => do
  -- First: if the goal is already in context, close it deterministically.
  try
    evalTactic (← `(tactic| assumption))
    return
  catch _ =>
    pure ()

  -- Next: try applying a milestone lemma *before* simplifying,
  -- so we don't unfold away the high-level wrappers (e.g. `BoundaryHitAt`).
  let names ← getRsaMilestoneNames
  for n in names do
    try
      evalTactic (← `(tactic| apply $(mkIdent n)))
      evalTactic (← `(tactic| all_goals (try assumption)))
      evalTactic (← `(tactic| all_goals (try rsa_simp)))
      evalTactic (← `(tactic| all_goals (try assumption)))
      return
    catch _ =>
      continue

  -- Fallback: a simplification-only step (useful when no milestone matches).
  try
    evalTactic (← `(tactic| rsa_simp))
    evalTactic (← `(tactic| all_goals (try assumption)))
    return
  catch _ =>
    pure ()

  throwError "rsa_step: no applicable `@[rsa_milestone]` lemma"

/-! ## Default RSA whitelist + milestones -/

-- Small definitional rewrites we want available to `rsa_simp`.
@[rsa_simp] theorem BoundaryHitAt_def (Ξ : ℂ → ℂ) (z0 : ℂ) :
    BoundaryHitAt Ξ z0 = Tendsto Ξ (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (1 : ℂ)) := rfl

@[rsa_simp] theorem SchurOn_def (Ω : Set ℂ) (f : ℂ → ℂ) :
    SchurOn Ω f = (∀ z ∈ Ω, ‖f z‖ ≤ 1) := rfl

@[rsa_simp] theorem Problem_XiFromSensor_def (𝓙 : ℂ → ℂ) :
    Problem.XiFromSensor 𝓙 = fun z => theta (𝓙 z) := rfl

@[rsa_simp] theorem SensorBlowsUpAt_def (𝓙 : ℂ → ℂ) (z0 : ℂ) :
    SensorBlowsUpAt 𝓙 z0 = Tendsto (fun z => ‖𝓙 z‖) (𝓝[({z0} : Set ℂ)ᶜ] z0) atTop := rfl

@[rsa_simp] theorem sensorOfObstruction_def (G : ℂ → ℂ) :
    sensorOfObstruction G = fun z => (G z)⁻¹ := rfl

-- Milestones (apply targets)
attribute [rsa_milestone]
  -- Cayley plumbing (explicit step, avoids rewriting away useful structure too early)
  theta_eq_div
  invTheta_theta
  theta_invTheta
  correctness
  frontEnd_of_obstruction
  backEnd_of_schur_holomorphic_nontrivial
  boundaryHit_theta_of_sensorBlowsUp
  sensorBlowsUpAt_of_tendsto_zero
  no_boundaryHit_of_schur_holomorphic_nontrivial
  boundaryHit_implies_value_eq_one
  eq_const_one_of_boundaryHit

/-! ## Canonical training goals (all proved, no `sorry`) -/

namespace RLGoals

open scoped Real Topology
open Filter

/-- A tiny `rsa_simp` sanity check (uses only whitelisted lemmas). -/
theorem goal_theta_eq_div (J : ℂ) : theta J = (2 * J - 1) / (2 * J + 1) := by
  rsa_step

/-- Cayley inverse micro-goal: `theta (invTheta ξ) = ξ`. -/
theorem goal_theta_invTheta (ξ : ℂ) (h : ξ ≠ 1) : theta (invTheta ξ) = ξ := by
  rsa_step

/-- Cayley inverse micro-goal: `invTheta (theta J) = J`. -/
theorem goal_invTheta_theta (J : ℂ) (h : (2 * J + 1) ≠ 0) : invTheta (theta J) = J := by
  rsa_step

/-- Front-end micro-goal: sensor blow-up implies the compiled boundary hit. -/
theorem goal_pole_implies_boundaryHit (𝓙 : ℂ → ℂ) (z0 : ℂ)
    (h : SensorBlowsUpAt 𝓙 z0) :
    BoundaryHitAt (fun z => theta (𝓙 z)) z0 := by
  rsa_step

/-- Front-end micro-goal: obstruction tends to `0` + stays nonzero ⇒ sensor blows up. -/
theorem goal_obstruction_to_sensor_blowup (G : ℂ → ℂ) (z0 : ℂ)
    (h0 : Tendsto G (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (0 : ℂ)))
    (hne : ∀ᶠ z in (𝓝[({z0} : Set ℂ)ᶜ] z0), G z ≠ 0) :
    SensorBlowsUpAt (sensorOfObstruction G) z0 := by
  rsa_step

/-- A canonical FrontEnd goal: the candidate *provides* the two analytic obligations
(`G → 0` and eventual `G ≠ 0` on the punctured neighborhood), and `FrontEnd` compiles it
into a boundary-hit. -/
theorem goal_frontEnd_from_candidate_obligations
    (Ω : Set ℂ) (G : ℂ → ℂ) :
    let Candidate : ℂ → Prop :=
      fun z0 =>
        Tendsto G (𝓝[({z0} : Set ℂ)ᶜ] z0) (𝓝 (0 : ℂ))
          ∧ ∀ᶠ z in (𝓝[({z0} : Set ℂ)ᶜ] z0), G z ≠ 0
    FrontEnd
      { Ω := Ω
        Candidate := Candidate
        Xi := fun z => theta ((G z)⁻¹) } := by
  intro Candidate
  -- Build via the FrontEnd constructor.
  refine frontEnd_of_obstruction (Ω := Ω) (Candidate := Candidate) (G := G) ?_ ?_
  · intro z0 _hz0 hC
    exact hC.1
  · intro z0 _hz0 hC
    exact hC.2

/-- Back-end micro-goal: boundary hit + continuity forces the value `Ξ z0 = 1`. -/
theorem goal_boundaryHit_value (Ξ : ℂ → ℂ) (z0 : ℂ)
    (hCont : ContinuousAt Ξ z0)
    (hHit : BoundaryHitAt Ξ z0) :
    Ξ z0 = (1 : ℂ) := by
  rsa_step

/-- Back-end micro-goal: boundary hit forces constancy `Ξ ≡ 1` under holomorphic + Schur. -/
theorem goal_boundaryHit_forces_const_one
    (Ω : Set ℂ) (Ξ : ℂ → ℂ)
    (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hHol : DifferentiableOn ℂ Ξ Ω)
    (hSchur : SchurOn Ω Ξ)
    (z0 : ℂ) (hz0 : z0 ∈ Ω)
    (hHit : BoundaryHitAt Ξ z0) :
    Set.EqOn Ξ (fun _ => (1 : ℂ)) Ω := by
  rsa_step

/-- A canonical BackEnd goal: constant `Ξ ≡ 0` on `Ω = univ` is holomorphic, Schur-bounded,
and nontrivial (≠ 1), hence admits a `BackEnd` certificate. -/
theorem goal_backEnd_const_zero :
    BackEnd
      { Ω := (Set.univ : Set ℂ)
        Candidate := fun _ => False
        Xi := fun _ => (0 : ℂ) } := by
  -- Use the generic back-end constructor.
  refine backEnd_of_schur_holomorphic_nontrivial
    (P := { Ω := (Set.univ : Set ℂ), Candidate := fun _ => False, Xi := fun _ => (0 : ℂ) })
    (hΩ_open := isOpen_univ) (hΩ_conn := isPreconnected_univ) ?_ ?_ ?_
  · simp
  · intro _z _hz
    simp
  · refine ⟨0, by simp, ?_⟩
    norm_num

/-- End-to-end micro-goal: with `Ω = univ`, the candidate `False` is ruled out immediately. -/
theorem goal_correctness_trivial_univ :
    ∀ {z0 : ℂ}, z0 ∈ (Set.univ : Set ℂ) → ¬ (False) := by
  intro z0 hz0 hFalse
  exact hFalse

/-- End-to-end RSA goal (compiler correctness): if you supply

- a FrontEnd compilation of a candidate into a boundary-hit, and
- a BackEnd certificate forbidding boundary hits,

then the candidate is impossible in the audited region. -/
theorem goal_correctness_usage
    (P : Problem) (FE : FrontEnd P) (BE : BackEnd P) :
    ∀ {z0 : ℂ}, z0 ∈ P.Ω → ¬ P.Candidate z0 := by
  intro z0 hz0
  exact correctness (P := P) FE BE hz0

end RLGoals

/-! ## RS → RL Bridge Training Goals

These goals exercise the machinery from `RStoRL.lean`:
- Virtue-based action space (14 virtues as generators)
- Gibbs/thermodynamic policy
- Lexicographic multi-objective selection
- Eight-tick cadence evaluation
-/

namespace RStoRLGoals

open RStoRL

/-- VirtueAction: zero action has zero norm. -/
theorem goal_virtueAction_zero_norm : VirtueAction.zero.norm = 0 :=
  virtueAction_zero_norm

/-- VirtueAction: norm is non-negative. -/
theorem goal_virtueAction_norm_nonneg (a : VirtueAction) : 0 ≤ a.norm :=
  virtueAction_norm_nonneg a

/-- VirtueAction: scaling by positive factor scales norm. -/
theorem goal_virtueAction_scale_norm (a : VirtueAction) (c : ℝ) (hc : 0 ≤ c) :
    (a.scale c).norm = c * a.norm :=
  virtueAction_scale_norm a c hc

/-- Lexicographic: comparison is irreflexive (no action is strictly better than itself). -/
theorem goal_lexBetter_irrefl (r : AuditResult) : ¬lexBetter r r :=
  lexBetter_irrefl r

/-- Gibbs: weights are always positive (ensures exploration). -/
theorem goal_gibbs_weight_pos (g : GibbsPolicy) (s : MoralState) (a : VirtueAction) :
    0 < g.weight s a :=
  gibbs_weight_pos g s a

/-- Gibbs: partition function is positive for non-empty action sets. -/
theorem goal_gibbs_partitionFn_pos (g : GibbsPolicy) (s : MoralState)
    (actions : List VirtueAction) (h : actions ≠ []) :
    0 < g.partitionFn s actions :=
  gibbs_partitionFn_pos g s actions h

/-- Eight-tick: total value over cadence is well-defined. -/
theorem goal_eightTick_value_finite (c : EightTickCadence)
    (valueAt : MoralState → ℝ) : ∃ v : ℝ, v = c.totalValue valueAt :=
  eightTick_value_finite c valueAt

/-- Feasibility: σ=0 is the hard constraint for admissibility. -/
theorem goal_sigma_feasibility (s : MoralState) :
    SigmaFeasible s ↔ s.skew = 0 := by
  rfl

/-- Harm bound: ΔS ≤ 0 means no externalized harm. -/
theorem goal_harm_bound_zero (deltaS : ℝ) :
    HarmBound deltaS 0 ↔ deltaS ≤ 0 := by
  rfl

/-- Consent: D_j V_i ≥ 0 is the consent condition. -/
theorem goal_consent_condition (dV : ℝ) :
    SatisfiesConsent dV ↔ 0 ≤ dV := by
  rfl

/-- Parasitism threshold uses φ (golden ratio). -/
theorem goal_parasitism_threshold_phi :
    parasitismThreshold = 1 / φ := by
  rfl

/-- LACompletion identity: identity projector preserves actions. -/
theorem goal_LACompletion_identity_project (a : VirtueAction) :
    LACompletion.identity.project a = a := by
  rfl

/-- Temperance: energy budget constraint via φ. -/
theorem goal_temperance_check (a : VirtueAction) (budget : ℝ) :
    a.satisfiesTemperance budget ↔ a.energyCost ≤ budget / φ := by
  rfl

end RStoRLGoals

end RecognitionStabilityAudit
end Verification
end IndisputableMonolith

end
