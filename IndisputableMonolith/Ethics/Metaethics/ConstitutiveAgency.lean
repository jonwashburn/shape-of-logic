import Mathlib
import IndisputableMonolith.Ethics.ThermodynamicInstabilityOfExtraction

/-!
# Track A — Constitutive Agency and Budget Exhaustion

This module implements Track A of the Metaethics Closure Program
(`Metaethics_Closure_Program_20260529.html`). It establishes the *physical*
half of the is–ought bridge: a recognition agent is a bounded recognition
structure, and sustained extraction (holding skew `σ` away from balance) is
self-terminating, because its maintenance cost `2(cosh σ − 1)` per window
exhausts any finite renewable budget in finite time.

Nothing here is normative yet. Every result is a descriptive necessity claim:
*if* a structure continues to be an agent, *then* it does not sustain
extraction. The normative bridge (from this necessity to an "ought") is built
in `TranscendentalKernel.lean` (Track C), and depends on exactly one named
posit. The other-regarding extension is in `CoupledNormativity.lean` (Track B).

Builds on the proved theorems of `IndisputableMonolith.Ethics.Extraction`
(`extraction_cost_eq_cosh`, `extraction_creates_surcharge`,
`extraction_cost_eq_zero_iff`).

## Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Ethics
namespace Metaethics

open scoped BigOperators

noncomputable section

/-! ## A2 — The keystone: extraction exhausts a bounded budget

The reserve of a structure that holds a constant skew `σ₀` against a renewable
per-window budget `B` evolves linearly with slope `B − cost(σ₀)`. If the
maintenance cost exceeds the budget, the reserve is driven below zero in finite
time. This is the lemma that turns "extraction is expensive" into "extraction
is fatal," which is the actual lever the metaethics uses. -/

/-- Reserve after `n` windows under a constant-skew `σ₀` policy with renewable
budget `B` and initial reserve `R₀`. -/
def cumulativeReserve (B σ₀ R₀ : ℝ) (n : ℕ) : ℝ :=
  R₀ + (n : ℝ) * (B - Extraction.extractionSystemCost σ₀)

/-- **A2 (keystone).** If the per-window maintenance cost of a sustained skew
`σ₀` exceeds the renewable budget `B`, then the reserve is non-positive from
some finite window onward: the structure cannot persist. -/
theorem extraction_exhausts_budget
    (B σ₀ R₀ : ℝ) (_hB : 0 < B) (_hR : 0 ≤ R₀)
    (hcost : Extraction.extractionSystemCost σ₀ > B) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → cumulativeReserve B σ₀ R₀ n ≤ 0 := by
  set d : ℝ := Extraction.extractionSystemCost σ₀ - B with hd
  have hd_pos : 0 < d := by rw [hd]; linarith
  refine ⟨⌈R₀ / d⌉₊, ?_⟩
  intro n hn
  unfold cumulativeReserve
  have hBc : B - Extraction.extractionSystemCost σ₀ = -d := by rw [hd]; ring
  rw [hBc]
  have hNd : R₀ / d ≤ (⌈R₀ / d⌉₊ : ℝ) := Nat.le_ceil _
  have hnN : (⌈R₀ / d⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : R₀ / d ≤ (n : ℝ) := le_trans hNd hnN
  have h2 : R₀ ≤ (n : ℝ) * d := (div_le_iff₀ hd_pos).mp h1
  have hmul : (n : ℝ) * (-d) = -((n : ℝ) * d) := by ring
  rw [hmul]; linarith

/-! ## A1 — The recognition agent

A recognition agent is a worldline of skews across eight-tick windows, a
finite renewable J-budget per window, and an initial reserve. Viability is a
positive reserve: the structure still has the capacity to maintain its
boundary. "Continuing as an agent" is viability at every window. -/

/-- A recognition agent: a per-window skew policy with a finite renewable
budget and a starting reserve. -/
structure RecognitionAgent where
  /-- Skew held at each eight-tick window. -/
  σ : ℕ → ℝ
  /-- Renewable J-capacity available per window. -/
  budget : ℝ
  budget_pos : 0 < budget
  /-- Starting reserve. -/
  initReserve : ℝ
  initReserve_nonneg : 0 ≤ initReserve

/-- Reserve of an agent after `n` windows: starting reserve plus the running
sum of (budget − maintenance cost) over each window. -/
def RecognitionAgent.reserve (S : RecognitionAgent) (n : ℕ) : ℝ :=
  S.initReserve +
    ∑ k ∈ Finset.range n, (S.budget - Extraction.extractionSystemCost (S.σ k))

/-- The agent is viable at window `n` when its reserve is positive. -/
def RecognitionAgent.viable (S : RecognitionAgent) (n : ℕ) : Prop :=
  0 < S.reserve n

/-- The agent continues as an agent when it is viable at every window. -/
def ContinuesAsAgent (S : RecognitionAgent) : Prop :=
  ∀ n : ℕ, S.viable n

/-- An agent sustains extraction when there is a skew floor `σ₀` whose
maintenance cost exceeds the budget and every window's cost is at least that
floor. This is the formal content of "systematically holding imbalance." -/
def SustainsExtraction (S : RecognitionAgent) : Prop :=
  ∃ σ₀ : ℝ, Extraction.extractionSystemCost σ₀ > S.budget ∧
    ∀ k : ℕ, Extraction.extractionSystemCost σ₀ ≤ Extraction.extractionSystemCost (S.σ k)

/-! ## A3 — Sustained extraction is self-defeating -/

/-- **A3.** An agent that sustains extraction ceases to be viable from some
finite window onward: the policy deletes the agent that runs it. -/
theorem extraction_policy_is_self_defeating (S : RecognitionAgent)
    (h : SustainsExtraction S) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ S.viable n := by
  obtain ⟨σ₀, hcost, hfloor⟩ := h
  set d : ℝ := Extraction.extractionSystemCost σ₀ - S.budget with hd
  have hd_pos : 0 < d := by rw [hd]; linarith
  refine ⟨⌈S.initReserve / d⌉₊, ?_⟩
  intro n hn
  unfold RecognitionAgent.viable
  rw [not_lt]
  -- Each window's net change is at most −d.
  have hterm : ∀ k ∈ Finset.range n,
      S.budget - Extraction.extractionSystemCost (S.σ k) ≤ -d := by
    intro k _
    have := hfloor k
    rw [hd]; linarith
  have hsum : ∑ k ∈ Finset.range n, (S.budget - Extraction.extractionSystemCost (S.σ k))
            ≤ ∑ _k ∈ Finset.range n, (-d) := Finset.sum_le_sum hterm
  have hconst : (∑ _k ∈ Finset.range n, (-d)) = (n : ℝ) * (-d) := by
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNd : S.initReserve / d ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have h2 : S.initReserve ≤ (n : ℝ) * d := (div_le_iff₀ hd_pos).mp hNd
  unfold RecognitionAgent.reserve
  have hmul : (n : ℝ) * (-d) = -((n : ℝ) * d) := by ring
  calc S.initReserve
        + ∑ k ∈ Finset.range n, (S.budget - Extraction.extractionSystemCost (S.σ k))
      ≤ S.initReserve + (n : ℝ) * (-d) := by
          have := hsum; rw [hconst] at this; linarith
    _ = S.initReserve - (n : ℝ) * d := by rw [hmul]; ring
    _ ≤ 0 := by linarith

/-! ## A4 — The constitutive "ought" (descriptive necessity)

`AgentOught P` says `P` is a *necessary condition* of continued agency: every
agent that continues to be an agent satisfies `P`. This is pure modal/necessity
content — no value is built into the definition. The normative reading is
supplied only in Track C, and only via the named kernel. -/

/-- A property `P` is an agent-ought when it is a necessary condition of
continued agency. -/
def AgentOught (P : RecognitionAgent → Prop) : Prop :=
  ∀ S : RecognitionAgent, ContinuesAsAgent S → P S

/-- **A4.** Not sustaining extraction is an agent-ought: every agent that
continues to be an agent does not sustain extraction. This is the is–ought
lever stated as a theorem about necessity, proved from A3. -/
theorem sigma_bounding_is_agent_ought :
    AgentOught (fun S => ¬ SustainsExtraction S) := by
  intro S hcont hext
  obtain ⟨N, hN⟩ := extraction_policy_is_self_defeating S hext
  exact (hN N le_rfl) (hcont N)

/-! ### A4′ — Extraction is not itself an agent-ought

To show "do not extract" is a genuine necessary condition (and not vacuous), we
exhibit a continuing agent that does not extract: the balanced agent holding
`σ ≡ 0`. Its maintenance cost is zero, so its reserve only grows. Hence
"sustains extraction" is not a property of every continuing agent. -/

/-- The balanced agent: holds perfect balance (`σ ≡ 0`) with unit budget and
unit starting reserve. -/
def balancedAgent : RecognitionAgent where
  σ := fun _ => 0
  budget := 1
  budget_pos := one_pos
  initReserve := 1
  initReserve_nonneg := zero_le_one

private theorem extractionCost_zero : Extraction.extractionSystemCost 0 = 0 :=
  (Extraction.extraction_cost_eq_zero_iff 0).mpr rfl

/-- The balanced agent continues as an agent: its reserve is always positive. -/
theorem balancedAgent_continues : ContinuesAsAgent balancedAgent := by
  intro n
  show 0 < balancedAgent.reserve n
  unfold RecognitionAgent.reserve
  have hnonneg :
      0 ≤ ∑ k ∈ Finset.range n,
        (balancedAgent.budget - Extraction.extractionSystemCost (balancedAgent.σ k)) := by
    apply Finset.sum_nonneg
    intro k _
    show (0 : ℝ) ≤ 1 - Extraction.extractionSystemCost 0
    rw [extractionCost_zero]; norm_num
  show (0 : ℝ) < balancedAgent.initReserve + _
  have hinit : balancedAgent.initReserve = 1 := rfl
  linarith

/-- The balanced agent does not sustain extraction. -/
theorem balancedAgent_not_sustains : ¬ SustainsExtraction balancedAgent := by
  rintro ⟨σ₀, hcost, hfloor⟩
  have h0 := hfloor 0
  rw [show balancedAgent.σ 0 = 0 from rfl, extractionCost_zero] at h0
  rw [show balancedAgent.budget = 1 from rfl] at hcost
  linarith

/-- **A4′.** Sustaining extraction is *not* an agent-ought: it is not a
necessary condition of continued agency (the balanced agent is a counterwitness).
Combined with A4, this shows the moral law tracks a genuine asymmetry, not a
trivial classification. -/
theorem extraction_not_agent_ought :
    ¬ AgentOught (fun S => SustainsExtraction S) := by
  intro hO
  exact balancedAgent_not_sustains (hO balancedAgent balancedAgent_continues)

/-! ## A5 — The temptation structure (why immorality is locally rewarding)

Individual hedonic valence is `σ/(1+|σ|)`, which is strictly positive for
`σ > 0`. So holding a positive skew (extracting) is *locally* rewarding, even
though A3 shows it is *globally* fatal. This is the formal shape of akrasia:
the conflict between immediate valence and long-run viability. The framework
explains temptation rather than ignoring it. -/

/-- Local hedonic valence as a function of skew. -/
def valence (σ : ℝ) : ℝ := σ / (1 + |σ|)

/-- Extraction is locally rewarding: positive skew yields positive valence. -/
theorem valence_pos_of_pos {σ : ℝ} (hσ : 0 < σ) : 0 < valence σ := by
  unfold valence
  have hden : 0 < 1 + |σ| := by positivity
  exact div_pos hσ hden

/-- **A5 (temptation).** A positive-skew window is locally rewarding
(`0 < valence σ`) yet, when its cost exceeds budget, globally fatal (the agent
is non-viable from some window onward). The two facts together are the
akrasia structure: local valence rewards what long-run viability forbids. -/
theorem extraction_tempting_but_fatal (S : RecognitionAgent)
    (hext : SustainsExtraction S) {σ : ℝ} (hσ : 0 < σ) :
    0 < valence σ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ S.viable n :=
  ⟨valence_pos_of_pos hσ, extraction_policy_is_self_defeating S hext⟩

end

end Metaethics
end Ethics
end IndisputableMonolith
