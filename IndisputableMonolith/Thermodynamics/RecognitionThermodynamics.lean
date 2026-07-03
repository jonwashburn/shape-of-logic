import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Recognition Thermodynamics

This module defines the statistical mechanics of Recognition Science (RS).
It extends the "T=0" cost minimization (J=0) to finite Recognition Temperature (TR).

## Core Definitions

1. **Recognition Temperature (TR)**: Parameterizes the strictness of J-minimization.
2. **Recognition Beta (β)**: Thermodynamic beta (1/TR), the "inverse temperature".
3. **Gibbs Measure**: The probability distribution p(x) ∝ exp(-J(x)/TR).
4. **Recognition Entropy (SR)**: Quantifies the degeneracy of near-minima.
5. **Recognition Free Energy (FR)**: The quantity minimized by RS dynamics at finite TR.

## Connection to RS Foundation

The key insight is that RS already has the structure for thermodynamics:
- J(x) = ½(x + 1/x) - 1 is the "energy" (cost)
- The Born rule weight exp(-C) from cost C is the Gibbs weight
- φ-ladder structure provides natural discretization
- 8-tick cycle provides fundamental time unit τ₀

## References
- RS_UNDISCOVERED_TERRITORIES.md
- Recognition-Science-Full-Theory.txt
-/

namespace IndisputableMonolith
namespace Thermodynamics

open Real
open Cost
open scoped BigOperators

/-! ## Core Thermodynamic Structures -/

/-- Recognition Temperature parameterizes the noise/exploration level.
    T_R = 0 corresponds to deterministic RS (only J=0 states exist).
    T_R → ∞ corresponds to maximum disorder. -/
structure RecognitionSystem where
  TR : ℝ
  TR_pos : 0 < TR

/-- Thermodynamic beta (inverse temperature) for a recognition system. -/
noncomputable def RecognitionSystem.beta (sys : RecognitionSystem) : ℝ := 1 / sys.TR

/-- Beta is positive. -/
theorem RecognitionSystem.beta_pos (sys : RecognitionSystem) : 0 < sys.beta := by
  unfold RecognitionSystem.beta
  exact div_pos one_pos sys.TR_pos

/-- Beta * TR = 1. -/
theorem RecognitionSystem.beta_mul_TR (sys : RecognitionSystem) : sys.beta * sys.TR = 1 := by
  unfold RecognitionSystem.beta
  field_simp [sys.TR_pos.ne']

/-! ## Gibbs Weights and Partition Functions -/

/-- The Gibbs weight (Boltzmann factor) of a state with ratio x.
    This is the unnormalized probability: exp(-J(x)/TR). -/
noncomputable def gibbs_weight (sys : RecognitionSystem) (x : ℝ) : ℝ :=
  exp (- Jcost x / sys.TR)

/-- Gibbs weight is always positive. -/
theorem gibbs_weight_pos (sys : RecognitionSystem) (x : ℝ) : 0 < gibbs_weight sys x :=
  exp_pos _

/-- Gibbs weight at x=1 is exp(0) = 1 (the ground state). -/
theorem gibbs_weight_one (sys : RecognitionSystem) : gibbs_weight sys 1 = 1 := by
  unfold gibbs_weight
  simp [Jcost_unit0]

/-- The Partition Function Z for a discrete set of states.
    Z = ∑_ω exp(-J(X(ω))/TR) -/
noncomputable def partition_function {Ω : Type*} [Fintype Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) : ℝ :=
  ∑ ω, gibbs_weight sys (X ω)

/-- The partition function is positive. -/
theorem partition_function_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) : 0 < partition_function sys X := by
  unfold partition_function
  apply Finset.sum_pos
  · intro ω _
    exact gibbs_weight_pos sys (X ω)
  · exact Finset.univ_nonempty

/-- The Gibbs probability distribution on a discrete set of states.
    p(ω) = exp(-J(X(ω))/TR) / Z -/
noncomputable def gibbs_measure {Ω : Type*} [Fintype Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) (ω : Ω) : ℝ :=
  gibbs_weight sys (X ω) / partition_function sys X

/-- Gibbs measure is non-negative. -/
theorem gibbs_measure_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) (ω : Ω) : 0 ≤ gibbs_measure sys X ω := by
  unfold gibbs_measure
  exact div_nonneg (gibbs_weight_pos sys (X ω)).le (partition_function_pos sys X).le

/-- Gibbs measure sums to 1. -/
theorem gibbs_measure_sum_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) : ∑ ω, gibbs_measure sys X ω = 1 := by
  unfold gibbs_measure partition_function
  rw [← Finset.sum_div]
  exact div_self (partition_function_pos sys X).ne'

/-- Gibbs measure is always positive. -/
theorem gibbs_measure_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) (ω : Ω) : 0 < gibbs_measure sys X ω := by
  unfold gibbs_measure
  apply div_pos
  · exact gibbs_weight_pos sys (X ω)
  · exact partition_function_pos sys X

/-- A probability distribution on a discrete set of states. -/
structure ProbabilityDistribution (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : ∑ ω, p ω = 1

/-! ## Entropy and Free Energy -/

/-- Recognition Entropy S_R for a probability distribution p.
    S_R(p) = -∑_ω p(ω) ln(p(ω))
    Convention: 0 * ln(0) = 0 (handled via lim). -/
noncomputable def recognition_entropy {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : ℝ :=
  - ∑ ω, if p ω > 0 then p ω * log (p ω) else 0

/-- Expected J-cost under a probability distribution p.
    E_p[J] = ∑_ω p(ω) * J(X(ω)) -/
noncomputable def expected_cost {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * Jcost (X ω)

/-- Recognition Free Energy F_R = E[J] - TR * S_R.
    This is the fundamental variational quantity in RS thermodynamics. -/
noncomputable def recognition_free_energy {Ω : Type*} [Fintype Ω]
    (sys : RecognitionSystem) (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  expected_cost p X - sys.TR * recognition_entropy p

/-- Alternative formulation: F_R = -TR * ln(Z) for the Gibbs measure. -/
noncomputable def free_energy_from_Z {Ω : Type*} [Fintype Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) : ℝ :=
  - sys.TR * log (partition_function sys X)

/-- **THEOREM: Free Energy Identity**
    F_R = -TR * ln(Z) for the Gibbs measure. -/
theorem free_energy_identity {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (sys : RecognitionSystem) (X : Ω → ℝ) :
    recognition_free_energy sys (gibbs_measure sys X) X = free_energy_from_Z sys X := by
  simp only [recognition_free_energy, expected_cost, recognition_entropy, free_energy_from_Z,
             gibbs_measure, gibbs_weight, partition_function]
  set Z := ∑ ω, exp (-Jcost (X ω) / sys.TR) with hZ
  have hZ_pos : 0 < Z := by
    rw [hZ]
    apply Finset.sum_pos
    · intro ω _
      exact exp_pos _
    · exact Finset.univ_nonempty
  -- LHS = Σ (p * J) - TR * (- Σ p log p) = Σ (p * J) + TR * Σ p log p
  -- Simplify the expression first
  simp only [sub_eq_add_neg, neg_neg, neg_mul, ← mul_neg]
  -- Now LHS = Σ (p * J) + TR * Σ (p * log p)
  rw [Finset.mul_sum]
  -- Expand the log in entropy: log(exp(-J/TR) / Z)
  have h_log : ∀ ω, (if exp (-Jcost (X ω) / sys.TR) / Z > 0 then
      (exp (-Jcost (X ω) / sys.TR) / Z) * log (exp (-Jcost (X ω) / sys.TR) / Z) else 0) =
      (exp (-Jcost (X ω) / sys.TR) / Z) * (-Jcost (X ω) / sys.TR - log Z) := by
    intro ω
    have h_p_pos : exp (-Jcost (X ω) / sys.TR) / Z > 0 := div_pos (exp_pos _) hZ_pos
    simp only [h_p_pos, if_true]
    rw [log_div (exp_pos _).ne' hZ_pos.ne', log_exp]
  simp only [h_log]
  -- Now we have: Σ (p * J) + Σ (TR * p * (-J/TR - log Z))
  rw [← Finset.sum_add_distrib]
  -- Combine terms for each ω
  have h_omega : ∀ ω, (exp (-Jcost (X ω) / sys.TR) / Z) * Jcost (X ω) +
                      sys.TR * ((exp (-Jcost (X ω) / sys.TR) / Z) * (-Jcost (X ω) / sys.TR - log Z)) =
                      -sys.TR * log Z * (exp (-Jcost (X ω) / sys.TR) / Z) := by
    intro ω
    field_simp [sys.TR_pos.ne', hZ_pos.ne']
    ring
  simp only [h_omega]
  rw [← Finset.mul_sum]
  have h_sum_p : (∑ ω, exp (-Jcost (X ω) / sys.TR) / Z) = 1 := by
    rw [← Finset.sum_div, div_self hZ_pos.ne']
  rw [h_sum_p]
  ring

/-! ## Kullback-Leibler Divergence -/

/-- The KL divergence D_KL(q || p) measures how q differs from p.
    D_KL(q || p) = ∑_ω q(ω) * ln(q(ω)/p(ω)) -/
noncomputable def kl_divergence {Ω : Type*} [Fintype Ω] (q p : Ω → ℝ) : ℝ :=
  ∑ ω, if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0

/-- KL divergence is non-negative (Gibbs' inequality).
    D_KL(q || p) ≥ 0 with equality iff q = p. -/
theorem kl_divergence_nonneg {Ω : Type*} [Fintype Ω]
    (q p : Ω → ℝ) (hq : ∀ ω, 0 ≤ q ω) (hp : ∀ ω, 0 < p ω)
    (hq_sum : ∑ ω, q ω = 1) (hp_sum : ∑ ω, p ω = 1) :
    0 ≤ kl_divergence q p := by
  unfold kl_divergence
  -- Use log x ≤ x - 1, which implies -log x ≥ 1 - x
  -- q log (q/p) = -q log (p/q) ≥ q (1 - p/q) = q - p
  have h_le : ∀ ω, (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) ≥ q ω - p ω := by
    intro ω
    split_ifs with h
    · -- case q ω > 0 and p ω > 0
      obtain ⟨hq_pos, hp_pos⟩ := h
      have hr_pos : 0 < p ω / q ω := div_pos hp_pos hq_pos
      have : log (q ω / p ω) ≥ 1 - p ω / q ω := by
        rw [log_div hq_pos.ne' hp_pos.ne']
        have h_log_le := log_le_sub_one_of_pos hr_pos
        rw [log_div hp_pos.ne' hq_pos.ne'] at h_log_le
        linarith
      have hq_q : q ω * log (q ω / p ω) ≥ q ω * (1 - p ω / q ω) := by
        apply mul_le_mul_of_nonneg_left this hq_pos.le
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hq_pos.ne'] at hq_q
      exact hq_q
    · -- case q ω ≤ 0 or p ω ≤ 0
      have hq0 : q ω = 0 := by
        have : ¬ (q ω > 0 ∧ p ω > 0) := h
        simp only [hp ω, and_true, not_lt] at this
        exact le_antisymm this (hq ω)
      rw [hq0]
      linarith [hp ω]

  -- Sum over all ω
  calc 0 = (∑ ω, q ω) - (∑ ω, p ω) := by rw [hq_sum, hp_sum, sub_self]
       _ = ∑ ω, (q ω - p ω) := by rw [Finset.sum_sub_distrib]
       _ ≤ ∑ ω, (if q ω > 0 ∧ p ω > 0 then q ω * log (q ω / p ω) else 0) := Finset.sum_le_sum (fun ω _ => h_le ω)



/-! ## Connecting to RS: φ-Temperature Scale -/

/-- The natural temperature scale in RS is set by the φ-ladder.
    T_φ = J_bit = ln(φ) where φ is the golden ratio. -/
noncomputable def T_phi : ℝ := log Foundation.PhiForcing.φ

/-- T_φ > 0 since φ > 1. -/
theorem T_phi_pos : 0 < T_phi := by
  unfold T_phi
  exact log_pos Foundation.PhiForcing.phi_gt_one

/-- A recognition system at the φ-temperature. -/
noncomputable def phi_temperature_system : RecognitionSystem where
  TR := T_phi
  TR_pos := T_phi_pos

/-! ## Coherence Threshold -/

/-- The coherence parameter C = 1 marks a phase transition.
    When TR < T_critical, the system is in a "frozen" (coherent) phase.
    When TR > T_critical, the system is "hot" (disordered). -/
structure CoherenceThreshold where
  /-- The critical temperature for phase transition -/
  T_critical : ℝ
  /-- Critical temperature is positive -/
  T_critical_pos : 0 < T_critical
  /-- The coherence parameter at temperature T -/
  coherence : ℝ → ℝ
  /-- Coherence = 1 at the critical point -/
  coherence_at_critical : coherence T_critical = 1

/-- The RS coherence threshold: C = T_φ / TR.
    C ≥ 1 corresponds to coherent (quantum/recognition) regime.
    C < 1 corresponds to decoherent (classical) regime. -/
noncomputable def rs_coherence (sys : RecognitionSystem) : ℝ := T_phi / sys.TR

/-- At the φ-temperature, coherence = 1 (critical point). -/
theorem coherence_at_phi_temp : rs_coherence phi_temperature_system = 1 := by
  unfold rs_coherence phi_temperature_system
  simp [T_phi_pos.ne']

/-! ## Eight-Tick Structure -/

/-- The fundamental time unit in RS is 8 ticks (τ₀). -/
def eight_tick : ℕ := 8

/-- The natural frequency scale: f_0 = 1 / (8 * τ₀).
    This sets the IR cutoff for recognition dynamics. -/
noncomputable def fundamental_frequency (tau_0 : ℝ) (_h : tau_0 > 0) : ℝ :=
  1 / (eight_tick * tau_0)

end Thermodynamics
end IndisputableMonolith
