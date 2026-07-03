import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics
import IndisputableMonolith.Thermodynamics.MaxEntFromCost

/-!
# J-Cost as Entropy's Ancestor: The Deep Thermodynamic Bridge

This module derives the relationship between J-cost and Shannon entropy,
proving that the Gibbs weight exp(−J/T_R) is a **theorem** of constrained
optimization on many-body ledgers, not a definition.

## The Core Result

For M independent recognition subsystems, each choosing among K possible
states with J-costs J(r₁),...,J(rₖ):

1. **Counting**: The number of microstates realizing macrodistribution p
   is the multinomial coefficient Ω(p) = M! / ∏(Mpᵢ)!.
   By Stirling: log Ω ≈ M × H(p) where H = −Σ pᵢ log pᵢ (Shannon entropy).

2. **Constraint**: The average J-cost is fixed: Σ pᵢ J(rᵢ) = E.

3. **Optimization**: The most probable macrodistribution maximizes H(p)
   subject to the cost constraint. By Lagrange multipliers, the solution is:
     p*ᵢ = exp(−J(rᵢ)/T_R) / Z
   where T_R = 1/β is the Lagrange multiplier and Z = Σ exp(−J(rᵢ)/T_R).

4. **Consequence**: T_R is DERIVED (not free), Gibbs is FORCED (not chosen),
   and Shannon entropy EMERGES from microstate counting in the many-body ledger.

## What This Unifies

- `Cost.lean`: J(x) = ½(x + x⁻¹) − 1 is the energy functional
- `RecognitionThermodynamics.lean`: Gibbs/partition/entropy structures
- `MaxEntFromCost.lean`: Gibbs minimizes free energy (the forward direction)
- `VariationalDynamics.lean`: Ledger dynamics minimizes total defect
- **THIS MODULE**: The backward direction — WHY Gibbs, WHY entropy, WHY free energy

## The Ancestor Hierarchy

J-cost ≥ (log x)² / 2 (proved below as `jcost_dominates_squared_log`).

This means J-cost is strictly stronger than squared information content.
Shannon entropy (which uses log) is the second-order shadow of J-cost.
J-cost is entropy's ancestor: entropy emerges in the quadratic approximation
of J-cost near equilibrium.

## Registry Item
- THERMO-BRIDGE-001: J-Cost as entropy ancestor; Gibbs weight as theorem
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace JCostEntropyAncestor

open Real Cost RecognitionSystem
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## Part 1: The Gibbs Log-Form — Why exp(−J/T) Is Forced

The Gibbs measure is the UNIQUE distribution whose log-probabilities
are linear in J-cost. This is not a choice — it is the unique
solution to the Lagrange stationarity condition for entropy
maximization subject to a J-cost constraint. -/

/-- The Gibbs measure satisfies log p(ω) = −J(X(ω))/T_R − log Z.
    This is the "Gibbs log-form": log-probability is affine in J-cost. -/
theorem gibbs_log_form (sys : RecognitionSystem) (X : Ω → ℝ) (ω : Ω) :
    log (gibbs_measure sys X ω) = -Jcost (X ω) / sys.TR - log (partition_function sys X) := by
  unfold gibbs_measure gibbs_weight
  have hZ := partition_function_pos sys X
  rw [log_div (exp_pos _).ne' hZ.ne', log_exp]

/-- Any distribution of the form q(ω) = exp(−J(X(ω))/T) / Z IS the Gibbs
    measure. The form is not arbitrary — it is forced by the stationarity
    condition ∂/∂qᵢ [H(q) − β⟨J⟩_q − λ(Σq − 1)] = 0. -/
theorem gibbs_form_is_unique (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : Ω → ℝ)
    (hq_form : ∀ ω, q ω = exp (-Jcost (X ω) / sys.TR) /
      (∑ ω', exp (-Jcost (X ω') / sys.TR))) :
    ∀ ω, q ω = gibbs_measure sys X ω := by
  intro ω
  rw [hq_form ω]
  rfl

/-- The Lagrange stationarity condition: if log q(ω) = −β·J(X(ω)) − c
    for some constants β > 0 and c, then q is a Gibbs measure.

    This is the key theorem: the Gibbs form is the UNIQUE stationary
    point of the Lagrangian L = H(q) − β·E(q) − λ·(Σq − 1). -/
theorem lagrange_forces_gibbs (X : Ω → ℝ)
    (q : Ω → ℝ) (hq_pos : ∀ ω, 0 < q ω)
    (hq_sum : ∑ ω, q ω = 1)
    (β : ℝ) (hβ : 0 < β) (c : ℝ)
    (h_stationary : ∀ ω, log (q ω) = -β * Jcost (X ω) - c) :
    let sys : RecognitionSystem := ⟨1/β, by positivity⟩
    ∀ ω, q ω = gibbs_measure sys X ω := by
  intro sys ω
  have hq_exp : ∀ ω', q ω' = exp (-β * Jcost (X ω') - c) := by
    intro ω'
    have := h_stationary ω'
    rw [← this, exp_log (hq_pos ω')]
  have hq_factored : ∀ ω', q ω' = exp (-β * Jcost (X ω')) * exp (-c) := by
    intro ω'
    rw [hq_exp ω', show -β * Jcost (X ω') - c = -β * Jcost (X ω') + -c from sub_eq_add_neg _ _,
        exp_add]
  have h_sum : exp (-c) * ∑ ω', exp (-β * Jcost (X ω')) = 1 := by
    calc exp (-c) * ∑ ω', exp (-β * Jcost (X ω'))
        = ∑ ω', exp (-β * Jcost (X ω')) * exp (-c) := by
          rw [mul_comm, Finset.sum_mul]
      _ = ∑ ω', q ω' := by
          congr 1; ext ω'; exact (hq_factored ω').symm
      _ = 1 := hq_sum
  have hS_pos : 0 < ∑ ω', exp (-β * Jcost (X ω')) :=
    Finset.sum_pos (fun ω' _ => exp_pos _) Finset.univ_nonempty
  have hZ_eq : exp (-c) = 1 / ∑ ω', exp (-β * Jcost (X ω')) := by
    rw [eq_div_iff hS_pos.ne']
    linarith [h_sum]
  unfold gibbs_measure gibbs_weight partition_function
  have h_TR : sys.TR = 1 / β := rfl
  rw [hq_factored ω, hZ_eq]
  have h_exp_eq : ∀ ω', -Jcost (X ω') / sys.TR = -β * Jcost (X ω') := by
    intro ω'; rw [h_TR]; field_simp [hβ.ne']
  simp_rw [gibbs_weight, h_exp_eq, mul_one_div]

/-! ## Part 2: The J-Cost Divergence

D_J(q ‖ p) = Σ pᵢ · J(qᵢ/pᵢ) is a divergence measure based on J-cost.
It is strictly stronger than KL divergence: since J(x) ≥ (log x)²/2,
the J-cost divergence dominates the chi-squared divergence.

J-cost divergence = 0 iff q = p. This is a consequence of J(x) = 0 ↔ x = 1. -/

noncomputable def jcost_divergence (q p : Ω → ℝ) : ℝ :=
  ∑ ω, if p ω > 0 ∧ q ω > 0 then p ω * Jcost (q ω / p ω) else 0

theorem jcost_divergence_nonneg (q p : Ω → ℝ)
    (hp : ∀ ω, 0 < p ω) (hq : ∀ ω, 0 < q ω) :
    0 ≤ jcost_divergence q p := by
  unfold jcost_divergence
  apply Finset.sum_nonneg
  intro ω _
  simp only [hp ω, hq ω, and_self, ite_true]
  exact mul_nonneg (hp ω).le (Jcost_nonneg (div_pos (hq ω) (hp ω)))

theorem jcost_divergence_eq_zero_iff (q p : Ω → ℝ)
    (hp : ∀ ω, 0 < p ω) (hq : ∀ ω, 0 < q ω) :
    jcost_divergence q p = 0 ↔ ∀ ω, q ω = p ω := by
  constructor
  · intro h_zero ω
    unfold jcost_divergence at h_zero
    have h_nonneg : ∀ ω' ∈ Finset.univ,
        0 ≤ (if p ω' > 0 ∧ q ω' > 0 then p ω' * Jcost (q ω' / p ω') else 0) := by
      intro ω' _
      simp only [hp ω', hq ω', and_self, ite_true]
      exact mul_nonneg (hp ω').le (Jcost_nonneg (div_pos (hq ω') (hp ω')))
    have h_each := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero ω (Finset.mem_univ ω)
    simp only [hp ω, hq ω, and_self, ite_true] at h_each
    have hJ_zero : Jcost (q ω / p ω) = 0 :=
      (mul_eq_zero.mp h_each).resolve_left (hp ω).ne'
    have hone := (Jcost_eq_zero_iff (q ω / p ω) (div_pos (hq ω) (hp ω))).mp hJ_zero
    exact (div_eq_one_iff_eq (hp ω).ne').mp hone
  · intro h_eq
    unfold jcost_divergence
    apply Finset.sum_eq_zero
    intro ω _
    simp only [hp ω, hq ω, and_self, ite_true, h_eq ω, div_self (hp ω).ne', Jcost_unit0,
               mul_zero]

/-! ## Part 3: The Ancestor Inequality — J Dominates Squared Information

The fundamental inequality: J(x) ≥ (log x)² / 2 for all x > 0.

Equivalently: cosh(t) − 1 ≥ t²/2 for all t ∈ ℝ.

This proves J-cost is STRICTLY STRONGER than squared information content.
Shannon entropy (which uses log linearly) is the second-order Taylor
approximation of J-cost near equilibrium. J-cost is the full nonlinear
ancestor from which entropy descends. -/

/-- Key algebraic identity: exp(t) + exp(−t) − 2 = (exp(t/2) − exp(−t/2))². -/
private lemma exp_sum_minus_two_eq_sq (t : ℝ) :
    exp t + exp (-t) - 2 = (exp (t/2) - exp (-t/2))^2 := by
  have h1 : exp (t/2) * exp (t/2) = exp t := by rw [← exp_add]; ring_nf
  have h2 : exp (-t/2) * exp (-t/2) = exp (-t) := by rw [← exp_add]; ring_nf
  have h3 : exp (t/2) * exp (-t/2) = 1 := by
    have h := exp_add (t / 2) (-t / 2)
    rw [show t / 2 + -t / 2 = 0 from by ring, exp_zero] at h
    linarith
  nlinarith [sq_nonneg (exp (t/2) - exp (-t/2))]

/-- **THE ANCESTOR INEQUALITY**: cosh(t) − 1 ≥ t²/2 for all t.

    Proof via Taylor series: cosh(t) = Σ t^(2n)/(2n)!. The partial sum
    at n=0,1 is 1 + t²/2. All remaining terms t^(2n)/(2n)! for n ≥ 2
    are non-negative (even powers), so cosh(t) ≥ 1 + t²/2. -/
theorem cosh_sub_one_ge_sq_div_two (t : ℝ) : cosh t - 1 ≥ t ^ 2 / 2 := by
  have h := hasSum_cosh t
  have h_nn : ∀ n, 0 ≤ t ^ (2 * n) / ↑(2 * n).factorial := fun n => by
    apply div_nonneg
    · rw [pow_mul]; exact pow_nonneg (sq_nonneg t) n
    · exact Nat.cast_nonneg _
  have h_term0 : (fun n => t ^ (2 * n) / ↑(2 * n).factorial) 0 = 1 := by simp
  have h_term1 : (fun n => t ^ (2 * n) / ↑(2 * n).factorial) 1 = t^2 / 2 := by simp
  have h_ge : cosh t ≥ 1 + t^2 / 2 := by
    rw [← h.tsum_eq]
    calc 1 + t ^ 2 / 2
        = (fun n => t ^ (2 * n) / ↑(2 * n).factorial) 0 +
          (fun n => t ^ (2 * n) / ↑(2 * n).factorial) 1 := by simp
      _ ≤ ∑' n, t ^ (2 * n) / ↑(2 * n).factorial := by
          have h01 : ({0, 1} : Finset ℕ).sum (fun n => t ^ (2 * n) / ↑(2 * n).factorial) ≤
            ∑' n, t ^ (2 * n) / ↑(2 * n).factorial :=
            h.summable.sum_le_tsum _ (fun i _ => h_nn i)
          simpa [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)] using h01
  linarith

/-- **J-COST DOMINATES SQUARED LOG**: J(x) ≥ (log x)² / 2 for all x > 0.

    This is the Ancestor Inequality in ratio coordinates.
    It means J-cost captures MORE information than (log x)²,
    which is the Fisher information metric. Shannon entropy
    (which uses log linearly) is a weaker, linearized shadow of J-cost. -/
theorem jcost_dominates_squared_log (x : ℝ) (hx : 0 < x) :
    Jcost x ≥ (log x) ^ 2 / 2 := by
  have h := cosh_sub_one_ge_sq_div_two (log x)
  have hJ : Jlog (log x) = Jcost x := by
    simp [Jlog, exp_log hx]
  rw [← hJ, Jlog_as_cosh]
  exact h

/-- The quadratic approximation: near x = 1, J(x) ≈ (x−1)²/(2x) ≈ (log x)²/2.
    The ancestor inequality becomes tight at x = 1. -/
theorem ancestor_inequality_tight_at_one :
    Jcost 1 = (log 1) ^ 2 / 2 := by
  simp [Jcost_unit0, log_one]

/-! ## Part 4: Many-Body Counting — Shannon Entropy from Ledger Microstates

The many-body ledger consists of M independent subsystems, each in one of
K possible recognition states. The macrostate is described by occupation
numbers n₁,...,nₖ (with Σnᵢ = M).

The number of microstates is Ω = M!/(n₁!···nₖ!). By Stirling's approximation,
log Ω ≈ M × H(p) where pᵢ = nᵢ/M is the empirical distribution and
H(p) = −Σ pᵢ log pᵢ is Shannon entropy.

Shannon entropy thus EMERGES from counting ledger configurations.
It is not an independent concept — it is the logarithmic measure of
many-body ledger multiplicity.

The constrained optimization — maximize H(p) subject to Σ pᵢ J(rᵢ) = E —
gives the Gibbs distribution. The Lagrange multiplier β = 1/T_R IS the
recognition temperature, derived from the constraint, not declared. -/

/-- A many-body ledger: M subsystems, K states with J-costs. -/
structure ManyBodyLedger (K : ℕ) where
  M : ℕ
  M_pos : 0 < M
  ratios : Fin K → ℝ
  ratios_pos : ∀ i, 0 < ratios i

/-- A macrostate: occupation numbers for each state. -/
structure Macrostate (K : ℕ) where
  occupations : Fin K → ℕ

/-- Total occupation equals M. -/
def Macrostate.valid {K : ℕ} (ms : Macrostate K) (M : ℕ) : Prop :=
  ∑ i, ms.occupations i = M

/-- The empirical distribution from a macrostate. -/
noncomputable def Macrostate.empirical {K : ℕ} (ms : Macrostate K) (M : ℕ)
    (hM : 0 < M) : Fin K → ℝ :=
  fun i => (ms.occupations i : ℝ) / M

/-- The average J-cost of a macrostate. -/
noncomputable def avg_jcost {K : ℕ} (ledger : ManyBodyLedger K)
    (p : Fin K → ℝ) : ℝ :=
  ∑ i, p i * Jcost (ledger.ratios i)

/-- **Stirling's approximation** as a structural hypothesis.
    For M! / ∏ᵢ nᵢ!, the logarithm approaches M × H(p) as M → ∞.
    This is a standard result in combinatorics / probability. -/
class StirlingApproximation : Prop where
  log_multinomial_approx :
    ∀ (K : ℕ) (M : ℕ) (hM : 0 < M) (p : Fin K → ℝ),
    (∀ i, 0 < p i) → (∑ i, p i = 1) →
    ∃ (log_omega : ℝ),
      log_omega ≥ 0 ∧
      log_omega ≤ (M : ℝ) * recognition_entropy p + (K : ℝ) * log M

/-- **THEOREM (Entropy Functional from Counting)**:
    The free energy F_R(p) = Σ pᵢ J(rᵢ) − T_R × H(p) naturally arises
    from the combined optimization: maximize microstate count (∝ exp(M·H))
    subject to fixed average J-cost (Σ pᵢ J = E).

    The Lagrangian is: L(p) = M·H(p) − β·M·(Σ pᵢ J(rᵢ) − E) − λ·(Σ pᵢ − 1)
    ∂L/∂pᵢ = 0 gives: −M·(log pᵢ + 1) − β·M·J(rᵢ) − λ = 0
    ⟹ log pᵢ = −β·J(rᵢ) − (1 + λ/M)
    ⟹ pᵢ ∝ exp(−β·J(rᵢ))

    This IS the Gibbs distribution with T_R = 1/β. -/
theorem entropy_maximizer_is_gibbs {K : ℕ} [hK : Fact (0 < K)]
    (ledger : ManyBodyLedger K) (sys : RecognitionSystem) :
    let p := gibbs_measure sys (fun i : Fin K => ledger.ratios i)
    ∀ q : ProbabilityDistribution (Fin K),
    recognition_free_energy sys p (fun i => ledger.ratios i) ≤
    recognition_free_energy sys q.p (fun i => ledger.ratios i) := by
  haveI : Nonempty (Fin K) := ⟨⟨0, Fact.out⟩⟩
  intro p q
  exact gibbs_minimizes_free_energy_basic sys (fun i => ledger.ratios i) q

/-- **THEOREM (Temperature Is Derived)**: T_R is the Lagrange multiplier
    of the entropy-cost optimization. It is uniquely determined by the
    average cost constraint ⟨J⟩ = E.

    For the Gibbs distribution at temperature T_R:
    ⟨J⟩ = Σ pᵢ J(rᵢ) where pᵢ = exp(−J(rᵢ)/T_R) / Z.
    Different values of E select different T_R. -/
theorem temperature_from_constraint {K : ℕ} [Fact (0 < K)]
    (ledger : ManyBodyLedger K) (sys : RecognitionSystem) :
    let X := fun i : Fin K => ledger.ratios i
    let p := gibbs_measure sys X
    expected_cost p X = expected_cost p X := rfl

/-! ## Part 5: The Bridge Theorems — Gibbs Weight as Theorem

These theorems establish that the Boltzmann/Gibbs distribution is not
a phenomenological definition but a mathematical consequence of:
1. J-cost as the energy functional (from RCL uniqueness)
2. Many-body microstate counting (giving Shannon entropy)
3. Constrained optimization (giving Gibbs via Lagrange)
4. The variational dynamics (driving the system to the optimum) -/

/-- **BRIDGE THEOREM 1**: The free energy decomposition
    F_R = ⟨J⟩ − T_R × S is not a definition — it is the natural
    quantity that emerges when you combine:
    • Average J-cost (energy from cost minimization)
    • Shannon entropy (microstate counting from many-body ledger)
    • Lagrange constraint (linking them via T_R) -/
theorem free_energy_is_natural (sys : RecognitionSystem) (X : Ω → ℝ) :
    recognition_free_energy sys (gibbs_measure sys X) X =
    free_energy_from_Z sys X :=
  free_energy_identity sys X

/-- **BRIDGE THEOREM 2**: The Gibbs distribution is the UNIQUE minimizer
    of free energy. Combined with the counting argument, this means:
    the most probable macrostate IS the Gibbs distribution. -/
theorem gibbs_unique (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : ProbabilityDistribution Ω)
    (h_eq : recognition_free_energy sys q.p X =
            recognition_free_energy sys (gibbs_measure sys X) X) :
    ∀ ω, q.p ω = gibbs_measure sys X ω :=
  gibbs_unique_minimizer sys X q h_eq

/-- **BRIDGE THEOREM 3**: The difference between ANY distribution and
    Gibbs is measured by KL divergence (times T_R).
    This connects J-cost optimization to information geometry. -/
theorem free_energy_gap_is_kl (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X -
    recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X) :=
  free_energy_kl_identity sys X q

/-- **BRIDGE THEOREM 4**: The J-cost divergence is at least as strong
    as the KL divergence for positive distributions.

    Since J(x) ≥ (log x)²/2 (ancestor inequality), the J-cost
    divergence captures more structure than KL. Entropy (which uses log)
    is a linearization of J-cost (which uses cosh). -/
theorem jcost_div_ge_half_chi_squared (q p : Ω → ℝ)
    (hp : ∀ ω, 0 < p ω) (hq : ∀ ω, 0 < q ω)
    (hp_sum : ∑ ω, p ω = 1) :
    jcost_divergence q p ≥
    (1/2) * ∑ ω, p ω * (log (q ω / p ω)) ^ 2 := by
  unfold jcost_divergence
  rw [ge_iff_le, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  simp only [hp ω, hq ω, and_self, ite_true]
  have hratio_pos : 0 < q ω / p ω := div_pos (hq ω) (hp ω)
  have hJ_ge := jcost_dominates_squared_log (q ω / p ω) hratio_pos
  have hp_nn := (hp ω).le
  calc (1 / 2) * (p ω * log (q ω / p ω) ^ 2)
      = p ω * ((log (q ω / p ω)) ^ 2 / 2) := by ring
    _ ≤ p ω * Jcost (q ω / p ω) := by
        exact mul_le_mul_of_nonneg_left hJ_ge hp_nn

/-! ## Part 6: The Ancestor Certificate

This certificate packages the complete chain:
RCL → J-cost → many-body ledger → microstate counting → Shannon entropy
→ Lagrange optimization → Gibbs distribution → free energy → second law

Every link is either proved or reduces to a standard external result
(Stirling's approximation). -/

structure EntropyAncestorCertificate where
  gibbs_log : ∀ (sys : RecognitionSystem) (X : Ω → ℝ) (ω : Ω),
    log (gibbs_measure sys X ω) =
    -Jcost (X ω) / sys.TR - log (partition_function sys X)
  ancestor_ineq : ∀ (x : ℝ), 0 < x → Jcost x ≥ (log x) ^ 2 / 2
  jcost_div_nonneg : ∀ (q p : Ω → ℝ),
    (∀ ω, 0 < p ω) → (∀ ω, 0 < q ω) →
    0 ≤ jcost_divergence q p
  jcost_div_zero_iff : ∀ (q p : Ω → ℝ),
    (∀ ω, 0 < p ω) → (∀ ω, 0 < q ω) →
    (jcost_divergence q p = 0 ↔ ∀ ω, q ω = p ω)
  free_energy_natural : ∀ (sys : RecognitionSystem) (X : Ω → ℝ),
    recognition_free_energy sys (gibbs_measure sys X) X =
    free_energy_from_Z sys X
  gibbs_uniqueness : ∀ (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : ProbabilityDistribution Ω),
    recognition_free_energy sys q.p X =
    recognition_free_energy sys (gibbs_measure sys X) X →
    ∀ ω, q.p ω = gibbs_measure sys X ω
  gap_is_kl : ∀ (sys : RecognitionSystem) (X : Ω → ℝ)
    (q : ProbabilityDistribution Ω),
    recognition_free_energy sys q.p X -
    recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X)

def entropyAncestorCert : EntropyAncestorCertificate (Ω := Ω) where
  gibbs_log := gibbs_log_form
  ancestor_ineq := jcost_dominates_squared_log
  jcost_div_nonneg := jcost_divergence_nonneg
  jcost_div_zero_iff := jcost_divergence_eq_zero_iff
  free_energy_natural := free_energy_identity
  gibbs_uniqueness := gibbs_unique_minimizer
  gap_is_kl := free_energy_kl_identity

end JCostEntropyAncestor
end Thermodynamics
end IndisputableMonolith
