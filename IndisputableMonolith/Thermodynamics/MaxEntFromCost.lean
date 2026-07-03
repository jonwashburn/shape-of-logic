import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Thermodynamics.RecognitionThermodynamics

/-!
# Maximum Entropy from Cost Minimization

This module proves that the Gibbs distribution emerges from the principle of
maximum entropy subject to a cost constraint.
-/

namespace IndisputableMonolith
namespace Thermodynamics

open Real Cost RecognitionSystem

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable (sys : RecognitionSystem) (X : Ω → ℝ)

/-- **THEOREM: The Free Energy - KL Divergence Identity**
    F_R(q) - F_R(Gibbs) = TR * D_KL(q || Gibbs)

    **Proof**: F_R(q) = ⟨X⟩_q - TR*S(q) = ∑ q_ω X_ω + TR ∑ q_ω log q_ω
    For Gibbs: p_ω = exp(-X_ω/TR)/Z, so log p_ω = -X_ω/TR - log Z
    D_KL(q||p) = ∑ q_ω log(q_ω/p_ω) = ∑ q_ω log q_ω + ∑ q_ω (X_ω/TR + log Z)
               = -S(q)/TR + ⟨X⟩_q/TR + log Z
    TR * D_KL = -TR*S(q) + ⟨X⟩_q + TR*log Z = F_R(q) - (-TR*log Z) = F_R(q) - F_R(Gibbs) -/
theorem free_energy_kl_identity (q : ProbabilityDistribution Ω) :
    recognition_free_energy sys q.p X - recognition_free_energy sys (gibbs_measure sys X) X =
    sys.TR * kl_divergence q.p (gibbs_measure sys X) := by
  -- Use the fact that F_R(Gibbs) = -TR * log(Z) from free_energy_identity
  have h_gibbs_FR := free_energy_identity sys X
  rw [h_gibbs_FR]
  unfold recognition_free_energy expected_cost recognition_entropy free_energy_from_Z

  -- F_R(q) = ∑ q J - TR * (-∑ q log q) = ∑ q J + TR ∑ q log q
  -- D_KL(q||p) = ∑ q log(q/p) where p = gibbs
  -- TR * D_KL = TR ∑ q log q - TR ∑ q log p
  -- log p_ω = log(exp(-J_ω/TR)/Z) = -J_ω/TR - log Z
  -- TR ∑ q log p = TR ∑ q (-J_ω/TR - log Z) = -∑ q J - TR log Z ∑ q = -∑ q J - TR log Z
  -- TR * D_KL = TR ∑ q log q + ∑ q J + TR log Z
  -- F_R(q) - F_R(Gibbs) = (∑ q J + TR ∑ q log q) - (-TR log Z) = ∑ q J + TR ∑ q log q + TR log Z
  -- These match! QED.

  unfold kl_divergence gibbs_measure partition_function
  simp only [gibbs_weight]
  set Z := ∑ ω, exp (-Jcost (X ω) / sys.TR) with hZ
  have hZ_pos : 0 < Z := by
    rw [hZ]; apply Finset.sum_pos (fun ω _ => exp_pos _) Finset.univ_nonempty
  have hq_sum := q.sum_one
  set S := ∑ ω : Ω, (if q.p ω > 0 then q.p ω * log (q.p ω) else 0)
  have lhs_simp :
    (∑ ω, q.p ω * Jcost (X ω) - sys.TR * -S) - -sys.TR * log Z =
    ∑ ω, q.p ω * Jcost (X ω) + sys.TR * S + sys.TR * log Z := by ring
  rw [lhs_simp]
  rw [show sys.TR * log Z = ∑ ω : Ω, sys.TR * log Z * q.p ω from
    by rw [← Finset.mul_sum, hq_sum, mul_one]]
  show ∑ ω, q.p ω * Jcost (X ω) + sys.TR * S + ∑ ω, sys.TR * log Z * q.p ω =
    sys.TR * ∑ ω, (if q.p ω > 0 ∧ exp (-Jcost (X ω) / sys.TR) / Z > 0
      then q.p ω * log (q.p ω / (exp (-Jcost (X ω) / sys.TR) / Z)) else 0)
  rw [show sys.TR * S = ∑ ω : Ω, sys.TR * (if q.p ω > 0 then q.p ω * log (q.p ω) else 0) from
    by rw [Finset.mul_sum]]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have h_gibbs_pos : 0 < exp (-Jcost (X ω) / sys.TR) / Z := div_pos (exp_pos _) hZ_pos
  by_cases hq_pos : 0 < q.p ω
  · simp only [show q.p ω > 0 from hq_pos, show exp (-Jcost (X ω) / sys.TR) / Z > 0 from h_gibbs_pos,
               and_self, ite_true]
    rw [log_div (ne_of_gt hq_pos) (ne_of_gt h_gibbs_pos),
        log_div (exp_pos _).ne' hZ_pos.ne', log_exp]
    field_simp [sys.TR_pos.ne']
    ring
  · push_neg at hq_pos
    have hq_zero : q.p ω = 0 := le_antisymm hq_pos (q.nonneg ω)
    simp [hq_zero]

/-- **THEOREM: Free Energy Minimization**
    The Gibbs distribution minimizes the Recognition Free Energy. -/
theorem gibbs_minimizes_free_energy_basic (p : ProbabilityDistribution Ω) :
    recognition_free_energy sys (gibbs_measure sys X) X ≤ recognition_free_energy sys p.p X := by
  have h := free_energy_kl_identity sys X p
  have hkl := kl_divergence_nonneg p.p (gibbs_measure sys X)
    p.nonneg
    (fun ω => gibbs_measure_pos sys X ω)
    p.sum_one
    (gibbs_measure_sum_one sys X)
  calc recognition_free_energy sys (gibbs_measure sys X) X
      = recognition_free_energy sys p.p X - sys.TR * kl_divergence p.p (gibbs_measure sys X) := by
        rw [← h]; ring
    _ ≤ recognition_free_energy sys p.p X := by
        have hTR := sys.TR_pos
        nlinarith

/-- **THEOREM: MaxEnt Subject to Cost**
    The Gibbs distribution has maximum entropy among all distributions with the same
    expected cost. -/
theorem max_ent_subject_to_cost (p : ProbabilityDistribution Ω)
    (h_cost : expected_cost p.p X = expected_cost (gibbs_measure sys X) X) :
    recognition_entropy p.p ≤ recognition_entropy (gibbs_measure sys X) := by
  have h_min := gibbs_minimizes_free_energy_basic sys X p
  unfold recognition_free_energy at h_min
  rw [h_cost] at h_min
  have hTR := sys.TR_pos
  -- expected_cost - TR * entropy_gibbs ≤ expected_cost - TR * entropy_p
  -- -TR * entropy_gibbs ≤ -TR * entropy_p
  -- TR * entropy_p ≤ TR * entropy_gibbs
  -- entropy_p ≤ entropy_gibbs
  nlinarith

/-- **THEOREM: KL Divergence Zero Characterization**
    D_KL(q || p) = 0 iff q = p.

    **Proof**: KL divergence is non-negative by Jensen's inequality applied to
    the convex function -log. It equals zero iff log(q/p) = 0 a.s., i.e., q = p. -/
theorem kl_divergence_zero_iff_eq {Ω : Type*} [Fintype Ω]
    (q p : Ω → ℝ) (hq_nn : ∀ ω, 0 ≤ q ω) (hp_pos : ∀ ω, 0 < p ω)
    (hq_sum : ∑ ω, q ω = 1) (hp_sum : ∑ ω, p ω = 1) :
    kl_divergence q p = 0 ↔ ∀ ω, q ω = p ω := by
  constructor
  · intro h_kl_zero ω
    unfold kl_divergence at h_kl_zero
    let excess := fun ω' =>
      (if q ω' > 0 ∧ p ω' > 0 then q ω' * log (q ω' / p ω') else 0) - (q ω' - p ω')
    have h_excess_nn : ∀ ω' ∈ Finset.univ, 0 ≤ excess ω' := by
      intro ω' _
      simp only [excess]
      by_cases hq : 0 < q ω'
      · have hp' := hp_pos ω'
        simp only [hq, hp', and_self, ite_true]
        have hr := div_pos hp' hq
        have h_le := log_le_sub_one_of_pos hr
        rw [log_div hp'.ne' hq.ne'] at h_le
        have h_mult := mul_le_mul_of_nonneg_left h_le hq.le
        have h_expand : q ω' * (p ω' / q ω' - 1) = p ω' - q ω' := by
          field_simp [hq.ne']
        rw [log_div hq.ne' hp'.ne']
        linarith
      · push_neg at hq
        have hq' := hq_nn ω'
        have hq_zero : q ω' = 0 := le_antisymm hq hq'
        simp [hq_zero, (hp_pos ω').le]
    have h_qp_sum : ∑ ω', (q ω' - p ω') = 0 := by
      rw [Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]
    have h_excess_sum : ∑ ω', excess ω' = 0 := by
      have h_unfold : ∑ ω', excess ω' =
        ∑ ω', ((if q ω' > 0 ∧ p ω' > 0 then q ω' * log (q ω' / p ω') else 0) - (q ω' - p ω')) :=
        Finset.sum_congr rfl (fun _ _ => rfl)
      rw [h_unfold, Finset.sum_sub_distrib, h_kl_zero, h_qp_sum, sub_self]
    have h_each_zero : ∀ ω' ∈ Finset.univ, excess ω' = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg h_excess_nn).mp h_excess_sum
    have h_this := h_each_zero ω (Finset.mem_univ ω)
    simp only [excess] at h_this
    by_cases hq : 0 < q ω
    · have hp' := hp_pos ω
      simp only [hq, hp', and_self, ite_true] at h_this
      -- h_this : q ω * log (q ω / p ω) - (q ω - p ω) = 0
      -- Derive: log(q/p) = 1 - p/q
      have h_eq : q ω * log (q ω / p ω) = q ω - p ω := by linarith
      have h_log_eq : log (q ω / p ω) = 1 - p ω / q ω := by
        have step1 : log (q ω / p ω) = (q ω - p ω) / q ω := by
          rw [eq_div_iff hq.ne']; linarith [h_eq]
        rw [step1, sub_div, div_self hq.ne']
      -- Derive: log(p/q) = p/q - 1
      have hpq_pos : 0 < p ω / q ω := div_pos hp' hq
      have h_log_pq : log (p ω / q ω) = p ω / q ω - 1 := by
        have : log (p ω / q ω) = -log (q ω / p ω) := by
          rw [log_div hp'.ne' hq.ne', log_div hq.ne' hp'.ne']; ring
        rw [this, h_log_eq]; ring
      -- If q ≠ p then p/q ≠ 1, so strict inequality log(p/q) < p/q - 1 contradicts equality
      by_contra h_ne_eq
      have h_pq_ne_one : p ω / q ω ≠ 1 := by
        intro h; exact h_ne_eq ((div_eq_one_iff_eq hq.ne').mp h).symm
      have h_log_pq_ne : log (p ω / q ω) ≠ 0 := by
        rw [h_log_pq, sub_ne_zero]; exact h_pq_ne_one
      have h_strict := Real.add_one_lt_exp h_log_pq_ne
      rw [exp_log hpq_pos] at h_strict
      linarith [h_log_pq]
    · push_neg at hq
      have hq' := hq_nn ω
      have hq_zero : q ω = 0 := le_antisymm hq hq'
      simp only [hq_zero, show ¬(0 < (0:ℝ)) from not_lt.mpr le_rfl, false_and, ite_false] at h_this
      linarith [hp_pos ω]
  · -- q = p → D_KL = 0: direct computation
    intro h_eq
    unfold kl_divergence
    apply Finset.sum_eq_zero
    intro ω _
    simp only [h_eq ω, div_self (ne_of_gt (hp_pos ω)), log_one, mul_zero]
    split_ifs <;> rfl

/-- The Gibbs distribution is the unique minimizer of free energy. -/
theorem gibbs_unique_minimizer (q : ProbabilityDistribution Ω)
    (h_eq : recognition_free_energy sys q.p X = recognition_free_energy sys (gibbs_measure sys X) X) :
    ∀ ω, q.p ω = gibbs_measure sys X ω := by
  have h := free_energy_kl_identity sys X q
  rw [h_eq, sub_self] at h
  have hTR := sys.TR_pos
  have hkl_zero : kl_divergence q.p (gibbs_measure sys X) = 0 := by
    rw [eq_comm] at h
    have := mul_eq_zero.mp h
    cases this with
    | inl hTR0 => linarith
    | inr hkl0 => exact hkl0
  apply (kl_divergence_zero_iff_eq q.p (gibbs_measure sys X) q.nonneg (fun ω => gibbs_measure_pos sys X ω) q.sum_one (gibbs_measure_sum_one sys X)).mp
  exact hkl_zero

end Thermodynamics
end IndisputableMonolith
