import Mathlib
import IndisputableMonolith.Constants

/-!
# Growth Bounds: Exponential Defeats Polynomial

Pure real analysis results establishing that exponential growth
eventually dominates any polynomial. Specific instances for
the φ-ladder vs. cubic volume growth close the Fermi chain.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GrowthBounds

open Constants

/-! ## §1 Bernoulli and base results -/

/-- Bernoulli's inequality: for a ≥ 1, a^n ≥ 1 + n*(a-1). -/
theorem exp_ge_linear (a : ℝ) (ha : 1 ≤ a) (n : ℕ) :
    a ^ n ≥ 1 + (n : ℝ) * (a - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have ha_nonneg : 0 ≤ a := by linarith
    have hk_nn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc a ^ (k + 1) = a ^ k * a := pow_succ a k
      _ ≥ (1 + (k : ℝ) * (a - 1)) * a := by
          exact mul_le_mul_of_nonneg_right ih ha_nonneg
      _ = a + (k : ℝ) * a * (a - 1) := by ring
      _ ≥ a + (k : ℝ) * 1 * (a - 1) := by
          nlinarith [mul_nonneg hk_nn (sub_nonneg.mpr ha), sq_nonneg (a - 1)]
      _ = 1 + ((k : ℝ) + 1) * (a - 1) := by ring
      _ = 1 + (↑(k + 1) : ℝ) * (a - 1) := by push_cast; ring

/-- For a > 1 and any M, there exists N such that a^N > M. -/
theorem exponential_exceeds_bound (a : ℝ) (ha : 1 < a) (M : ℝ) :
    ∃ N : ℕ, a ^ N > M := by
  have ha_sub : 0 < a - 1 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((M - 1) / (a - 1))
  refine ⟨N, ?_⟩
  have hge := exp_ge_linear a (le_of_lt ha) N
  have hN_bound : (N : ℝ) * (a - 1) > M - 1 := by
    have := (div_lt_iff₀ ha_sub).mp hN
    linarith
  linarith

/-- φ eventually exceeds any bound. -/
theorem phi_pow_exceeds (M : ℝ) : ∃ N : ℕ, phi ^ N > M :=
  exponential_exceeds_bound phi one_lt_phi M

/-! ## §2 The four-power trick -/

/-- phi^(4*M) ≥ (M/2)^4.
    Proof: phi^(4*M) = (phi^M)^4 ≥ (M*(phi-1))^4 ≥ (M/2)^4. -/
lemma phi_four_power_lower (M : ℕ) :
    phi ^ (4 * M) ≥ ((M : ℝ) / 2) ^ 4 := by
  have hphi_half : phi - 1 ≥ 1 / 2 := by linarith [phi_gt_onePointFive]
  have hM_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- Simplify: phi^(4M) = (phi^M)^4
  have hpow : phi ^ (4 * M) = (phi ^ M) ^ 4 := by
    rw [← pow_mul]; ring_nf
  rw [hpow]
  -- phi^M ≥ M/2
  have hbern : phi ^ M ≥ 1 + (M : ℝ) * (phi - 1) :=
    exp_ge_linear phi (le_of_lt (by linarith [phi_gt_onePointFive])) M
  have hge_half : phi ^ M ≥ (M : ℝ) / 2 := by nlinarith
  -- (phi^M)^4 ≥ (M/2)^4
  exact pow_le_pow_left₀ (by positivity) hge_half 4

/-! ## §3 φ-exponential defeats cubic -/

/-- **φ-EXPONENTIAL DEFEATS CUBIC** (zero sorry)

    For any C > 0, ∃ N such that φ^N > C · N³.
    Witness: N = 4*(k+1) where k+1 > 1024*C.
    Proof: φ^(4*(k+1)) ≥ ((k+1)/2)^4 = (k+1)^4/16 > C*(4*(k+1))^3 = 64C*(k+1)^3
           when (k+1) > 1024C. -/
theorem phi_exp_defeats_cubic (C : ℝ) (_hC : 0 < C) :
    ∃ N : ℕ, phi ^ N > C * (N : ℝ) ^ 3 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1024 * C)
  refine ⟨4 * (k + 1), ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
  have hk1_gt : (k : ℝ) + 1 > 1024 * C := by
    have h := hk; push_cast at h ⊢; linarith
  have hlow : phi ^ (4 * (k + 1)) ≥ (((k : ℝ) + 1) / 2) ^ 4 := by
    have := phi_four_power_lower (k + 1)
    push_cast at this ⊢
    linarith
  have hM3_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 := pow_pos hk1 3
  have hgoal : (((k : ℝ) + 1) / 2) ^ 4 > C * (↑(4 * (k + 1)) : ℝ) ^ 3 := by
    push_cast
    nlinarith [mul_pos (show (k : ℝ) + 1 - 1024 * C > 0 by linarith) hM3_pos]
  linarith

/-- **φ-EXPONENTIAL DEFEATS SHIFTED CUBIC** (zero sorry)

    For any C > 0, ∃ N such that φ^N > C · (N+1)³.
    Witness: N = 4*(k+1) where k+1 > 2000*C.
    Needed for the density bound which uses volume V₀*(N+1)³. -/
theorem phi_exp_defeats_cubic_succ (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, phi ^ N > C * ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2000 * C)
  refine ⟨4 * (k + 1), ?_⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by exact_mod_cast Nat.succ_pos k
  have hk1_gt : (k : ℝ) + 1 > 2000 * C := by
    have h := hk; push_cast at h ⊢; linarith
  have hlow : phi ^ (4 * (k + 1)) ≥ (((k : ℝ) + 1) / 2) ^ 4 := by
    have := phi_four_power_lower (k + 1)
    push_cast at this ⊢; linarith
  -- (4*(k+1)+1)^3 ≤ (5*(k+1))^3 since 4*(k+1)+1 ≤ 5*(k+1) iff 1 ≤ k+1, which holds
  have h5k1 : (4 : ℝ) * ((k : ℝ) + 1) + 1 ≤ 5 * ((k : ℝ) + 1) := by nlinarith
  have hM3_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 3 := pow_pos hk1 3
  -- (k+1)^4/16 > C*(5*(k+1))^3 = 125*C*(k+1)^3 when (k+1) > 2000*C
  have hgoal : (((k : ℝ) + 1) / 2) ^ 4 > C * (5 * ((k : ℝ) + 1)) ^ 3 := by
    nlinarith [mul_pos (show (k : ℝ) + 1 - 2000 * C > 0 by linarith) hM3_pos]
  have hcast : ((↑(4 * (k + 1)) : ℝ) + 1) = 4 * ((k : ℝ) + 1) + 1 := by
    push_cast; ring
  rw [hcast]
  calc phi ^ (4 * (k + 1))
      ≥ (((k : ℝ) + 1) / 2) ^ 4 := hlow
    _ > C * (5 * ((k : ℝ) + 1)) ^ 3 := hgoal
    _ ≥ C * (4 * ((k : ℝ) + 1) + 1) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC)
        exact pow_le_pow_left₀ (by positivity) h5k1 3

/-! ## §4 Density bound -/

/-- **LOCAL DENSITY EVENTUALLY EXCEEDS ANY THRESHOLD**

    K₀ * φ^N / (V₀ * (N+1)³) → ∞ as N → ∞. -/
theorem density_exceeds_threshold (K₀ : ℝ) (hK₀ : 0 < K₀)
    (V₀ : ℝ) (hV₀ : 0 < V₀) (threshold : ℝ) (hT : 0 < threshold) :
    ∃ N : ℕ, K₀ * phi ^ N / (V₀ * ((N : ℝ) + 1) ^ 3) > threshold := by
  -- Need phi^N > (threshold * V₀ / K₀) * (N+1)^3
  have hC : 0 < threshold * V₀ / K₀ := by positivity
  obtain ⟨N, hN⟩ := phi_exp_defeats_cubic_succ (threshold * V₀ / K₀) hC
  refine ⟨N, ?_⟩
  have hdenom_pos : 0 < V₀ * ((N : ℝ) + 1) ^ 3 := by positivity
  rw [gt_iff_lt, lt_div_iff₀ hdenom_pos]
  -- Goal: threshold * (V₀ * (N+1)^3) < K₀ * phi^N
  -- From hN: phi^N > (threshold*V₀/K₀) * (N+1)^3
  -- So K₀ * phi^N > K₀ * (threshold*V₀/K₀) * (N+1)^3 = threshold*V₀*(N+1)^3
  have hphi_pos : 0 < phi ^ N := pow_pos phi_pos N
  have hNN3 : 0 < ((N : ℝ) + 1) ^ 3 := by positivity
  have hK0phi : K₀ * phi ^ N > K₀ * (threshold * V₀ / K₀) * ((N : ℝ) + 1) ^ 3 := by
    have := mul_lt_mul_of_pos_left hN hK₀
    simp only [mul_comm, mul_assoc] at this ⊢
    linarith
  have hsimp : K₀ * (threshold * V₀ / K₀) * ((N : ℝ) + 1) ^ 3 =
               threshold * V₀ * ((N : ℝ) + 1) ^ 3 := by
    have hK0ne : K₀ ≠ 0 := ne_of_gt hK₀
    field_simp [hK0ne]
  rw [hsimp] at hK0phi
  linarith

end GrowthBounds
end Foundation
end IndisputableMonolith
