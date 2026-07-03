import Mathlib
import IndisputableMonolith.NavierStokes.Galerkin3D

/-!
# Galerkin Equicontinuity — McShane Extension (Proved)

Lipschitz constant for Fourier coefficients + rational approximation
+ Lipschitz dense extension via the McShane upper extension.

All results proved — no sorry, no axiom.
-/

namespace IndisputableMonolith.NavierStokes.GalerkinEquicontinuity

open Filter Topology

noncomputable section

def lipschitzConst (ν B kSq_val C_bilin : ℝ) : ℝ :=
  ν * kSq_val * B + C_bilin * B ^ 2

theorem lipschitzConst_nonneg {ν B kSq_val C_bilin : ℝ}
    (hν : 0 ≤ ν) (hB : 0 ≤ B) (hkSq : 0 ≤ kSq_val) (hC : 0 ≤ C_bilin) :
    0 ≤ lipschitzConst ν B kSq_val C_bilin := by
  unfold lipschitzConst; positivity

/-- For any real t and ε > 0, there's a rational q with |t - q| < ε. -/
theorem exists_rat_near (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, |t - (q : ℝ)| < ε := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - ε < t + ε by linarith)
  exact ⟨q, by rw [abs_lt]; constructor <;> linarith⟩

/-- Limit of bounded sequence is in closed ball. -/
theorem limit_in_closedBall {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X) (c : X) (R : ℝ) (x : X)
    (hf : ∀ n, dist (f n) c ≤ R)
    (hx : Tendsto f atTop (𝓝 x)) :
    dist x c ≤ R :=
  le_of_tendsto (hx.dist tendsto_const_nhds) (Filter.Eventually.of_forall hf)

/-!
## McShane upper extension

g(t) = inf_{q ∈ ℚ} (g_rat(q) + L * |t - q|)

This is L-Lipschitz and extends g_rat.
-/

private theorem mcshane_bddBelow
    (g_rat : ℚ → ℝ) (L : ℝ) (hL : 0 ≤ L) (t : ℝ)
    (h_g_lip : ∀ q₁ q₂ : ℚ, |g_rat q₁ - g_rat q₂| ≤ L * |(q₁ : ℝ) - q₂|) :
    BddBelow (Set.range (fun q : ℚ => g_rat q + L * |t - (q : ℝ)|)) := by
  refine ⟨g_rat 0 - L * |t|, ?_⟩
  rintro x ⟨q, rfl⟩
  have hg := h_g_lip 0 q
  -- Triangle: |0 - q| ≤ |t - q| + |t|
  have htri : |(0 : ℝ) - (q : ℝ)| ≤ |t - (q : ℝ)| + |t| := by
    have h1 := abs_add_le ((0 : ℝ) - t) (t - (q : ℝ))
    have h2 : (0 : ℝ) - t + (t - (q : ℝ)) = 0 - (q : ℝ) := by ring
    rw [h2] at h1
    have h3 : |(0 : ℝ) - t| = |t| := by
      have : (0 : ℝ) - t = -t := by ring
      rw [this, abs_neg]
    linarith
  have hmul := mul_le_mul_of_nonneg_left htri hL
  have hexp : L * (|t - (q : ℝ)| + |t|) = L * |t - (q : ℝ)| + L * |t| := by ring
  have ha : g_rat 0 - g_rat q ≤ L * |(0 : ℝ) - (q : ℝ)| := by
    have hg' : |g_rat 0 - g_rat q| ≤ L * |(0 : ℝ) - (q : ℝ)| := by
      have := hg; simp only [Rat.cast_zero] at this; exact this
    linarith [le_abs_self (g_rat 0 - g_rat q)]
  linarith [ha, hmul, hexp]

private theorem mcshane_at_rat
    (g_rat : ℚ → ℝ) (L : ℝ) (hL : 0 ≤ L) (q₀ : ℚ)
    (h_g_lip : ∀ q₁ q₂ : ℚ, |g_rat q₁ - g_rat q₂| ≤ L * |(q₁ : ℝ) - q₂|) :
    iInf (fun q : ℚ => g_rat q + L * |(q₀ : ℝ) - (q : ℝ)|) = g_rat q₀ := by
  apply le_antisymm
  · -- Upper: iInf ≤ value at q₀ (= g_rat q₀ + 0)
    apply ciInf_le_of_le (mcshane_bddBelow g_rat L hL q₀ h_g_lip) q₀
    simp
  · -- Lower: g_rat q₀ ≤ every value
    apply le_ciInf
    intro q
    have h := h_g_lip q₀ q
    linarith [le_abs_self (g_rat q₀ - g_rat q)]

private theorem mcshane_lipschitz
    (g_rat : ℚ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_g_lip : ∀ q₁ q₂ : ℚ, |g_rat q₁ - g_rat q₂| ≤ L * |(q₁ : ℝ) - q₂|)
    (t₁ t₂ : ℝ) :
    |iInf (fun q : ℚ => g_rat q + L * |t₁ - (q : ℝ)|) -
     iInf (fun q : ℚ => g_rat q + L * |t₂ - (q : ℝ)|)| ≤ L * |t₁ - t₂| := by
  rw [abs_le]
  -- Helper: triangle inequality for absolute values
  have tri₁₂ : ∀ q : ℚ, |t₂ - (q : ℝ)| ≤ |t₁ - (q : ℝ)| + |t₁ - t₂| := fun q => by
    have h := abs_add_le (t₂ - t₁) (t₁ - (q : ℝ))
    have : t₂ - t₁ + (t₁ - (q : ℝ)) = t₂ - (q : ℝ) := by ring
    rw [this] at h
    linarith [abs_sub_comm t₁ t₂]
  have tri₂₁ : ∀ q : ℚ, |t₁ - (q : ℝ)| ≤ |t₂ - (q : ℝ)| + |t₁ - t₂| := fun q => by
    have h := abs_add_le (t₁ - t₂) (t₂ - (q : ℝ))
    have : t₁ - t₂ + (t₂ - (q : ℝ)) = t₁ - (q : ℝ) := by ring
    rw [this] at h; linarith
  constructor
  · -- iInf₁ - iInf₂ ≥ -L|t₁-t₂|, i.e., iInf₂ ≤ iInf₁ + L|t₁-t₂|
    suffices h : iInf (fun q : ℚ => g_rat q + L * |t₂ - (q : ℝ)|) ≤
                 iInf (fun q : ℚ => g_rat q + L * |t₁ - (q : ℝ)|) + L * |t₁ - t₂| by linarith
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro q
    have hle := ciInf_le (mcshane_bddBelow g_rat L hL t₂ h_g_lip) q
    have hm := mul_le_mul_of_nonneg_left (tri₁₂ q) hL
    linarith [show L * (|t₁ - (q : ℝ)| + |t₁ - t₂|) =
              L * |t₁ - (q : ℝ)| + L * |t₁ - t₂| from by ring]
  · -- iInf₁ - iInf₂ ≤ L|t₁-t₂|, i.e., iInf₁ ≤ iInf₂ + L|t₁-t₂|
    suffices h : iInf (fun q : ℚ => g_rat q + L * |t₁ - (q : ℝ)|) ≤
                 iInf (fun q : ℚ => g_rat q + L * |t₂ - (q : ℝ)|) + L * |t₁ - t₂| by linarith
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro q
    have hle := ciInf_le (mcshane_bddBelow g_rat L hL t₁ h_g_lip) q
    have hm := mul_le_mul_of_nonneg_left (tri₂₁ q) hL
    linarith [show L * (|t₂ - (q : ℝ)| + |t₁ - t₂|) =
              L * |t₂ - (q : ℝ)| + L * |t₁ - t₂| from by ring]

/-- **Lipschitz dense extension via McShane.**

An L-Lipschitz function g_rat on ℚ extends to an L-Lipschitz g on ℝ.
Moreover, if f_n → g_rat at each rational and f_n is uniformly L-Lipschitz,
then f_n → g at every real t (the 3ε argument).

The extension is the McShane upper extension: g(t) = inf_q (g_rat q + L|t-q|). -/
theorem lipschitz_dense_extension
    (f : ℕ → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_lip : ∀ n t₁ t₂, |f n t₁ - f n t₂| ≤ L * |t₁ - t₂|)
    (g_rat : ℚ → ℝ)
    (h_conv_rat : ∀ q : ℚ, Tendsto (fun n => f n (q : ℝ)) atTop (𝓝 (g_rat q)))
    (h_g_lip : ∀ q₁ q₂ : ℚ, |g_rat q₁ - g_rat q₂| ≤ L * |(q₁ : ℝ) - q₂|) :
    ∃ g : ℝ → ℝ,
      (∀ q : ℚ, g (q : ℝ) = g_rat q) ∧
      (∀ t₁ t₂, |g t₁ - g t₂| ≤ L * |t₁ - t₂|) ∧
      (∀ t : ℝ, Tendsto (fun n => f n t) atTop (𝓝 (g t))) := by
  let g : ℝ → ℝ := fun t => iInf (fun q : ℚ => g_rat q + L * |t - (q : ℝ)|)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro q₀; exact mcshane_at_rat g_rat L hL q₀ h_g_lip
  · intro t₁ t₂; exact mcshane_lipschitz g_rat L hL h_g_lip t₁ t₂
  · -- 3ε argument: f_n → g at every real t
    intro t
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨q, hq⟩ := exists_rat_near t (show 0 < ε / (3 * (L + 1)) by positivity)
    have hgq : g (q : ℝ) = g_rat q := mcshane_at_rat g_rat L hL q h_g_lip
    have h_conv_q := h_conv_rat q
    rw [Metric.tendsto_atTop] at h_conv_q
    obtain ⟨N, hN⟩ := h_conv_q (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 : |f n t - f n (q : ℝ)| ≤ L * |t - (q : ℝ)| := h_lip n t q
    have h2 : |f n (q : ℝ) - g_rat q| < ε / 3 := by
      have := hN n hn; rwa [Real.dist_eq] at this
    have h3' : |g_rat q - g t| ≤ L * |t - (q : ℝ)| := by
      rw [← hgq]
      have hmc := mcshane_lipschitz g_rat L hL h_g_lip (q : ℝ) t
      rwa [abs_sub_comm (q : ℝ) t] at hmc
    have hLt : L * |t - (q : ℝ)| < ε / 3 := by
      have hpos : 0 < 3 * (L + 1) := by positivity
      calc L * |t - (q : ℝ)|
          ≤ (L + 1) * |t - (q : ℝ)| := by nlinarith [abs_nonneg (t - (q : ℝ))]
        _ < (L + 1) * (ε / (3 * (L + 1))) := by nlinarith [abs_nonneg (t - (q : ℝ))]
        _ = ε / 3 := by field_simp
    -- Triangle: |f n t - g t| ≤ |fn t - fn q| + |fn q - g_rat q| + |g_rat q - g t|
    have htri1 : |f n t - g t| ≤ |f n t - f n (q : ℝ)| + |f n (q : ℝ) - g t| := by
      have h := abs_add_le (f n t - f n (q : ℝ)) (f n (q : ℝ) - g t)
      have heq : (f n t - f n (q : ℝ)) + (f n (q : ℝ) - g t) = f n t - g t := by ring
      rwa [heq] at h
    have htri2 : |f n (q : ℝ) - g t| ≤ |f n (q : ℝ) - g_rat q| + |g_rat q - g t| := by
      have h := abs_add_le (f n (q : ℝ) - g_rat q) (g_rat q - g t)
      have heq : (f n (q : ℝ) - g_rat q) + (g_rat q - g t) = f n (q : ℝ) - g t := by ring
      rwa [heq] at h
    linarith

end

end IndisputableMonolith.NavierStokes.GalerkinEquicontinuity
