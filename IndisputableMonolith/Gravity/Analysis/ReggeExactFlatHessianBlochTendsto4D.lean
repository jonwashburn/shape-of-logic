import Mathlib

/-!
# Abstract cosine two-jet Tendsto for finite trig polynomials

Reusable Mathlib-only lemmas for the exact midpoint Bloch symbol route.
Does not import the 1208-row coupling table (elaboration-heavy).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactFlatHessianBlochTendsto4D

open BigOperators Filter Topology

noncomputable section

private theorem cos_sub_one_eq_neg_two_sin_sq (θ : ℝ) :
    Real.cos (2 * θ) - 1 = -(2 * Real.sin θ ^ 2) := by
  have h : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul (x := θ)
  have hs : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]

/-- `(cos(q a) - 1) / q² → -a²/2` on the punctured neighborhood of `0`. -/
theorem cos_sub_one_div_sq_tendsto (a : ℝ) :
    Tendsto (fun q : ℝ => (Real.cos (q * a) - 1) / q ^ 2)
      (𝓝[≠] (0 : ℝ)) (nhds (-(a ^ 2) / 2)) := by
  by_cases ha : a = 0
  · subst ha
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hq0 : q ≠ 0 := hq
    simp [Real.cos_zero, hq0]
  · have hcongr :
        (fun q : ℝ => (Real.cos (q * a) - 1) / q ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
          fun q : ℝ => -(a ^ 2 / 2) * (Real.sinc (q * a / 2)) ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      have hθ : (2 : ℝ) * (q * a / 2) = q * a := by ring
      have htrig := cos_sub_one_eq_neg_two_sin_sq (q * a / 2)
      rw [hθ] at htrig
      have hqa2 : q * a / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero hq ha) two_ne_zero
      have hstep :
          (-(2 * Real.sin (q * a / 2) ^ 2)) / q ^ 2 =
            -(a ^ 2 / 2) * (Real.sin (q * a / 2) / (q * a / 2)) ^ 2 := by
        field_simp [hq, ha, hqa2]
      calc
        (Real.cos (q * a) - 1) / q ^ 2
            = (-(2 * Real.sin (q * a / 2) ^ 2)) / q ^ 2 := by rw [htrig]
        _ = -(a ^ 2 / 2) * (Real.sin (q * a / 2) / (q * a / 2)) ^ 2 := hstep
        _ = -(a ^ 2 / 2) * (Real.sinc (q * a / 2)) ^ 2 := by
          rw [Real.sinc_of_ne_zero hqa2]

    let f : ℝ → ℝ := fun q => -(a ^ 2 / 2) * (Real.sinc ((a / 2) * q)) ^ 2
    have hfun :
        (fun q : ℝ => -(a ^ 2 / 2) * (Real.sinc (q * a / 2)) ^ 2) = f := by
      funext q; simp only [f]; ring_nf
    have hcont : Continuous f :=
      continuous_const.mul
        ((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2)
    have hlim0 : Tendsto f (𝓝 (0 : ℝ)) (nhds (f 0)) := hcont.continuousAt.tendsto
    have hf0 : f 0 = -(a ^ 2 / 2) := by simp [f, Real.sinc_zero]
    have hlim :
        Tendsto (fun q : ℝ => -(a ^ 2 / 2) * (Real.sinc (q * a / 2)) ^ 2)
          (𝓝[≠] (0 : ℝ)) (nhds (-(a ^ 2 / 2))) := by
      rw [hfun, ← hf0]
      exact hlim0.mono_left nhdsWithin_le_nhds
    have htarget : (-(a ^ 2) / 2) = -(a ^ 2 / 2) := by ring
    rw [htarget]
    exact (tendsto_congr' hcongr).mpr hlim

def centeredTrigPoly {ι : Type*} (w θ : ι → ℝ) (s : Finset ι) (t : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (Real.cos (t * θ i) - 1)

def centeredTrigPolyM2 {ι : Type*} (w θ : ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, w i * (-(θ i) ^ 2 / 2)

/-- **THEOREM:** centered Finset trig poly `/ t²` tends to its cosine two-jet. -/
theorem tendsto_centeredTrigPoly_div_sq
    {ι : Type*} (w θ : ι → ℝ) (s : Finset ι) :
    Tendsto (fun t : ℝ => centeredTrigPoly w θ s t / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (nhds (centeredTrigPolyM2 w θ s)) := by
  have hsum :
      Tendsto
        (fun t : ℝ =>
          ∑ i ∈ s, w i * ((Real.cos (t * θ i) - 1) / t ^ 2))
        (𝓝[≠] (0 : ℝ))
        (nhds (∑ i ∈ s, w i * (-(θ i) ^ 2 / 2))) := by
    refine tendsto_finset_sum s fun i _ =>
      (cos_sub_one_div_sq_tendsto (θ i)).const_mul (w i)
  have hcongr :
      (fun t : ℝ => centeredTrigPoly w θ s t / t ^ 2) =ᶠ[𝓝[≠] (0 : ℝ)]
        fun t : ℝ =>
          ∑ i ∈ s, w i * ((Real.cos (t * θ i) - 1) / t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    unfold centeredTrigPoly
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [ht]
  exact (tendsto_congr' hcongr).mpr hsum

/-- Division glue: `(centered/t²)/n → m2/n` when `n ≠ 0`. -/
theorem tendsto_centeredTrigPoly_m2_div
    {ι : Type*} (w θ : ι → ℝ) (s : Finset ι) (n : ℝ) (hn : n ≠ 0) :
    Tendsto (fun t : ℝ => centeredTrigPoly w θ s t / (t ^ 2 * n))
      (𝓝[≠] (0 : ℝ)) (nhds (centeredTrigPolyM2 w θ s / n)) := by
  have h := tendsto_centeredTrigPoly_div_sq w θ s
  have hdiv := h.div_const n
  refine (tendsto_congr' ?_).mpr hdiv
  filter_upwards [self_mem_nhdsWithin] with t ht
  field_simp [ht, hn]

end

end ReggeExactFlatHessianBlochTendsto4D
end Analysis
end Gravity
end IndisputableMonolith
