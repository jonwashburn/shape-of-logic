import IndisputableMonolith.Gravity.SevenGaps.HingeStationarityCore

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace SourcedMinimizerSupDiameter

open Set

noncomputable section

/-!
# Sourced-action approximate-minimizer sup-norm diameter

MODEL flag (inherited from `HingeStationarityCore`): the deficit-source
coupling term `-(c/n) * sum_i t_i` inside `sourcedAction` is an explicit
constitutive MODEL input, not derived from the bare RecognitionLedger.
Everything proved ABOUT that action — including the diameter bound below —
is THEOREM.
-/

/-- Helper: g(h) = sinh(s+h) - sinh s - h. -/
private noncomputable def g (s : ℝ) (h : ℝ) : ℝ :=
  Real.sinh (s + h) - Real.sinh s - h

/-- Helper: F(h) = cosh(s+h) - cosh s - sinh s * h - h²/2. -/
private noncomputable def F (s : ℝ) (h : ℝ) : ℝ :=
  Real.cosh (s + h) - Real.cosh s - Real.sinh s * h - h ^ 2 / 2

private theorem hasDerivAt_g (s h : ℝ) :
    HasDerivAt (g s) (Real.cosh (s + h) - 1) h := by
  have hsinh :
      HasDerivAt (fun x : ℝ => Real.sinh (s + x)) (Real.cosh (s + h)) h := by
    have hcomp :=
      (Real.hasDerivAt_sinh (s + h)).comp h ((hasDerivAt_id h).const_add s)
    simpa [Function.comp_def] using hcomp
  have hconst : HasDerivAt (fun _ : ℝ => Real.sinh s) 0 h := hasDerivAt_const h _
  have hid : HasDerivAt (fun x : ℝ => x) 1 h := hasDerivAt_id h
  have hsub := (hsinh.sub hconst).sub hid
  simpa [g] using hsub

private theorem g_zero (s : ℝ) : g s 0 = 0 := by
  simp [g]

private theorem g_monotone (s : ℝ) : Monotone (g s) := by
  refine monotone_of_deriv_nonneg (fun x => (hasDerivAt_g s x).differentiableAt) ?_
  intro x
  rw [(hasDerivAt_g s x).deriv]
  linarith [Real.one_le_cosh (s + x)]

private theorem g_nonneg_of_nonneg (s h : ℝ) (hh : 0 ≤ h) : 0 ≤ g s h := by
  have := (g_monotone s) hh
  simpa [g_zero] using this

private theorem g_nonpos_of_nonpos (s h : ℝ) (hh : h ≤ 0) : g s h ≤ 0 := by
  have := (g_monotone s) hh
  simpa [g_zero] using this

private theorem hasDerivAt_F (s h : ℝ) : HasDerivAt (F s) (g s h) h := by
  have hcosh :
      HasDerivAt (fun x : ℝ => Real.cosh (s + x)) (Real.sinh (s + h)) h := by
    have hcomp :=
      (Real.hasDerivAt_cosh (s + h)).comp h ((hasDerivAt_id h).const_add s)
    simpa [Function.comp_def] using hcomp
  have hconst : HasDerivAt (fun _ : ℝ => Real.cosh s) 0 h := hasDerivAt_const h _
  have hlin : HasDerivAt (fun x : ℝ => Real.sinh s * x) (Real.sinh s) h := by
    simpa using (hasDerivAt_id h).const_mul (Real.sinh s)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / 2) h h := by
    have hpow := (hasDerivAt_pow 2 h).div_const 2
    convert hpow using 1
    ring
  have h1 := (hcosh.sub hconst).sub hlin
  have h2 := h1.sub hsq
  -- h2 : HasDerivAt (...fun form...) (sinh(s+h) - sinh s - h) h
  simpa [F, g] using h2

private theorem F_zero (s : ℝ) : F s 0 = 0 := by
  simp [F]

private theorem F_nonneg (s h : ℝ) : 0 ≤ F s h := by
  have hdiff : Differentiable ℝ (F s) := fun x => (hasDerivAt_F s x).differentiableAt
  have hcont : Continuous (F s) := hdiff.continuous
  have hmono : MonotoneOn (F s) (Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
      hdiff.differentiableOn ?_
    intro x hx
    have hx0 : 0 < x := by
      have : x ∈ Ioi (0 : ℝ) := by rwa [interior_Ici] at hx
      exact this
    rw [(hasDerivAt_F s x).deriv]
    exact g_nonneg_of_nonneg s x hx0.le
  have hanti : AntitoneOn (F s) (Iic (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn
      hdiff.differentiableOn ?_
    intro x hx
    have hx0 : x < 0 := by
      have : x ∈ Iio (0 : ℝ) := by rwa [interior_Iic] at hx
      exact this
    rw [(hasDerivAt_F s x).deriv]
    exact g_nonpos_of_nonpos s x hx0.le
  rcases le_total h 0 with hle | hge
  · -- h ≤ 0: antitone ⇒ F 0 ≤ F h
    have := hanti hle (le_rfl : (0 : ℝ) ≤ 0) hle
    -- this : F 0 ≤ F h? Wait AntitoneOn: x≤y → f y ≤ f x, so F 0 ≤ F h
    simpa [F_zero] using this
  · -- 0 ≤ h: monotone ⇒ F 0 ≤ F h
    have := hmono (le_rfl : (0 : ℝ) ≤ 0) hge hge
    simpa [F_zero] using this

/-- Per-tick quadratic well at the stationary point s = arsinh a. -/
private theorem sourced_tick_quadratic_well (a t : ℝ) :
    Real.cosh t - 1 - a * t - (Real.cosh (Real.arsinh a) - 1 - a * Real.arsinh a)
      ≥ (1 / 2) * (t - Real.arsinh a) ^ 2 := by
  set s := Real.arsinh a
  set h := t - s with hh
  have hs : Real.sinh s = a := Real.sinh_arsinh a
  have hF := F_nonneg s h
  have ht : t = s + h := by simp [h]
  have hrewrite :
      Real.cosh t - 1 - a * t - (Real.cosh s - 1 - a * s)
        = Real.cosh (s + h) - Real.cosh s - Real.sinh s * h := by
    rw [ht, hs]
    ring
  have hge :
      Real.cosh (s + h) - Real.cosh s - Real.sinh s * h ≥ h ^ 2 / 2 := by
    have : F s h ≥ 0 := hF
    simp only [F] at this
    linarith
  calc
    Real.cosh t - 1 - a * t - (Real.cosh s - 1 - a * s)
        = Real.cosh (s + h) - Real.cosh s - Real.sinh s * h := hrewrite
    _ ≥ h ^ 2 / 2 := hge
    _ = (1 / 2) * (t - s) ^ 2 := by
          simp [h]
          ring

/-- One-point distance from an eps-approximate minimizer to the well. -/
private theorem approx_tick_dist
    (n : ℕ) (c : ℝ) (eps : ℝ) (_heps : 0 ≤ eps)
    (u : Fin n → ℝ)
    (hu : sourcedAction n c u ≤ sourcedAction n c (sourcedMinimizer n c) + eps)
    (i : Fin n) :
    |u i - Real.arsinh (c / n)| ≤ Real.sqrt (2 * eps) := by
  set s := Real.arsinh (c / n)
  set a := c / n
  have hwell := sourced_tick_quadratic_well a (u i)
  have hexcess :
      sourcedAction n c u - sourcedAction n c (sourcedMinimizer n c) ≤ eps := by
    linarith [hu]
  have hsum :
      sourcedAction n c u - sourcedAction n c (sourcedMinimizer n c)
        = ∑ j : Fin n,
            ((Real.cosh (u j) - 1 - a * u j)
              - (Real.cosh s - 1 - a * s)) := by
    rw [sourcedAction_eq_sum, sourcedAction_eq_sum]
    simp only [sourcedMinimizer, a, s]
    rw [← Finset.sum_sub_distrib]
  have hterm_nonneg :
      ∀ j : Fin n,
        0 ≤
          (Real.cosh (u j) - 1 - a * u j)
            - (Real.cosh s - 1 - a * s) := by
    intro j
    have := sourced_pointwise_le a (u j)
    simp only [a, s] at this ⊢
    linarith
  have hsingle :
      (Real.cosh (u i) - 1 - a * u i) - (Real.cosh s - 1 - a * s)
        ≤ sourcedAction n c u - sourcedAction n c (sourcedMinimizer n c) := by
    rw [hsum]
    exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
  have htick :
      (Real.cosh (u i) - 1 - a * u i) - (Real.cosh s - 1 - a * s) ≤ eps :=
    le_trans hsingle hexcess
  have hquad :
      (1 / 2 : ℝ) * (u i - s) ^ 2
        ≤ (Real.cosh (u i) - 1 - a * u i) - (Real.cosh s - 1 - a * s) := by
    simpa [s, a] using hwell
  have hsq : (u i - s) ^ 2 ≤ 2 * eps := by
    nlinarith [hquad, htick]
  exact Real.abs_le_sqrt hsq

/-- **THEOREM (sourced-action approximate-minimizer sup-norm diameter).**
For any abstract global minimizer `m` of the sourced hinge action and any
two eps-approximate minimizers `u`, `v`, every tick satisfies
`|u i - v i| ≤ 2 * √(2ε)`. The deficit-source coupling inside
`sourcedAction` remains MODEL; the diameter bound is THEOREM. -/
theorem sourced_minimizer_sup_diameter
    (n : ℕ) (c : ℝ) (m : Fin n → ℝ)
    (hm : ∀ t, sourcedAction n c m ≤ sourcedAction n c t)
    (eps : ℝ) (heps : 0 ≤ eps)
    (u v : Fin n → ℝ)
    (hu : sourcedAction n c u ≤ sourcedAction n c m + eps)
    (hv : sourcedAction n c v ≤ sourcedAction n c m + eps)
    (i : Fin n) :
    |u i - v i| ≤ 2 * Real.sqrt (2 * eps) := by
  -- Step 1: parent uniqueness pins the abstract minimizer to the canonical well.
  have hparent := sourced_unique_minimizer n c m
  have hle_can : sourcedAction n c (sourcedMinimizer n c) ≤ sourcedAction n c m :=
    hparent.1
  have hle_m : sourcedAction n c m ≤ sourcedAction n c (sourcedMinimizer n c) :=
    hm (sourcedMinimizer n c)
  have heq_act :
      sourcedAction n c m = sourcedAction n c (sourcedMinimizer n c) :=
    le_antisymm hle_m hle_can
  have hm_eq : m = sourcedMinimizer n c := hparent.2 heq_act
  have hu' :
      sourcedAction n c u ≤ sourcedAction n c (sourcedMinimizer n c) + eps := by
    simpa [hm_eq] using hu
  have hv' :
      sourcedAction n c v ≤ sourcedAction n c (sourcedMinimizer n c) + eps := by
    simpa [hm_eq] using hv
  have bu := approx_tick_dist n c eps heps u hu' i
  have bv := approx_tick_dist n c eps heps v hv' i
  set s := Real.arsinh (c / n)
  have htri : |u i - v i| ≤ |u i - s| + |v i - s| := by
    calc
      |u i - v i| ≤ |u i - s| + |s - v i| := abs_sub_le (u i) s (v i)
      _ = |u i - s| + |v i - s| := by rw [abs_sub_comm s (v i)]
  have hsum : |u i - s| + |v i - s| ≤ Real.sqrt (2 * eps) + Real.sqrt (2 * eps) :=
    add_le_add bu bv
  have htwo :
      Real.sqrt (2 * eps) + Real.sqrt (2 * eps) = 2 * Real.sqrt (2 * eps) := by
    ring
  calc
    |u i - v i| ≤ |u i - s| + |v i - s| := htri
    _ ≤ Real.sqrt (2 * eps) + Real.sqrt (2 * eps) := hsum
    _ = 2 * Real.sqrt (2 * eps) := htwo

end

end SourcedMinimizerSupDiameter
end SevenGaps
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.SevenGaps.SourcedMinimizerSupDiameter.sourced_minimizer_sup_diameter
