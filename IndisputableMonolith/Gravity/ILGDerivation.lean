import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.ILG

namespace IndisputableMonolith.Gravity.ILG

open Constants

/-- **THEOREM: ILG Time-Kernel Derivation**
    The time-kernel $w_t$ is uniquely determined by the recognition lag $C_{lag} = \varphi^{-5}$
    and the fine-structure exponent $\alpha$.

    This theorem formalizes the connection between the RRF gradient cost and the
    effective modified gravity at large scales. -/
theorem w_t_formula_grounded (P : Params) (Tdyn τ0 : ℝ) :
    P.Clag = phi ^ (-(5 : ℝ)) →
    P.alpha = (1 - 1/phi) / 2 →
    w_t P Tdyn τ0
      = 1 + (phi ^ (-(5 : ℝ)))
          * (Real.rpow (max defaultConfig.eps_t (Tdyn / τ0)) ((1 - 1/phi) / 2) - 1) := by
  intro hClag hAlpha
  simp [w_t, w_t_with, hClag, hAlpha]

/-- **Kernel strict monotonicity (rotational flattening, part 1).**
    On the un-clamped region (`eps_t ≤ Tdyn/τ0`), the ILG time-kernel is
    strictly increasing in the dynamical time whenever `alpha > 0` and
    `Clag > 0`. Longer orbits get a strictly larger recognition-lag
    enhancement, so the ILG rotation curve decays strictly slower than
    Keplerian at every radius: `w(T₂)·K/r₂ ÷ w(T₁)·K/r₁ > (K/r₂)/(K/r₁)`. -/
theorem w_t_strictMono_unclamped (P : Params) (τ0 : ℝ) (hτ : 0 < τ0)
    (hα : 0 < P.alpha) (hC : 0 < P.Clag) :
    ∀ T₁ T₂ : ℝ, defaultConfig.eps_t ≤ T₁ / τ0 → T₁ < T₂ →
      w_t P T₁ τ0 < w_t P T₂ τ0 := by
  intro T₁ T₂ h1 hlt
  have heps : (0 : ℝ) < defaultConfig.eps_t := by norm_num [defaultConfig]
  have h1pos : (0 : ℝ) < T₁ / τ0 := lt_of_lt_of_le heps h1
  have hdiv : T₁ / τ0 < T₂ / τ0 := by gcongr
  have hm1 : max defaultConfig.eps_t (T₁ / τ0) = T₁ / τ0 := max_eq_right h1
  have hm2 : max defaultConfig.eps_t (T₂ / τ0) = T₂ / τ0 :=
    max_eq_right (le_trans h1 hdiv.le)
  have hr : Real.rpow (T₁ / τ0) P.alpha < Real.rpow (T₂ / τ0) P.alpha :=
    Real.rpow_lt_rpow h1pos.le hdiv hα
  simp only [w_t, w_t_with, hm1, hm2]
  nlinarith [hr, hC]

/-- **Kernel divergence (rotational flattening, part 2).**
    For `alpha > 0`, `Clag > 0`, the enhancement is unbounded in the
    dynamical time: `w_t → ∞` as `Tdyn → ∞`. No finite radius exhausts the
    recognition-lag correction. -/
theorem w_t_tendsto_atTop (P : Params) (τ0 : ℝ) (hτ : 0 < τ0)
    (hα : 0 < P.alpha) (hC : 0 < P.Clag) :
    Filter.Tendsto (fun Tdyn => w_t P Tdyn τ0) Filter.atTop Filter.atTop := by
  have h1 : Filter.Tendsto (fun T : ℝ => T / τ0) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_div_const hτ
  have h2 : Filter.Tendsto (fun T : ℝ => max defaultConfig.eps_t (T / τ0))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun T => le_max_right _ _) h1
  have h3 : Filter.Tendsto (fun t : ℝ => Real.rpow t P.alpha)
      Filter.atTop Filter.atTop := tendsto_rpow_atTop hα
  have h4 := h3.comp h2
  have h5 := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) h4
  have h6 := Filter.Tendsto.const_mul_atTop hC h5
  have h7 := Filter.tendsto_atTop_add_const_left Filter.atTop (1 : ℝ) h6
  simpa [w_t, w_t_with, Function.comp, sub_eq_add_neg] using h7

/-- **THEOREM: Rotational flattening forced (honest form).**
    Replaces the former vacuous placeholder (`∃ v_flat, ... ∀ r, True`, which
    proved nothing). What the ILG kernel actually forces, and what this
    theorem states: for `alpha > 0` and `Clag > 0` the enhancement
    (i) strictly grows with dynamical time on the un-clamped region, and
    (ii) diverges as `Tdyn → ∞`. Consequently the enhanced squared velocity
    `w_t(Tdyn(r)) · v_N(r)²` decays strictly slower than the Newtonian
    `v_N(r)² ∝ 1/r` at every scale, which is the structural content of
    "rotation curves flatten." The exact asymptotic velocity value is an
    empirical matter (SPARC fits), not a theorem, and is not claimed here. -/
theorem rotational_flatness_forced (P : Params) (τ0 : ℝ) (hτ : 0 < τ0)
    (hα : 0 < P.alpha) (hC : 0 < P.Clag) :
    (∀ T₁ T₂ : ℝ, defaultConfig.eps_t ≤ T₁ / τ0 → T₁ < T₂ →
      w_t P T₁ τ0 < w_t P T₂ τ0)
    ∧ Filter.Tendsto (fun Tdyn => w_t P Tdyn τ0) Filter.atTop Filter.atTop :=
  ⟨w_t_strictMono_unclamped P τ0 hτ hα hC, w_t_tendsto_atTop P τ0 hτ hα hC⟩

/-- The enhancement exceeds every finite bound: for any `M` there is a
    dynamical time beyond which `w_t > M`. (Direct consequence of the
    divergence half of `rotational_flatness_forced`.) -/
theorem rotational_flatness_unbounded (P : Params) (τ0 : ℝ) (hτ : 0 < τ0)
    (hα : 0 < P.alpha) (hC : 0 < P.Clag) (M : ℝ) :
    ∃ T : ℝ, ∀ T' ≥ T, M < w_t P T' τ0 := by
  have h := (rotational_flatness_forced P τ0 hτ hα hC).2
  have hev : ∀ᶠ T' in Filter.atTop, M + 1 ≤ w_t P T' τ0 :=
    Filter.tendsto_atTop.mp h (M + 1)
  rcases Filter.eventually_atTop.mp hev with ⟨T, hT⟩
  exact ⟨T, fun T' hT' => lt_of_lt_of_le (by linarith) (hT T' hT')⟩

end ILG
end IndisputableMonolith.Gravity
