import Mathlib

/-!
# Spectral convergence toolkit: quantitative eigenvalue limits

QG full-theory campaign, Phase 2a (reusable analysis toolkit).

## Status: THEOREM (all results below are proved, axiom-clean; no sorry,
## no admit, no `: True` shells).

## Lemmas and their campaign consumers

* `eigenvalue_limit_of_uniform_bound`: a `C/N²` eventual bound on
  `|λ_N - Λ|` forces `λ_N → Λ`. Names the squeeze pattern that Phase 4
  (curved operator convergence) applies branch by branch.
* `sub_cube_le_sin` / `abs_sin_sub_le_cube`: the global cubic Taylor bound
  `|sin t - t| ≤ t³/6` for `t ≥ 0`, proved from
  `Real.one_sub_sq_div_two_le_cos` by a monotonicity argument. Mathlib's
  `Real.sin_bound` only covers `|t| ≤ 1`; this version has no smallness
  hypothesis, which the eigenvalue expansion below needs since `πk/N` is
  not small for large wavenumber `k`.
* `discrete_sine_eigenvalue_expansion`: the sharp quantitative version of
  the DiscreteLichnerowicz flat TT limit:
  `|4N² sin²(πk/N) - (2πk)²| ≤ ((2πk)⁴/12)/N²` for `N ≥ 1`. This upgrades
  the qualitative `Tendsto` of
  `IndisputableMonolith/Gravity/SevenGaps/DiscreteLichnerowicz.lean`
  (`discreteEigenvalue_tendsto`) to an explicit rate, which Phase 4 curved
  perturbation bounds consume.
* `discrete_sine_eigenvalue_tendsto`: the qualitative limit re-derived from
  the rate through `eigenvalue_limit_of_uniform_bound`, verifying that the
  two toolkit pieces compose.
* `spectrum_gap_persistence`: converging eigenvalue branches with distinct
  limits eventually separate. The tool Phase 4 uses to keep curved
  eigenvalue branches apart.

## Downscope note

The campaign brief listed a fourth target, `min_max_monotone_perturbation`
(Courant-Fischer transport of pointwise quadratic-form domination to
eigenvalue domination). Mathlib's `Matrix.IsHermitian` API (as vendored
here) provides eigenvalues via diagonalization but no min-max
characterization, so the transport is not cheap; it is recorded here as
future work rather than sunk time. Nothing below depends on it.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis

open Filter Topology

/-- Helper: `C / N² → 0` as `N → ∞` over the naturals. -/
theorem const_div_sq_tendsto_zero (C : ℝ) :
    Filter.Tendsto (fun N : ℕ => C / (N : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun N : ℕ => ((N : ℝ)) ^ 2) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop two_ne_zero
    exact h1.comp tendsto_natCast_atTop_atTop
  exact tendsto_const_nhds.div_atTop hpow

/-- THEOREM (squeeze with rate). If the discrete eigenvalues `lam N` satisfy
`|lam N - Λ| ≤ C/N²` for all `N ≥ N₀`, then `lam N → Λ`. Trivial, but it
names the pattern Phase 4 applies to every curved eigenvalue branch. -/
theorem eigenvalue_limit_of_uniform_bound (lam : ℕ → ℝ) (Λ C : ℝ) (N₀ : ℕ)
    (h : ∀ N : ℕ, N₀ ≤ N → |lam N - Λ| ≤ C / (N : ℝ) ^ 2) :
    Filter.Tendsto lam Filter.atTop (nhds Λ) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => dist_nonneg) ?_
    (const_div_sq_tendsto_zero C)
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  rw [Real.dist_eq]
  exact h N hN

/-- THEOREM (global cubic sine lower bound). For `t ≥ 0`,
`t - t³/6 ≤ sin t`. Proof: `g(s) = sin s - s + s³/6` has derivative
`cos s - 1 + s²/2 ≥ 0` (by `Real.one_sub_sq_div_two_le_cos`), so `g` is
monotone and `g(t) ≥ g(0) = 0`. No smallness hypothesis on `t`. -/
theorem sub_cube_le_sin (t : ℝ) (ht : 0 ≤ t) :
    t - t ^ 3 / 6 ≤ Real.sin t := by
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun x : ℝ => Real.sin x - x + x ^ 3 / 6)
        (Real.cos s - 1 + (3 : ℝ) * s ^ 2 / 6) s := by
    intro s
    have hp : HasDerivAt (fun x : ℝ => x ^ 3) ((3 : ℝ) * s ^ 2) s := by
      have h := hasDerivAt_pow 3 s
      norm_num at h
      exact h
    exact ((Real.hasDerivAt_sin s).sub (hasDerivAt_id s)).add (hp.div_const 6)
  have hmono : Monotone (fun x : ℝ => Real.sin x - x + x ^ 3 / 6) := by
    refine monotone_of_hasDerivAt_nonneg hderiv ?_
    rw [Pi.le_def]
    intro s
    simp only [Pi.zero_apply]
    have hc := Real.one_sub_sq_div_two_le_cos (x := s)
    linarith
  have h0 : (fun x : ℝ => Real.sin x - x + x ^ 3 / 6) 0 = 0 := by
    simp
  have h := hmono ht
  rw [h0] at h
  simp only at h
  linarith

/-- THEOREM (global cubic Taylor bound for sine). For `t ≥ 0`,
`|sin t - t| ≤ t³/6`. Combines `Real.sin_le` (upper) with
`sub_cube_le_sin` (lower). Unlike Mathlib's `Real.sin_bound`, no `|t| ≤ 1`
hypothesis is needed. -/
theorem abs_sin_sub_le_cube (t : ℝ) (ht : 0 ≤ t) :
    |Real.sin t - t| ≤ t ^ 3 / 6 := by
  have h1 : Real.sin t ≤ t := Real.sin_le ht
  have h2 : t - t ^ 3 / 6 ≤ Real.sin t := sub_cube_le_sin t ht
  have h3 : 0 ≤ t ^ 3 / 6 := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- THEOREM (quantitative flat TT eigenvalue expansion). For every
wavenumber `k` and lattice resolution `N ≥ 1`,

`|4N² sin²(πk/N) - (2πk)²| ≤ ((2πk)⁴/12) / N²`.

This is the sharp rate behind the qualitative limit
`DiscreteLichnerowicz.discreteEigenvalue_tendsto`. Derivation: with
`x = πk/N` we have `(2πk)² = 4N²x²`, so the error factors as
`4N² (sin x - x)(sin x + x)`; then `|sin x - x| ≤ x³/6`
(`abs_sin_sub_le_cube`) and `|sin x + x| ≤ 2x` give the bound
`(4/3) N² x⁴ = ((2πk)⁴/12)/N²`. Phase 4 curved perturbation bounds consume
this explicit constant `C(k) = (2πk)⁴/12`. -/
theorem discrete_sine_eigenvalue_expansion (k N : ℕ) (hN : 1 ≤ N) :
    |4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2
        - (2 * Real.pi * (k : ℝ)) ^ 2|
      ≤ (2 * Real.pi * (k : ℝ)) ^ 4 / 12 / (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set x : ℝ := Real.pi * (k : ℝ) / (N : ℝ) with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    exact div_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg k)) hNpos.le
  have hkey : (2 * Real.pi * (k : ℝ)) ^ 2 = 4 * (N : ℝ) ^ 2 * x ^ 2 := by
    rw [hxdef]
    field_simp
    ring
  have hfac : 4 * (N : ℝ) ^ 2 * Real.sin x ^ 2 - (2 * Real.pi * (k : ℝ)) ^ 2
      = (4 * (N : ℝ) ^ 2) * ((Real.sin x - x) * (Real.sin x + x)) := by
    rw [hkey]
    ring
  have h4N : |4 * (N : ℝ) ^ 2| = 4 * (N : ℝ) ^ 2 := abs_of_nonneg (by positivity)
  have hbound1 : |Real.sin x - x| ≤ x ^ 3 / 6 := abs_sin_sub_le_cube x hx0
  have hbound2 : |Real.sin x + x| ≤ 2 * x := by
    calc |Real.sin x + x| ≤ |Real.sin x| + |x| := abs_add_le _ _
      _ ≤ |x| + |x| := by
          have := Real.abs_sin_le_abs (x := x)
          linarith
      _ = 2 * x := by rw [abs_of_nonneg hx0]; ring
  calc |4 * (N : ℝ) ^ 2 * Real.sin x ^ 2 - (2 * Real.pi * (k : ℝ)) ^ 2|
      = (4 * (N : ℝ) ^ 2) * (|Real.sin x - x| * |Real.sin x + x|) := by
        rw [hfac, abs_mul, h4N, abs_mul]
    _ ≤ (4 * (N : ℝ) ^ 2) * (x ^ 3 / 6 * (2 * x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hbound1 hbound2 (abs_nonneg _) (by positivity)
    _ = (2 * Real.pi * (k : ℝ)) ^ 4 / 12 / (N : ℝ) ^ 2 := by
        rw [hxdef]
        field_simp
        ring

/-- THEOREM (rated limit, composing the toolkit). The flat discrete TT
eigenvalue `4N² sin²(πk/N)` converges to `(2πk)²`, obtained by feeding the
quantitative expansion into `eigenvalue_limit_of_uniform_bound` with
`C = (2πk)⁴/12`. Re-derives
`DiscreteLichnerowicz.discreteEigenvalue_tendsto` with an explicit rate. -/
theorem discrete_sine_eigenvalue_tendsto (k : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => 4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2)
      Filter.atTop (nhds ((2 * Real.pi * (k : ℝ)) ^ 2)) :=
  eigenvalue_limit_of_uniform_bound _ _ ((2 * Real.pi * (k : ℝ)) ^ 4 / 12) 1
    (fun N hN => discrete_sine_eigenvalue_expansion k N hN)

/-- THEOREM (gap persistence). If two eigenvalue branches converge to
distinct limits `Λ < Μ`, then eventually `lam N < mu N`: spectral gaps
survive discretization for large `N`. The tool Phase 4 uses to separate
curved eigenvalue branches. -/
theorem spectrum_gap_persistence (lam mu : ℕ → ℝ) (Λ Μ : ℝ)
    (hlam : Filter.Tendsto lam Filter.atTop (nhds Λ))
    (hmu : Filter.Tendsto mu Filter.atTop (nhds Μ))
    (hlt : Λ < Μ) :
    ∀ᶠ N : ℕ in Filter.atTop, lam N < mu N :=
  hlam.eventually_lt hmu hlt

end Analysis
end Gravity
end IndisputableMonolith
