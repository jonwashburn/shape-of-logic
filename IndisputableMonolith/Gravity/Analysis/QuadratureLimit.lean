import Mathlib

/-!
# Quadrature limit toolkit: hinge sums converge to continuum integrals

QG full-theory campaign, Phase 2a (reusable analysis toolkit).

## Status: THEOREM (all results below are proved, axiom-clean; no sorry,
## no admit, no `: True` shells).

## What this module provides

Mathlib (as vendored here) has no elementary "uniform-mesh Riemann sums of a
continuous function converge to the interval integral" statement: the
`BoxIntegral` library works at the level of tagged-partition filters, and
`TrapezoidalRule` gives error bounds for C^2 integrands only. The core lemma
`riemannSum_tendsto_integral` below is therefore proved from scratch via
Heine-Cantor uniform continuity (`IsCompact.uniformContinuousOn_of_continuous`)
and the adjacent-interval splitting
`intervalIntegral.sum_integral_adjacent_intervals`.

## Lemmas and their campaign consumers

* `riemannSum_tendsto_integral`: for `f` continuous on `[a, b]`, the
  left-endpoint uniform-mesh Riemann sums
  `Σ_{k<N} f(a + k(b-a)/N) · (b-a)/N` tend to `∫ x in a..b, f x`.
  Consumed by Phase 5 (continuum bracket limit) as the generic
  discrete-action-to-integral bridge.
* `latticeSum_tendsto_integral`: the campaign-facing hinge-sum shape,
  `(1/N) Σ_{k<N} f(k/N) → ∫ x in 0..1, f x`.
  Consumed by Phase 4 (curved operator convergence) and Phase 5.
* `weightedLatticeSum_tendsto`: same with a continuous weight,
  `(1/N) Σ_{k<N} f(k/N) w(k/N) → ∫ f·w`. Consumed by Phase 5 for
  measure-weighted hinge sums.
* `sq_error_sum_tendsto_zero`: a uniform per-term `C/N²` bound forces the
  N-term absolute error sum to vanish. Consumed by Phase 4 remainder
  estimates (curved perturbation of the flat spectrum).
* `error_sum_tendsto_zero`: signed version of the previous lemma.

These generalize the scoped quadrature reductions in
`IndisputableMonolith/Gravity/D2ScalarDirichletQuadratureLimit.lean` (which
packages the limit as a hypothesis structure) by actually proving the limit
for continuous integrands, and they generalize the flat eigenvalue
convergence pattern of
`IndisputableMonolith/Gravity/SevenGaps/DiscreteLichnerowicz.lean`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis

open Filter Topology MeasureTheory

/-- THEOREM (core quadrature limit). For `f : ℝ → ℝ` continuous on `[a, b]`
with `a ≤ b`, the left-endpoint uniform-mesh Riemann sums
`Σ_{k<N} f(a + k(b-a)/N) · ((b-a)/N)` converge to `∫ x in a..b, f x` as
`N → ∞`.

Proof: Heine-Cantor gives uniform continuity of `f` on the compact interval;
splitting the integral over the `N` mesh cells
(`intervalIntegral.sum_integral_adjacent_intervals`) reduces the error to a
sum of `N` cell errors, each bounded by `ε · (b-a)/N` once the mesh
`(b-a)/N` is below the uniform-continuity scale `δ`. -/
theorem riemannSum_tendsto_integral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        f (a + (k : ℝ) * (b - a) / (N : ℝ)) * ((b - a) / (N : ℝ)))
      Filter.atTop (nhds (∫ x in a..b, f x)) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst heq
    simp only [sub_self, mul_zero, zero_div, add_zero,
      Finset.sum_const_zero, intervalIntegral.integral_same]
    exact tendsto_const_nhds
  · have hba : 0 < b - a := sub_pos.2 hlt
    rw [Metric.tendsto_atTop]
    intro ε hε
    set ε' : ℝ := ε / (2 * (b - a)) with hε'def
    have hε' : 0 < ε' := div_pos hε (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.uniformContinuousOn_iff_le.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε' hε'
    obtain ⟨M, hM⟩ := exists_nat_ge ((b - a) / δ)
    refine ⟨max M 1, fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hN
    have hNM : M ≤ N := le_trans (le_max_left M 1) hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hmesh : (b - a) / (N : ℝ) ≤ δ := by
      rw [div_le_iff₀ hNpos]
      have h1 : (b - a) / δ ≤ (N : ℝ) := le_trans hM (by exact_mod_cast hNM)
      have h2 : δ * ((b - a) / δ) ≤ δ * (N : ℝ) :=
        mul_le_mul_of_nonneg_left h1 hδpos.le
      have h3 : δ * ((b - a) / δ) = b - a := by field_simp
      linarith
    set p : ℕ → ℝ := fun k => a + (k : ℝ) * (b - a) / (N : ℝ) with hp
    have hp0 : p 0 = a := by simp [hp]
    have hpN : p N = b := by
      simp only [hp]
      field_simp
      ring
    have hstep : ∀ k : ℕ, p (k + 1) - p k = (b - a) / (N : ℝ) := by
      intro k
      simp only [hp]
      push_cast
      ring
    have hmeshpos : 0 ≤ (b - a) / (N : ℝ) := div_nonneg hba.le hNpos.le
    have hple : ∀ k : ℕ, p k ≤ p (k + 1) := by
      intro k
      have := hstep k
      linarith
    have hmem : ∀ k : ℕ, k ≤ N → p k ∈ Set.Icc a b := by
      intro k hk
      have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
      have hq : 0 ≤ (b - a) / (N : ℝ) := hmeshpos
      have h2 := mul_le_mul_of_nonneg_left hkN hq
      have hNb : (b - a) / (N : ℝ) * (N : ℝ) = b - a := by field_simp
      have hknn : 0 ≤ (k : ℝ) * (b - a) / (N : ℝ) :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg k) hba.le) hNpos.le
      have hcomm : (k : ℝ) * (b - a) / (N : ℝ) = (b - a) / (N : ℝ) * (k : ℝ) := by
        ring
      constructor
      · simp only [hp]
        linarith
      · simp only [hp]
        linarith [h2, hNb, hcomm]
    have hint : ∀ k, k < N → IntervalIntegrable f volume (p k) (p (k + 1)) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable
      apply hf.mono
      rw [Set.uIcc_of_le (hple k)]
      exact Set.Icc_subset_Icc (hmem k hk.le).1 (hmem (k + 1) hk).2
    have hsplit : (∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), f x)
        = ∫ x in a..b, f x := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hint, hp0, hpN]
    have hkey : (∑ k ∈ Finset.range N, f (p k) * ((b - a) / (N : ℝ)))
        - (∫ x in a..b, f x)
        = ∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), (f (p k) - f x) := by
      rw [← hsplit, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < N := Finset.mem_range.1 hk
      have hsub : (∫ x in p k..p (k + 1), (f (p k) - f x))
          = (∫ _x in p k..p (k + 1), f (p k)) - ∫ x in p k..p (k + 1), f x :=
        intervalIntegral.integral_sub intervalIntegrable_const (hint k hk')
      rw [hsub, intervalIntegral.integral_const, hstep k, smul_eq_mul]
      ring
    have hbound : ∀ k ∈ Finset.range N,
        |∫ x in p k..p (k + 1), (f (p k) - f x)| ≤ ε' * ((b - a) / (N : ℝ)) := by
      intro k hk
      have hk' : k < N := Finset.mem_range.1 hk
      have hCbound : ∀ x ∈ Set.uIoc (p k) (p (k + 1)), ‖f (p k) - f x‖ ≤ ε' := by
        intro x hx
        rw [Set.uIoc_of_le (hple k)] at hx
        have hxmem : x ∈ Set.Icc a b :=
          ⟨le_trans (hmem k hk'.le).1 hx.1.le, le_trans hx.2 (hmem (k + 1) hk').2⟩
        have hdist : dist (p k) x ≤ δ := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.1.le] : p k - x ≤ 0)]
          have hupper : x ≤ p k + (b - a) / (N : ℝ) := by
            have := hstep k
            linarith [hx.2]
          linarith [hmesh]
        have h := hδ (p k) (hmem k hk'.le) x hxmem hdist
        rw [Real.dist_eq] at h
        rwa [Real.norm_eq_abs]
      calc |∫ x in p k..p (k + 1), (f (p k) - f x)|
          ≤ ε' * |p (k + 1) - p k| := by
            rw [← Real.norm_eq_abs]
            exact intervalIntegral.norm_integral_le_of_norm_le_const hCbound
        _ = ε' * ((b - a) / (N : ℝ)) := by
            rw [hstep k, abs_of_nonneg hmeshpos]
    have hsum_bound : |(∑ k ∈ Finset.range N, f (p k) * ((b - a) / (N : ℝ)))
        - ∫ x in a..b, f x| ≤ ε' * (b - a) := by
      rw [hkey]
      calc |∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), (f (p k) - f x)|
          ≤ ∑ k ∈ Finset.range N, |∫ x in p k..p (k + 1), (f (p k) - f x)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range N, ε' * ((b - a) / (N : ℝ)) :=
            Finset.sum_le_sum hbound
        _ = (N : ℝ) * (ε' * ((b - a) / (N : ℝ))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ε' * (b - a) := by
            field_simp
    have hfinal : ε' * (b - a) < ε := by
      have hhalf : ε' * (b - a) = ε / 2 := by
        rw [hε'def]
        field_simp
      linarith [hhalf]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt hsum_bound hfinal

/-- THEOREM (campaign-facing hinge-sum form). For `f` continuous on `[0, 1]`,
the lattice averages `(1/N) Σ_{k<N} f(k/N)` converge to `∫ x in 0..1, f x`.
This is the exact shape of discrete-gravity hinge sums (one summand per
lattice hinge, spacing `1/N`); Phases 4 and 5 consume it directly. -/
theorem latticeSum_tendsto_integral (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Filter.Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) * ∑ k ∈ Finset.range N, f ((k : ℝ) / (N : ℝ)))
      Filter.atTop (nhds (∫ x in (0:ℝ)..1, f x)) := by
  have h := riemannSum_tendsto_integral f 0 1 zero_le_one hf
  refine h.congr fun N => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have harg : (0 : ℝ) + (k : ℝ) * (1 - 0) / (N : ℝ) = (k : ℝ) / (N : ℝ) := by ring
  have hw : ((1 : ℝ) - 0) / (N : ℝ) = 1 / (N : ℝ) := by norm_num
  rw [harg, hw, mul_comm]

/-- THEOREM (weighted hinge-sum form). For `f` and a weight `w` both
continuous on `[0, 1]`, `(1/N) Σ_{k<N} f(k/N) w(k/N) → ∫ x in 0..1, f x · w x`.
A direct corollary of `latticeSum_tendsto_integral` applied to `f·w`; stated
separately because Phase 5 consumes exactly this weighted shape
(measure-weighted hinge sums). -/
theorem weightedLatticeSum_tendsto (f w : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hw : ContinuousOn w (Set.Icc 0 1)) :
    Filter.Tendsto
      (fun N : ℕ => (1 / (N : ℝ)) *
        ∑ k ∈ Finset.range N, f ((k : ℝ) / (N : ℝ)) * w ((k : ℝ) / (N : ℝ)))
      Filter.atTop (nhds (∫ x in (0:ℝ)..1, f x * w x)) :=
  latticeSum_tendsto_integral (fun x => f x * w x) (hf.mul hw)

/-- THEOREM (remainder collapse). If the per-term errors `g N k` are
uniformly bounded by `C/N²` for `k < N`, then the `N`-term absolute error
sum `Σ_{k<N} |g N k|` tends to `0`: the total error is at most `C/N`.
Load-bearing for Phase 4 remainder terms (curved perturbations of the flat
spectrum enter as `O(1/N²)` per mode). -/
theorem sq_error_sum_tendsto_zero (g : ℕ → ℕ → ℝ) (C : ℝ)
    (hg : ∀ N : ℕ, ∀ k, k < N → |g N k| ≤ C / (N : ℝ) ^ 2) :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, |g N k|)
      Filter.atTop (nhds 0) := by
  have hub : ∀ N : ℕ, (∑ k ∈ Finset.range N, |g N k|) ≤ C / (N : ℝ) := by
    intro N
    calc (∑ k ∈ Finset.range N, |g N k|)
        ≤ ∑ _k ∈ Finset.range N, C / (N : ℝ) ^ 2 :=
          Finset.sum_le_sum fun k hk => hg N k (Finset.mem_range.1 hk)
      _ = (N : ℝ) * (C / (N : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = C / (N : ℝ) := by
          rcases Nat.eq_zero_or_pos N with h0 | hpos
          · subst h0; simp
          · have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
            field_simp
  exact squeeze_zero (fun N => Finset.sum_nonneg fun k _ => abs_nonneg _) hub
    (tendsto_const_div_atTop_nhds_zero_nat C)

/-- THEOREM (signed remainder collapse). Same hypothesis as
`sq_error_sum_tendsto_zero`; the signed error sum `Σ_{k<N} g N k` also tends
to `0`. Phase 4 consumes this form when remainders carry signs. -/
theorem error_sum_tendsto_zero (g : ℕ → ℕ → ℝ) (C : ℝ)
    (hg : ∀ N : ℕ, ∀ k, k < N → |g N k| ≤ C / (N : ℝ) ^ 2) :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, g N k)
      Filter.atTop (nhds 0) := by
  have h1 := sq_error_sum_tendsto_zero g C hg
  have h2 : Filter.Tendsto (fun N : ℕ => |∑ k ∈ Finset.range N, g N k|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun N => abs_nonneg _)
      (fun N => Finset.abs_sum_le_sum_abs _ _) h1
  have hneg : Filter.Tendsto (fun N : ℕ => -|∑ k ∈ Finset.range N, g N k|)
      Filter.atTop (nhds 0) := by
    simpa using h2.neg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg h2
    (fun N => neg_abs_le _) (fun N => le_abs_self _)

end Analysis
end Gravity
end IndisputableMonolith
