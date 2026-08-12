import Mathlib
import IndisputableMonolith.Gravity.Analysis.QuadratureLimit
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracket
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureContinuumSmearing
import IndisputableMonolith.Gravity.SevenGaps.WeightedHypersurfaceBracket

/-!
# Wave C2 R4: dynamic bracket shape continuum (rate-h) + ledger name held free

Lands the sampled-lapse Wronskian rate-`h` residual named as OPEN in
`weightedStructureSum_tendsto`, packaged with the R2 lattice RHS *shape* and
the R3 dynamic structure profile as
`dynamic_bracket_shape_continuum_limit`.

## Honesty / demotion (2026-07-22 Codex critic)

The freestanding Riemann object `sampledDynamicBracketSum` is **not**
provably equal to `bracket (HamDyn N) (HamDyn M)` at sampled phase points:
`HamDyn` / `bracket_HamDyn_HamDyn` exist only at `n = 2`, and the
non-periodic mesh leaves a ZMod wraparound term undischarged. The ledger
name `dirac_algebra_continuum_limit` is therefore **held free** pending an
honest general-`n` `HamDynN` binding + periodic wrap treatment. The
rate-`h` analysis (`wronskian_rate_h_tendsto`, forward-density control)
remains real and is consumed by the renamed shape theorem.

## Scaling (derived before stating)

Lattice summand shape of `bracket_HamDyn_HamDyn`:
`W_k * G_k * (π_{k+1} Δq_k)` with
* discrete Wronskian `W_k = O(1/n)` for C¹ lapses,
* structure `G_k = 1 + q(k/n)² = O(1)`,
* raw momentum-flux `π_{k+1} Δq_k = O(1/n)` for C¹ fields.
Product per site `O(1/n²)`; `n` sites give raw sum `O(1/n)`. The honest
scaled object is therefore **`n · Σ`**, converging to
`∫ (N M' - M N') · G · (p · q')`. (An `n²` prefactor would diverge; a bare
unscaled sum vanishes.)

## Further honesty

* Does **not** flip `gap5_constraint_recovery` (needs R6 as well).
* Decoy: frozen-1 continuum integrand differs from the dynamic `G = 1+q²`
  integrand for `q = id`.
* R3 smearing-shape reach alone does not contain this Wronskian rate content;
  the new content is `wronskian_rate_h_tendsto`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DiracAlgebraContinuum

open HypersurfaceDeformation WeightedHypersurfaceBracket
open DynamicStructureFunctionBlocker
open DynamicStructureBracket DynamicStructureContinuumSmearing
open Filter Topology Set

noncomputable section

open Finset

/-! ## Continuum profiles -/

/-- Continuum momentum-flux density `D(t) = p(t) · q'(t)`. -/
def continuumMomentumFlux (p q : ℝ → ℝ) : ℝ → ℝ :=
  fun t => p t * deriv q t

/-- Continuum Dirac structure density:
`(N M' - M N') · G · D` with `G = 1 + q²`. -/
def continuumDiracDensity (N M q p : ℝ → ℝ) : ℝ → ℝ :=
  fun t =>
    (N t * deriv M t - M t * deriv N t) *
      (dynamicStructureProfile q t * continuumMomentumFlux p q t)

/-- Sampled RHS shape of `bracket_HamDyn_HamDyn` on the unit-interval mesh
`k/n` (non-periodic forward differences). -/
def sampledDynamicBracketSum (n : ℕ) (N M q p : ℝ → ℝ) : ℝ :=
  ∑ k ∈ range n,
    (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
        M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) *
      (dynamicStructureProfile q ((k : ℝ) / n) *
        (p ((k + 1 : ℕ) / n) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n))))

/-- Continuum Wronskian density `(N M' - M N')`. -/
def continuumWronskian (N M : ℝ → ℝ) : ℝ → ℝ :=
  fun t => N t * deriv M t - M t * deriv N t

/-! ## Local mesh facts -/

private lemma mesh_lt (n k : ℕ) (hn : 0 < n) (_hk : k < n) :
    (k : ℝ) / n < ((k + 1 : ℕ) : ℝ) / n :=
  div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self k)
    (Nat.cast_pos.mpr hn)

private lemma mesh_step (n k : ℕ) :
    ((k + 1 : ℕ) : ℝ) / n - (k : ℝ) / n = 1 / (n : ℝ) := by
  rw [Nat.cast_succ, add_div, add_sub_cancel_left]

private lemma mesh_le_one (n k : ℕ) (hk : k < n) :
    ((k + 1 : ℕ) : ℝ) / n ≤ 1 := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hk)
  exact (div_le_one hn0).2 (by exact_mod_cast Nat.succ_le_of_lt hk)

private lemma mesh_nonneg (n k : ℕ) : (0 : ℝ) ≤ (k : ℝ) / n :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma sample_mem_Icc (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
  refine ⟨mesh_nonneg n k, ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp
  · exact (div_le_one (Nat.cast_pos.mpr hn)).2 (by exact_mod_cast hk)

private lemma sample_mem_Icc_lt (n k : ℕ) (hk : k < n) :
    (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
  sample_mem_Icc n k hk.le

private lemma Ioo_mesh_subset_Icc (n k : ℕ) (_hn : 0 < n) (hk : k < n) :
    Ioo ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨le_trans (mesh_nonneg n k) hx.1.le,
    le_trans hx.2.le (mesh_le_one n k hk)⟩

private lemma exists_norm_bound_on_Icc (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ C := by
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨max C0 0, le_max_right _ _, fun x hx => ?_⟩
  have : ‖f x‖ ≤ C0 := hC0 x hx
  simpa [Real.norm_eq_abs] using le_trans this (le_max_left C0 0)

/-! ## (A) Rate-h Wronskian quadrature -/

/-- Discrete Wronskian via two mean-value applications. -/
theorem discrete_wronskian_mvt (N M : ℝ → ℝ)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M)
    (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    ∃ c ∈ Ioo ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n),
      ∃ d ∈ Ioo ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n),
        N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
            M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)
          = (1 / (n : ℝ)) *
              (N ((k : ℝ) / n) * deriv M c - M ((k : ℝ) / n) * deriv N d) := by
  set a : ℝ := (k : ℝ) / n
  set b : ℝ := ((k + 1 : ℕ) : ℝ) / n
  have hab : a < b := mesh_lt n k hn hk
  have hIcc_ab : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨le_trans (mesh_nonneg n k) hx.1, le_trans hx.2 (mesh_le_one n k hk)⟩
  have hNdiff : Differentiable ℝ N := hN.differentiable (by norm_num)
  have hMdiff : Differentiable ℝ M := hM.differentiable (by norm_num)
  have hNc : ContinuousOn N (Icc a b) := hN.continuous.continuousOn.mono hIcc_ab
  have hMc : ContinuousOn M (Icc a b) := hM.continuous.continuousOn.mono hIcc_ab
  have hNd : DifferentiableOn ℝ N (Ioo a b) := fun x _ => (hNdiff x).differentiableWithinAt
  have hMd : DifferentiableOn ℝ M (Ioo a b) := fun x _ => (hMdiff x).differentiableWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_deriv_eq_slope M hab hMc hMd
  obtain ⟨d, hd, hdEq⟩ := exists_deriv_eq_slope N hab hNc hNd
  refine ⟨c, hc, d, hd, ?_⟩
  have hden : b - a = 1 / (n : ℝ) := by
    dsimp [a, b]; exact mesh_step n k
  have hMdiff' : M b - M a = (1 / (n : ℝ)) * deriv M c := by
    have : deriv M c = (M b - M a) / (b - a) := hcEq
    rw [this, hden]; field_simp
  have hNdiff' : N b - N a = (1 / (n : ℝ)) * deriv N d := by
    have : deriv N d = (N b - N a) / (b - a) := hdEq
    rw [this, hden]; field_simp
  calc
    N a * M b - M a * N b
        = N a * (M b - M a) - M a * (N b - N a) := by ring
    _ = N a * ((1 / (n : ℝ)) * deriv M c) - M a * ((1 / (n : ℝ)) * deriv N d) := by
        rw [hMdiff', hNdiff']
    _ = (1 / (n : ℝ)) * (N a * deriv M c - M a * deriv N d) := by ring

private lemma continuous_continuumWronskian (N M : ℝ → ℝ)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M) :
    Continuous (continuumWronskian N M) :=
  (hN.continuous.mul hM.continuous_deriv_one).sub
    (hM.continuous.mul hN.continuous_deriv_one)

private lemma wronskian_cell_error_abs (N M : ℝ → ℝ)
    (n k : ℕ) (hn : 0 < n)
    {c d : ℝ}
    (hEq : N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
        M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)
      = (1 / (n : ℝ)) *
          (N ((k : ℝ) / n) * deriv M c - M ((k : ℝ) / n) * deriv N d)) :
    |(N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
          M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
        (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)|
      = (1 / (n : ℝ)) *
          |N ((k : ℝ) / n) * (deriv M c - deriv M ((k : ℝ) / n)) -
            M ((k : ℝ) / n) * (deriv N d - deriv N ((k : ℝ) / n))| := by
  have hcell :
      (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
          M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
        (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)
      = (1 / (n : ℝ)) *
          (N ((k : ℝ) / n) * (deriv M c - deriv M ((k : ℝ) / n)) -
            M ((k : ℝ) / n) * (deriv N d - deriv N ((k : ℝ) / n))) := by
    rw [hEq]; simp only [continuumWronskian]; ring
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [hcell, abs_mul, abs_of_pos (div_pos one_pos hnR)]

/-- THEOREM (A). Sampled-lapse Wronskian rate-`h` quadrature limit. -/
theorem wronskian_rate_h_tendsto (N M F : ℝ → ℝ)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M)
    (hF : ContinuousOn F (Icc 0 1)) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) *
            F ((k : ℝ) / n))
      atTop
      (nhds (∫ t in (0 : ℝ)..1, continuumWronskian N M t * F t)) := by
  have hWrCont : ContinuousOn (continuumWronskian N M) (Icc 0 1) :=
    (continuous_continuumWronskian N M hN hM).continuousOn
  have hRiemann :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            ∑ k ∈ range n, continuumWronskian N M ((k : ℝ) / n) * F ((k : ℝ) / n))
        atTop (nhds (∫ t in (0 : ℝ)..1, continuumWronskian N M t * F t)) :=
    Analysis.weightedLatticeSum_tendsto (continuumWronskian N M) F hWrCont hF
  have hErr :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ range n,
            ((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
              F ((k : ℝ) / n))
        atTop (nhds 0) := by
    obtain ⟨BN, hBN0, hBN⟩ :=
      exists_norm_bound_on_Icc N hN.continuous.continuousOn
    obtain ⟨BM, hBM0, hBM⟩ :=
      exists_norm_bound_on_Icc M hM.continuous.continuousOn
    obtain ⟨BF, hBF0, hBF⟩ := exists_norm_bound_on_Icc F hF
    have hNdb : ContinuousOn (deriv N) (Icc 0 1) :=
      hN.continuous_deriv_one.continuousOn
    have hMdb : ContinuousOn (deriv M) (Icc 0 1) :=
      hM.continuous_deriv_one.continuousOn
    rw [Metric.tendsto_atTop]
    intro ε hε
    set K : ℝ := BN * BF + BM * BF + 1
    have hKpos : 0 < K := by
      have : 0 ≤ BN * BF := mul_nonneg hBN0 hBF0
      have : 0 ≤ BM * BF := mul_nonneg hBM0 hBF0
      positivity
    set ε' : ℝ := ε / (2 * K)
    have hε' : 0 < ε' := div_pos hε (by positivity)
    obtain ⟨δN, hδNpos, hδN⟩ :=
      Metric.uniformContinuousOn_iff_le.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hNdb) ε' hε'
    obtain ⟨δM, hδMpos, hδM⟩ :=
      Metric.uniformContinuousOn_iff_le.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hMdb) ε' hε'
    set δ : ℝ := min δN δM
    have hδpos : 0 < δ := lt_min hδNpos hδMpos
    obtain ⟨M₀, hM₀⟩ := exists_nat_ge (1 / δ)
    refine ⟨max M₀ 1, fun n hnAll => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_right M₀ 1) hnAll
    have hnM : M₀ ≤ n := le_trans (le_max_left M₀ 1) hnAll
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
    have hmesh : (1 : ℝ) / n ≤ δ := by
      have h1 : (1 : ℝ) / δ ≤ n := le_trans hM₀ (by exact_mod_cast hnM)
      have : δ * ((1 : ℝ) / δ) ≤ δ * n :=
        mul_le_mul_of_nonneg_left h1 hδpos.le
      have : (1 : ℝ) ≤ δ * n := by convert this using 1; field_simp
      exact (div_le_iff₀ hnR).2 (by linarith)
    have hmeshN : (1 : ℝ) / n ≤ δN := le_trans hmesh (min_le_left _ _)
    have hmeshM : (1 : ℝ) / n ≤ δM := le_trans hmesh (min_le_right _ _)
    have hterm : ∀ k ∈ range n,
        |((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
            (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
          F ((k : ℝ) / n)|
          ≤ (1 / (n : ℝ)) * ε' * (BN * BF + BM * BF) := by
      intro k hk
      have hk' : k < n := mem_range.1 hk
      obtain ⟨c, hc, d, hd, hEq⟩ := discrete_wronskian_mvt N M hN hM n k hnpos hk'
      have ha : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := sample_mem_Icc_lt n k hk'
      have hb : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
        sample_mem_Icc n (k + 1) (Nat.succ_le_of_lt hk')
      have hcI : c ∈ Icc (0 : ℝ) 1 := Ioo_mesh_subset_Icc n k hnpos hk' hc
      have hdI : d ∈ Icc (0 : ℝ) 1 := Ioo_mesh_subset_Icc n k hnpos hk' hd
      have hdistc : dist c ((k : ℝ) / n) ≤ δM := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
        have : c - (k : ℝ) / n ≤ 1 / (n : ℝ) := by
          have := hc.2.le; have := mesh_step n k; linarith
        exact le_trans this hmeshM
      have hdistd : dist d ((k : ℝ) / n) ≤ δN := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hd.1.le)]
        have : d - (k : ℝ) / n ≤ 1 / (n : ℝ) := by
          have := hd.2.le; have := mesh_step n k; linarith
        exact le_trans this hmeshN
      have hdM : |deriv M c - deriv M ((k : ℝ) / n)| ≤ ε' := by
        simpa [Real.dist_eq] using hδM c hcI ((k : ℝ) / n) ha hdistc
      have hdN : |deriv N d - deriv N ((k : ℝ) / n)| ≤ ε' := by
        simpa [Real.dist_eq] using hδN d hdI ((k : ℝ) / n) ha hdistd
      have hAbs := wronskian_cell_error_abs N M n k hnpos hEq
      have herr :
          |N ((k : ℝ) / n) * (deriv M c - deriv M ((k : ℝ) / n)) -
              M ((k : ℝ) / n) * (deriv N d - deriv N ((k : ℝ) / n))|
            ≤ BN * ε' + BM * ε' := by
        calc
          _ ≤ |N ((k : ℝ) / n)| * |deriv M c - deriv M ((k : ℝ) / n)| +
                |M ((k : ℝ) / n)| * |deriv N d - deriv N ((k : ℝ) / n)| := by
              calc
                _ ≤ |N ((k : ℝ) / n) * (deriv M c - deriv M ((k : ℝ) / n))| +
                      |M ((k : ℝ) / n) * (deriv N d - deriv N ((k : ℝ) / n))| :=
                    abs_sub _ _
                _ = |N ((k : ℝ) / n)| * |deriv M c - deriv M ((k : ℝ) / n)| +
                      |M ((k : ℝ) / n)| * |deriv N d - deriv N ((k : ℝ) / n)| := by
                    simp [abs_mul]
          _ ≤ BN * ε' + BM * ε' := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul (hBN _ ha) hdM (abs_nonneg _) hBN0
              · exact mul_le_mul (hBM _ ha) hdN (abs_nonneg _) hBM0
      calc
        |((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
            (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
          F ((k : ℝ) / n)|
            = |(N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)| *
              |F ((k : ℝ) / n)| := abs_mul _ _
        _ = (1 / (n : ℝ)) *
              |N ((k : ℝ) / n) * (deriv M c - deriv M ((k : ℝ) / n)) -
                M ((k : ℝ) / n) * (deriv N d - deriv N ((k : ℝ) / n))| *
            |F ((k : ℝ) / n)| := by rw [hAbs]
        _ ≤ (1 / (n : ℝ)) * (BN * ε' + BM * ε') * BF := by
            refine mul_le_mul ?_ (hBF _ ha) (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left herr (div_nonneg zero_le_one hnR.le)
        _ = (1 / (n : ℝ)) * ε' * (BN * BF + BM * BF) := by ring
    have hsum :
        |∑ k ∈ range n,
            ((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
              F ((k : ℝ) / n)|
          ≤ ε' * (BN * BF + BM * BF) := by
      calc
        _ ≤ ∑ k ∈ range n,
              |((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                    M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                  (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
                F ((k : ℝ) / n)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ range n, (1 / (n : ℝ)) * ε' * (BN * BF + BM * BF) :=
            sum_le_sum hterm
        _ = (n : ℝ) * ((1 / (n : ℝ)) * ε' * (BN * BF + BM * BF)) := by
            rw [sum_const, card_range, nsmul_eq_mul]
        _ = ε' * (BN * BF + BM * BF) := by field_simp
    have hfinal : ε' * (BN * BF + BM * BF) < ε := by
      have hle : BN * BF + BM * BF ≤ K := by simp only [K]; linarith
      have : ε' * (BN * BF + BM * BF) ≤ ε' * K :=
        mul_le_mul_of_nonneg_left hle hε'.le
      have hhalf : ε' * K = ε / 2 := by simp only [ε']; field_simp
      linarith
    rw [Real.dist_eq]
    have hdist : |∑ k ∈ range n,
            ((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
              F ((k : ℝ) / n) - 0| =
        |∑ k ∈ range n,
            ((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
              F ((k : ℝ) / n)| := by simp
    rw [hdist]
    exact lt_of_le_of_lt hsum hfinal
  have haddRM := hRiemann.add hErr
  have hlimRM :
      (∫ t in (0 : ℝ)..1, continuumWronskian N M t * F t) + 0
        = ∫ t in (0 : ℝ)..1, continuumWronskian N M t * F t :=
    add_zero _
  have hMain' :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
              ∑ k ∈ range n,
                continuumWronskian N M ((k : ℝ) / n) * F ((k : ℝ) / n) +
            ∑ k ∈ range n,
              ((N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                    M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) -
                  (1 / (n : ℝ)) * continuumWronskian N M ((k : ℝ) / n)) *
                F ((k : ℝ) / n))
        atTop (nhds (∫ t in (0 : ℝ)..1, continuumWronskian N M t * F t)) := by
    -- `convert` reduces the `nhds` mismatch to the bare limit equality.
    convert haddRM
    exact hlimRM.symm
  refine hMain'.congr fun n => ?_
  rw [Finset.mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  ring

/-! ## Forward-difference rate for C¹ profiles -/

theorem forward_diff_mvt (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q)
    (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    ∃ c ∈ Ioo ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n),
      (n : ℝ) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n)) = deriv q c := by
  set a : ℝ := (k : ℝ) / n
  set b : ℝ := ((k + 1 : ℕ) : ℝ) / n
  have hab : a < b := mesh_lt n k hn hk
  have hIcc_ab : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨le_trans (mesh_nonneg n k) hx.1, le_trans hx.2 (mesh_le_one n k hk)⟩
  have hqdiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hqc : ContinuousOn q (Icc a b) := hq.continuous.continuousOn.mono hIcc_ab
  have hqd : DifferentiableOn ℝ q (Ioo a b) := fun x _ => (hqdiff x).differentiableWithinAt
  obtain ⟨c, hc, hcEq⟩ := exists_deriv_eq_slope q hab hqc hqd
  refine ⟨c, hc, ?_⟩
  have hden : b - a = 1 / (n : ℝ) := by
    dsimp [a, b]; exact mesh_step n k
  have : deriv q c = (q b - q a) / (b - a) := hcEq
  rw [this, hden]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- Uniform control: scaled forward density vs `p · q'`. -/
theorem forward_density_uniform (q p : ℝ → ℝ)
    (hq : ContDiff ℝ 1 q) (hp : ContinuousOn p (Icc 0 1)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ k < n,
      |p ((k + 1 : ℕ) / n) * ((n : ℝ) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n))) -
          p ((k : ℝ) / n) * deriv q ((k : ℝ) / n)| < ε := by
  obtain ⟨BP, hBP0, hBP⟩ := exists_norm_bound_on_Icc p hp
  obtain ⟨Bq', hBq'0, hBq'⟩ :=
    exists_norm_bound_on_Icc (deriv q) hq.continuous_deriv_one.continuousOn
  have hqd := hq.continuous_deriv_one
  intro ε hε
  set ε' : ℝ := ε / (2 * (BP + Bq' + 1))
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨δp, hδppos, hδp⟩ :=
    Metric.uniformContinuousOn_iff_le.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hp) ε' hε'
  obtain ⟨δq, hδqpos, hδq⟩ :=
    Metric.uniformContinuousOn_iff_le.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hqd.continuousOn) ε' hε'
  set δ : ℝ := min δp δq
  have hδpos : 0 < δ := lt_min hδppos hδqpos
  obtain ⟨M₀, hM₀⟩ := exists_nat_ge (1 / δ)
  refine ⟨max M₀ 1, fun n hnAll k hk => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right M₀ 1) hnAll
  have hnM : M₀ ≤ n := le_trans (le_max_left M₀ 1) hnAll
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hnpos
  have hmesh : (1 : ℝ) / n ≤ δ := by
    have h1 : (1 : ℝ) / δ ≤ n := le_trans hM₀ (by exact_mod_cast hnM)
    have : δ * ((1 : ℝ) / δ) ≤ δ * n :=
      mul_le_mul_of_nonneg_left h1 hδpos.le
    have : (1 : ℝ) ≤ δ * n := by convert this using 1; field_simp
    exact (div_le_iff₀ hnR).2 (by linarith)
  have hmeshp : (1 : ℝ) / n ≤ δp := le_trans hmesh (min_le_left _ _)
  have hmeshq : (1 : ℝ) / n ≤ δq := le_trans hmesh (min_le_right _ _)
  obtain ⟨c, hc, hcEq⟩ := forward_diff_mvt q hq n k hnpos hk
  have ha : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := sample_mem_Icc_lt n k hk
  have hb : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
    sample_mem_Icc n (k + 1) (Nat.succ_le_of_lt hk)
  have hcI : c ∈ Icc (0 : ℝ) 1 := Ioo_mesh_subset_Icc n k hnpos hk hc
  have hdistc : dist c ((k : ℝ) / n) ≤ δq := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hc.1.le)]
    have : c - (k : ℝ) / n ≤ 1 / (n : ℝ) := by
      have := hc.2.le; have := mesh_step n k; linarith
    exact le_trans this hmeshq
  have hdistp : dist (((k + 1 : ℕ) : ℝ) / n) ((k : ℝ) / n) ≤ δp := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (mesh_lt n k hnpos hk).le)]
    rw [mesh_step]; exact hmeshp
  have hqerr : |deriv q c - deriv q ((k : ℝ) / n)| ≤ ε' := by
    simpa [Real.dist_eq] using hδq c hcI ((k : ℝ) / n) ha hdistc
  have hperr : |p ((k + 1 : ℕ) / n) - p ((k : ℝ) / n)| ≤ ε' := by
    simpa [Real.dist_eq] using hδp _ hb _ ha hdistp
  have hrew :
      p ((k + 1 : ℕ) / n) * ((n : ℝ) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n))) -
          p ((k : ℝ) / n) * deriv q ((k : ℝ) / n)
        = (p ((k + 1 : ℕ) / n) - p ((k : ℝ) / n)) * deriv q c +
            p ((k : ℝ) / n) * (deriv q c - deriv q ((k : ℝ) / n)) := by
    rw [hcEq]; ring
  rw [hrew]
  have h1 : |(p ((k + 1 : ℕ) / n) - p ((k : ℝ) / n)) * deriv q c| ≤ ε' * Bq' := by
    rw [abs_mul]
    exact mul_le_mul hperr (hBq' c hcI) (abs_nonneg _) hε'.le
  have h2 : |p ((k : ℝ) / n) * (deriv q c - deriv q ((k : ℝ) / n))| ≤ BP * ε' := by
    rw [abs_mul]
    exact mul_le_mul (hBP _ ha) hqerr (abs_nonneg _) hBP0
  have hsum :=
    le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hbound : ε' * Bq' + BP * ε' < ε := by
    have : ε' * (BP + Bq') ≤ ε' * (BP + Bq' + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hε'.le
    have hhalf : ε' * (BP + Bq' + 1) = ε / 2 := by simp only [ε']; field_simp
    linarith
  exact lt_of_le_of_lt hsum hbound

/-! ## Binding lemmas (R2 / R3) -/

theorem dynamicStructureProfile_eq_one_add_sq (q : ℝ → ℝ) (t : ℝ) :
    dynamicStructureProfile q t = 1 + (q t) ^ 2 :=
  rfl

theorem bracket_HamDyn_shape (N M : ZMod 2 → ℝ) (x : PhaseSpace 2) :
    bracket (HamDyn N) (HamDyn M) x
      = ∑ j : ZMod 2, (N j * M (j + 1) - M j * N (j + 1)) *
          (DynamicStructureFunctionBlocker.concreteDynamicInverseMetric x j *
            (x.2 (j + 1) * (x.1 (j + 1) - x.1 j))) :=
  bracket_HamDyn_HamDyn N M x

theorem sampledDynamicBracketSum_scaled_eq (n : ℕ) (N M q p : ℝ → ℝ) :
    (n : ℝ) * sampledDynamicBracketSum n N M q p
      = ∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) *
            (dynamicStructureProfile q ((k : ℝ) / n) *
              (p ((k + 1 : ℕ) / n) *
                ((n : ℝ) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n))))) := by
  unfold sampledDynamicBracketSum
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

/-! ## Wronskian × uniform error → 0 -/

private theorem wronskian_times_uniform_error_tendsto_zero
    (N M : ℝ → ℝ) (err : ℕ → ℕ → ℝ)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M)
    (herr : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ k < n, |err n k| < ε) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k)
      atTop (nhds 0) := by
  obtain ⟨BN, hBN0, hBN⟩ :=
    exists_norm_bound_on_Icc N hN.continuous.continuousOn
  obtain ⟨BM, hBM0, hBM⟩ :=
    exists_norm_bound_on_Icc M hM.continuous.continuousOn
  obtain ⟨BNd, hBNd0, hBNd⟩ :=
    exists_norm_bound_on_Icc (deriv N) hN.continuous_deriv_one.continuousOn
  obtain ⟨BMd, hBMd0, hBMd⟩ :=
    exists_norm_bound_on_Icc (deriv M) hM.continuous_deriv_one.continuousOn
  have hWbound : ∀ (n k : ℕ), 0 < n → k < n →
      |N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
          M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)|
        ≤ (1 / (n : ℝ)) * (BN * BMd + BM * BNd) := by
    intro n k hn hk
    obtain ⟨c, hc, d, hd, hEq⟩ := discrete_wronskian_mvt N M hN hM n k hn hk
    have ha := sample_mem_Icc_lt n k hk
    have hcI := Ioo_mesh_subset_Icc n k hn hk hc
    have hdI := Ioo_mesh_subset_Icc n k hn hk hd
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [hEq, abs_mul, abs_of_pos (div_pos one_pos hnR)]
    have :
        |N ((k : ℝ) / n) * deriv M c - M ((k : ℝ) / n) * deriv N d|
          ≤ BN * BMd + BM * BNd := by
      calc
        _ ≤ |N ((k : ℝ) / n)| * |deriv M c| + |M ((k : ℝ) / n)| * |deriv N d| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ BN * BMd + BM * BNd := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul (hBN _ ha) (hBMd c hcI) (abs_nonneg _) hBN0
            · exact mul_le_mul (hBM _ ha) (hBNd d hdI) (abs_nonneg _) hBM0
    exact mul_le_mul_of_nonneg_left this (div_nonneg zero_le_one hnR.le)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := BN * BMd + BM * BNd + 1
  have hCpos : 0 < C := by
    have : 0 ≤ BN * BMd := mul_nonneg hBN0 hBMd0
    have : 0 ≤ BM * BNd := mul_nonneg hBM0 hBNd0
    positivity
  obtain ⟨N₀, hN₀⟩ := herr (ε / (2 * C)) (by positivity)
  refine ⟨max N₀ 1, fun n hnAll => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N₀ 1) hnAll
  have hnN : N₀ ≤ n := le_trans (le_max_left N₀ 1) hnAll
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have herr' : ∀ k < n, |err n k| < ε / (2 * C) := hN₀ n hnN
  set η : ℝ := ε / (2 * C)
  have hηpos : 0 < η := by positivity
  have hterm : ∀ k ∈ range n,
      |(N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
            M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k|
        ≤ (1 / (n : ℝ)) * (BN * BMd + BM * BNd) * η := by
    intro k hk
    have hk' : k < n := mem_range.1 hk
    have h1 := hWbound n k hnpos hk'
    have h2 : |err n k| ≤ η := (herr' k hk').le
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hsum :
      |∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k|
        ≤ (BN * BMd + BM * BNd) * η := by
    calc
      _ ≤ ∑ k ∈ range n,
            |(N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range n, (1 / (n : ℝ)) * (BN * BMd + BM * BNd) * η :=
          sum_le_sum hterm
      _ = (BN * BMd + BM * BNd) * η := by
          rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  have hfinal : (BN * BMd + BM * BNd) * η < ε := by
    have hle : BN * BMd + BM * BNd ≤ C := by simp only [C]; linarith
    have : (BN * BMd + BM * BNd) * η ≤ C * η :=
      mul_le_mul_of_nonneg_right hle hηpos.le
    have : C * η = ε / 2 := by simp only [η]; field_simp
    linarith
  rw [Real.dist_eq]
  have hdist :
      |∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k - 0| =
        |∑ k ∈ range n,
          (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
              M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k| := by
    simp
  rw [hdist]
  exact lt_of_le_of_lt hsum hfinal

/-! ## (B) Shape continuum (not the ledger terminal) -/

/-- THEOREM (B, shape only). Sampled-and-scaled freestanding dynamic-bracket
*shape* sums converge to the continuum Dirac hypersurface-deformation density
with phase-space-dependent structure function `G = 1 + q²`.

This is a true Riemann / rate-`h` theorem about `sampledDynamicBracketSum`.
It is **not** a binding of `bracket (HamDyn ·) (HamDyn ·)` (that object is
only at `n = 2`), and it does **not** occupy the ledger name
`dirac_algebra_continuum_limit`.

Scaling: `n · Σ W_k G_k (π_{k+1} Δq_k) → ∫ (N M' - M N') G (p q')`. -/
theorem dynamic_bracket_shape_continuum_limit (N M q p : ℝ → ℝ)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M) (hq : ContDiff ℝ 1 q)
    (hp : ContinuousOn p (Icc 0 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * sampledDynamicBracketSum n N M q p)
      atTop
      (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t)) := by
  have hG : ContinuousOn (dynamicStructureProfile q) (Icc 0 1) :=
    continuousOn_dynamicStructureProfile q hq.continuous.continuousOn
  have hF : ContinuousOn
      (fun t => dynamicStructureProfile q t * continuumMomentumFlux p q t)
      (Icc 0 1) :=
    hG.mul (hp.mul hq.continuous_deriv_one.continuousOn)
  have hMain :=
    wronskian_rate_h_tendsto N M
      (fun t => dynamicStructureProfile q t * continuumMomentumFlux p q t)
      hN hM hF
  -- Target integral equality (definitional after unfolding the density abbrevs).
  have hint :
      (∫ t in (0 : ℝ)..1,
          continuumWronskian N M t *
            (dynamicStructureProfile q t * continuumMomentumFlux p q t))
        = ∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t :=
    intervalIntegral.integral_congr fun t _ => by
      simp only [continuumDiracDensity, continuumWronskian]
  let densErr (n k : ℕ) : ℝ :=
    p ((k + 1 : ℕ) / n) * ((n : ℝ) * (q ((k + 1 : ℕ) / n) - q ((k : ℝ) / n))) -
      continuumMomentumFlux p q ((k : ℝ) / n)
  let err (n k : ℕ) : ℝ :=
    dynamicStructureProfile q ((k : ℝ) / n) * densErr n k
  obtain ⟨BG, hBG0, hBG⟩ := exists_norm_bound_on_Icc _ hG
  have herr : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ k < n, |err n k| < ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ :=
      forward_density_uniform q p hq hp (ε / (BG + 1)) (by positivity)
    refine ⟨N₀, fun n hn k hk => ?_⟩
    have ha : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := sample_mem_Icc_lt n k hk
    have hde : |densErr n k| < ε / (BG + 1) := by
      simpa [densErr, continuumMomentumFlux] using hN₀ n hn k hk
    have hbound : |err n k| ≤ (BG + 1) * |densErr n k| := by
      dsimp [err]
      rw [abs_mul]
      have : |dynamicStructureProfile q ((k : ℝ) / n)| ≤ BG + 1 :=
        le_trans (hBG _ ha) (by linarith)
      exact mul_le_mul this le_rfl (abs_nonneg _) (by linarith)
    have hlt : (BG + 1) * |densErr n k| < (BG + 1) * (ε / (BG + 1)) :=
      mul_lt_mul_of_pos_left hde (by positivity)
    have hεeq : (BG + 1) * (ε / (BG + 1)) = ε := by field_simp
    linarith
  have hErrTend :=
    wronskian_times_uniform_error_tendsto_zero N M err hN hM herr
  have hEq : ∀ n : ℕ,
      (n : ℝ) * sampledDynamicBracketSum n N M q p
        = (∑ k ∈ range n,
              (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) *
                (dynamicStructureProfile q ((k : ℝ) / n) *
                  continuumMomentumFlux p q ((k : ℝ) / n))) +
          ∑ k ∈ range n,
            (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k := by
    intro n
    rw [sampledDynamicBracketSum_scaled_eq, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    dsimp [err, densErr, continuumMomentumFlux]
    ring
  have hadd := hMain.add hErrTend
  have hlimEq :
      (∫ t in (0 : ℝ)..1,
          continuumWronskian N M t *
            (dynamicStructureProfile q t * continuumMomentumFlux p q t)) + 0
        = ∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t := by
    rw [add_zero, hint]
  have hadd' :
      Tendsto
        (fun n : ℕ =>
          (∑ k ∈ range n,
              (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) *
                (dynamicStructureProfile q ((k : ℝ) / n) *
                  continuumMomentumFlux p q ((k : ℝ) / n))) +
            ∑ k ∈ range n,
              (N ((k : ℝ) / n) * M ((k + 1 : ℕ) / n) -
                  M ((k : ℝ) / n) * N ((k + 1 : ℕ) / n)) * err n k)
        atTop
        (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t)) := by
    -- `convert` reduces the `nhds` mismatch to the bare limit equality.
    convert hadd
    exact hlimEq.symm
  exact hadd'.congr fun n => (hEq n).symm

/-! ## (C) Decoys -/

/-- DECOY: dynamic `G = 1 + id²` is not the frozen-1 profile. -/
theorem frozen_structure_differs_from_dynamic_id :
    dynamicStructureProfile id (1 : ℝ) ≠ (1 : ℝ) := by
  simp [dynamicStructureProfile]

/-- Explicit continuum-density mismatch at `t = 1` for
`N ≡ 1`, `M = id`, `p ≡ 1`, `q = id`: dynamic value `2`, frozen value `1`. -/
theorem frozen_continuum_density_differs_from_dynamic :
    continuumDiracDensity (fun _ => (1 : ℝ)) id id (fun _ => (1 : ℝ)) (1 : ℝ)
      ≠
    ((1 : ℝ) * deriv id (1 : ℝ) - id (1 : ℝ) * deriv (fun _ : ℝ => (1 : ℝ)) (1 : ℝ)) *
      ((1 : ℝ) * continuumMomentumFlux (fun _ => (1 : ℝ)) id (1 : ℝ)) := by
  simp [continuumDiracDensity, continuumMomentumFlux, dynamicStructureProfile,
    deriv_id, deriv_const]

/-! ### Axiom receipts -/

#print axioms discrete_wronskian_mvt
#print axioms wronskian_rate_h_tendsto
#print axioms forward_diff_mvt
#print axioms forward_density_uniform
#print axioms dynamic_bracket_shape_continuum_limit
#print axioms frozen_structure_differs_from_dynamic_id
#print axioms frozen_continuum_density_differs_from_dynamic

end
end DiracAlgebraContinuum
end SevenGaps
end Gravity
end IndisputableMonolith
