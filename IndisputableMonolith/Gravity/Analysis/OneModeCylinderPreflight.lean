import Mathlib
import IndisputableMonolith.Gravity.Analysis.SpectralConvergence

/-!
# One-mode cylinder-measure preflight (candidate C10 preflight; NOT the path-sum measure)

QG full-theory campaign, Phase 2b SLACK lane M.

## HONESTY / SCOPE HEADER (read before citing)

This module is a ONE-MODE TOY PREFLIGHT for the panel's live bet C10 (a
Gaussian cylinder-measure limit over the frozen quadratic energy). It

* is NOT the path-sum measure and does NOT construct any field-theoretic
  measure: everything here concerns a single Fourier mode `k` on a
  one-dimensional periodic lattice;
* carries NO flag weight: no campaign flag is flipped, claimed, or
  supported by this file;
* is separate from the Test G lane by design (separate file, separate
  claims, no shared definitions).

Everything proved below is a genuine Mathlib-measure statement about the
real Gaussian measure `ProbabilityTheory.gaussianReal`; there are no
formal-symbol stand-ins, no `sorry`, no new axioms, no `True` shells.

## Fixed normalization (declared a priori; nothing below is fitted)

The lattice is the `N`-site discretization of the unit circle (spacing
`1/N`). For Fourier mode `k ≥ 1` the discrete Hessian eigenvalue of the
frozen quadratic energy, in lattice units, is

  `λ_N(k) := 4 N² sin²(πk/N)`  (`latticeEigenvalue`),

exactly the expression whose quantitative continuum limit
`|λ_N(k) − (2πk)²| ≤ ((2πk)⁴/12)/N²` is proved in
`SpectralConvergence.discrete_sine_eigenvalue_expansion` (and whose
qualitative version lives in `DiscreteLichnerowicz`). The continuum
eigenvalue is `(2πk)²` (`continuumEigenvalue`), the `−d²/dx²` eigenvalue
of `e^{2πikx}` on the unit-length circle. The Boltzmann weight of the
frozen quadratic energy `½ λ x²` is the centered Gaussian of variance

  `v_N(k) := λ_N(k)⁻¹`  (`modeVarianceReal`, packaged as `ℝ≥0` in
  `modeVariance`),

and the actual one-mode measure is `modeMeasure k N := gaussianReal 0
(modeVariance k N)`, a real Mathlib measure on `ℝ`. At degenerate
resolutions (`N ∣ k`, where `λ_N(k) = 0`) Lean's `0⁻¹ = 0` convention
makes `modeMeasure` the Dirac mass at `0`; every quantitative statement
below is therefore scoped to `N ≥ 4k`, where `λ_N(k) ≥ (2πk)²/2 > 0`
(`latticeEigenvalue_lower_bound`) and the measure is a genuinely
non-degenerate Gaussian (`modeVariance_ne_zero`).

## What is proved (all THEOREM, axiom-clean)

1. Moment/characteristic identities for the actual measure, for every
   `k N t`:
   `integral_exp_modeMeasure`: `∫ exp(t·x) dμ_N = exp(v_N t²/2)`
   (moment-generating identity, real integral against `gaussianReal`);
   `charFun_modeMeasure`: `charFun μ_N t = exp(−v_N t²/2)`;
   `secondMoment_modeMeasure`: `∫ x² dμ_N = v_N`.
2. Rate: for `k ≥ 1`, `N ≥ 4k`,
   `modeVarianceReal_rate`: `|v_N − (2πk)⁻²| ≤ (1/6)/N²`. The constant
   is UNIFORM in `k`: the naive `C(k) = 2·((2πk)⁴/12)/(2πk)⁴` from the
   Phase-2a expansion collapses to `1/6` because the eventual eigenvalue
   lower bound `λ_N ≥ (2πk)²/2` cancels the `(2πk)⁴` growth.
3. Measure convergence, two honest formulations (the vendored Mathlib
   has no Lévy continuity theorem, so weak convergence is NOT claimed):
   `secondMoment_tendsto`: `∫ x² dμ_N → (2πk)⁻²`;
   `charFun_modeMeasure_tendsto`: `charFun μ_N t → exp(−(2πk)⁻² t²/2)`
   pointwise in `t` (the characteristic function of the limiting
   Gaussian; the classical Lévy argument would upgrade this to weak
   convergence, but that upgrade is not available in Mathlib and is
   not claimed here).
4. Non-vacuity: `limitVariance_pos`: `(2πk)⁻² > 0` for `k ≥ 1`;
   `instIsProbabilityMeasureModeMeasure`: `μ_N` is a probability
   measure for ALL `k N` (including degenerate ones); and
   `modeVariance_ne_zero`: in scope `N ≥ 4k` the Gaussian is
   non-degenerate, so nothing below is a statement about a Dirac mass.

## Mathlib API surface used

`ProbabilityTheory.gaussianReal` (+ its `IsProbabilityMeasure`
instance), `mgf_id_gaussianReal`, `charFun_gaussianReal`,
`integral_id_gaussianReal`, `variance_fun_id_gaussianReal`,
`variance_eq_integral`, all from
`Mathlib.Probability.Distributions.Gaussian.Real`; plus the Phase-2a
toolkit `discrete_sine_eigenvalue_expansion` /
`eigenvalue_limit_of_uniform_bound` from `SpectralConvergence`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace OneModeCylinder

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- Discrete Hessian eigenvalue of Fourier mode `k` on the `N`-site
periodic lattice, in lattice units: `λ_N(k) = 4N² sin²(πk/N)`. This is
the exact expression of `discrete_sine_eigenvalue_expansion`. -/
def latticeEigenvalue (k N : ℕ) : ℝ :=
  4 * (N : ℝ) ^ 2 * Real.sin (Real.pi * (k : ℝ) / (N : ℝ)) ^ 2

/-- Continuum eigenvalue of mode `k`: `(2πk)²`, the `−d²/dx²` eigenvalue
of `e^{2πikx}` on the unit circle. -/
def continuumEigenvalue (k : ℕ) : ℝ := (2 * Real.pi * (k : ℝ)) ^ 2

/-- One-mode Gaussian variance in lattice units: `v_N(k) = λ_N(k)⁻¹`
(junk value `0` at degenerate resolutions, by Lean's `0⁻¹ = 0`). -/
def modeVarianceReal (k N : ℕ) : ℝ := (latticeEigenvalue k N)⁻¹

/-- The variance packaged as `ℝ≥0`, as `gaussianReal` requires. -/
def modeVariance (k N : ℕ) : ℝ≥0 := Real.toNNReal (modeVarianceReal k N)

/-- The actual one-mode measure: the centered real Gaussian measure of
variance `v_N(k)`. A genuine Mathlib measure on `ℝ`, not a symbol. -/
def modeMeasure (k N : ℕ) : Measure ℝ := gaussianReal 0 (modeVariance k N)

/-- `λ_N(k) ≥ 0` always (it is `4N²` times a square). -/
theorem latticeEigenvalue_nonneg (k N : ℕ) : 0 ≤ latticeEigenvalue k N := by
  unfold latticeEigenvalue
  positivity

/-- `v_N(k) ≥ 0` always. -/
theorem modeVarianceReal_nonneg (k N : ℕ) : 0 ≤ modeVarianceReal k N :=
  inv_nonneg.mpr (latticeEigenvalue_nonneg k N)

/-- The `ℝ≥0` packaging is faithful: `(modeVariance k N : ℝ)` is exactly
`λ_N(k)⁻¹`. -/
theorem coe_modeVariance (k N : ℕ) :
    ((modeVariance k N : ℝ≥0) : ℝ) = modeVarianceReal k N :=
  Real.coe_toNNReal _ (modeVarianceReal_nonneg k N)

/-- NON-VACUITY (target 4): `μ_N` is a probability measure for every
`k N`, inherited from Mathlib's `gaussianReal` instance. -/
instance instIsProbabilityMeasureModeMeasure (k N : ℕ) :
    IsProbabilityMeasure (modeMeasure k N) := by
  unfold modeMeasure
  infer_instance

/-! ## Target 1: moment and characteristic-function identities -/

/-- TARGET 1 (moment-generating identity, exactly as briefed): for the
actual normalized Gaussian measure `μ_N`,
`∫ exp(t·x) dμ_N = exp(v_N t²/2)`. Proved from Mathlib's
`mgf_id_gaussianReal` with mean `0`. -/
theorem integral_exp_modeMeasure (k N : ℕ) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(modeMeasure k N)
      = Real.exp ((modeVariance k N : ℝ) * t ^ 2 / 2) := by
  unfold modeMeasure
  have h := congrFun
    (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := modeVariance k N)) t
  simp only [mgf, id_eq, zero_mul, zero_add] at h
  exact h

/-- TARGET 1 (characteristic function): `charFun μ_N t = exp(−v_N t²/2)`.
Proved from Mathlib's `charFun_gaussianReal` with mean `0`. -/
theorem charFun_modeMeasure (k N : ℕ) (t : ℝ) :
    charFun (modeMeasure k N) t
      = Complex.exp (-(((modeVariance k N : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
  unfold modeMeasure
  rw [charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- TARGET 1 (second moment): `∫ x² dμ_N = v_N`. Proved from Mathlib's
`variance_fun_id_gaussianReal` plus the zero-mean identity. -/
theorem secondMoment_modeMeasure (k N : ℕ) :
    ∫ x, x ^ 2 ∂(modeMeasure k N) = ((modeVariance k N : ℝ≥0) : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := modeVariance k N)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  unfold modeMeasure
  exact h

/-! ## Target 2: quantitative variance limit with an explicit rate -/

/-- Eventual eigenvalue lower bound: for `k ≥ 1` and `N ≥ 4k`,
`λ_N(k) ≥ (2πk)²/2`. Derived from the Phase-2a expansion: the error
`((2πk)⁴/12)/N²` is at most `(2πk)²/2` once `(2πk)² ≤ 6N²`, which
`π ≤ 4` and `N ≥ 4k` guarantee. This is what keeps `λ_N(k)⁻¹`
controlled in the rate bound. -/
theorem latticeEigenvalue_lower_bound (k N : ℕ) (hk : 1 ≤ k)
    (hN : 4 * k ≤ N) :
    continuumEigenvalue k / 2 ≤ latticeEigenvalue k N := by
  have hN1 : 1 ≤ N := by omega
  have hexp := discrete_sine_eigenvalue_expansion k N hN1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hNR : (4 : ℝ) * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hpi2 : Real.pi * Real.pi ≤ 16 := by
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hN2 : 16 * (k : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith [hkR, hNR]
  have h1 : (2 * Real.pi * (k : ℝ)) ^ 2 ≤ 6 * (N : ℝ) ^ 2 := by
    nlinarith [hpi2, hN2, sq_nonneg (k : ℝ),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 16 - Real.pi * Real.pi)
        (sq_nonneg (k : ℝ))]
  have h12 : (0 : ℝ) < 12 * (N : ℝ) ^ 2 := by positivity
  have hkey : (2 * Real.pi * (k : ℝ)) ^ 4 / 12 / (N : ℝ) ^ 2
      ≤ (2 * Real.pi * (k : ℝ)) ^ 2 / 2 := by
    rw [div_div, div_le_iff₀ h12]
    nlinarith [h1, sq_nonneg (2 * Real.pi * (k : ℝ))]
  have habs := abs_le.mp hexp
  unfold continuumEigenvalue latticeEigenvalue
  linarith [habs.1, hkey]

/-- In scope (`k ≥ 1`, `N ≥ 4k`) the eigenvalue is strictly positive. -/
theorem latticeEigenvalue_pos (k N : ℕ) (hk : 1 ≤ k) (hN : 4 * k ≤ N) :
    0 < latticeEigenvalue k N := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hLam : 0 < continuumEigenvalue k := by
    unfold continuumEigenvalue
    have : 0 < 2 * Real.pi * (k : ℝ) := by
      have := Real.pi_pos
      nlinarith
    positivity
  linarith [latticeEigenvalue_lower_bound k N hk hN]

/-- In scope the variance is strictly positive: the Gaussian is
non-degenerate. -/
theorem modeVarianceReal_pos (k N : ℕ) (hk : 1 ≤ k) (hN : 4 * k ≤ N) :
    0 < modeVarianceReal k N :=
  inv_pos.mpr (latticeEigenvalue_pos k N hk hN)

/-- NON-VACUITY (target 4): in scope `μ_N` is a genuinely non-degenerate
Gaussian (not the Dirac mass): its `ℝ≥0` variance parameter is
nonzero. -/
theorem modeVariance_ne_zero (k N : ℕ) (hk : 1 ≤ k) (hN : 4 * k ≤ N) :
    modeVariance k N ≠ 0 := by
  have hpos := modeVarianceReal_pos k N hk hN
  simp only [modeVariance, ne_eq, Real.toNNReal_eq_zero, not_le]
  exact hpos

/-- TARGET 2 (rate): for `k ≥ 1` and `N ≥ 4k`,
`|v_N(k) − (2πk)⁻²| ≤ (1/6)/N²`. The constant `C(k) = 1/6` is uniform
in `k`: `|λ⁻¹ − Λ⁻¹| = |Λ − λ|/(λΛ) ≤ (Λ²/12/N²)/(Λ²/2) = (1/6)/N²`
with `Λ = (2πk)²`, using the Phase-2a expansion for the numerator and
`latticeEigenvalue_lower_bound` for the denominator. -/
theorem modeVarianceReal_rate (k N : ℕ) (hk : 1 ≤ k) (hN : 4 * k ≤ N) :
    |modeVarianceReal k N - (continuumEigenvalue k)⁻¹|
      ≤ 1 / 6 / (N : ℝ) ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hNR : (4 : ℝ) * (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hLam_pos : 0 < continuumEigenvalue k := by
    unfold continuumEigenvalue
    have : 0 < 2 * Real.pi * (k : ℝ) := by
      have := Real.pi_pos
      nlinarith
    positivity
  have hlow := latticeEigenvalue_lower_bound k N hk hN
  have hlam_pos : 0 < latticeEigenvalue k N := latticeEigenvalue_pos k N hk hN
  -- Numerator: the Phase-2a expansion, with `(2πk)⁴ = Λ²`.
  have hnum : |continuumEigenvalue k - latticeEigenvalue k N|
      ≤ (continuumEigenvalue k) ^ 2 / 12 / (N : ℝ) ^ 2 := by
    rw [abs_sub_comm]
    have h4 : (continuumEigenvalue k) ^ 2 = (2 * Real.pi * (k : ℝ)) ^ 4 := by
      unfold continuumEigenvalue
      ring
    rw [h4]
    exact discrete_sine_eigenvalue_expansion k N hN1
  -- Denominator: `λΛ ≥ Λ²/2`.
  have hden : (continuumEigenvalue k) ^ 2 / 2
      ≤ latticeEigenvalue k N * continuumEigenvalue k := by
    have := mul_le_mul_of_nonneg_right hlow hLam_pos.le
    nlinarith [this]
  have hinv : (latticeEigenvalue k N)⁻¹ - (continuumEigenvalue k)⁻¹
      = (continuumEigenvalue k - latticeEigenvalue k N)
        / (latticeEigenvalue k N * continuumEigenvalue k) :=
    inv_sub_inv hlam_pos.ne' hLam_pos.ne'
  unfold modeVarianceReal
  rw [hinv, abs_div, abs_of_pos (mul_pos hlam_pos hLam_pos)]
  calc |continuumEigenvalue k - latticeEigenvalue k N|
        / (latticeEigenvalue k N * continuumEigenvalue k)
      ≤ ((continuumEigenvalue k) ^ 2 / 12 / (N : ℝ) ^ 2)
        / ((continuumEigenvalue k) ^ 2 / 2) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 1 / 6 / (N : ℝ) ^ 2 := by
        field_simp
        ring

/-! ## Target 3: measure convergence (two honest formulations) -/

/-- The variances converge with the `(1/6)/N²` rate: `v_N(k) → (2πk)⁻²`.
Composes the rate with the Phase-2a squeeze
`eigenvalue_limit_of_uniform_bound`. -/
theorem modeVarianceReal_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun N : ℕ => modeVarianceReal k N) Filter.atTop
      (nhds ((continuumEigenvalue k)⁻¹)) :=
  eigenvalue_limit_of_uniform_bound _ _ (1 / 6) (4 * k)
    (fun N hN => modeVarianceReal_rate k N hk hN)

/-- TARGET 3 (second moments converge): the actual Gaussian integrals
`∫ x² dμ_N` converge to the continuum mode variance `(2πk)⁻²`. -/
theorem secondMoment_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun N : ℕ => ∫ x, x ^ 2 ∂(modeMeasure k N))
      Filter.atTop (nhds ((continuumEigenvalue k)⁻¹)) := by
  refine Filter.Tendsto.congr (fun N => ?_) (modeVarianceReal_tendsto k hk)
  rw [secondMoment_modeMeasure, coe_modeVariance]

/-- TARGET 3 (characteristic functions converge pointwise): for every
`t`, `charFun μ_N t → exp(−(2πk)⁻² t²/2)`, the characteristic function
of the centered Gaussian of variance `(2πk)⁻²`. This is the strongest
convergence statement the vendored Mathlib supports without new axioms
(no Lévy continuity theorem is available, so the classical upgrade to
weak convergence is NOT claimed here). -/
theorem charFun_modeMeasure_tendsto (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    Filter.Tendsto (fun N : ℕ => charFun (modeMeasure k N) t)
      Filter.atTop
      (nhds (Complex.exp
        (-((((continuumEigenvalue k)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)))) := by
  have h0 : Filter.Tendsto
      (fun N : ℕ => ((modeVarianceReal k N : ℝ) : ℂ)) Filter.atTop
      (nhds ((((continuumEigenvalue k)⁻¹ : ℝ) : ℂ))) :=
    (Complex.continuous_ofReal.tendsto _).comp (modeVarianceReal_tendsto k hk)
  have h1 : Filter.Tendsto
      (fun N : ℕ => -(((modeVarianceReal k N : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
      Filter.atTop
      (nhds (-((((continuumEigenvalue k)⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    ((h0.mul_const ((t : ℂ) ^ 2)).div_const (2 : ℂ)).neg
  refine Filter.Tendsto.congr (fun N => ?_) h1.cexp
  rw [charFun_modeMeasure k N t, coe_modeVariance]

/-! ## Target 4: non-vacuity of the limit -/

/-- TARGET 4 (J ≠ 0): the limiting variance `(2πk)⁻²` is strictly
positive for every mode `k ≥ 1`: the limit object is a non-degenerate
Gaussian, not a point mass. -/
theorem limitVariance_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < (continuumEigenvalue k)⁻¹ := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : 0 < continuumEigenvalue k := by
    unfold continuumEigenvalue
    have : 0 < 2 * Real.pi * (k : ℝ) := by
      have := Real.pi_pos
      nlinarith
    positivity
  exact inv_pos.mpr this

end

end OneModeCylinder
end Analysis
end Gravity
end IndisputableMonolith
