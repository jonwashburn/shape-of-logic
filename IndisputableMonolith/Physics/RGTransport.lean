import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

/-!
# Renormalization Group Transport for Mass Residues

This module formalizes the **RG transport** that defines the empirical mass residue `f^exp`.

## Background

In the Standard Model, fermion masses run with the renormalization scale μ according to:

  `d(ln m)/d(ln μ) = -γ_m(μ)`

where `γ_m(μ)` is the mass anomalous dimension, depending on couplings `α_s(μ), α(μ), ...`.

The **integrated residue** from scale `μ₀` to `μ₁` is:

  `f(μ₀, μ₁) = (1/λ) ∫_{ln μ₀}^{ln μ₁} γ_m(μ') d(ln μ')`

where `λ = ln φ` is the normalization constant used in the mass formula.

## Relation to Mass Formula

The structural mass `m_struct` is defined at the anchor `μ⋆`. The physical mass relates via:

  `m(μ⋆) = m_phys · φ^{f(μ⋆, m_phys)}`

If `m(μ⋆) = m_struct`, then:

  `m_phys = m_struct · φ^{-f}`

## What This Module Provides

1. **AnomalousDimension**: A structure representing the mass anomalous dimension γ_m(μ).
2. **RGTransport**: The integral formula that defines the residue.
3. **Connection theorems**: Relating the transport to the mass ratio.

## What This Module Does NOT Provide

The actual QCD 4L / QED 2L kernels. Those would require extensive Standard Model machinery.
This module provides the *mathematical framework* that such kernels would plug into.

## See Also

- `IndisputableMonolith/Physics/AnchorPolicy.lean`: The axiom `f_residue` is intended to be
  the result of this transport at the anchor scale.
- `IndisputableMonolith/Physics/AnchorPolicyCertified.lean`: If you want to avoid global axioms
  and instead depend on externally certified residue intervals.
- `IndisputableMonolith/Physics/RunningCouplings.lean`: Threshold scales and crossover structure.
- `IndisputableMonolith/Physics/ElectronMass/Necessity.lean`: Proven bounds on electron mass
  and residues using interval arithmetic.
-/

namespace IndisputableMonolith
namespace Physics
namespace RGTransport

open IndisputableMonolith.Constants
open IndisputableMonolith.RSBridge
open MeasureTheory

noncomputable section

/-! ## Anomalous Dimension Structure -/

/-- Running coupling at scale μ. This is an abstract interface; the actual SM couplings
    (α_s, α, α_2) would be specializations. -/
structure RunningCoupling where
  /-- The coupling value at scale μ (in GeV). -/
  at_scale : ℝ → ℝ
  /-- The coupling is positive in the perturbative regime. -/
  positive_in_pert : ∀ μ, μ > 1 → at_scale μ > 0
  /-- Asymptotic freedom: coupling decreases at high scale (for QCD). -/
  asymp_free : ∀ μ₁ μ₂, μ₁ < μ₂ → μ₂ > 100 → at_scale μ₂ < at_scale μ₁

/-- The mass anomalous dimension γ_m(μ).
    In general, this is a function of the scale and the fermion species.
    It encodes how the running mass changes with μ. -/
structure AnomalousDimension where
  /-- The anomalous dimension value for fermion f at scale μ. -/
  gamma : Fermion → ℝ → ℝ
  /-- The anomalous dimension is smooth (differentiable). -/
  smooth : ∀ f, Differentiable ℝ (gamma f)
  /-- Perturbative bound: |γ| is bounded in the perturbative regime. -/
  pert_bounded : ∃ B > 0, ∀ f μ, μ > 1 → |gamma f μ| < B

/-! ## RG Transport Integral -/

/-- The λ-normalization constant: `λ = ln(φ)`. -/
def lambda : ℝ := Real.log phi

/-- λ is positive. -/
theorem lambda_pos : lambda > 0 := by
  have h : 1 < phi := one_lt_phi
  exact Real.log_pos h

/-! ## Canonical one-loop beta/gamma kernels (Level-B groundwork) -/

/-- One-loop QCD beta coefficient in the convention `beta0 = 11 - 2*nf/3`. -/
def beta0QCD (nf : ℕ) : ℚ := (11 : ℚ) - (2 : ℚ) * nf / 3

/-- Real-valued view of `beta0QCD`. -/
def beta0QCDReal (nf : ℕ) : ℝ := (beta0QCD nf : ℝ)

/-- One-loop QCD running for `alpha_s`:
`d alpha_s / d ln mu = -(beta0/(2*pi)) * alpha_s^2`. -/
noncomputable def betaQCD1L (nf : ℕ) (alphaS : ℝ) : ℝ :=
  -((beta0QCDReal nf) / (2 * Real.pi)) * alphaS ^ 2

/-- One-loop QED running with an effective charge-weight factor.
This keeps the kernel explicit while allowing policy-level charge sums. -/
noncomputable def betaQED1L (chargeWeight : ℝ) (alpha : ℝ) : ℝ :=
  (chargeWeight / (3 * Real.pi)) * alpha ^ 2

/-- Minimal one-loop mass anomalous-dimension scaffold for QCD.
The exact scheme-dependent higher-loop expression is left to Level-B extensions. -/
noncomputable def gammaMassQCD1L (alphaS : ℝ) : ℝ :=
  (2 / Real.pi) * alphaS

/-- Minimal one-loop mass anomalous-dimension scaffold for QED. -/
noncomputable def gammaMassQED1L (chargeSq : ℝ) (alpha : ℝ) : ℝ :=
  (3 * chargeSq / (4 * Real.pi)) * alpha

theorem beta0QCD_nf0 : beta0QCD 0 = 11 := by
  norm_num [beta0QCD]

theorem beta0QCD_asymp_free (nf : ℕ) (hnf : nf ≤ 16) : 0 < beta0QCD nf := by
  unfold beta0QCD
  have hnfQ : (nf : ℚ) ≤ 16 := by
    exact_mod_cast hnf
  have h_le : (2 : ℚ) * nf / 3 ≤ (2 : ℚ) * 16 / 3 := by
    exact div_le_div_of_nonneg_right (by nlinarith [hnfQ]) (by norm_num)
  have h_lt : (2 : ℚ) * 16 / 3 < 11 := by norm_num
  have h_frac_lt : (2 : ℚ) * nf / 3 < 11 := lt_of_le_of_lt h_le h_lt
  linarith

theorem betaQCD1L_vanishes_at_zero (nf : ℕ) :
    betaQCD1L nf 0 = 0 := by
  simp [betaQCD1L]

theorem gammaMassQCD1L_zero : gammaMassQCD1L 0 = 0 := by
  simp [gammaMassQCD1L]

/-! ## RK4 integrator scaffold with enclosure bounds -/

/-- RK4 increment from stage values `(k1,k2,k3,k4)`. -/
def rk4Increment (h k1 k2 k3 k4 : ℝ) : ℝ :=
  (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4)

/-- One RK4 step for `x' = f(x)` with step size `h`. -/
def rk4Step (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  let k1 := f x
  let k2 := f (x + (h / 2) * k1)
  let k3 := f (x + (h / 2) * k2)
  let k4 := f (x + h * k3)
  x + rk4Increment h k1 k2 k3 k4

theorem rk4Step_eq_self_of_zero (f : ℝ → ℝ)
    (hzero : ∀ y, f y = 0) (x h : ℝ) :
    rk4Step f x h = x := by
  simp [rk4Step, rk4Increment, hzero]

/-- Algebraic enclosure: if each RK4 stage is bounded by `M`, then one-step
deviation is bounded by `|h|*M`. -/
theorem abs_rk4Increment_le (M h k1 k2 k3 k4 : ℝ)
    (hk1 : |k1| ≤ M) (hk2 : |k2| ≤ M)
    (hk3 : |k3| ≤ M) (hk4 : |k4| ≤ M) :
    |rk4Increment h k1 k2 k3 k4| ≤ |h| * M := by
  have hsum1 : |k1 + 2 * k2 + 2 * k3 + k4| ≤ |k1| + |2 * k2 + 2 * k3 + k4| := by
    simpa [Real.norm_eq_abs, add_assoc] using
      (norm_add_le k1 (2 * k2 + 2 * k3 + k4))
  have hsum2 : |2 * k2 + 2 * k3 + k4| ≤ |2 * k2| + |2 * k3 + k4| := by
    simpa [Real.norm_eq_abs, add_assoc] using
      (norm_add_le (2 * k2) (2 * k3 + k4))
  have hsum3 : |2 * k3 + k4| ≤ |2 * k3| + |k4| := by
    simpa [Real.norm_eq_abs] using (norm_add_le (2 * k3) k4)
  have h2k2 : |2 * k2| = 2 * |k2| := by
    norm_num [abs_mul]
  have h2k3 : |2 * k3| = 2 * |k3| := by
    norm_num [abs_mul]
  have hsum :
      |k1 + 2 * k2 + 2 * k3 + k4| ≤ |k1| + 2 * |k2| + 2 * |k3| + |k4| := by
    nlinarith [hsum1, hsum2, hsum3, h2k2, h2k3]
  have hsumM : |k1 + 2 * k2 + 2 * k3 + k4| ≤ 6 * M := by
    nlinarith [hsum, hk1, hk2, hk3, hk4]
  calc
    |rk4Increment h k1 k2 k3 k4|
        = |h / 6| * |k1 + 2 * k2 + 2 * k3 + k4| := by
            simp [rk4Increment, abs_mul]
    _ = (|h| / 6) * |k1 + 2 * k2 + 2 * k3 + k4| := by
          simp [abs_div]
    _ ≤ (|h| / 6) * (6 * M) := by
          gcongr
    _ = |h| * M := by ring

/-- RK4 one-step enclosure bound for function evaluations at the four RK stages. -/
theorem rk4Step_deviation_le (f : ℝ → ℝ) (x h M : ℝ)
    (hk1 : |f x| ≤ M)
    (hk2 : |f (x + (h / 2) * f x)| ≤ M)
    (hk3 : |f (x + (h / 2) * f (x + (h / 2) * f x))| ≤ M)
    (hk4 : |f (x + h * f (x + (h / 2) * f (x + (h / 2) * f x)))| ≤ M) :
    |rk4Step f x h - x| ≤ |h| * M := by
  unfold rk4Step
  set k1 : ℝ := f x
  set k2 : ℝ := f (x + (h / 2) * k1)
  set k3 : ℝ := f (x + (h / 2) * k2)
  set k4 : ℝ := f (x + h * k3)
  have hk1' : |k1| ≤ M := by simpa [k1] using hk1
  have hk2' : |k2| ≤ M := by simpa [k1, k2] using hk2
  have hk3' : |k3| ≤ M := by simpa [k1, k2, k3] using hk3
  have hk4' : |k4| ≤ M := by simpa [k1, k2, k3, k4] using hk4
  have hinc :
      |rk4Increment h k1 k2 k3 k4| ≤ |h| * M :=
    abs_rk4Increment_le M h k1 k2 k3 k4 hk1' hk2' hk3' hk4'
  have hstep : |(x + rk4Increment h k1 k2 k3 k4) - x| = |rk4Increment h k1 k2 k3 k4| := by
    ring_nf
  simpa [hstep]

/-- The integrated residue from ln-scale `lnμ₀` to `lnμ₁`.

    `f(μ₀, μ₁) = (1/λ) ∫_{lnμ₀}^{lnμ₁} γ(exp(t)) dt`

    This is the abstract definition; the actual computation requires the SM kernels.
    We parameterize by an `AnomalousDimension` structure. -/
def integratedResidue (γ : AnomalousDimension) (f : Fermion) (lnμ₀ lnμ₁ : ℝ) : ℝ :=
  (1 / lambda) * ∫ t in Set.Icc lnμ₀ lnμ₁, γ.gamma f (Real.exp t)

/-! ## Connection to Mass Formula -/

/-- The running mass at scale μ, given the mass at scale μ₀ and an anomalous dimension.

    `m(μ) = m(μ₀) · exp(-∫_{ln μ₀}^{ln μ} γ(μ') d(ln μ'))`

    This is the solution to `d(ln m)/d(ln μ) = -γ_m(μ)`. -/
def runningMass (γ : AnomalousDimension) (f : Fermion) (m_μ₀ : ℝ) (lnμ₀ lnμ : ℝ) : ℝ :=
  m_μ₀ * Real.exp (-(∫ t in Set.Icc lnμ₀ lnμ, γ.gamma f (Real.exp t)))

/-- The mass ratio between two scales.

    `m(μ₁)/m(μ₀) = exp(-∫_{ln μ₀}^{ln μ₁} γ d(ln μ))` -/
theorem mass_ratio_formula (γ : AnomalousDimension) (f : Fermion) (m_μ₀ : ℝ)
    (lnμ₀ lnμ₁ : ℝ) (hm : m_μ₀ ≠ 0) :
    runningMass γ f m_μ₀ lnμ₀ lnμ₁ / m_μ₀ =
      Real.exp (-(∫ t in Set.Icc lnμ₀ lnμ₁, γ.gamma f (Real.exp t))) := by
  simp only [runningMass]
  field_simp

/-! ## Anchor Relation -/

/-- The anchor scale from the papers: μ⋆ = 182.201 GeV. -/
def muStar : ℝ := 182.201

theorem muStar_pos : muStar > 0 := by norm_num [muStar]

/-- ln(μ⋆) for use in integral bounds. -/
def lnMuStar : ℝ := Real.log muStar

/-- The residue at the anchor, relative to a reference ln-scale.

    `f_i(μ⋆, μ_ref) := (1/λ) ∫_{ln μ⋆}^{lnμ_ref} γ_i(exp(t)) dt`

    This is what the axiom `f_residue` in `AnchorPolicy.lean` is intended to represent. -/
def residueAtAnchor (γ : AnomalousDimension) (f : Fermion) (lnμ_ref : ℝ) : ℝ :=
  integratedResidue γ f lnMuStar lnμ_ref

/-- The claim of Single Anchor Phenomenology: at the anchor scale μ⋆, the residue
    equals the closed-form display F(Z).

    `residueAtAnchor γ f (ln m_phys) ≈ gap(ZOf f)`

    This is what `display_identity_at_anchor` in `AnchorPolicy.lean` asserts. -/
def anchorClaimHolds (γ : AnomalousDimension) (tolerance : ℝ) : Prop :=
  ∀ (f : Fermion) (lnμ_ref : ℝ),
    |residueAtAnchor γ f lnμ_ref - gap (ZOf f)| < tolerance

/-! ## Stationarity at the Anchor -/

/-- The derivative of the residue with respect to the upper integration limit.
    This equals (1/λ) · γ(exp(lnμ)) = (1/λ) · γ(μ) by the fundamental theorem of calculus.

    Stationarity of the residue at μ⋆ means this vanishes, i.e., γ(μ⋆) = 0. -/
def residueDerivative (γ : AnomalousDimension) (f : Fermion) (lnμ : ℝ) : ℝ :=
  (1 / lambda) * γ.gamma f (Real.exp lnμ)

theorem stationarity_iff_gamma_zero (γ : AnomalousDimension) (f : Fermion) :
    residueDerivative γ f lnMuStar = 0 ↔ γ.gamma f muStar = 0 := by
  simp only [residueDerivative, lnMuStar]
  rw [Real.exp_log muStar_pos]
  have hlambda : lambda ≠ 0 := ne_of_gt lambda_pos
  constructor
  · intro h
    have hmul : (1 / lambda) * γ.gamma f muStar = 0 := h
    have h1 : (1 / lambda) ≠ 0 := one_div_ne_zero hlambda
    exact (mul_eq_zero.mp hmul).resolve_left h1
  · intro h
    simp [h]

/-! ## Relation to φ-Power Form -/

/-- The mass ratio in φ-power form.

    If `m(μ₁)/m(μ₀) = exp(-λ · f)`, then `m(μ₁)/m(μ₀) = φ^{-f}`.

    Note: `-lambda * f_residue` parses as `(-lambda) * f_residue` by precedence. -/
theorem mass_ratio_phi_power (f_residue : ℝ) :
    Real.exp (-lambda * f_residue) = phi ^ (-f_residue) := by
  have hphi_pos : 0 < phi := lt_trans (by norm_num : (0 : ℝ) < 1) one_lt_phi
  simp only [lambda]
  -- `-Real.log phi * f_residue` equals `Real.log phi * (-f_residue)`
  have h1 : -Real.log phi * f_residue = Real.log phi * (-f_residue) := by ring
  rw [h1]
  -- Now goal is: Real.exp (Real.log phi * -f_residue) = phi ^ (-f_residue)
  have h2 : Real.log phi * -f_residue = -f_residue * Real.log phi := by ring
  rw [h2, ← Real.log_rpow hphi_pos, Real.exp_log (Real.rpow_pos_of_pos hphi_pos _)]

/-! ## Summary -/

/-
This module provides the mathematical framework for understanding the RG transport
that defines the empirical residue f^exp:

1. **AnomalousDimension** captures the structure of γ_m(μ).
2. **integratedResidue** is the integral formula (1/λ)∫γ dt.
3. **residueAtAnchor** specializes to the anchor scale μ⋆.
4. **anchorClaimHolds** states the phenomenological claim that this equals gap(Z).
5. **stationarity_iff_gamma_zero** shows the stationarity condition.

The actual SM kernels are NOT implemented here. This is the interface that such
an implementation would satisfy.
-/

end

end RGTransport
end Physics
end IndisputableMonolith
