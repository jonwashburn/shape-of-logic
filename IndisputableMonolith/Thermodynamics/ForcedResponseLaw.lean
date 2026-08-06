import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Forced response law: exact calculus and bridge boundary

This module separates the exact derivative of canonical J-cost from the
additional physical premises needed to identify that derivative with flux.

The canonical log-ratio profile and its derivative are theorems. A general
coordinate bridge `s = bridge affinity` contributes its own derivative, and a
mobility law contributes another factor. The resulting flux shape is therefore
conditional on those two inputs.
-/

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseLaw

open Real
open Cost

noncomputable section

/-- Canonical J-cost written in the log-ratio coordinate. -/
def canonicalLogCost (s : ℝ) : ℝ :=
  Jcost (exp s)

/-- The canonical log-ratio cost is exactly `cosh s - 1`. -/
theorem canonicalLogCost_eq_cosh_sub_one (s : ℝ) :
    canonicalLogCost s = cosh s - 1 := by
  simpa [canonicalLogCost, FunctionalEquation.G] using
    FunctionalEquation.Jcost_G_eq_cosh_sub_one s

/-- The force conjugate to the canonical log-ratio coordinate is `sinh s`. -/
theorem canonicalLogCost_deriv (s : ℝ) :
    deriv canonicalLogCost s = sinh s := by
  have hfun : canonicalLogCost = fun t : ℝ => cosh t - 1 := by
    funext t
    exact canonicalLogCost_eq_cosh_sub_one t
  rw [hfun]
  exact (Real.hasDerivAt_cosh s).sub_const 1 |>.deriv

/-- Canonical cost after an arbitrary differentiable map from physical
affinity to log-ratio. -/
def bridgedCost (bridge : ℝ → ℝ) (affinity : ℝ) : ℝ :=
  canonicalLogCost (bridge affinity)

/-- The bridge contributes a free Jacobian factor and changes the argument of
the hyperbolic sine. -/
theorem bridgedCost_deriv
    {bridge : ℝ → ℝ} {affinity bridgeSlope : ℝ}
    (hbridge : HasDerivAt bridge bridgeSlope affinity) :
    deriv (bridgedCost bridge) affinity =
      bridgeSlope * sinh (bridge affinity) := by
  have hcanonical :
      HasDerivAt canonicalLogCost (sinh (bridge affinity)) (bridge affinity) := by
    have hfun : canonicalLogCost = fun t : ℝ => cosh t - 1 := by
      funext t
      exact canonicalLogCost_eq_cosh_sub_one t
    rw [hfun]
    exact (Real.hasDerivAt_cosh (bridge affinity)).sub_const 1
  have hcomp := hcanonical.comp affinity hbridge
  simpa [bridgedCost, mul_comm] using hcomp.deriv

/-- A gradient-flow flux supplied with an independently chosen mobility. This
is a model definition, not a derivation of physical transport from J-cost. -/
def gradientFlux (mobility bridge : ℝ → ℝ) (affinity : ℝ) : ℝ :=
  mobility affinity * deriv (bridgedCost bridge) affinity

/-- Under a differentiable bridge, the gradient-flow model has the displayed
response. Both `mobility` and `bridge` remain inputs. -/
theorem gradientFlux_formula
    (mobility : ℝ → ℝ)
    {bridge : ℝ → ℝ} {affinity bridgeSlope : ℝ}
    (hbridge : HasDerivAt bridge bridgeSlope affinity) :
    gradientFlux mobility bridge affinity =
      mobility affinity * (bridgeSlope * sinh (bridge affinity)) := by
  rw [gradientFlux, bridgedCost_deriv hbridge]

/-- A linear affinity bridge with scale `k`. -/
def linearBridge (k : ℝ) : ℝ → ℝ :=
  fun affinity => k * affinity

/-- Even a linear bridge changes both the prefactor and the argument. -/
theorem linearBridge_cost_deriv (k affinity : ℝ) :
    deriv (bridgedCost (linearBridge k)) affinity =
      k * sinh (k * affinity) := by
  apply bridgedCost_deriv
  simpa [linearBridge] using (hasDerivAt_id affinity).const_mul k

/-- The identity and doubled bridges give distinct cost profiles. Thus the
canonical cost alone cannot select the physical affinity scale. -/
theorem identity_and_double_bridge_costs_differ :
    bridgedCost (linearBridge 1) 1 ≠ bridgedCost (linearBridge 2) 1 := by
  unfold bridgedCost
  rw [canonicalLogCost_eq_cosh_sub_one (linearBridge 1 1),
    canonicalLogCost_eq_cosh_sub_one (linearBridge 2 1)]
  simp only [linearBridge, mul_one]
  have hlt : cosh (1 : ℝ) < cosh 2 := by
    rw [Real.cosh_lt_cosh]
    norm_num
  linarith

/-- Dimensionless Butler-Volmer response shape. -/
def butlerVolmerShape (alpha affinity : ℝ) : ℝ :=
  exp (alpha * affinity) - exp (-(1 - alpha) * affinity)

/-- At symmetry factor one half, Butler-Volmer is the symmetric sinh law. -/
theorem butlerVolmer_half_eq_two_sinh (affinity : ℝ) :
    butlerVolmerShape (1 / 2) affinity = 2 * sinh (affinity / 2) := by
  rw [butlerVolmerShape, Real.sinh_eq]
  ring_nf

/-- Every Butler-Volmer symmetry factor can be written as the same half-affinity
`sinh` profile multiplied by an affinity-dependent factor. -/
theorem butlerVolmer_factorization (alpha affinity : ℝ) :
    butlerVolmerShape alpha affinity =
      2 * exp ((alpha - 1 / 2) * affinity) * sinh (affinity / 2) := by
  rw [butlerVolmerShape, Real.sinh_eq]
  have hforward :
      alpha * affinity =
        (alpha - 1 / 2) * affinity + affinity / 2 := by
    ring
  have hbackward :
      -(1 - alpha) * affinity =
        (alpha - 1 / 2) * affinity + -(affinity / 2) := by
    ring
  rw [hforward, hbackward, Real.exp_add, Real.exp_add]
  ring

/-- The mobility that absorbs an arbitrary Butler-Volmer symmetry factor when
the log-ratio bridge is fixed to half-affinity. -/
def butlerVolmerMobility (alpha affinity : ℝ) : ℝ :=
  4 * exp ((alpha - 1 / 2) * affinity)

/-- The absorbing mobility is strictly positive for every symmetry factor and
affinity. -/
theorem butlerVolmerMobility_pos (alpha affinity : ℝ) :
    0 < butlerVolmerMobility alpha affinity := by
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- Even after fixing the bridge to half-affinity, every Butler-Volmer symmetry
factor is realizable by choosing the displayed positive mobility. Therefore a
free mobility prevents the cost-gradient model from selecting `alpha = 1 / 2`.
-/
theorem every_butlerVolmer_alpha_is_gradientFlux (alpha affinity : ℝ) :
    gradientFlux (butlerVolmerMobility alpha) (linearBridge (1 / 2)) affinity =
      butlerVolmerShape alpha affinity := by
  rw [gradientFlux, linearBridge_cost_deriv, butlerVolmer_factorization]
  simp only [butlerVolmerMobility]
  ring_nf

/-- Positive forward and backward rate pairs can have the same ratio but
different net rates. Ratio-level premises therefore do not determine flux
amplitude. -/
theorem rate_ratio_does_not_determine_net_rate :
    ∃ q₁plus q₁minus q₂plus q₂minus : ℝ,
      0 < q₁plus ∧ 0 < q₁minus ∧ 0 < q₂plus ∧ 0 < q₂minus ∧
      q₁plus / q₁minus = q₂plus / q₂minus ∧
      q₁plus - q₁minus ≠ q₂plus - q₂minus := by
  refine ⟨2, 1, 4, 2, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
  · norm_num

end

end ForcedResponseLaw
end Thermodynamics
end IndisputableMonolith
