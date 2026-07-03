import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.GapWeight

/-!
# Alpha Exponential Form: Structural Analysis

## The Remaining Open Step (Gap B from Validation Program)

The canonical formula for α⁻¹ in `Constants/Alpha.lean` is:

    α⁻¹ = α_seed · exp(-f_gap / α_seed)

where α_seed = 4π·11 and f_gap = w₈·ln(φ).

The integer 44 = 4·11 is a forced combinatorial identity (11 = passive edges of Q₃,
proved in `AlphaDerivation.lean`). But its *identification* as the α⁻¹ seed coupling
is NOT forced (4π·11 vs the cycle-rank 5 / quadratic π², see `Constants/AlphaGenesis/`),
and the *exponential form* itself is currently a `def`, not derived from a
first-principles variational or structural argument. So the exact infrared
α⁻¹(0) = 137.035999 stays a boundary condition, OPEN.

This module does not close the gap in a definitive sense, but it does:

1. **Prove positivity of α⁻¹**: the exponential form produces a positive
   value, consistent with the physical requirement.
2. **Identify the differential equation satisfied**: α⁻¹(f_gap) satisfies
   the logarithmic ODE that is the hallmark of running-coupling behavior.
3. **Document the structural motivation**: the 1/n! Taylor coefficients of
   exp arise from the J-cost's log-coordinate structure (cosh expansion).
4. **Explicitly state the uniqueness question** as an unproved Prop,
   identifying what would be needed to close the gap.

## What remains genuinely open after this module

The *form* α_seed · exp(-f_gap/α_seed) is distinguished from alternatives
like α_seed / (1 + f_gap/α_seed) or α_seed · (1 - f_gap/α_seed)^n by
higher-order structure. The Lean currently does not prove that the
exponential Taylor coefficients are uniquely forced by RS structure.

Physical motivations (Boltzmann-like suppression, renormalization-group
improvement, J-cost log-structure) are documented but not formalized as
uniqueness theorems. This is flagged in `epistemic_layers.md` as a BRIDGE
claim and the exponential form is a specific instance.

-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaExponentialForm

open Real Constants

noncomputable section

/-! ## Part 1: Basic Properties of the Exponential Form -/

/-- The alphaInv formula unfolds to the exponential expression. -/
theorem alphaInv_def : alphaInv = alpha_seed * Real.exp (-(f_gap / alpha_seed)) := rfl

/-- The seed is positive: α_seed = 4π·11 > 0. -/
theorem alpha_seed_positive : 0 < alpha_seed := by
  unfold alpha_seed
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

/-- The exponential formula produces a positive value. -/
theorem alphaInv_positive : 0 < alphaInv := by
  unfold alphaInv
  exact mul_pos alpha_seed_positive (Real.exp_pos _)

/-- The exponential factor is in (0, 1] since f_gap ≥ 0 (assuming w₈ > 0). -/
theorem exp_factor_bounded (hfg : 0 ≤ f_gap) :
    0 < Real.exp (-(f_gap / alpha_seed)) ∧ Real.exp (-(f_gap / alpha_seed)) ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    apply neg_nonpos_of_nonneg
    exact div_nonneg hfg (le_of_lt alpha_seed_positive)

/-- The ratio alphaInv/alpha_seed equals the exponential factor. -/
theorem alphaInv_seed_ratio :
    alphaInv / alpha_seed = Real.exp (-(f_gap / alpha_seed)) := by
  unfold alphaInv
  field_simp

/-! ## Part 2: The Logarithmic Structure

Taking the natural log of α⁻¹/α_seed gives:
    ln(α⁻¹/α_seed) = -f_gap/α_seed

This is the defining relation of the exponential form in log coordinates.
It says that the logarithm of the coupling ratio is LINEAR in f_gap with
slope -1/α_seed.
-/

/-- The log of the ratio alphaInv/alpha_seed equals -f_gap/alpha_seed. -/
theorem log_alphaInv_seed_ratio :
    Real.log (alphaInv / alpha_seed) = -(f_gap / alpha_seed) := by
  rw [alphaInv_seed_ratio]
  exact Real.log_exp _

/-- Equivalent: ln(α⁻¹) = ln(α_seed) - f_gap/α_seed. -/
theorem log_alphaInv_eq :
    Real.log alphaInv = Real.log alpha_seed - f_gap / alpha_seed := by
  have h := log_alphaInv_seed_ratio
  rw [Real.log_div (ne_of_gt alphaInv_positive) (ne_of_gt alpha_seed_positive)] at h
  linarith

/-! ## Part 3: The Differential Equation

The exponential form α⁻¹ = α_seed · exp(-f_gap/α_seed) satisfies the ODE
(treating α⁻¹ as a function of f_gap with α_seed fixed):

    d(α⁻¹)/d(f_gap) = -α⁻¹/α_seed

This is the defining characteristic of the exponential family: the
logarithmic derivative is constant.

This ODE is analogous to the renormalization-group equation for a running
coupling, with α_seed playing the role of a "scale" setting the logarithmic
derivative.
-/

/-- The alphaInv function parameterized by f_gap value. -/
noncomputable def alphaInv_of_gap (g : ℝ) : ℝ := alpha_seed * Real.exp (-(g / alpha_seed))

/-- At the canonical f_gap, alphaInv_of_gap agrees with alphaInv. -/
theorem alphaInv_of_gap_at_canonical : alphaInv_of_gap f_gap = alphaInv := rfl

/-- The derivative of alphaInv with respect to f_gap. -/
theorem deriv_alphaInv_of_gap (g : ℝ) :
    deriv alphaInv_of_gap g = -(alphaInv_of_gap g / alpha_seed) := by
  unfold alphaInv_of_gap
  -- h1: derivative of g → -(g/alpha_seed) is -(1/alpha_seed)
  have h_id : HasDerivAt (fun g : ℝ => g) 1 g := hasDerivAt_id g
  have h_div : HasDerivAt (fun g : ℝ => g / alpha_seed) (1 / alpha_seed) g :=
    h_id.div_const alpha_seed
  have h1 : HasDerivAt (fun g : ℝ => -(g / alpha_seed)) (-(1 / alpha_seed)) g :=
    h_div.neg
  -- h2: derivative of exp(-(g/alpha_seed))
  have h2 : HasDerivAt (fun g : ℝ => Real.exp (-(g / alpha_seed)))
      (Real.exp (-(g / alpha_seed)) * (-(1 / alpha_seed))) g :=
    (Real.hasDerivAt_exp _).comp g h1
  -- h3: scale by alpha_seed
  have h3 : HasDerivAt (fun g : ℝ => alpha_seed * Real.exp (-(g / alpha_seed)))
      (alpha_seed * (Real.exp (-(g / alpha_seed)) * (-(1 / alpha_seed)))) g :=
    h2.const_mul alpha_seed
  -- Simplify the derivative expression
  have heq : alpha_seed * (Real.exp (-(g / alpha_seed)) * (-(1 / alpha_seed)))
       = -(alpha_seed * Real.exp (-(g / alpha_seed)) / alpha_seed) := by
    field_simp
  rw [← heq]
  exact h3.deriv

/-- The logarithmic derivative: d ln(α⁻¹)/d(f_gap) = -1/α_seed (constant). -/
theorem logarithmic_derivative_constant (g : ℝ) :
    deriv (fun g => Real.log (alphaInv_of_gap g)) g = -(1 / alpha_seed) := by
  have hpos : 0 < alphaInv_of_gap g := by
    unfold alphaInv_of_gap
    exact mul_pos alpha_seed_positive (Real.exp_pos _)
  have h_log_eq : ∀ g, Real.log (alphaInv_of_gap g) =
      Real.log alpha_seed + (-(g / alpha_seed)) := by
    intro g
    unfold alphaInv_of_gap
    rw [Real.log_mul (ne_of_gt alpha_seed_positive) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  -- deriv of (Real.log α_seed + (-(g / α_seed))) = deriv of (-(g/α_seed)) = -1/α_seed
  have h_fun_eq : (fun g => Real.log (alphaInv_of_gap g)) =
      (fun g => Real.log alpha_seed + (-(g / alpha_seed))) := by
    funext g
    exact h_log_eq g
  rw [h_fun_eq]
  have h_const_derivable : HasDerivAt (fun _ : ℝ => Real.log alpha_seed) 0 g :=
    hasDerivAt_const g _
  have h_lin_derivable : HasDerivAt (fun g => -(g / alpha_seed)) (-(1 / alpha_seed)) g := by
    have h1 : HasDerivAt (fun g : ℝ => g) 1 g := hasDerivAt_id g
    have h2 : HasDerivAt (fun g : ℝ => g / alpha_seed) (1 / alpha_seed) g :=
      h1.div_const alpha_seed
    exact h2.neg
  have : HasDerivAt (fun g => Real.log alpha_seed + (-(g / alpha_seed))) (0 + -(1 / alpha_seed)) g :=
    h_const_derivable.add h_lin_derivable
  rw [zero_add] at this
  exact this.deriv

/-! ## Part 4: Inheritance from J-Cost Log Structure

The J-cost J(x) = cosh(ln x) - 1 has Taylor expansion in log coordinates:

    J(e^t) = cosh(t) - 1 = Σ t^(2n)/(2n)! = t²/2 + t⁴/24 + t⁶/720 + ...

The factorial coefficients 1/(2n)! come from the d'Alembert uniqueness proof
(`law_of_logic_forces_jcost`). Any cost functional satisfying the RCL has these
coefficients in its log-coordinate expansion.

The exponential form α_seed · exp(-f_gap/α_seed) inherits factorial
coefficients in its Taylor expansion around f_gap = 0, and these match the
coefficients in the J-cost expansion.
-/

/-- The first-order (linear) term of α⁻¹ in f_gap: matches a naive
    perturbative expansion. -/
theorem alphaInv_linear_term :
    alphaInv_of_gap 0 = alpha_seed := by
  unfold alphaInv_of_gap
  simp [Real.exp_zero]

/-- The first derivative at f_gap = 0: rate of decrease is -1 per unit
    gap (independent of α_seed at leading order). -/
theorem alphaInv_linear_rate :
    deriv alphaInv_of_gap 0 = -1 := by
  rw [deriv_alphaInv_of_gap]
  rw [alphaInv_linear_term]
  field_simp

/-! ## Part 5: The Uniqueness Question (Open)

A full forcing argument would prove that the exponential form is the
UNIQUE form satisfying certain structural constraints. The simplest
candidate uniqueness statement:

Given a function g : ℝ → ℝ such that:
1. g is smooth (C^∞)
2. g(0) = α_seed and g'(0) = -1 (so leading-order behavior matches
   α_seed - f_gap)
3. The logarithmic derivative (log g)'(x) is CONSTANT (equal to -1/α_seed)

Then g(x) = α_seed · exp(-x/α_seed).

Condition (3) is the distinctive feature: it says the relative rate of
change of g is scale-free (same at all x). This IS a forcing property
(standard ODE uniqueness), but it is also a STRUCTURAL ASSUMPTION that
needs physical justification in the RS context.

Alternative formulas like α_seed / (1 + x/α_seed) have non-constant log
derivative ((d/dx) log(α_seed/(1+x/α_seed)) = -1/(α_seed + x), which
depends on x), so they don't satisfy (3).

Whether RS structure FORCES the log-derivative to be constant is the
genuine open question.
-/

/-- **Open question as a Prop**: the exponential form is uniquely
    determined by constant logarithmic derivative. -/
def exponential_form_from_constant_log_derivative : Prop :=
  ∀ (g : ℝ → ℝ),
    (g 0 = alpha_seed) →
    (∀ x, 0 < g x) →
    ContDiff ℝ ⊤ g →
    (∀ x, deriv (fun y => Real.log (g y)) x = -(1 / alpha_seed)) →
    ∀ x, g x = alpha_seed * Real.exp (-(x / alpha_seed))

/-- **OPEN STATUS**: This uniqueness claim follows from standard ODE theory
    (if log g' is constant = k, then g(x) = g(0) · e^(kx), which is unique
    under Picard-Lindelöf). We leave it unproved here as it is provable in
    principle but requires ODE machinery.

    The *physical* question — WHY the log derivative should be constant
    in the RS derivation — is the true remaining gap. -/
theorem exponential_form_uniqueness_ode_principle :
    True := trivial

/-! ## Summary of What This Module Proves

1. **Structural properties** of the exponential form:
   * `alphaInv_def`: α⁻¹ is the exponential expression (unfold)
   * `alphaInv_positive`: α⁻¹ > 0
   * `exp_factor_bounded`: the exponential factor is in (0, 1] when f_gap ≥ 0

2. **Log-coordinate structure**:
   * `log_alphaInv_seed_ratio`: ln(α⁻¹/α_seed) = -f_gap/α_seed (linear in f_gap)
   * `log_alphaInv_eq`: ln(α⁻¹) = ln(α_seed) - f_gap/α_seed

3. **Differential structure**:
   * `deriv_alphaInv_of_gap`: dα⁻¹/df_gap = -α⁻¹/α_seed (the defining ODE)
   * `logarithmic_derivative_constant`: d ln(α⁻¹)/df_gap = -1/α_seed
     (constant logarithmic rate)

4. **Leading-order consistency**:
   * `alphaInv_linear_term`: at f_gap=0, α⁻¹ = α_seed
   * `alphaInv_linear_rate`: at f_gap=0, dα⁻¹/df_gap = -1

## What's NOT proved

1. **Uniqueness from structural principles**: the formula is defined, not
   derived. `exponential_form_from_constant_log_derivative` states a
   candidate uniqueness but is not proved.
2. **Forcing of the constant log-derivative**: why RS requires
   (d/df_gap) ln(α⁻¹) to be constant (and specifically = -1/α_seed)
   remains a BRIDGE claim between the formalism and physics.

## Residual Openness

The exponential form of α⁻¹ is best understood as a STRUCTURAL CHOICE
inherited from the J-cost's log-coordinate behavior, rather than as a
derived consequence. It is a natural choice given:
- The J-cost's exponential/cosh structure in log coordinates.
- The requirement of positivity for all f_gap values.
- The linear leading-order behavior α⁻¹ ≈ α_seed - f_gap.
- The scale-free running (constant logarithmic derivative).

But NONE of these individually force the exponential form uniquely without
additional assumptions. The integer 44 IS forced (proved in
`alpha_44_forcing.md`). The exponential form is PLAUSIBLE but not uniquely
forced in the current Lean.

This is documented in `epistemic_layers.md` as a BRIDGE claim.

-/

end

end AlphaExponentialForm
end Constants
end IndisputableMonolith
