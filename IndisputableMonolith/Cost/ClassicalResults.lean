import Mathlib

/-!
# Classical Mathematical Results

This module declares well-established mathematical results as axioms pending
full Lean formalization. Each axiom is justified with academic references.

These are NOT new physical assumptions - they are standard mathematical facts
from real analysis, complex analysis, and functional equations that would
require substantial Mathlib infrastructure to prove formally.

## Justification

All axioms in this module are:
1. **Textbook results** with multiple independent proofs in literature
2. **Computationally verifiable** (can be checked numerically to arbitrary precision)
3. **Used routinely** in mathematical physics without re-proving
4. **Candidates for future formalization** when infrastructure is available

## References

1. Aczél, J. (1966). *Lectures on Functional Equations and Their Applications*. Academic Press.
2. Kuczma, M. (2009). *An Introduction to the Theory of Functional Equations and Inequalities*. Birkhäuser.
3. Ahlfors, L. V. (1979). *Complex Analysis* (3rd ed.). McGraw-Hill.
4. Conway, J. B. (1978). *Functions of One Complex Variable*. Springer.
5. Apostol, T. M. (1974). *Mathematical Analysis* (2nd ed.). Addison-Wesley.
6. Rudin, W. (1976). *Principles of Mathematical Analysis* (3rd ed.). McGraw-Hill.

-/

namespace IndisputableMonolith
namespace Cost
namespace ClassicalResults

open Real Complex

/-! ## Provable Classical Results -/

private lemma spherical_cap_pos (θmin : ℝ) (hθ : θmin ∈ Set.Icc (0 : ℝ) (Real.pi/2)) :
    0 ≤ (2 * Real.pi * (1 - Real.cos θmin)) := by
  have h1 : Real.cos θmin ≤ 1 := Real.cos_le_one θmin
  have h2 : 0 ≤ 1 - Real.cos θmin := by linarith
  have h3 : 0 ≤ 2 * Real.pi := by positivity
  exact mul_nonneg h3 h2

private lemma exp_mul_rearrange (c₁ c₂ φ₁ φ₂ : ℝ) :
    Complex.exp (-(c₁+c₂)/2) * Complex.exp ((φ₁+φ₂) * I) =
    (Complex.exp (-c₁/2) * Complex.exp (φ₁ * I)) * (Complex.exp (-c₂/2) * Complex.exp (φ₂ * I)) := by
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Provable version with integrability hypotheses -/
theorem piecewise_path_integral_additive_integrable (f : ℝ → ℝ) (a b c : ℝ)
    (hab : IntervalIntegrable f MeasureTheory.volume a b)
    (hbc : IntervalIntegrable f MeasureTheory.volume b c) :
    ∫ x in a..c, f x = (∫ x in a..b, f x) + (∫ x in b..c, f x) :=
  (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm

/-! ## Real/Complex Hyperbolic Functions -/

theorem real_cosh_exponential_expansion (t : ℝ) :
    ((Real.exp t + Real.exp (-t)) / 2) = Real.cosh t := by
  simpa using (Real.cosh_eq t).symm

/-! ## Complex Exponential Norms -/

theorem complex_norm_exp_ofReal (r : ℝ) : ‖Complex.exp r‖ = Real.exp r := by
  rw [Complex.norm_exp]
  simp [Complex.ofReal_re]

theorem complex_norm_exp_I_mul (θ : ℝ) : ‖Complex.exp (θ * I)‖ = 1 := by
  simpa using Complex.norm_exp_ofReal_mul_I θ

/-! ## Trigonometric/logarithmic limits and monotonic consequences -/

theorem neg_log_sin_tendsto_atTop_at_zero_right :
    Filter.Tendsto (fun θ => - Real.log (Real.sin θ)) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  -- sin(θ) → 0⁺ as θ → 0⁺, so log(sin(θ)) → -∞, so -log(sin(θ)) → +∞
  -- Use: f → -∞ implies -f → +∞
  rw [← Filter.tendsto_neg_atBot_iff]
  simp only [neg_neg]
  -- Now need: log(sin θ) → -∞ as θ → 0⁺

  -- sin θ → 0 as θ → 0 (from continuity)
  have h_sin_tends_zero : Filter.Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_cont : Continuous Real.sin := Real.continuous_sin
    simpa [Real.sin_zero] using h_cont.tendsto 0 |>.mono_left nhdsWithin_le_nhds

  -- sin θ > 0 near 0⁺ (eventually)
  have h_sin_pos : ∀ᶠ θ in nhdsWithin 0 (Set.Ioi 0), 0 < Real.sin θ := by
    have h_Iio_pi : Set.Iio Real.pi ∈ nhds (0 : ℝ) := Iio_mem_nhds Real.pi_pos
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h_Iio_pi] with θ hθ_pos hθ_lt_pi
    exact Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi

  -- Combine: sin θ → 0⁺ as θ → 0⁺
  have h_sin_tends_zero_pos :
      Filter.Tendsto Real.sin (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h_sin_tends_zero, h_sin_pos⟩

  -- log x → -∞ as x → 0⁺
  have h_log_atBot := Real.tendsto_log_nhdsGT_zero

  -- Compose
  exact h_log_atBot.comp h_sin_tends_zero_pos

theorem theta_min_spec_inequality :
    ∀ (Amax θ : ℝ), 0 < Amax → 0 < θ → θ ≤ π/2 →
      (- Real.log (Real.sin θ) ≤ Amax) →
      θ ≥ Real.arcsin (Real.exp (-Amax)) := by
  intro Amax θ _hAmax hθpos hθle hlog
  have h1 : Real.log (Real.sin θ) ≥ -Amax := by linarith
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos (by linarith [Real.pi_pos])
  have h2 : Real.sin θ ≥ Real.exp (-Amax) := by
    have := Real.exp_log hsin_pos
    rw [← this]
    exact Real.exp_le_exp.mpr h1
  have h3 : Real.arcsin (Real.sin θ) = θ := by
    apply Real.arcsin_sin
    · linarith
    · linarith [Real.pi_pos]
  rw [← h3]
  exact Real.arcsin_le_arcsin h2

theorem theta_min_range :
    ∀ Amax > 0,
      0 < Real.arcsin (Real.exp (-Amax)) ∧ Real.arcsin (Real.exp (-Amax)) ≤ π/2 := by
  intro Amax hAmax
  constructor
  · rw [Real.arcsin_pos]
    exact Real.exp_pos _
  · exact Real.arcsin_le_pi_div_two _

theorem spherical_cap_measure_bounds :
    ∀ θmin ∈ Set.Icc (0 : ℝ) (Real.pi/2),
      0 ≤ (2 * Real.pi * (1 - Real.cos θmin)) :=
  spherical_cap_pos

/-! ## Complex Exponential Algebra -/

theorem complex_exp_mul_rearrange :
    ∀ (c₁ c₂ φ₁ φ₂ : ℝ),
      Complex.exp (-(c₁+c₂)/2) * Complex.exp ((φ₁+φ₂) * I) =
      (Complex.exp (-c₁/2) * Complex.exp (φ₁ * I)) * (Complex.exp (-c₂/2) * Complex.exp (φ₂ * I)) :=
  exp_mul_rearrange

/-!
NOTE: `continuousOn_extends_to_continuous` was removed because it is mathematically false.
Counterexample: `sin(1/x)` is continuous on `(0, ∞)` but has no continuous extension to `0`.
See `docs/FALSE_AXIOMS_ANALYSIS.md` for details.
-/

end ClassicalResults
end Cost
end IndisputableMonolith
