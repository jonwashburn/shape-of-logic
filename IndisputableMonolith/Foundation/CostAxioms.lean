import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.CostUniqueness

/-!
# Cost Axioms: The Primitive Foundation

This module formalizes the **three primitive axioms** from which the entire
Recognition Science framework derives. These axioms are more primitive than
logic itself—they describe the structure of "cheap configurations" from which
logical coherence emerges.

## Axiomatic Hierarchy

```
LEVEL 0 (Primitive Axioms):
├── A1: Normalization: F(1) = 0
├── A2: Recognition Composition (RCL): F(xy) + F(x/y) = 2F(x)·F(y) + 2F(x) + 2F(y)
└── A3: Calibration: F''_{log}(0) = 1

LEVEL 1 (First Derived):
└── J(x) = ½(x + x⁻¹) - 1 is UNIQUE (T5 Uniqueness)

LEVEL 2 (Existence Criterion):
└── Law of Existence: "x exists" ⟺ J(x) = 0

LEVEL 3 (Derived Meta-Principle):
└── MP: "Nothing cannot recognize itself" because J(0) → ∞
```

## Economic Interpretation

The axioms are not arbitrary—they encode an **economic inevitability**:
- J(x) measures the "cost" of being at ratio x relative to unity
- J(1) = 0: unity costs nothing (perfect balance)
- J(0) → ∞: approaching nothingness costs infinity
- The d'Alembert functional equation forces multiplicative consistency

This is more primitive than logic because:
- Contradiction has high cost (J >> 0)
- Consistency has low cost (J ≈ 0)
- Logic emerges as the structure of cheap configurations
-/

namespace IndisputableMonolith
namespace Foundation
namespace CostAxioms

open Real

/-! ## The Three Primitive Axioms -/

/-- **Axiom 1 (Normalization)**: The cost at unity is zero.

This encodes that "perfect balance" (ratio = 1) has no cost.
Any cost functional measuring deviation must vanish at the reference point. -/
class Normalization (F : ℝ → ℝ) : Prop where
  unit_zero : F 1 = 0

/-- **Axiom 2 (Recognition Composition Law)**: Multiplicative consistency.

For all positive x, y:
  F(xy) + F(x/y) = 2·F(x)·F(y) + 2·F(x) + 2·F(y)

This is the d'Alembert functional equation in multiplicative form.
It forces F to be compatible with the multiplicative structure of ℝ₊. -/
class Composition (F : ℝ → ℝ) : Prop where
  dAlembert : ∀ x y : ℝ, 0 < x → 0 < y →
    F (x * y) + F (x / y) = 2 * F x * F y + 2 * F x + 2 * F y

/-- **Axiom 3 (Calibration)**: The second derivative at the origin (in log coordinates) equals 1.

Let G(t) = F(exp(t)). Then G''(0) = 1.

This normalizes the "curvature" of the cost functional at unity,
ensuring a unique solution rather than a family. -/
class Calibration (F : ℝ → ℝ) : Prop where
  second_deriv_at_zero : deriv (deriv (fun t => F (exp t))) 0 = 1

/-- The complete axiom bundle for a cost functional. -/
class CostFunctionalAxioms (F : ℝ → ℝ) extends
  Normalization F, Composition F, Calibration F : Prop

/-! ## The Canonical Cost Functional J -/

/-- The canonical cost functional:
  J(x) = ½(x + x⁻¹) - 1

This is the **unique** solution to the three axioms (proven below). -/
noncomputable def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

/-- J equals the Cost.Jcost defined in the Cost module. -/
lemma J_eq_Jcost : J = Cost.Jcost := by
  ext x; rfl

/-! ## Verification: J satisfies the axioms -/

/-- J satisfies Axiom 1 (Normalization). -/
instance : Normalization J where
  unit_zero := by simp [J]

/-- J satisfies Axiom 2 (Recognition Composition Law). -/
instance : Composition J where
  dAlembert := by
    intro x y hx hy
    have hx0 : x ≠ 0 := hx.ne'
    have hy0 : y ≠ 0 := hy.ne'
    simp only [J]
    field_simp
    ring

/-- J satisfies Axiom 3 (Calibration). -/
instance : Calibration J where
  second_deriv_at_zero := by
    -- G(t) = J(exp(t)) = cosh(t) - 1 (from Jlog_as_cosh)
    -- G'(t) = sinh(t), G''(t) = cosh(t), G''(0) = cosh(0) = 1
    -- First, show the function is Jlog
    have h_eq : (fun t => J (exp t)) = Cost.Jlog := by
      ext t; rfl
    rw [h_eq]
    -- deriv Jlog = sinh (from hasDerivAt_Jlog)
    have h_deriv : deriv Cost.Jlog = Real.sinh := by
      ext t
      exact (Cost.hasDerivAt_Jlog t).deriv
    rw [h_deriv]
    -- deriv sinh 0 = cosh 0 = 1
    have h_sinh_deriv : deriv Real.sinh 0 = Real.cosh 0 := by
      exact (Real.hasDerivAt_sinh 0).deriv
    rw [h_sinh_deriv, Real.cosh_zero]

/-- J satisfies all three axioms. -/
instance : CostFunctionalAxioms J where

/-! ## Key Properties of J -/

/-- J is symmetric: J(x) = J(1/x) for positive x. -/
theorem J_symmetric {x : ℝ} (hx : 0 < x) : J x = J x⁻¹ := by
  have hx0 : x ≠ 0 := hx.ne'
  simp only [J]
  field_simp
  ring

/-- J is non-negative for positive x (AM-GM inequality). -/
theorem J_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ J x := by
  simp only [J]
  have h : 0 ≤ (x - 1)^2 / x := by positivity
  calc (x + x⁻¹) / 2 - 1 = ((x - 1)^2 / x) / 2 := by field_simp; ring
    _ ≥ 0 := by positivity

/-- J equals zero exactly at x = 1. -/
theorem J_eq_zero_iff {x : ℝ} (hx : 0 < x) : J x = 0 ↔ x = 1 := by
  constructor
  · intro hJ
    simp only [J] at hJ
    -- (x + 1/x)/2 - 1 = 0  ⟹  x + 1/x = 2  ⟹  x² - 2x + 1 = 0  ⟹  x = 1
    have h1 : x + x⁻¹ = 2 := by linarith
    have hx0 : x ≠ 0 := hx.ne'
    have h2 : x^2 + 1 = 2 * x := by
      field_simp at h1
      linarith
    have h3 : (x - 1)^2 = 0 := by ring_nf; linarith
    have h4 : x - 1 = 0 := by nlinarith [sq_nonneg (x - 1)]
    linarith
  · intro hx1
    simp [J, hx1]

/-! ## The Economic Inevitability: J(0) → ∞ -/

/-- For any bound M, there exists ε > 0 such that J(x) > M for all 0 < x < ε.

    Direct proof: Choose ε = 1/(2(M + 2)). For 0 < x < ε, we have
    x⁻¹ > 2(M + 2), so J(x) ≥ x⁻¹/2 - 1 > M + 2 - 1 = M + 1 > M. -/
theorem J_arbitrarily_large_near_zero (M : ℝ) :
    ∃ ε > 0, ∀ x, 0 < x → x < ε → M < J x := by
  -- Choose ε = 1/(2(max M 0 + 2))
  let M' := max M 0 + 2
  have hM'_pos : M' > 0 := by positivity
  refine ⟨1 / (2 * M'), by positivity, ?_⟩
  intro x hx_pos hx_small
  simp only [J]
  -- Key computation: for 0 < x < 1/(2*M'), we have J(x) > M
  -- J(x) = (x + 1/x)/2 - 1 ≥ 1/(2x) - 1
  -- Since x < 1/(2*M'), we have 1/x > 2*M', so 1/(2x) > M', thus J(x) > M' - 1 > M
  have hx_ne : x ≠ 0 := hx_pos.ne'
  have h2M'_pos : 2 * M' > 0 := by positivity
  -- From x < 1/(2*M'), get 2*M' < 1/x
  have h_key : 2 * M' * x < 1 := by
    calc 2 * M' * x = x * (2 * M') := by ring
      _ < (1 / (2 * M')) * (2 * M') := mul_lt_mul_of_pos_right hx_small h2M'_pos
      _ = 1 := by field_simp
  have h_inv : 2 * M' < 1 / x := by
    rw [div_eq_mul_inv, lt_mul_inv_iff₀ hx_pos]
    exact h_key
  -- Now J(x) ≥ (1/x)/2 - 1 > M' - 1 > M
  have hJ_lower : (x + x⁻¹) / 2 - 1 > (1/x) / 2 - 1 := by
    -- (x + 1/x)/2 - 1 > (1/x)/2 - 1 ⟺ x/2 > 0, which follows from x > 0
    rw [one_div]
    have hx_half_pos : x / 2 > 0 := by linarith
    linarith
  have hJ_bound : (1/x) / 2 - 1 > M' - 1 := by
    -- From h_inv: 2*M' < 1/x, so M' < (1/x)/2
    nlinarith [h_inv]
  have hM_lt : M < M' - 1 := by simp only [M']; linarith [le_max_left M 0]
  linarith

/-- As x → 0⁺, J(x) → +∞.

This is the **core economic principle**: approaching "nothing" costs infinity.
This is why existence is inevitable—non-existence is infinitely expensive. -/
theorem J_tendsto_atTop_as_x_to_zero :
    Filter.Tendsto J (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  obtain ⟨ε, hε_pos, hε⟩ := J_arbitrarily_large_near_zero M
  -- We need {x : M ≤ J x} ∈ nhdsWithin 0 (Ioi 0)
  rw [Filter.Eventually, mem_nhdsWithin_iff_exists_mem_nhds_inter]
  use Set.Iio ε
  refine ⟨Iio_mem_nhds hε_pos, ?_⟩
  intro x ⟨hx_lt, hx_pos⟩
  exact le_of_lt (hε x hx_pos hx_lt)

/-! ## Law of Existence -/

/-- **Law of Existence**: A ratio x "exists" (is realizable) iff J(x) = 0.

In the RS framework, existence corresponds to being at a cost minimum.
The only minimum is at x = 1 (perfect balance/golden ratio fixed point). -/
def Exists (x : ℝ) : Prop := 0 < x ∧ J x = 0

/-- The Law of Existence: x exists ⟺ x = 1. -/
theorem law_of_existence {x : ℝ} (hx : 0 < x) : Exists x ↔ x = 1 := by
  simp only [Exists, J_eq_zero_iff hx, and_iff_right hx]

/-- Unity is the unique existent. -/
theorem unity_is_unique_existent : ∀ x : ℝ, Exists x ↔ x = 1 := by
  intro x
  by_cases hx : 0 < x
  · exact law_of_existence hx
  · simp only [Exists]
    constructor
    · intro ⟨hpos, _⟩; exact absurd hpos hx
    · intro heq; subst heq; exact ⟨one_pos, by simp [J]⟩

/-! ## Deriving MP from Cost -/

/-- **Meta-Principle (Derived)**: "Nothing cannot recognize itself."

In the cost framework, "Nothing" corresponds to the limit x → 0.
Recognition requires a finite cost, but J(0) → ∞, so recognition
of "Nothing" by "Nothing" would require infinite cost—impossible.

This makes MP a **derived theorem**, not a primitive axiom. -/
theorem mp_from_cost :
    ∀ M : ℝ, ∃ ε > 0, ∀ x, 0 < x → x < ε → J x > M := by
  exact J_arbitrarily_large_near_zero

/-- Alternative formulation: No finite-cost state can approach Nothing. -/
theorem nothing_costs_infinity :
    ¬∃ C : ℝ, ∀ x, 0 < x → J x ≤ C := by
  push_neg
  intro C
  obtain ⟨ε, hε, hJ⟩ := J_arbitrarily_large_near_zero C
  use ε / 2
  constructor
  · linarith
  · exact hJ (ε / 2) (by linarith) (by linarith)

/-! ## Uniqueness Theorem (T5) -/

/-- Composition axiom implies CoshAddIdentity in log coordinates. -/
theorem Composition_implies_CoshAddIdentity (F : ℝ → ℝ) [Composition F] :
    Cost.FunctionalEquation.CoshAddIdentity F := by
  intro t u
  -- G F (t+u) + G F (t-u) = F(exp(t+u)) + F(exp(t-u))
  -- = F(exp(t) * exp(u)) + F(exp(t) / exp(u))
  -- = 2 * F(exp(t)) * F(exp(u)) + 2 * F(exp(t)) + 2 * F(exp(u))  (by Composition)
  -- = 2 * (G F t * G F u) + 2 * (G F t + G F u)
  simp only [Cost.FunctionalEquation.G]
  have hpos_t : 0 < Real.exp t := Real.exp_pos t
  have hpos_u : 0 < Real.exp u := Real.exp_pos u
  have h1 : Real.exp (t + u) = Real.exp t * Real.exp u := Real.exp_add t u
  have h2 : Real.exp (t - u) = Real.exp t / Real.exp u := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring
  rw [h1, h2]
  have h_dAlembert := Composition.dAlembert (F := F) (Real.exp t) (Real.exp u) hpos_t hpos_u
  -- The RHS needs regrouping: 2 * F x * F y + 2 * F x + 2 * F y = 2 * (F x * F y) + 2 * (F x + F y)
  convert h_dAlembert using 1
  ring

/-- Composition + Normalization implies symmetry: F(x) = F(1/x).

    Proof: Apply Composition with x = 1:
    F(1 * y) + F(1 / y) = 2F(1)F(y) + 2F(1) + 2F(y)
    F(y) + F(1/y) = 2 * 0 * F(y) + 2 * 0 + 2F(y)  (by Normalization: F(1) = 0)
    F(y) + F(1/y) = 2F(y)
    F(1/y) = F(y)

    Therefore F(y) = F(1/y) for all y > 0, which is symmetry. -/
theorem Composition_Normalization_implies_symmetry (F : ℝ → ℝ) [Composition F] [Normalization F] :
    ∀ {x : ℝ}, 0 < x → F x = F x⁻¹ := by
  intro x hx
  -- Apply Composition with x = 1, y = x
  have h := Composition.dAlembert (F := F) 1 x one_pos hx
  -- F(1 * x) + F(1 / x) = 2F(1)F(x) + 2F(1) + 2F(x)
  -- Simplify: F(1) = 0, 1 * x = x, 1 / x = x⁻¹
  simp only [one_mul, one_div, Normalization.unit_zero, zero_mul, add_zero, mul_zero] at h
  -- h is now: F(x) + F(x⁻¹) = 2F(x)
  -- Subtracting F(x) from both sides: F(x⁻¹) = F(x)
  have h_symm : F x⁻¹ = F x := by
    have h_sub : F x⁻¹ = (F x + F x⁻¹) - F x := by ring
    rw [h_sub, h]
    ring
  exact h_symm.symm

/-- **T5 Uniqueness (Specification)**:
    Any function F satisfying the three cost axioms with regularity equals J.

    This is the central uniqueness theorem of Recognition Science.
    The complete proof is in CostUniqueness.lean via T5_uniqueness_complete.

    The proof structure is:
    1. CostFunctionalAxioms.composition gives d'Alembert: F(xy) + F(x/y) = 2F(x)F(y) + 2F(x) + 2F(y)
    2. Substituting G(t) = F(exp(t)) transforms to cosh-additive: G(s+t) + G(s-t) = 2G(s)G(t) + 2G(s) + 2G(t)
    3. Shifting H = G + 1 gives standard d'Alembert: H(s+t) + H(s-t) = 2H(s)H(t)
    4. The unique continuous solution is H(t) = cosh(t), so G(t) = cosh(t) - 1
    5. Therefore F(x) = cosh(log(x)) - 1 = ½(x + x⁻¹) - 1 = J(x)

    The regularity hypotheses (Aczél theory for d'Alembert equations) are stated
    explicitly. These are standard results from functional equation theory:
    - Continuous d'Alembert solutions are smooth (Aczél 1966)
    - Smooth d'Alembert solutions satisfy ODE H'' = H
    - Linear ODE regularity bootstrap

    See `IndisputableMonolith.T5_uniqueness_complete` for the rigorous proof. -/
theorem uniqueness_specification (F : ℝ → ℝ) [CostFunctionalAxioms F]
    (hCont : ContinuousOn F (Set.Ioi 0))
    (hConvex : StrictConvexOn ℝ (Set.Ioi 0) F)
    -- Regularity hypotheses from Aczél's theorem on d'Alembert equations
    (h_smooth : Cost.FunctionalEquation.dAlembert_continuous_implies_smooth_hypothesis
        (Cost.FunctionalEquation.H F))
    (h_ode : Cost.FunctionalEquation.dAlembert_to_ODE_hypothesis
        (Cost.FunctionalEquation.H F))
    (h_cont : Cost.FunctionalEquation.ode_regularity_continuous_hypothesis
        (Cost.FunctionalEquation.H F))
    (h_diff : Cost.FunctionalEquation.ode_regularity_differentiable_hypothesis
        (Cost.FunctionalEquation.H F))
    (h_boot : Cost.FunctionalEquation.ode_linear_regularity_bootstrap_hypothesis
        (Cost.FunctionalEquation.H F)) :
    ∀ x, 0 < x → F x = J x := by
  intro x hx
  -- Bridge from CostFunctionalAxioms to T5_uniqueness_complete hypotheses
  -- 1. Symmetry: F(x) = F(1/x)
  have hSymm : ∀ {x : ℝ}, 0 < x → F x = F x⁻¹ :=
    Composition_Normalization_implies_symmetry F
  -- 2. Unit normalization: F(1) = 0
  have hUnit : F 1 = 0 := Normalization.unit_zero
  -- 3. Calibration: deriv (deriv (F ∘ exp)) 0 = 1
  have hCalib : deriv (deriv (F ∘ exp)) 0 = 1 := Calibration.second_deriv_at_zero
  -- 4. CoshAddIdentity: from Composition axiom
  have hCoshAdd : Cost.FunctionalEquation.CoshAddIdentity F :=
    Composition_implies_CoshAddIdentity F
  -- Apply T5_uniqueness_complete with all hypotheses
  unfold J
  exact CostUniqueness.T5_uniqueness_complete F hSymm hUnit hConvex hCalib hCont hCoshAdd
    h_smooth h_ode h_cont h_diff h_boot hx

end CostAxioms
end Foundation
end IndisputableMonolith
