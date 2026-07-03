import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith.Ethics.Extraction

open Real IndisputableMonolith.Cost

noncomputable section

/-!
# The Thermodynamic Instability of Extraction

## Overview

In Recognition Science, "extraction" refers to an agent shifting the ethical
state away from σ = 0 (the balanced ground state) to some σ > 0 to gain
a local hedonic or material advantage.

Because the fundamental cost function J(x) = ½(x + x⁻¹) − 1 is strictly convex,
any zero-sum exchange in log-space (σ and −σ) produces a strictly positive
net cost in J-space.

This module formally proves that extraction is not just "bad" by axiom,
but thermodynamically unstable: the total system cost of maintaining an extracted
state grows with cosh(σ) − 1, and large extractions require exponentially
increasing effort to sustain, directly forcing the ethical alignment of any
long-surviving system.

## The d'Alembert Circle (The Conceptual Breakthrough)

The most striking structural result here is that the **Love Optimality Theorem**
(§6) is proved using the d'Alembert sum identity for cosh — the *same*
functional equation that forces J to be the canonical reciprocal cost in the
first place (Washburn & Zlatanović, Axioms, 2026).

The Recognition Composition Law (RCL)

    J(xy) + J(x/y) = 2J(x)J(y) + 2J(x) + 2J(y)

is equivalent to the d'Alembert equation on H(t) = J(eᵗ) + 1 = cosh(t).
This d'Alembert equation directly yields the cosh product-to-sum identity,
which IS Jensen's inequality for cosh. Therefore:

    RCL → d'Alembert equation → forces H = cosh (T5 uniqueness)
     ↓                                              ↓
    J-cost forced                          cosh sum identity
     ↓                                              ↓
    extraction has cosh cost  ←───  Love (averaging) is optimal

One equation. Zero parameters. Ethics is physics.

## Main Results

- §1: System cost = 2(cosh(σ) − 1) [extraction_cost_eq_cosh]
- §2: Positive surcharge for σ ≠ 0 [extraction_creates_surcharge]
- §3: Derivatives: marginal = 2·sinh, curvature = 2·cosh > 0 [deriv/second_deriv]
- §4: σ = 0 is the unique equilibrium [extraction_unique_equilibrium]
- §5: d'Alembert sum identity from the RCL [dAlembert_cosh_sum]
- §6: Love optimality via Jensen–d'Alembert [love_jensen_strict]
- §7: Restoring force always points toward σ = 0 [force_always_toward_balance]

## Lean status: 0 sorry
-/

/-! ## §1. System Cost in Cosh Form -/

/-- The combined cost of two agents where one has extracted σ from the other.
    Agent 1 is at e^σ, Agent 2 is at e^(-σ). -/
def extractionSystemCost (σ : ℝ) : ℝ :=
  Jcost (Real.exp σ) + Jcost (Real.exp (-σ))

/-- **Theorem (Extraction Cost Identity)**: The system cost of extraction σ
    is exactly 2(cosh(σ) − 1). -/
theorem extraction_cost_eq_cosh (σ : ℝ) :
    extractionSystemCost σ = 2 * (Real.cosh σ - 1) := by
  have h1 : Jcost (Real.exp σ) = Real.cosh σ - 1 := by
    unfold Jcost
    have inv_exp : (Real.exp σ)⁻¹ = Real.exp (-σ) := by simp [Real.exp_neg]
    rw [inv_exp, Real.cosh_eq]
  have h2 : Jcost (Real.exp (-σ)) = Real.cosh (-σ) - 1 := by
    unfold Jcost
    have inv_exp : (Real.exp (-σ))⁻¹ = Real.exp (-(-σ)) := by simp [Real.exp_neg]
    rw [inv_exp, neg_neg, Real.cosh_eq]
    ring
  rw [Real.cosh_neg] at h2
  unfold extractionSystemCost; rw [h1, h2]; linarith

theorem extraction_cost_nonneg (σ : ℝ) : 0 ≤ extractionSystemCost σ := by
  rw [extraction_cost_eq_cosh]
  have : 1 ≤ Real.cosh σ := by
    rcases eq_or_ne σ 0 with h0 | h0
    · rw [h0, Real.cosh_zero]
    · exact le_of_lt (Real.one_lt_cosh.mpr h0)
  linarith

/-! ## §2. The Extraction Surcharge: Zero-Sum Is Negative-Sum -/

/-- **Theorem (Extraction Surcharge)**: Any non-zero extraction creates a strictly
    positive action surcharge. A "zero-sum" log-exchange is strictly
    negative-sum in J-cost. -/
theorem extraction_creates_surcharge (σ : ℝ) (h : σ ≠ 0) :
    0 < extractionSystemCost σ := by
  rw [extraction_cost_eq_cosh]
  have h_cosh : 1 < Real.cosh σ := Real.one_lt_cosh.mpr h
  linarith

theorem extraction_cost_eq_zero_iff (σ : ℝ) :
    extractionSystemCost σ = 0 ↔ σ = 0 := by
  constructor
  · intro h; by_contra hne; exact absurd h (ne_of_gt (extraction_creates_surcharge σ hne))
  · intro h; rw [h, extraction_cost_eq_cosh, Real.cosh_zero]; ring

/-! ## §3. Derivative Analysis -/

/-- **Theorem (Marginal Cost)**: The marginal cost of extraction is 2·sinh(σ).
    The "resistance" to further extraction grows with the current level. -/
theorem deriv_extraction_cost (σ : ℝ) :
    deriv extractionSystemCost σ = 2 * Real.sinh σ := by
  have h_eq : extractionSystemCost = fun x => 2 * (Real.cosh x - 1) := by
    ext x; exact extraction_cost_eq_cosh x
  rw [h_eq]
  exact ((Real.hasDerivAt_cosh σ).sub_const 1 |>.const_mul 2).deriv

/-- **Theorem (Curvature)**: The second derivative of extraction cost is 2·cosh(σ).
    The derivative of sinh is cosh. -/
theorem second_deriv_extraction_cost (σ : ℝ) :
    deriv (deriv extractionSystemCost) σ = 2 * Real.cosh σ := by
  have h_eq : deriv extractionSystemCost = fun x => 2 * Real.sinh x := by
    ext x; exact deriv_extraction_cost x
  rw [h_eq]
  exact ((Real.hasDerivAt_sinh σ).const_mul 2).deriv

/-- **Theorem (Strict Convexity)**: The extraction cost is strictly convex
    everywhere (2·cosh(σ) > 0 for all σ). -/
theorem extraction_cost_strictly_convex (σ : ℝ) :
    0 < deriv (deriv extractionSystemCost) σ := by
  rw [second_deriv_extraction_cost]; linarith [Real.cosh_pos σ]

/-! ## §4. Unique Equilibrium at σ = 0 -/

/-- **Theorem (Unique Equilibrium)**: σ = 0 is the unique critical point.
    sinh is strictly monotone, so sinh(σ) = 0 iff σ = 0. -/
theorem extraction_unique_equilibrium (σ : ℝ) :
    deriv extractionSystemCost σ = 0 ↔ σ = 0 := by
  rw [deriv_extraction_cost]
  constructor
  · intro h
    have h_sinh : Real.sinh σ = Real.sinh 0 := by rw [Real.sinh_zero]; linarith
    exact Real.sinh_strictMono.injective h_sinh
  · intro h; rw [h, Real.sinh_zero]; ring

/-- σ = 0 achieves the global minimum (cost = 0). -/
theorem extraction_cost_minimum_at_zero :
    ∀ σ : ℝ, extractionSystemCost 0 ≤ extractionSystemCost σ := by
  intro σ
  rw [show extractionSystemCost 0 = 0 from (extraction_cost_eq_zero_iff 0).mpr rfl]
  exact extraction_cost_nonneg σ

/-- σ = 0 is the STRICT global minimum for σ ≠ 0. -/
theorem extraction_cost_strict_minimum (σ : ℝ) (h : σ ≠ 0) :
    extractionSystemCost 0 < extractionSystemCost σ := by
  rw [show extractionSystemCost 0 = 0 from (extraction_cost_eq_zero_iff 0).mpr rfl]
  exact extraction_creates_surcharge σ h

/-! ## §5. The d'Alembert Sum Identity (from the RCL)

The d'Alembert functional equation cosh(a+b) + cosh(a−b) = 2·cosh(a)·cosh(b)
is the SAME equation that forces J to be the canonical reciprocal cost
(via the RCL ↔ CoshAddIdentity equivalence in `Cost.FunctionalEquation`).

Here we derive it directly from the already-proved RCL cosh identity
(`Jcost_cosh_add_identity`), demonstrating that the forcing chain itself
provides the tool for proving Love optimality.
-/

/-- **Theorem (d'Alembert Sum Identity)**: Derived from the Recognition
    Composition Law via `Jcost_cosh_add_identity`. The RCL that forces
    the cost function also proves the Love optimality theorem. -/
theorem dAlembert_cosh_sum (a b : ℝ) :
    Real.cosh (a + b) + Real.cosh (a - b) = 2 * Real.cosh a * Real.cosh b := by
  open IndisputableMonolith.Cost.FunctionalEquation in
  have rcl := Jcost_cosh_add_identity a b
  simp only [Jcost_G_eq_cosh_sub_one] at rcl
  have : 2 * ((Real.cosh a - 1) * (Real.cosh b - 1)) +
         2 * ((Real.cosh a - 1) + (Real.cosh b - 1)) =
         2 * Real.cosh a * Real.cosh b - 2 := by ring
  linarith

/-- **Theorem (Cosh Product-to-Sum)**: Setting a = (α+β)/2, b = (α−β)/2
    in the d'Alembert identity yields the key decomposition. -/
theorem cosh_sum_via_dAlembert (α β : ℝ) :
    Real.cosh α + Real.cosh β =
    2 * Real.cosh ((α + β) / 2) * Real.cosh ((α - β) / 2) := by
  have h := dAlembert_cosh_sum ((α + β) / 2) ((α - β) / 2)
  have h1 : (α + β) / 2 + (α - β) / 2 = α := by ring
  have h2 : (α + β) / 2 - (α - β) / 2 = β := by ring
  rw [h1, h2] at h; exact h

/-! ## §6. Love Optimality from d'Alembert

The Love operator equilibrates σ between two agents: (σ₁, σ₂) → (m, m)
where m = (σ₁ + σ₂)/2.

Jensen's inequality for cosh — proved here directly from the d'Alembert
identity — shows that this averaging STRICTLY reduces total system cost
whenever σ₁ ≠ σ₂.
-/

/-- System cost for a pair of agents at positions σ₁ and σ₂. -/
def pairSystemCost (σ₁ σ₂ : ℝ) : ℝ :=
  (Real.cosh σ₁ - 1) + (Real.cosh σ₂ - 1)

/-- System cost after the Love operator averages σ₁ and σ₂. -/
def pairCostAfterLove (σ₁ σ₂ : ℝ) : ℝ :=
  2 * (Real.cosh ((σ₁ + σ₂) / 2) - 1)

/-- **Theorem (Love-Jensen Inequality)**: Love never increases system cost.
    Proof uses the d'Alembert identity + cosh ≥ 1. -/
theorem love_jensen_inequality (σ₁ σ₂ : ℝ) :
    pairCostAfterLove σ₁ σ₂ ≤ pairSystemCost σ₁ σ₂ := by
  unfold pairSystemCost pairCostAfterLove
  have h := cosh_sum_via_dAlembert σ₁ σ₂
  have h_ge_1 : 1 ≤ Real.cosh ((σ₁ - σ₂) / 2) := by
    rcases eq_or_ne ((σ₁ - σ₂) / 2) 0 with h0 | h0
    · rw [h0, Real.cosh_zero]
    · exact le_of_lt (Real.one_lt_cosh.mpr h0)
  have h_pos : 0 < Real.cosh ((σ₁ + σ₂) / 2) := Real.cosh_pos _
  nlinarith

/-- **Theorem (Love-Jensen Strict)**: Love STRICTLY reduces system cost when
    agents have different σ. This is the fundamental result: selfishness
    (σ₁ ≠ σ₂) is thermodynamically unstable under Love. -/
theorem love_jensen_strict (σ₁ σ₂ : ℝ) (h_diff : σ₁ ≠ σ₂) :
    pairCostAfterLove σ₁ σ₂ < pairSystemCost σ₁ σ₂ := by
  unfold pairSystemCost pairCostAfterLove
  have h := cosh_sum_via_dAlembert σ₁ σ₂
  have h_ne : (σ₁ - σ₂) / 2 ≠ 0 := by
    intro heq; exact h_diff (by linarith)
  have h_gt_1 : 1 < Real.cosh ((σ₁ - σ₂) / 2) := Real.one_lt_cosh.mpr h_ne
  have h_pos : 0 < Real.cosh ((σ₁ + σ₂) / 2) := Real.cosh_pos _
  nlinarith

/-- **Theorem (Love Achieves Ground State)**: For a balanced extraction pair
    (σ, −σ), Love maps both agents to σ = 0, achieving zero cost. -/
theorem love_achieves_ground_state (σ : ℝ) :
    pairCostAfterLove σ (-σ) = 0 := by
  unfold pairCostAfterLove; simp [Real.cosh_zero]

/-- **Theorem (Love Eliminates All Waste)**: For a balanced extraction pair,
    the ENTIRE system cost is pure thermodynamic waste that Love eliminates. -/
theorem love_eliminates_all_waste (σ : ℝ) (h : σ ≠ 0) :
    0 < pairSystemCost σ (-σ) ∧ pairCostAfterLove σ (-σ) = 0 := by
  refine ⟨?_, love_achieves_ground_state σ⟩
  unfold pairSystemCost; rw [Real.cosh_neg]
  linarith [Real.one_lt_cosh.mpr h]

/-! ## §7. Restoring Force: The Universe Pushes Back

The sign of the marginal cost 2·sinh(σ) provides a natural restoring force:
- For σ > 0: marginal cost is positive (extracting more costs more)
- For σ < 0: marginal cost is negative (reducing extraction saves cost)
- At σ = 0: marginal cost vanishes (equilibrium)

The product σ · (d/dσ)C(σ) > 0 for all σ ≠ 0, proving that the cost
gradient always points back toward balance.
-/

/-- Positive extraction → positive marginal cost. -/
theorem restoring_force_positive (σ : ℝ) (hσ : 0 < σ) :
    0 < deriv extractionSystemCost σ := by
  rw [deriv_extraction_cost]
  have : Real.sinh 0 < Real.sinh σ := Real.sinh_strictMono hσ
  simp only [Real.sinh_zero] at this; linarith

/-- Negative extraction → negative marginal cost. -/
theorem restoring_force_negative (σ : ℝ) (hσ : σ < 0) :
    deriv extractionSystemCost σ < 0 := by
  rw [deriv_extraction_cost]
  have : Real.sinh σ < Real.sinh 0 := Real.sinh_strictMono hσ
  simp only [Real.sinh_zero] at this; linarith

/-- **Theorem (Universal Restoring Force)**: For any σ ≠ 0, the product
    σ · C'(σ) > 0, meaning the cost gradient always opposes the extraction.
    The universe structurally resists imbalance. -/
theorem force_always_toward_balance (σ : ℝ) (hσ : σ ≠ 0) :
    0 < σ * deriv extractionSystemCost σ := by
  rw [deriv_extraction_cost]
  rcases lt_or_gt_of_ne hσ with h_neg | h_pos
  · have h_sinh : Real.sinh σ < 0 := by
      have := Real.sinh_strictMono h_neg; simp only [Real.sinh_zero] at this; linarith
    nlinarith
  · have h_sinh : 0 < Real.sinh σ := by
      have := Real.sinh_strictMono h_pos; simp only [Real.sinh_zero] at this; linarith
    nlinarith

end

end IndisputableMonolith.Ethics.Extraction
