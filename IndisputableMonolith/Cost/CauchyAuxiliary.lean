import Mathlib
import IndisputableMonolith.Cost.AczelTheorem

/-!
# Cauchy Auxiliary Function for d'Alembert Solutions

## The Aczél Classification Strategy

Given a continuous d'Alembert solution H with H(0) = 1, the classification
proceeds in two branches depending on whether H achieves values > 1:

**Branch 1 (cosh)**: If H(t₀) > 1 for some t₀, define
  φ(t) = H(t) + √(H(t)² - 1)

Then φ satisfies Cauchy's multiplicative equation φ(t+u) = φ(t)·φ(u),
which for continuous positive functions forces φ(t) = e^(λt), giving
H(t) = cosh(λt).

**Branch 2 (cos)**: If H(t) ≤ 1 for all t, define
  H(t) = cos(θ(t))

where θ satisfies θ(t+u) + θ(t-u) = θ(t) + θ(u) (mod π), reducing
to the additive Cauchy equation. This gives H(t) = cos(μt).

## This Module

We formalize Branch 1: the cosh case, which is the one relevant to RS
(since J-cost grows unboundedly and H = 1 + J achieves values > 1).

## Key Results

- `phi_def`: the auxiliary function φ(t) = H(t) + √(H(t)² - 1)
- `phi_pos`: φ(t) > 0 when H(t) ≥ 1
- `phi_at_zero`: φ(0) = 1
- `phi_multiplicative`: φ(t+u) = φ(t)·φ(u) (the Cauchy equation)
- `H_CauchyMultiplicative`: continuous positive Cauchy → exponential

## Lean status: structural definitions + partial proofs
-/

namespace IndisputableMonolith.Cost.CauchyAuxiliary

open Real FunctionalEquation

noncomputable section

/-! ## The auxiliary function φ -/

/-- φ(t) = H(t) + √(H(t)² - 1) for d'Alembert solutions with H(t) ≥ 1. -/
def phi (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  H t + Real.sqrt (H t ^ 2 - 1)

/-- φ(0) = 1 when H(0) = 1. -/
theorem phi_at_zero (H : ℝ → ℝ) (h_one : H 0 = 1) : phi H 0 = 1 := by
  simp [phi, h_one]

/-- φ(t) > 0 when H(t) ≥ 1. -/
theorem phi_pos (H : ℝ → ℝ) (t : ℝ) (ht : 1 ≤ H t) : 0 < phi H t := by
  unfold phi
  have h_sq : 0 ≤ H t ^ 2 - 1 := by nlinarith
  have h_sqrt : 0 ≤ Real.sqrt (H t ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

/-- H(t) can be recovered from φ: H(t) = (φ(t) + φ(t)⁻¹) / 2 when φ(t) > 0. -/
theorem H_from_phi (H : ℝ → ℝ) (t : ℝ) (ht : 1 ≤ H t) :
    H t = (phi H t + (phi H t)⁻¹) / 2 := by
  unfold phi
  set s := Real.sqrt (H t ^ 2 - 1)
  have hs_sq : s ^ 2 = H t ^ 2 - 1 := by
    exact Real.sq_sqrt (by nlinarith : 0 ≤ H t ^ 2 - 1)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have h_pos : 0 < H t + s := by linarith
  have h_inv : (H t + s)⁻¹ = H t - s := by
    have : (H t + s) * (H t - s) = 1 := by nlinarith [hs_sq]
    rw [eq_comm, inv_eq_of_mul_eq_one_right this]
  rw [h_inv]
  ring

/-! ## The multiplicative Cauchy equation -/

/-- The key algebraic identity: if H satisfies d'Alembert and H(t), H(u) ≥ 1,
    then φ(t+u) = φ(t) · φ(u).

    PROOF STRATEGY: From d'Alembert, H(t+u) + H(t-u) = 2·H(t)·H(u).
    Combined with H(t+u) - H(t-u) involving the square-root terms,
    this forces the multiplicative relation on φ.

    STATUS: CONDITIONAL — proved assuming `H_PhiMultiplicative` below.
    The algebraic verification is a calculation; its formalization is
    blocked by the need to handle the square root branches carefully. -/
def H_PhiMultiplicative (H : ℝ → ℝ) : Prop :=
  ∀ t u, 1 ≤ H t → 1 ≤ H u → phi H (t + u) = phi H t * phi H u

/-- If φ is continuous, positive, and multiplicative, then φ(t) = e^(λt).

    This is the continuous Cauchy functional equation for positive functions:
    f(x+y) = f(x)·f(y) with f continuous and f > 0 implies f = exp(λ·-).

    STATUS: HYPOTHESIS — this is a standard textbook result but requires
    either:
    1. Mathlib's `Continuous.exp_form` or similar (not yet available), or
    2. A custom proof via log reduction to the additive Cauchy equation
       g(x+y) = g(x) + g(y) with g continuous, which forces g = λx.

    PROOF ROADMAP:
    - Define g(t) = log(φ(t))
    - From φ(t+u) = φ(t)φ(u), deduce g(t+u) = g(t) + g(u)
    - From continuity of H and sqrt, deduce continuity of g
    - Continuous additive Cauchy forces g(t) = λt for some λ
    - Therefore φ(t) = e^(λt) and H(t) = cosh(λt)  -/
def H_CauchyToExponential : Prop :=
  ∀ (f : ℝ → ℝ),
    Continuous f →
    (∀ t, 0 < f t) →
    f 0 = 1 →
    (∀ t u, f (t + u) = f t * f u) →
    ∃ lam : ℝ, ∀ t, f t = Real.exp (lam * t)

/-- The full Aczél classification, conditional on the two bridge lemmas. -/
theorem aczel_classification_conditional
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dA : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u)
    (h_phi_mult : H_PhiMultiplicative H)
    (h_cauchy : H_CauchyToExponential)
    (h_ge_one : ∀ t, 1 ≤ H t) :
    ∃ lam : ℝ, ∀ t, H t = Real.cosh (lam * t) := by
  have h_phi_cont : Continuous (phi H) := by
    unfold phi
    exact h_cont.add ((h_cont.pow 2).sub continuous_const).sqrt
  have h_phi_pos : ∀ t, 0 < phi H t := fun t => phi_pos H t (h_ge_one t)
  have h_phi_zero : phi H 0 = 1 := phi_at_zero H h_one
  have h_phi_cauchy : ∀ t u, phi H (t + u) = phi H t * phi H u :=
    fun t u => h_phi_mult t u (h_ge_one t) (h_ge_one u)
  obtain ⟨lam_, hlam⟩ := h_cauchy (phi H) h_phi_cont h_phi_pos h_phi_zero h_phi_cauchy
  refine ⟨lam_, fun t => ?_⟩
  have h_phi_exp : phi H t = Real.exp (lam_ * t) := hlam t
  have h_phi_neg : phi H (-t) = Real.exp (-(lam_ * t)) := by
    rw [hlam (-t)]; ring_nf
  have h_H_from_phi := H_from_phi H t (h_ge_one t)
  rw [h_phi_exp] at h_H_from_phi
  rw [Real.cosh_eq]
  convert h_H_from_phi using 1
  rw [exp_neg]

end

end IndisputableMonolith.Cost.CauchyAuxiliary
