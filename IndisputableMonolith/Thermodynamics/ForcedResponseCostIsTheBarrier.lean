/-
# Linearity and its sign are consequences, not choices

`ForcedResponseCostDeterminedActivity` closed the derivation hole by ASSUMING that the
direction-blind traffic is linear in the recognition cost, and then took the SIGN of the
proportionality constant from Marcus theory's linear response. Both of those were weaknesses of a
recognizable kind: a premise chosen because it works, and a sign borrowed from the theory the law is
supposed to be tested against.

This module removes both.

## What replaces the assumed linearity

The physical identification is that the mean barrier of an elementary step IS the recognition cost of
the step's distinction, expressed in thermal units. Call the conversion `B`, so that

  `mean barrier / kT = B (recognition cost)`.

Three properties of `B` follow from what a cost is rather than from what we want:

* ADDITIVITY. Recognition costs of independent acts add; that additivity is the composition law that
  forced `J` in the first place. So a compound recognition of total cost `u + v` must convert to
  `B u + B v`, since otherwise the same physical barrier would depend on how the accounting was
  grouped.
* CONTINUITY. A barrier varies continuously with the cost of the rearrangement it represents.
* MONOTONICITY. A larger recognition cost is a larger barrier, never a smaller one.

Additivity with continuity forces `B u = B 1 * u` (Cauchy's equation, via Mathlib's
`AddMonoidHom.toRealLinearMap`). Monotonicity forces `0 <= B 1`. So linearity is a theorem, and the
proportionality constant is nonnegative.

## Why the sign matters so much

With `P A = P 0 - B (cost A)` and `B 1 >= 0`, the traffic FALLS as the drive grows, so the transfer
coefficient DECREASES and reaches zero at a finite drive. That is the barrierless point. Two earlier
passes of this campaign carried the opposite sign, copied from an electrochemistry sign convention,
which had the barrierless point moving outward instead of inward. Here the direction is forced by the
single fact that a cost is nonnegative, with no appeal to Marcus theory at any step.

The subtraction in `P A = P 0 - B (cost A)` is not a further choice: a barrier suppresses a rate, so
`log rate = log prefactor - barrier`, and `P` is the mean of the two log rates.

## What is still not derived

The scale `b` inside the cost, that is what drive counts as one unit of recognition. The gate
FRL-COLLAPSE-20260725 bounded it from below by measurement (`b` is at least several times the
reorganization scale), which is now the sharpest external constraint the campaign holds.
-/

import Mathlib
import IndisputableMonolith.Thermodynamics.ForcedResponseCostDeterminedActivity

namespace IndisputableMonolith
namespace Thermodynamics
namespace ForcedResponseCostIsTheBarrier

open Real
open IndisputableMonolith.Thermodynamics.ForcedResponseDetailedBalanceNormalForm
open IndisputableMonolith.Thermodynamics.ForcedResponseCostDeterminedActivity

/-! ## The conversion from recognition cost to thermal barrier -/

/-- The properties a cost-to-barrier conversion has by virtue of being one. Additivity is the
composition law that forced the cost functional; continuity and monotonicity say that a barrier
varies continuously with, and increases with, the cost of the rearrangement it represents. -/
structure IsBarrierConversion (B : ℝ → ℝ) : Prop where
  additive : ∀ u v : ℝ, B (u + v) = B u + B v
  cont : Continuous B
  mono : Monotone B

/-- **Additivity with continuity forces linearity.** This is Cauchy's functional equation; the
content is that no nonlinear conversion can respect the additivity of cost, because then the same
physical barrier would depend on how the cost accounting was grouped. -/
theorem linear_of_isBarrierConversion {B : ℝ → ℝ} (h : IsBarrierConversion B) (u : ℝ) :
    B u = B 1 * u := by
  have homog : ∀ r x : ℝ, B (r * x) = r * B x := by
    intro r x
    have hsm :=
      (AddMonoidHom.toRealLinearMap
        (AddMonoidHom.mk' B (fun a b => h.additive a b)) h.cont).map_smul r x
    simpa [smul_eq_mul] using hsm
  have h1 := homog u 1
  rw [mul_one] at h1
  rw [h1]
  ring

/-- A conversion sends zero cost to zero barrier. -/
theorem map_zero_of_isBarrierConversion {B : ℝ → ℝ} (h : IsBarrierConversion B) :
    B 0 = 0 := by
  have := h.additive 0 0
  simp at this
  linarith

/-- **Monotonicity forces the constant to be nonnegative.** This is where the SIGN of the whole
prediction comes from, and it comes from nothing more than the fact that more cost is more barrier. -/
theorem const_nonneg_of_isBarrierConversion {B : ℝ → ℝ} (h : IsBarrierConversion B) :
    0 ≤ B 1 := by
  have h0 : B 0 = 0 := map_zero_of_isBarrierConversion h
  have := h.mono (by norm_num : (0 : ℝ) ≤ 1)
  linarith [h0, this]

/-! ## The traffic, with its form and sign both derived -/

/-- The direction-blind traffic when the mean barrier is the recognition cost converted to thermal
units. A barrier suppresses a rate, hence the subtraction. -/
noncomputable def barrierTraffic (P0 : ℝ) (B : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun A => P0 - B (recognitionCost b A)

/-- **The derived law.** With the conversion forced linear, the traffic is `P0 - B 1 * (cosh (A/b) - 1)`,
which is exactly `costActivity` with `c = -(B 1)`. So the shape that the previous module had to assume
is here a consequence, and the constant is pinned to be nonpositive. -/
theorem barrierTraffic_eq_costActivity {P0 : ℝ} {B : ℝ → ℝ} (h : IsBarrierConversion B) (b : ℝ) :
    barrierTraffic P0 B b = costActivity P0 (-(B 1)) b := by
  funext A
  simp only [barrierTraffic, costActivity]
  rw [linear_of_isBarrierConversion h]
  ring

/-- The traffic is even in the drive, because the recognition cost is. -/
theorem barrierTraffic_even {P0 : ℝ} {B : ℝ → ℝ} {b : ℝ} (hb : b ≠ 0) (A : ℝ) :
    barrierTraffic P0 B b (-A) = barrierTraffic P0 B b A := by
  simp only [barrierTraffic, recognitionCost, neg_div, Real.cosh_neg]

/-- **Reciprocity, now with linearity derived rather than assumed.** If the mean barrier is the
recognition cost in thermal units, then the response is odd and the two states are interchangeable. -/
theorem barrier_law_implies_reciprocity
    {F G : ℝ → ℝ} (hDB : DetailedBalance F G) {P0 : ℝ} {B : ℝ → ℝ} {b : ℝ}
    (h : IsBarrierConversion B)
    (hP : ∀ A : ℝ, deviation F A = barrierTraffic P0 B b A) :
    (∀ A : ℝ, responseOfLogRates F G (-A) = -responseOfLogRates F G A)
      ∧ StateExchange F G := by
  have hrw : ∀ A : ℝ, deviation F A = costActivity P0 (-(B 1)) b A := by
    intro A
    rw [hP A, barrierTraffic_eq_costActivity h b]
  exact costDeterminedActivity_implies_reciprocity hDB hrw

/-! ## The sign of the drift, forced without Marcus

The transfer coefficient of the derived law is `1/2 - (B 1 / b) * sinh (A / b)`. Since `B 1 >= 0` and
`b > 0`, the drift is nonpositive for positive drive: the coefficient DECREASES, and if the constant
is strictly positive it crosses zero at a finite drive, which is the barrierless point. None of this
uses Marcus theory. -/

/-- The transfer coefficient in the derived form. -/
theorem barrier_transferCoefficient {B : ℝ → ℝ} (h : IsBarrierConversion B) {b : ℝ} (hb : 0 < b)
    (A : ℝ) :
    transferCoefficient (-(B 1)) b A = 1 / 2 - (B 1 / b) * sinh (A / b) := by
  simp only [transferCoefficient]
  have : (-(B 1)) / b = -(B 1 / b) := by ring
  rw [this]
  ring

/-- **The drift is downward, and its sign is a consequence of cost being nonnegative.** For any
positive drive the derived transfer coefficient is at most one half. -/
theorem drift_is_downward {B : ℝ → ℝ} (h : IsBarrierConversion B) {b A : ℝ} (hb : 0 < b)
    (hA : 0 ≤ A) :
    transferCoefficient (-(B 1)) b A ≤ 1 / 2 := by
  rw [barrier_transferCoefficient h hb]
  have hc : 0 ≤ B 1 := const_nonneg_of_isBarrierConversion h
  have hsinh : 0 ≤ sinh (A / b) :=
    Real.sinh_nonneg_iff.mpr (div_nonneg hA (le_of_lt hb))
  have : 0 ≤ B 1 / b * sinh (A / b) :=
    mul_nonneg (div_nonneg hc (le_of_lt hb)) hsinh
  linarith

/-- Strict version: with a strictly positive conversion constant the drift is strictly downward at
any strictly positive drive, so a barrierless point exists at finite drive. -/
theorem drift_strictly_downward {B : ℝ → ℝ} (h : IsBarrierConversion B) {b A : ℝ}
    (hb : 0 < b) (hc : 0 < B 1) (hA : 0 < A) :
    transferCoefficient (-(B 1)) b A < 1 / 2 := by
  rw [barrier_transferCoefficient h hb]
  have hsinh : 0 < sinh (A / b) := Real.sinh_pos_iff.mpr (div_pos hA hb)
  have : 0 < B 1 / b * sinh (A / b) := mul_pos (div_pos hc hb) hsinh
  linarith

/-- **The barrierless point, located without any external theory.** The derived coefficient vanishes
exactly where `sinh (A/b) = b / (2 * B 1)`, that is at `A = b * arsinh (b / (2 * B 1))`. -/
theorem barrierless_point {B : ℝ → ℝ} (h : IsBarrierConversion B) {b : ℝ} (hb : 0 < b)
    (hc : 0 < B 1) :
    transferCoefficient (-(B 1)) b (b * Real.arsinh (b / (2 * B 1))) = 0 := by
  rw [barrier_transferCoefficient h hb]
  have hdiv : b * Real.arsinh (b / (2 * B 1)) / b = Real.arsinh (b / (2 * B 1)) := by
    field_simp
  rw [hdiv, Real.sinh_arsinh]
  have hb' : b ≠ 0 := hb.ne'
  have hc' : B 1 ≠ 0 := hc.ne'
  have key : B 1 / b * (b / (2 * B 1)) = 1 / 2 := by field_simp
  rw [key]
  ring

/-! ## What the module establishes

The chain is: mean barrier is the recognition cost in thermal units (the one physical premise), plus
additivity, continuity and monotonicity of a cost conversion (properties of being a cost), forces the
traffic to be `P0 - c * (cosh (A/b) - 1)` with `c >= 0`, which forces reciprocity
`alpha A + alpha (-A) = 1` and forces the drift downward to a barrierless point at finite drive.

The remaining freedom is the single scale `b`, and measurement has bounded it from below. The premise
that the mean barrier is a recognition cost is the falsifiable content: it is refuted by any
elementary step with a constant transfer coefficient different from one half, and by any nonzero even
part of the response where both directions are sampled in the same environment. Both falsifiers are
free of `b`, so no choice of scale protects the premise. -/

end ForcedResponseCostIsTheBarrier
end Thermodynamics
end IndisputableMonolith
