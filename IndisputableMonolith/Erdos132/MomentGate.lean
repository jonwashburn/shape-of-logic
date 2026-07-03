/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Moment-Gate Lemma: angle-independent symmetric function identities
for C₃ cross squared-distances.

Key insight: the three cross squared-distances d₀², d₁², d₂² between
orbits at radii a and b satisfy:
  e₁ = d₀² + d₁² + d₂² = 3(a² + b²)
  e₂ = d₀²·d₁² + d₀²·d₂² + d₁²·d₂² = 3(a²+b²)² − 3a²b²

These are independent of the relative phase θ. The structural
reason: cos is a root-of-unity sum over Z/3Z, so the elementary
symmetric functions of {cos(θ + 2πk/3) : k=0,1,2} are constant.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

namespace Erdos132.MomentGate

open Real

/-- Cross squared-distance between two C₃ orbit points at radii a, b
with relative phase θ and rotation index k. -/
def dSq (a b θ : ℝ) (k : ℕ) : ℝ :=
  a ^ 2 + b ^ 2 - 2 * a * b * cos (θ + 2 * π * k / 3)

/-- The C₃ root-of-unity sum: cos(θ) + cos(θ + 2π/3) + cos(θ + 4π/3) = 0.
This follows from the real part of ∑_{k=0}^{2} e^{i(θ + 2πk/3)} =
e^{iθ} · (1 + ω + ω²) = 0 where ω = e^{2πi/3}. -/
theorem cos_thirds_sum (θ : ℝ) :
    cos θ + cos (θ + 2 * π / 3) + cos (θ + 4 * π / 3) = 0 := by
  have hcos_add1 := cos_add θ (2 * π / 3)
  have hcos_add2 := cos_add θ (4 * π / 3)
  have hc1 : cos (2 * π / 3) = -(1 : ℝ) / 2 := by
    have h : (2 : ℝ) * π / 3 = π - π / 3 := by ring
    rw [h, cos_pi_sub, cos_pi_div_three]; ring
  have hs1 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    have h : (2 : ℝ) * π / 3 = π - π / 3 := by ring
    rw [h, sin_pi_sub]; exact sin_pi_div_three
  have hc2 : cos (4 * π / 3) = -(1 : ℝ) / 2 := by
    have h : (4 : ℝ) * π / 3 = 2 * π - 2 * π / 3 := by ring
    rw [h, cos_two_pi_sub, hc1]
  have hs2 : sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
    have h : (4 : ℝ) * π / 3 = 2 * π - 2 * π / 3 := by ring
    rw [h, sin_two_pi_sub, hs1]
  rw [hcos_add1, hcos_add2, hc1, hs1, hc2, hs2]; ring

/-- The sum of cos² over the three C₃ phases equals 3/2.
Proof: cos²x = (1 + cos 2x)/2, sum = 3/2 + (1/2)·cos_thirds_sum(2θ) = 3/2. -/
theorem cos_sq_thirds_sum (θ : ℝ) :
    cos θ ^ 2 + cos (θ + 2 * π / 3) ^ 2 + cos (θ + 4 * π / 3) ^ 2 = 3 / 2 := by
  have hid : ∀ x : ℝ, cos x ^ 2 = (1 + cos (2 * x)) / 2 := by
    intro x; have := cos_sq x; linarith [cos_sq x]
  rw [hid θ, hid (θ + 2 * π / 3), hid (θ + 4 * π / 3)]
  have h1 : 2 * (θ + 2 * π / 3) = 2 * θ + 4 * π / 3 := by ring
  have h2 : 2 * (θ + 4 * π / 3) = 2 * θ + 2 * π / 3 + 2 * π := by ring
  rw [h1, h2, cos_add_two_pi]
  have hsum := cos_thirds_sum (2 * θ)
  linarith [hsum]

/-- e₁ identity: the sum of cross squared-distances is 3(a²+b²).
Follows directly from cos_thirds_sum. -/
theorem sum_dSq_eq (a b θ : ℝ) :
    dSq a b θ 0 + dSq a b θ 1 + dSq a b θ 2 = 3 * (a ^ 2 + b ^ 2) := by
  simp only [dSq, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  set c0 := cos (θ + 2 * π * 0 / 3)
  set c1 := cos (θ + 2 * π * 1 / 3)
  set c2 := cos (θ + 2 * π * 2 / 3)
  suffices h : 2 * a * b * (c0 + c1 + c2) = 0 by linarith
  have hkey : c0 + c1 + c2 = 0 := by
    simp only [c0, c1, c2]
    have ha : (θ + 2 * π * 0 / 3 : ℝ) = θ := by ring
    have hb : (θ + 2 * π * 1 / 3 : ℝ) = θ + 2 * π / 3 := by ring
    have hc : (θ + 2 * π * 2 / 3 : ℝ) = θ + 4 * π / 3 := by ring
    rw [ha, hb, hc]; exact cos_thirds_sum θ
  rw [hkey]; ring

/-- e₂ identity: the sum of pairwise products equals 3(a²+b²)² − 3a²b².
Uses both cos_thirds_sum and cos_sq_thirds_sum via the algebraic identity
  LHS = 3A² − 4PA·(Σcos) + 4P²·(Σcos·cos) = 3A² − 0 + 4P²·(−3/4) = 3A² − 3P². -/
theorem pairprod_dSq_eq (a b θ : ℝ) :
    dSq a b θ 0 * dSq a b θ 1 + dSq a b θ 0 * dSq a b θ 2
      + dSq a b θ 1 * dSq a b θ 2
    = 3 * (a ^ 2 + b ^ 2) ^ 2 - 3 * a ^ 2 * b ^ 2 := by
  simp only [dSq, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  set A := a ^ 2 + b ^ 2
  set P := a * b
  set c0 := cos (θ + 2 * π * 0 / 3)
  set c1 := cos (θ + 2 * π * 1 / 3)
  set c2 := cos (θ + 2 * π * 2 / 3)
  suffices h : (A - 2*P*c0) * (A - 2*P*c1) + (A - 2*P*c0) * (A - 2*P*c2)
      + (A - 2*P*c1) * (A - 2*P*c2) = 3 * A ^ 2 - 3 * P ^ 2 by
    convert h using 1 <;> ring
  have hc_sum : c0 + c1 + c2 = 0 := by
    simp only [c0, c1, c2]
    have ha : (θ + 2 * π * 0 / 3 : ℝ) = θ := by ring
    have hb : (θ + 2 * π * 1 / 3 : ℝ) = θ + 2 * π / 3 := by ring
    have hc : (θ + 2 * π * 2 / 3 : ℝ) = θ + 4 * π / 3 := by ring
    rw [ha, hb, hc]; exact cos_thirds_sum θ
  have hc_sq : c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = 3 / 2 := by
    simp only [c0, c1, c2]
    have ha : (θ + 2 * π * 0 / 3 : ℝ) = θ := by ring
    have hb : (θ + 2 * π * 1 / 3 : ℝ) = θ + 2 * π / 3 := by ring
    have hc : (θ + 2 * π * 2 / 3 : ℝ) = θ + 4 * π / 3 := by ring
    rw [ha, hb, hc]; exact cos_sq_thirds_sum θ
  have hc_pp : c0 * c1 + c0 * c2 + c1 * c2 = -(3 : ℝ) / 4 := by
    nlinarith [sq_nonneg (c0 + c1 + c2), hc_sum, hc_sq]
  have key : 3*A^2 - 4*P*A*(c0+c1+c2) + 4*P^2*(c0*c1+c0*c2+c1*c2) = 3*A^2 - 3*P^2 := by
    rw [hc_sum, hc_pp]; ring
  linarith [key, show (A - 2*P*c0) * (A - 2*P*c1) + (A - 2*P*c0) * (A - 2*P*c2)
      + (A - 2*P*c1) * (A - 2*P*c2)
      = 3*A^2 - 4*P*A*(c0+c1+c2) + 4*P^2*(c0*c1+c0*c2+c1*c2) from by ring]

/-- The moment-gate theorem: if no triple from a finite set S satisfies
both the e₁ sum constraint and the e₂ pairwise-product constraint for
an orbit-pair (a, b), then no angle θ can place all three cross-distances
in S simultaneously. This is the key exclusion mechanism. -/
theorem moment_gate_obstruction {S : Finset ℝ} {a b : ℝ}
    (hgate : ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S,
      s₁ + s₂ + s₃ = 3 * (a ^ 2 + b ^ 2) →
      s₁ * s₂ + s₁ * s₃ + s₂ * s₃ ≠ 3 * (a ^ 2 + b ^ 2) ^ 2 - 3 * a ^ 2 * b ^ 2) :
    ∀ θ : ℝ, ¬(dSq a b θ 0 ∈ S ∧ dSq a b θ 1 ∈ S ∧ dSq a b θ 2 ∈ S) := by
  intro θ ⟨h0, h1, h2⟩
  have he₁ := sum_dSq_eq a b θ
  have he₂ := pairprod_dSq_eq a b θ
  exact absurd he₂ (hgate _ h0 _ h1 _ h2 he₁)

end Erdos132.MomentGate

end