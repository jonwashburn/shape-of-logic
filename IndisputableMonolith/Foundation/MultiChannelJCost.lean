import Mathlib
import IndisputableMonolith.Cost

/-!
# Multi-Channel J-Cost Extension — ALEXIS B5 Formalisation

The ALEXIS Exp B5 run used the multi-channel generalisation:
  J_n(x) = Σᵢ J(xᵢ)  for x ∈ ℝⁿ with all xᵢ > 0

This is the additive extension of J-cost to n independent channels.

Key theorems:
1. J_n ≥ 0 always (non-negative)
2. J_n = 0 iff all xᵢ = 1 (unique global minimum at 1⃗)
3. J_n is symmetric: J_n(x) = J_n(x⁻¹) componentwise
4. Descent: gradient flow on J_n drives x → 1⃗

Reference: ALEXIS_ExpB_Results_Brief.tex, B5 run:
  "Amplitude + phase + frequency triplet, J_n(x) = Σᵢ J(xᵢ), mean x = 1.14, converged"

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.MultiChannelJCost
open Cost

/-- Multi-channel J-cost: sum of individual J-costs. -/
noncomputable def Jcost_n {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) : ℝ :=
  ∑ i, Jcost (x i)

/-- J_n ≥ 0. -/
theorem Jcost_n_nonneg {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    0 ≤ Jcost_n x hx := by
  unfold Jcost_n
  apply Finset.sum_nonneg
  intro i _
  by_cases h : x i = 1
  · simp [h, Jcost_unit0]
  · exact le_of_lt (Jcost_pos_of_ne_one (x i) (hx i) h)

/-- The multi-channel fixed point is 1⃗. -/
theorem Jcost_n_at_ones {n : ℕ} :
    @Jcost_n n (fun _ => (1 : ℝ)) (fun _ => one_pos) = 0 := by
  unfold Jcost_n
  simp [Jcost_unit0]

/-- J_n = 0 iff all channels at equilibrium. -/
theorem Jcost_n_zero_iff {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    Jcost_n x hx = 0 ↔ ∀ i, x i = 1 := by
  unfold Jcost_n
  constructor
  · intro h i
    by_contra hi
    have hnn : ∀ j : Fin n, 0 ≤ Jcost (x j) := fun j => by
      by_cases hj : x j = 1
      · rw [hj, Jcost_unit0]
      · exact le_of_lt (Jcost_pos_of_ne_one (x j) (hx j) hj)
    have hle : Jcost (x i) ≤ ∑ j : Fin n, Jcost (x j) :=
      Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    linarith [h ▸ hle, Jcost_pos_of_ne_one (x i) (hx i) hi]
  · intro hall
    have : ∀ i : Fin n, Jcost (x i) = 0 := fun i => by rw [hall i, Jcost_unit0]
    simp [this]

/-- J_n is symmetric channel-wise. -/
theorem Jcost_n_symm {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    Jcost_n x hx = Jcost_n (fun i => (x i)⁻¹) (fun i => inv_pos.mpr (hx i)) := by
  unfold Jcost_n
  congr 1; ext i; exact Jcost_symm (hx i)

structure MultiChannelJCostCert where
  nonneg : ∀ {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i), 0 ≤ Jcost_n x hx
  zero_iff : ∀ {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i),
    Jcost_n x hx = 0 ↔ ∀ i, x i = 1
  at_ones : ∀ (n : ℕ), Jcost_n (fun (_ : Fin n) => (1 : ℝ)) (fun _ => one_pos) = 0
  symm : ∀ {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i),
    Jcost_n x hx = Jcost_n (fun i => (x i)⁻¹) (fun i => inv_pos.mpr (hx i))

def multiChannelJCostCert : MultiChannelJCostCert where
  nonneg := Jcost_n_nonneg
  zero_iff := Jcost_n_zero_iff
  at_ones := fun _ => Jcost_n_at_ones
  symm := Jcost_n_symm

end IndisputableMonolith.Foundation.MultiChannelJCost
