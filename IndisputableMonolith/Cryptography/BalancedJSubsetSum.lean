import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# 8-Balanced J-Subset Sum

This module defines the first RS-native cryptography candidate in a deliberately
boring form. It makes no security claim.

An instance has integer weights, residues in `ZMod 8`, phi-rungs, a target, and
a J-cost bound. A witness is a finite subset satisfying the target equation,
8-neutrality, and the cost bound.
-/

namespace IndisputableMonolith
namespace Cryptography
namespace BalancedJSubsetSum

open Constants

noncomputable section

/-- Phi-rung value, represented by `exp(k log phi)` to avoid integer-power API
details in the first definition module. -/
def rungValue (k : ℤ) : ℝ := Real.exp ((k : ℝ) * Real.log phi)

theorem rungValue_pos (k : ℤ) : 0 < rungValue k := by
  unfold rungValue
  exact Real.exp_pos _

@[simp] theorem rungValue_zero : rungValue 0 = 1 := by
  unfold rungValue
  norm_num

/-- One finite 8-Balanced J-Subset Sum instance. -/
structure BJSSInstance where
  n : ℕ
  weight : Fin n → ℤ
  residue : Fin n → ZMod 8
  rung : Fin n → ℤ
  target : ℤ
  bound : ℝ

/-- A candidate witness is just a selected support. -/
structure BJSSWitness (inst : BJSSInstance) where
  support : Finset (Fin inst.n)

/-- Integer target sum. -/
def weightSum (inst : BJSSInstance) (w : BJSSWitness inst) : ℤ :=
  ∑ i ∈ w.support, inst.weight i

/-- Mod-8 residue sum. -/
def residueSum (inst : BJSSInstance) (w : BJSSWitness inst) : ZMod 8 :=
  ∑ i ∈ w.support, inst.residue i

/-- J-cost contribution of a selected item. -/
def rungCost (inst : BJSSInstance) (i : Fin inst.n) : ℝ :=
  Cost.Jcost (rungValue (inst.rung i))

/-- Total J-cost of a witness support. -/
def totalJCost (inst : BJSSInstance) (w : BJSSWitness inst) : ℝ :=
  ∑ i ∈ w.support, rungCost inst i

def weightTarget (inst : BJSSInstance) (w : BJSSWitness inst) : Prop :=
  weightSum inst w = inst.target

def residueNeutral (inst : BJSSInstance) (w : BJSSWitness inst) : Prop :=
  residueSum inst w = 0

def jCostBound (inst : BJSSInstance) (w : BJSSWitness inst) : Prop :=
  totalJCost inst w ≤ inst.bound

/-- Full solution predicate for the finite BJSS problem. -/
def isSolution (inst : BJSSInstance) (w : BJSSWitness inst) : Prop :=
  weightTarget inst w ∧ residueNeutral inst w ∧ jCostBound inst w

theorem rungCost_nonneg (inst : BJSSInstance) (i : Fin inst.n) :
    0 ≤ rungCost inst i := by
  unfold rungCost
  exact Cost.Jcost_nonneg (rungValue_pos (inst.rung i))

theorem totalJCost_nonneg (inst : BJSSInstance) (w : BJSSWitness inst) :
    0 ≤ totalJCost inst w := by
  unfold totalJCost
  exact Finset.sum_nonneg (fun i _hi => rungCost_nonneg inst i)

/-- Classical decidability of the finite solution predicate. This is only a
finite search statement, not an efficiency claim. -/
noncomputable def solutionDecidable (inst : BJSSInstance) (w : BJSSWitness inst) :
    Decidable (isSolution inst w) := by
  classical
  exact inferInstance

/-- Ordinary subset-sum embeds by using zero residues, zero rungs, and zero
cost bound. -/
def fromSubsetSum {n : ℕ} (weight : Fin n → ℤ) (target : ℤ) : BJSSInstance where
  n := n
  weight := weight
  residue := fun _ => 0
  rung := fun _ => 0
  target := target
  bound := 0

theorem fromSubsetSum_totalJCost_zero {n : ℕ} (weight : Fin n → ℤ) (target : ℤ)
    (S : Finset (Fin n)) :
    totalJCost (fromSubsetSum weight target) ⟨S⟩ = 0 := by
  simp [totalJCost, rungCost, fromSubsetSum, Cost.Jcost_unit0]

/-- Any ordinary subset-sum solution gives a degenerate BJSS solution. -/
theorem fromSubsetSum_isSolution {n : ℕ} (weight : Fin n → ℤ) (target : ℤ)
    (S : Finset (Fin n)) (h : (∑ i ∈ S, weight i) = target) :
    isSolution (fromSubsetSum weight target) ⟨S⟩ := by
  constructor
  · simpa [weightTarget, weightSum, fromSubsetSum] using h
  constructor
  · simp [residueNeutral, residueSum, fromSubsetSum]
  · have hcost := fromSubsetSum_totalJCost_zero weight target S
    change totalJCost (fromSubsetSum weight target) ⟨S⟩ ≤ 0
    exact le_of_eq hcost

end

end BalancedJSubsetSum
end Cryptography
end IndisputableMonolith
