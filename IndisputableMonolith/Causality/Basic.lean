import Mathlib

namespace IndisputableMonolith
namespace Causality

variable {α : Type}

structure Kinematics (α : Type) where
  step : α → α → Prop

inductive ReachN (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z

def inBall (K : Kinematics α) (x : α) (n : Nat) (y : α) : Prop :=
  ∃ k ≤ n, ReachN K k x y

lemma reach_in_ball {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : inBall K x n y := ⟨n, le_rfl, h⟩

lemma reach_le_in_ball {K : Kinematics α} {x y : α} {k n : Nat}
  (hk : k ≤ n) (h : ReachN K k x y) : inBall K x n y := ⟨k, hk, h⟩

def Reaches (K : Kinematics α) (x y : α) : Prop := ∃ n, ReachN K n x y

lemma reaches_of_reachN {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : Reaches K x y := ⟨n, h⟩

lemma inBall_mono {K : Kinematics α} {x y : α} {n m : Nat}
  (hnm : n ≤ m) : inBall K x n y → inBall K x m y := by
  intro ⟨k, hk, hkreach⟩
  exact ⟨k, le_trans hk hnm, hkreach⟩

end Causality
end IndisputableMonolith
