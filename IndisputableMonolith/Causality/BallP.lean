import Mathlib
import IndisputableMonolith.Causality.Basic

namespace IndisputableMonolith
namespace Causality

variable {α : Type}

/-- `ballP K x n y` means y is within ≤ n steps of x via `K.step`. -/
def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

lemma ballP_mono {K : Kinematics α} {x : α} {n m : Nat}
  (hnm : n ≤ m) : {y | ballP K x n y} ⊆ {y | ballP K x m y} := by
  induction hnm with
  | refl => intro y hy; simpa using hy
  | @step m hm ih =>
      intro y hy
      exact Or.inl (ih hy)

lemma reach_mem_ballP {K : Kinematics α} {x y : α} :
  ∀ {n}, ReachN K n x y → ballP K x n y := by
  intro n h; induction h with
  | zero => simp [ballP]
  | @succ n x y z hxy hyz ih =>
      exact Or.inr ⟨y, ih, hyz⟩

lemma inBall_subset_ballP {K : Kinematics α} {x y : α} {n : Nat} :
  inBall K x n y → ballP K x n y := by
  intro ⟨k, hk, hreach⟩
  have : ballP K x k y := reach_mem_ballP (K:=K) (x:=x) (y:=y) hreach
  exact (ballP_mono (K:=K) (x:=x) hk) this

lemma ballP_subset_inBall {K : Kinematics α} {x y : α} :
  ∀ {n}, ballP K x n y → inBall K x n y := by
  intro n
  induction n generalizing y with
  | zero =>
      intro hy; rcases hy with rfl; exact ⟨0, le_rfl, ReachN.zero⟩
  | succ n ih =>
      intro hy
      cases hy with
      | inl hy' =>
          rcases ih hy' with ⟨k, hk, hkreach⟩
          exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hkreach⟩
      | inr h' =>
          rcases h' with ⟨z, hz, hstep⟩
          rcases ih hz with ⟨k, hk, hkreach⟩
          exact ⟨k + 1, Nat.succ_le_succ hk, ReachN.succ hkreach hstep⟩

end Causality
end IndisputableMonolith
