import Mathlib

namespace IndisputableMonolith
namespace Verification
namespace Necessity
namespace FibSubst

/-! 2-letter substitution system yielding Fibonacci recurrences on counts. -/

abbrev Word := List Bool

/-- The Fibonacci sequence: F(0)=0, F(1)=1, F(n+2)=F(n+1)+F(n) -/
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- Fibonacci substitution on a single symbol. -/
def fibSub : Bool → Word
  | false => [false, true]
  | true  => [false]

/-- Extend substitution to words by concatenation. -/
def fibSubWord (w : Word) : Word := w.flatMap fibSub

/-- Count of `false` symbols in a word. -/
def countFalse : Word → Nat
  | []        => 0
  | b :: bs   => (if b = false then 1 else 0) + countFalse bs

/-- Count of `true` symbols in a word. -/
def countTrue : Word → Nat
  | []        => 0
  | b :: bs   => (if b = true then 1 else 0) + countTrue bs

@[simp] lemma countFalse_nil : countFalse ([] : Word) = 0 := rfl
@[simp] lemma countTrue_nil : countTrue ([] : Word) = 0 := rfl

@[simp] lemma countFalse_cons_false (w : Word) :
  countFalse (false :: w) = countFalse w + 1 := by
  simp [countFalse, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

@[simp] lemma countFalse_cons_true (w : Word) :
  countFalse (true :: w) = countFalse w := by
  simp [countFalse]

@[simp] lemma countTrue_cons_false (w : Word) :
  countTrue (false :: w) = countTrue w := by
  simp [countTrue]

@[simp] lemma countTrue_cons_true (w : Word) :
  countTrue (true :: w) = countTrue w + 1 := by
  simp [countTrue, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma countFalse_append (w₁ w₂ : Word) :
  countFalse (w₁ ++ w₂) = countFalse w₁ + countFalse w₂ := by
  induction w₁ with
  | nil => simp
  | cons b bs ih =>
      cases b
      · simp [ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      · simp [ih]

lemma countTrue_append (w₁ w₂ : Word) :
  countTrue (w₁ ++ w₂) = countTrue w₁ + countTrue w₂ := by
  induction w₁ with
  | nil => simp
  | cons b bs ih =>
      cases b
      · simp [ih]
      · simp [ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Counts for substituted single symbols. -/
lemma counts_sub_false :
  countFalse (fibSub false) = 1 ∧ countTrue (fibSub false) = 1 := by
  simp [fibSub]

lemma counts_sub_true :
  countFalse (fibSub true) = 1 ∧ countTrue (fibSub true) = 0 := by
  simp [fibSub]

/-- Counts for substituted words decompose additively. -/
lemma counts_sub_word (w : Word) :
  countFalse (fibSubWord w) = countFalse w + countTrue w ∧
  countTrue (fibSubWord w) = countFalse w := by
  induction w with
  | nil => simp [fibSubWord]
  | cons b bs ih =>
      cases ih with
      | _ ihF ihT =>
        cases b
        · -- b = false
          have : fibSubWord (false :: bs) = fibSub false ++ fibSubWord bs := by
            simp [fibSubWord, List.flatMap]
          have hF : countFalse (fibSub false) = 1 := (counts_sub_false).1
          have hT : countTrue (fibSub false) = 1 := (counts_sub_false).2
          simp [this, countFalse_append, countTrue_append, ihF, ihT, hF, hT, countFalse_cons_false, countTrue_cons_false, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        · -- b = true
          have : fibSubWord (true :: bs) = fibSub true ++ fibSubWord bs := by
            simp [fibSubWord, List.flatMap]
          have hF : countFalse (fibSub true) = 1 := (counts_sub_true).1
          have hT : countTrue (fibSub true) = 0 := (counts_sub_true).2
          simp [this, countFalse_append, countTrue_append, ihF, ihT, hF, hT, countFalse_cons_true, countTrue_cons_true, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Iterate substitution starting from the seed word `[false]`. -/
def iter (n : Nat) : Word := (fibSubWord^[n]) [false]

@[simp] lemma counts_iter_succ (n : Nat) :
  countFalse (iter (n+1)) = countFalse (iter n) + countTrue (iter n) ∧
  countTrue (iter (n+1)) = countFalse (iter n) := by
  have h_unfold : iter (n+1) = fibSubWord (iter n) := by
    simp [iter, Function.iterate_succ_apply']
  rw [h_unfold]
  exact counts_sub_word (iter n)

/-- Fibonacci recursion on counts: starting from `[false]` we have
    counts (false) = (1,0) and recurrence
    F_{n+1} = F_n + T_n;  T_{n+1} = F_n. -/
lemma counts_iter_fib (n : Nat) :
  (countFalse (iter n), countTrue (iter n)) = (fib (n+1), fib n) := by
  induction n with
  | zero => simp [iter, fib]
  | succ n ih =>
      rcases counts_iter_succ n with ⟨hF, hT⟩
      have ihF : countFalse (iter n) = fib (n + 1) := (congrArg Prod.fst ih)
      have ihT : countTrue (iter n) = fib n := (congrArg Prod.snd ih)
      ext <;> simp [hF, hT, ihF, ihT, fib]

end FibSubst
end Necessity
end Verification
end IndisputableMonolith
