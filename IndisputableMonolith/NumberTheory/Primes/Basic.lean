import Mathlib

/-!
Basic prime-number footholds for the `reality` repo.

Design goals:
- Reuse Mathlib’s `Nat.Prime` and existing number theory library (don’t reinvent).
- Keep this namespace **axiom-free** and **sorry-free** so it can live in the main monolith.
- Provide small “sanity theorems” that confirm the module is wired correctly.
- Grow upward into analytic number theory only after the algebraic layer is stable.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open scoped BigOperators

/-! ### Sanity checks (compile-time smoke) -/

theorem prime_two : Nat.Prime 2 := by
  decide

theorem prime_three : Nat.Prime 3 := by
  decide

theorem not_prime_zero : ¬ Nat.Prime 0 := by
  decide

theorem not_prime_one : ¬ Nat.Prime 1 := by
  decide

/-! ### Local aliases (optional convenience) -/

/-- Repo-local alias for Mathlib’s `Nat.Prime` (kept transparent). -/
abbrev Prime (n : ℕ) : Prop := Nat.Prime n

@[simp] theorem prime_iff (n : ℕ) : Prime n ↔ Nat.Prime n := Iff.rfl

end Primes
end NumberTheory
end IndisputableMonolith
