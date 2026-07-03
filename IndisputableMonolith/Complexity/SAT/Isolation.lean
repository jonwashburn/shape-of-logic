import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- An XOR family for instances of size `n`. -/
abbrev XORFamily := (n : Nat) → List (XORSystem n)

/-- A system `H` isolates `φ` when `φ ∧ H` has exactly one satisfying assignment. -/
def isolates {n} (φ : CNF n) (H : XORSystem n) : Prop :=
  UniqueSolutionXOR { φ := φ, H := H }

/-- A family `𝓗` is isolating if for every satisfiable `φ`, some `H ∈ 𝓗 n` isolates `φ`. -/
def IsolatingFamily (𝓗 : XORFamily) : Prop :=
  ∀ {n} (φ : CNF n), Satisfiable φ → ∃ H ∈ 𝓗 n, isolates φ H

/-- Deterministic isolation: an explicit, uniformly constructible `𝓗` with polynomial size. -/
structure DeterministicIsolation where
  𝓗        : XORFamily
  polySize : ∃ c k : Nat, ∀ n, (𝓗 n).length ≤ c * n^k
  isolates_all : IsolatingFamily 𝓗

end SAT
end Complexity
end IndisputableMonolith
