import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF
import IndisputableMonolith.Complexity.SAT.XOR

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- Placeholder structure for an explicit small-bias family of XOR systems. -/
structure SmallBiasFamily where
  𝓗 : (n : Nat) → List (XORSystem n)

/-- Intended property: the family size is polynomial and approximates pairwise-independence.
    Note: We use n.succ to avoid n=0 edge cases; this is still O(n^k). -/
class HasPolySize (F : SmallBiasFamily) : Prop where
  bound : ∃ c k : Nat, ∀ n, (F.𝓗 n).length ≤ c * n.succ^k

/-! ## Explicit linear-mask family (Track A scaffold)

We instantiate a concrete deterministic family by taking every square-many
linear masks (viewed as bitmasks over the `n` variables) and pairing each mask
with both parity choices. This yields `O(n^2)` XOR systems, giving us a
polynomial-size handle for further combinatorial proofs. -/

open List

/-- Set of variables selected by a bitmask `mask`. -/
def maskVars (n mask : Nat) : List (Var n) :=
  (List.finRange n).filter fun v => Nat.testBit mask v.val

/-- XOR constraint induced by a mask/parity pair. -/
def constraintOfMask (n mask : Nat) (parity : Bool) : XORConstraint n :=
  { vars := maskVars n mask, parity := parity }

/-- Single-constraint XOR system (parity hash). -/
def systemOfMask (n mask : Nat) (parity : Bool) : XORSystem n :=
  [constraintOfMask n mask parity]

/-- Deterministic family: enumerate `(mask, parity)` pairs for mask < (n+1)^2. -/
def linearFamily : (n : Nat) → List (XORSystem n) := fun n =>
  (List.range ((n.succ) ^ 2)).flatMap fun mask =>
    [systemOfMask n mask false, systemOfMask n mask true]

/-- The linear-mask small-bias candidate. -/
def linearSmallBias : SmallBiasFamily :=
  { 𝓗 := linearFamily }

/-- Each mask contributes exactly 2 systems. -/
lemma twoSystems_length (n mask : Nat) :
    ([systemOfMask n mask false, systemOfMask n mask true] : List (XORSystem n)).length = 2 := rfl

/-- Linear family length bound: exactly 2 * (n+1)².
    Proof sketch: flatMap over range(k) where each element contributes list of length 2
    gives total length k * 2 = 2 * (n+1)². -/
lemma linearFamily_length_eq (n : Nat) :
    (linearFamily n).length = 2 * (n.succ ^ 2) := by
  unfold linearFamily
  induction (n.succ ^ 2) with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]
    rw [ih]
    simp only [twoSystems_length]
    omega

/-- Linear family length bound O((n+1)²). -/
lemma linearFamily_length_bound (n : Nat) :
    (linearFamily n).length ≤ 2 * (n.succ ^ 2) := by
  rw [linearFamily_length_eq]

/-- Polynomial bound witness for the linear family. -/
lemma linearFamily_poly_bound :
    ∃ c k : Nat, ∀ n, (linearFamily n).length ≤ c * n.succ ^ k := by
  refine ⟨2, 2, ?_⟩
  intro n
  exact linearFamily_length_bound n

instance linearSmallBias_poly : HasPolySize linearSmallBias :=
  ⟨linearFamily_poly_bound⟩

end SAT
end Complexity
end IndisputableMonolith
