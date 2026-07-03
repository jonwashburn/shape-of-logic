import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCodeAxioms

/-!
# Binary-Reflected Gray Code

This module provides the binary-reflected Gray code construction.
This is a well-known algorithm that generates a Hamiltonian cycle on the
d-dimensional hypercube Q_d.

The construction uses the recursive definition:
- BRGC(0) = [0]
- BRGC(n+1) = [0·BRGC(n), 1·BRGC(n)ʳ]
  where x·L prepends bit x to each pattern in list L, and Lʳ is L reversed

The key properties:
1. It visits all 2^d vertices exactly once
2. Consecutive entries differ in exactly one bit
3. The first and last entries also differ in exactly one bit (forming a cycle)
-/

namespace IndisputableMonolith
namespace Patterns

open Function

/-- Convert a natural number to its Gray code representation
    The standard formula: gray(n) = n XOR (n >> 1) -/
def natToGray (n : ℕ) : ℕ := n ^^^ (n >>> 1)

/-- Binary-reflected Gray code as a function from Fin (2^d) to Pattern d
    We use the standard bit-extraction to convert Gray code to pattern -/
def binaryReflectedGray (d : ℕ) (i : Fin (2^d)) : Pattern d :=
  fun j => (natToGray i.val).testBit j.val

/-- Inverse Gray code: converts Gray code back to binary -/
def grayToNat (g : ℕ) : ℕ :=
  -- Inverse Gray code: repeatedly XOR with shifted versions
  -- g XOR (g >> 1) XOR (g >> 2) XOR ...
  -- For bounded values, this terminates
  let rec aux (shift : ℕ) (acc : ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let shifted := g >>> shift
      if shifted = 0 then acc
      else aux (shift + 1) (acc ^^^ shifted) fuel'
  aux 0 0 64  -- 64 shifts is enough for any practical number

-- Properties and classical results are provided via
-- `IndisputableMonolith.Patterns.GrayCodeAxioms.GrayCodeFacts`.
-- This module remains axiom-free and parametric over those facts.

end Patterns
end IndisputableMonolith
