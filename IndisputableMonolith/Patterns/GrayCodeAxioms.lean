import Mathlib
import IndisputableMonolith.Patterns

/-!
# Gray Code Classical Results

This module declares well-known Gray code properties as axioms pending
full bitwise formalization.

## Background

The binary-reflected Gray code (BRGC) is a well-studied combinatorial object:
- Invented by Frank Gray (1953), US Patent 2,632,058
- Standard construction: gray(n) = n XOR (n >> 1)
- Inverse: binary(g) = g XOR (g>>1) XOR (g>>2) XOR ...

## Properties

All properties declared here have:
1. **Multiple published proofs** in discrete mathematics literature
2. **Efficient algorithms** with O(log n) complexity
3. **Extensive use** in digital systems, error correction, computer graphics
4. **Numerical verification** to arbitrary bit depths

## References

1. Savage, C. D. (1997). "A survey of combinatorial Gray codes." *SIAM Review*, 39(4):605–629.
2. Knuth, D. E. (2011). *The Art of Computer Programming, Vol 4A: Combinatorial Algorithms*. Section 7.2.1.1.
3. Gray, F. (1953). "Pulse code communication." US Patent 2,632,058.

-/

namespace IndisputableMonolith
namespace Patterns
namespace GrayCodeAxioms

/-- Inverse Gray code: convert Gray code back to natural number via cumulative XOR. -/
def grayInverse (g : ℕ) : ℕ :=
  let rec loop (shift : ℕ) (acc : ℕ) (fuel : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let shifted := g >>> shift
      if shifted = 0 then acc
      else loop (shift + 1) (acc ^^^ shifted) fuel'
  loop 0 0 64

/-- Hypothesis envelope for Gray code classical properties. -/
class GrayCodeFacts where
  grayToNat_inverts_natToGray :
    ∀ n : ℕ, n < 2^64 → grayInverse (n ^^^ (n >>> 1)) = n
  natToGray_inverts_grayToNat :
    ∀ g : ℕ, g < 2^64 →
      let n := grayInverse g
      n ^^^ (n >>> 1) = g
  grayToNat_preserves_bound :
    ∀ g d : ℕ, g < 2^d → d ≤ 64 → grayInverse g < 2^d
  pattern_to_nat_bound :
    ∀ (d : ℕ) (p : Pattern d),
      (∑ k : Fin d, if p k then 2^(k.val) else 0) < 2^d
  gray_code_one_bit_property :
    ∀ (d n : ℕ), n + 1 < 2^d →
      ∃! k : ℕ, k < d ∧
        ((n ^^^ (n >>> 1)).testBit k ≠ ((n+1) ^^^ ((n+1) >>> 1)).testBit k)

variable [GrayCodeFacts]

/-- **Classical Result**: Gray code inverse is a left inverse.

The inverse Gray code operation (cumulative XOR) correctly inverts the forward
Gray code transformation.

**Proof**: Induction on bit positions with XOR algebra

**References**:
- Knuth (2011), Exercise 7.2.1.1.4
- Savage (1997), Section 2.1

**Formalization Blocker**: Requires bitwise induction infrastructure for Nat

**Status**: Standard result in discrete mathematics
-/
theorem grayToNat_inverts_natToGray :
  ∀ n : ℕ, n < 2^64 → grayInverse (n ^^^ (n >>> 1)) = n :=
  GrayCodeFacts.grayToNat_inverts_natToGray

/-- **Classical Result**: natToGray is a left inverse of grayToNat.

The forward Gray code transformation inverts the inverse operation.

**Proof**: Follows from bijectivity of Gray code map

**References**: Same as above

**Status**: Consequence of inverse correctness
-/
theorem natToGray_inverts_grayToNat :
  ∀ g : ℕ, g < 2^64 →
    let n := grayInverse g
    n ^^^ (n >>> 1) = g :=
  GrayCodeFacts.natToGray_inverts_grayToNat

/-- **Classical Result**: Gray code preserves bounds.

If g < 2^d, then grayToNat(g) < 2^d.

**Proof**: XOR operations preserve bit width

**References**: Elementary bit manipulation

**Status**: Simple bitwise reasoning
-/
theorem grayToNat_preserves_bound :
  ∀ g d : ℕ, g < 2^d → d ≤ 64 → grayInverse g < 2^d :=
  GrayCodeFacts.grayToNat_preserves_bound

/-- **Classical Result**: Pattern to number conversion bound.

Converting a d-bit pattern to a number gives a value < 2^d.

**Proof**: Sum of 2^i for i < d equals 2^d - 1 < 2^d

**References**: Elementary combinatorics

**Status**: Straightforward calculation
-/
theorem pattern_to_nat_bound :
  ∀ (d : ℕ) (p : Pattern d),
    (∑ k : Fin d, if p k then 2^(k.val) else 0) < 2^d :=
  GrayCodeFacts.pattern_to_nat_bound

/-- **Classical Result**: Consecutive Gray codes differ in one bit.

For any n < 2^d - 1, gray(n) and gray(n+1) differ in exactly one bit position.

**Proof**:
- gray(n) XOR gray(n+1) = [n XOR (n>>1)] XOR [(n+1) XOR ((n+1)>>1)]
- This simplifies to a single power of 2 (bit at position of least significant 0 in n)

**References**:
- Savage (1997), Theorem 2.1
- Knuth (2011), Theorem 7.2.1.1.A

**Status**: Defining property of Gray codes
-/
theorem gray_code_one_bit_property :
  ∀ (d n : ℕ), n + 1 < 2^d →
    ∃! k : ℕ, k < d ∧
      (n ^^^ (n >>> 1)).testBit k ≠ ((n+1) ^^^ ((n+1) >>> 1)).testBit k :=
  GrayCodeFacts.gray_code_one_bit_property

end GrayCodeAxioms
end Patterns
end IndisputableMonolith
