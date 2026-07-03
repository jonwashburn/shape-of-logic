import Mathlib

/-!
# Erdős-Straus RCL Ledger Reduction

This file records the algebraic reduction behind the RCL attack on the
Erdős-Straus conjecture.

After choosing the first denominator `x`, the residual equation is

`c / N = 1 / y + 1 / z`, with `c = 4x - n` and `N = nx`.

Clearing denominators gives the balanced factor-pair condition

`(c y - N)(c z - N) = N^2`.

That is the discrete ledger form of the reciprocal split: a left and right
defect multiply back to the square budget.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ErdosStrausRCL

/-- Rational Erdős-Straus representation.  The integer problem is the
same statement with positive natural witnesses. -/
def HasRationalErdosStrausRepr (n : ℚ) : Prop :=
  ∃ x y z : ℚ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
    (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- The core ledger identity: a balanced factor pair for the residual
two-denominator split gives a three-unit Erdős-Straus representation. -/
theorem repr_of_balanced_factor_pair
    {n x c N d e y z : ℚ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hN : N = n * x)
    (hcdef : c = 4 * x - n)
    (hde : d * e = N ^ 2)
    (hyd : c * y = N + d)
    (hze : c * z = N + e) :
    HasRationalErdosStrausRepr n := by
  have hN_ne : N ≠ 0 := by
    rw [hN]
    exact mul_ne_zero hn hx
  have hd_eq : c * y - N = d := by linarith
  have he_eq : c * z - N = e := by linarith
  have hquad : (c * y - N) * (c * z - N) = N ^ 2 := by
    rw [hd_eq, he_eq, hde]
  have hfactor : c * (c * y * z - N * (y + z)) = 0 := by
    nlinarith [hquad]
  have hinner : c * y * z = N * (y + z) := by
    have hzero : c * y * z - N * (y + z) = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left hc
    linarith
  have hsplit : (1 : ℚ) / y + 1 / z = c / N := by
    field_simp [hy, hz, hN_ne]
    nlinarith [hinner]
  have hfirst : (4 : ℚ) / n = 1 / x + c / N := by
    rw [hN, hcdef]
    field_simp [hn, hx]
    ring
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  rw [hfirst, ← hsplit]
  ring

/-- Equivalent operational form: it is enough to find nonzero `y,z`
whose residual defects multiply to the square budget. -/
theorem repr_of_residual_square
    {n x c N y z : ℚ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hN : N = n * x)
    (hcdef : c = 4 * x - n)
    (hres : (c * y - N) * (c * z - N) = N ^ 2) :
    HasRationalErdosStrausRepr n := by
  refine repr_of_balanced_factor_pair
    (d := c * y - N) (e := c * z - N)
    hn hx hc hy hz hN hcdef hres ?_ ?_
  · ring
  · ring

/-- General residual-gate divisor split.  If `x = (n+c)/4` and a divisor
split `d*q = N` is chosen so that the displayed denominators are nonzero,
then the pair `d, N*q` is a balanced factor pair for the residual gate `c`. -/
theorem repr_of_gate_divisor_pair
    {n x c N d q : ℚ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hc : c ≠ 0)
    (hN : N = n * x)
    (hxdef : x = (n + c) / 4)
    (hdq : d * q = N)
    (hy : (N + d) / c ≠ 0)
    (hz : (N + N * q) / c ≠ 0) :
    HasRationalErdosStrausRepr n := by
  have hcdef : c = 4 * x - n := by
    rw [hxdef]
    field_simp
    ring
  have hde : d * (N * q) = N ^ 2 := by
    rw [← hdq]
    ring
  refine repr_of_balanced_factor_pair
    (c := c) (N := N) (d := d) (e := N * q)
    (y := (N + d) / c) (z := (N + N * q) / c)
    hn hx hc hy hz hN hcdef hde ?_ ?_
  · field_simp [hc]
  · field_simp [hc]

/-- The dominant hard-class gate.  For `n = 1 mod 4`, the minimal
choice is `x = (n+3)/4`, so `c = 3`.  A divisor split `d*q = N` gives a
balanced factor pair `d` and `N*q` for `N^2`, hence a representation. -/
theorem repr_c3_of_divisor_pair
    {n x N d q : ℚ}
    (hn : n ≠ 0) (hx : x ≠ 0)
    (hN : N = n * x)
    (hxdef : x = (n + 3) / 4)
    (hdq : d * q = N)
    (hy : (N + d) / 3 ≠ 0)
    (hz : (N + N * q) / 3 ≠ 0) :
    HasRationalErdosStrausRepr n := by
  have hc : (3 : ℚ) ≠ 0 := by norm_num
  exact repr_of_gate_divisor_pair
    (c := (3 : ℚ)) hn hx hc hN hxdef hdq hy hz

/-! ### Explicit residue-class theorems

Within `n ≡ 1 mod 4`, write `n mod 12 ∈ {1, 5, 9}`.  The two cases
`5 mod 12` and `9 mod 12` admit explicit Egyptian-fraction formulas with
gate `c = 3`; the genuine residual hard class is `n ≡ 1 mod 12`. -/

/-- Explicit Erdős-Straus representation for `n = 12k + 5`.

The gate-3 divisor pair takes `d = x = 3k + 2` (which is `2 mod 3`),
giving the closed-form three-unit sum below. -/
theorem erdos_straus_five_mod_twelve (k : ℕ) :
    (4 : ℚ) / (12 * (k : ℚ) + 5)
      = 1 / (3 * (k : ℚ) + 2)
        + 1 / (2 * (3 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1))
        + 1 / (2 * (12 * (k : ℚ) + 5) * (3 * (k : ℚ) + 2)
                 * (2 * (k : ℚ) + 1)) := by
  have h1 : (3 * (k : ℚ) + 2) > 0 := by positivity
  have h2 : (2 * (k : ℚ) + 1) > 0 := by positivity
  have h3 : (12 * (k : ℚ) + 5) > 0 := by positivity
  have h1' : (3 * (k : ℚ) + 2) ≠ 0 := ne_of_gt h1
  have h2' : (2 * (k : ℚ) + 1) ≠ 0 := ne_of_gt h2
  have h3' : (12 * (k : ℚ) + 5) ≠ 0 := ne_of_gt h3
  field_simp
  ring

/-- Explicit Erdős-Straus representation for `n = 12k + 9`.

Here `3 ∣ n`, so the gate-3 divisor pair takes `d = N` (i.e. `q = 1`)
and the second and third unit fractions coincide. -/
theorem erdos_straus_nine_mod_twelve (k : ℕ) :
    (4 : ℚ) / (12 * (k : ℚ) + 9)
      = 1 / (3 * (k : ℚ) + 3)
        + 1 / (6 * (4 * (k : ℚ) + 3) * ((k : ℚ) + 1))
        + 1 / (6 * (4 * (k : ℚ) + 3) * ((k : ℚ) + 1)) := by
  have h1 : (3 * (k : ℚ) + 3) > 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) > 0 := by positivity
  have h3 : ((k : ℚ) + 1) > 0 := by positivity
  have h1' : (3 * (k : ℚ) + 3) ≠ 0 := ne_of_gt h1
  have h2' : (4 * (k : ℚ) + 3) ≠ 0 := ne_of_gt h2
  have h3' : ((k : ℚ) + 1) ≠ 0 := ne_of_gt h3
  field_simp
  ring

/-! ### Natural-number existence

Cast the rational identities to the natural-number existence form. -/

/-- For every `n = 12k + 5`, an Erdős-Straus representation in `ℕ⁺`. -/
theorem erdos_straus_nat_five_mod_twelve (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / ((12 * k + 5 : ℕ) : ℚ)
        = (1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z := by
  refine ⟨3 * k + 2,
          2 * (3 * k + 2) * (2 * k + 1),
          2 * (12 * k + 5) * (3 * k + 2) * (2 * k + 1),
          by positivity, by positivity, by positivity, ?_⟩
  have h := erdos_straus_five_mod_twelve k
  have hcast : ((12 * k + 5 : ℕ) : ℚ) = 12 * (k : ℚ) + 5 := by push_cast; ring
  rw [hcast]
  push_cast
  convert h using 2

/-- For every `n = 12k + 9`, an Erdős-Straus representation in `ℕ⁺`. -/
theorem erdos_straus_nat_nine_mod_twelve (k : ℕ) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / ((12 * k + 9 : ℕ) : ℚ)
        = (1 : ℚ) / x + (1 : ℚ) / y + (1 : ℚ) / z := by
  refine ⟨3 * k + 3,
          6 * (4 * k + 3) * (k + 1),
          6 * (4 * k + 3) * (k + 1),
          by positivity, by positivity, by positivity, ?_⟩
  have h := erdos_straus_nine_mod_twelve k
  have hcast : ((12 * k + 9 : ℕ) : ℚ) = 12 * (k : ℚ) + 9 := by push_cast; ring
  rw [hcast]
  push_cast
  convert h using 2

/-! ### Discrete c = 3 divisor sufficiency

For `n ≡ 1 mod 4`, the gate-3 representation succeeds whenever there
exist nonzero rationals `d, q` with `d · q = n · (n+3)/4` and the
displayed denominators `(N+d)/3` and `(N+Nq)/3` are nonzero. The
arithmetic content is captured by `repr_c3_of_divisor_pair`. -/

/-! ### Sub-residue classes within `n ≡ 1 mod 12`

Refine `n ≡ 1 mod 12` by writing `n = 12k + 1`.  When `k` is odd we have
`n ≡ 13 mod 24`, and `(n+3)/4 = 6m + 4 = 2(3m+2)` is even (writing
`k = 2m+1`), so the divisor `d = 2 ≡ 2 mod 3` succeeds.  The remaining
sub-class is `n ≡ 1 mod 24`. -/

/-- Explicit Erdős-Straus representation for `n = 24m + 13`.

Since `(n+3)/4 = 2(3m+2)` is even, `d = 2` gives the gate-3 split.
With `A = (24m+13)(3m+2) = N/2`, the formula is

```text
4/n = 1/(6m+4) + 1/(2(A+1)/3) + 1/(2A(A+1)/3).
```
-/
theorem erdos_straus_thirteen_mod_twentyfour (m : ℕ) :
    (4 : ℚ) / (24 * (m : ℚ) + 13)
      = 1 / (6 * (m : ℚ) + 4)
        + 1 / (2 * ((24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) + 1) / 3)
        + 1 / (2 * ((24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2))
                 * ((24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) + 1) / 3) := by
  have h1 : (6 * (m : ℚ) + 4) > 0 := by positivity
  have h2 : (3 * (m : ℚ) + 2) > 0 := by positivity
  have h3 : (24 * (m : ℚ) + 13) > 0 := by positivity
  have hA : (24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) > 0 := mul_pos h3 h2
  have hA1 : (24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) + 1 > 0 := by linarith
  have h1' : (6 * (m : ℚ) + 4) ≠ 0 := ne_of_gt h1
  have h3' : (24 * (m : ℚ) + 13) ≠ 0 := ne_of_gt h3
  have hA' : (24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) ≠ 0 := ne_of_gt hA
  have hA1' : (24 * (m : ℚ) + 13) * (3 * (m : ℚ) + 2) + 1 ≠ 0 := ne_of_gt hA1
  field_simp
  ring

-- Natural-number existence form is omitted: the rational identity above is
-- the substantive content; converting to ℕ requires showing `3 ∣ 2(A+1)` and
-- `3 ∣ 2A(A+1)` for `A = (24m+13)(3m+2)`, which is a routine omega/Nat
-- manipulation we leave for a follow-up pass.

end ErdosStrausRCL
end NumberTheory
end IndisputableMonolith
