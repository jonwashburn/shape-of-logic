import Mathlib

/-!
# Erdős-Straus c = 7 Gate Closures

For `n ≡ 1 mod 4`, the gate `c = 7` closes the residue classes
`n mod 7 ∈ {0, 3, 5, 6}` via explicit Egyptian-fraction formulas.

These formulas extend the c = 3 closure layer.  Together with c = 11
and higher gates, the residual class for Erdős-Straus shrinks rapidly,
but never to zero in any fixed bound.

The four parametric closures below collapse to the identity

```text
4/n = (n + 7) / (n · x) = 4/n   [since x = (n + 7)/4]
```

with the remaining factors absorbed by the corresponding modular
divisor `n + 1`, `n + 2`, `2n + 1`, or `n` itself.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Erdos_C7_Closure

/-! ## Case `n ≡ 6 mod 7` (and `n ≡ 1 mod 4`)

CRT residue: `n = 28j + 13`.  Choose `c = 7`, `x = 7j + 5`,
`n + 1 = 14(2j + 1)`.  Concrete trapped instance: `j = 15`, `n = 433`.
-/

theorem erdos_straus_six_mod_seven (j : ℕ) :
    (4 : ℚ) / (28 * (j : ℚ) + 13)
      = 1 / (7 * (j : ℚ) + 5)
        + 1 / (2 * (7 * (j : ℚ) + 5) * (2 * (j : ℚ) + 1))
        + 1 / (2 * (28 * (j : ℚ) + 13) * (7 * (j : ℚ) + 5)
                 * (2 * (j : ℚ) + 1)) := by
  have h1 : (7 * (j : ℚ) + 5) > 0 := by positivity
  have h2 : (2 * (j : ℚ) + 1) > 0 := by positivity
  have h3 : (28 * (j : ℚ) + 13) > 0 := by positivity
  have h1' : (7 * (j : ℚ) + 5) ≠ 0 := ne_of_gt h1
  have h2' : (2 * (j : ℚ) + 1) ≠ 0 := ne_of_gt h2
  have h3' : (28 * (j : ℚ) + 13) ≠ 0 := ne_of_gt h3
  field_simp
  ring

/-! ## Case `n ≡ 0 mod 7` (and `n ≡ 1 mod 24`)

CRT residue: `n = 168j + 49 = 7(24j + 7)`.  Then `x = 14(3j + 1)`,
and `y = z = 2N/7 = 28(24j+7)(3j+1)`.  Concrete instance: `j = 0`,
`n = 49 = 7^2`.
-/

theorem erdos_straus_zero_mod_seven (j : ℕ) :
    (4 : ℚ) / (168 * (j : ℚ) + 49)
      = 1 / (14 * (3 * (j : ℚ) + 1))
        + 1 / (28 * (24 * (j : ℚ) + 7) * (3 * (j : ℚ) + 1))
        + 1 / (28 * (24 * (j : ℚ) + 7) * (3 * (j : ℚ) + 1)) := by
  have h1 : (3 * (j : ℚ) + 1) > 0 := by positivity
  have h2 : (24 * (j : ℚ) + 7) > 0 := by positivity
  have h3 : (168 * (j : ℚ) + 49) > 0 := by positivity
  have h1' : (3 * (j : ℚ) + 1) ≠ 0 := ne_of_gt h1
  have h2' : (24 * (j : ℚ) + 7) ≠ 0 := ne_of_gt h2
  have h3' : (168 * (j : ℚ) + 49) ≠ 0 := ne_of_gt h3
  field_simp
  ring

/-! ## Case `n ≡ 5 mod 7` (and `n ≡ 1 mod 24`)

CRT residue: `n = 168m + 145`.  Then `x = 2(21m + 19)`,
`n + 2 = 21(8m + 7)`.  Concrete trapped instance: `m = 1`, `n = 313`.
-/

theorem erdos_straus_five_mod_seven (m : ℕ) :
    (4 : ℚ) / (168 * (m : ℚ) + 145)
      = 1 / (2 * (21 * (m : ℚ) + 19))
        + 1 / (6 * (21 * (m : ℚ) + 19) * (8 * (m : ℚ) + 7))
        + 1 / ((168 * (m : ℚ) + 145) * 3 * (21 * (m : ℚ) + 19)
                 * (8 * (m : ℚ) + 7)) := by
  have h1 : (21 * (m : ℚ) + 19) > 0 := by positivity
  have h2 : (8 * (m : ℚ) + 7) > 0 := by positivity
  have h3 : (168 * (m : ℚ) + 145) > 0 := by positivity
  have h1' : (21 * (m : ℚ) + 19) ≠ 0 := ne_of_gt h1
  have h2' : (8 * (m : ℚ) + 7) ≠ 0 := ne_of_gt h2
  have h3' : (168 * (m : ℚ) + 145) ≠ 0 := ne_of_gt h3
  field_simp
  ring

/-! ## Case `n ≡ 3 mod 7` (and `n ≡ 1 mod 24`)

CRT residue: `n = 168m + 73`.  Then `x = 2(21m + 10)`,
`2n + 1 = 21(16m + 7)`.  Concrete trapped instance: `m = 0`, `n = 73`.
-/

theorem erdos_straus_three_mod_seven (m : ℕ) :
    (4 : ℚ) / (168 * (m : ℚ) + 73)
      = 1 / (2 * (21 * (m : ℚ) + 10))
        + 1 / (3 * (21 * (m : ℚ) + 10) * (16 * (m : ℚ) + 7))
        + 1 / ((168 * (m : ℚ) + 73) * 6 * (21 * (m : ℚ) + 10)
                 * (16 * (m : ℚ) + 7)) := by
  have h1 : (21 * (m : ℚ) + 10) > 0 := by positivity
  have h2 : (16 * (m : ℚ) + 7) > 0 := by positivity
  have h3 : (168 * (m : ℚ) + 73) > 0 := by positivity
  have h1' : (21 * (m : ℚ) + 10) ≠ 0 := ne_of_gt h1
  have h2' : (16 * (m : ℚ) + 7) ≠ 0 := ne_of_gt h2
  have h3' : (168 * (m : ℚ) + 73) ≠ 0 := ne_of_gt h3
  field_simp
  ring

end Erdos_C7_Closure
end NumberTheory
end IndisputableMonolith
