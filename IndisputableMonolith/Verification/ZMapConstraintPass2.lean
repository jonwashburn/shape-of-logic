import Mathlib

/-!
# Z-Map Constraint Pass 2

This module gives a partial derivational closure for the `Z`-map polynomial:

`Z = c + a·Q̃² + b·Q̃⁴`.

Using the quark family targets
- up-type: `Z_u = 276` at `Q̃ = 4`,
- down-type: `Z_d = 24` at `Q̃ = -2`,

and mild structural constraints
- `0 ≤ a` (quadratic weight nonnegative),
- `0 < b` (quartic term present),

we prove the coefficients are uniquely forced:
- `a = 1`,
- `b = 1`,
- `c = 4`.

This does not yet derive the polynomial from first principles of recognition
topology, but it removes a large part of coefficient arbitrariness.
-/

namespace IndisputableMonolith
namespace Verification
namespace ZMapConstraintPass2

/-- Quartic-even charge polynomial template. -/
def Zpoly (c a b q : ℤ) : ℤ :=
  c + a * q ^ (2 : ℕ) + b * q ^ (4 : ℕ)

/-- Quark constraints force `(a,b,c) = (1,1,4)` under mild structural assumptions. -/
theorem quark_constraints_force_coeffs
    {c a b : ℤ}
    (h_up   : Zpoly c a b 4    = 276)
    (h_down : Zpoly c a b (-2) = 24)
    (ha_nonneg : 0 ≤ a)
    (hb_pos : 0 < b) :
    a = 1 ∧ b = 1 ∧ c = 4 := by
  have hup : c + 16 * a + 256 * b = 276 := by
    simpa [Zpoly, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using h_up
  have hdown : c + 4 * a + 16 * b = 24 := by
    simpa [Zpoly, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
      using h_down
  have hrel : a + 20 * b = 21 := by
    linarith [hup, hdown]
  have hb_one : b = 1 := by
    omega
  have ha_one : a = 1 := by
    omega
  have hc_four : c = 4 := by
    linarith [hdown, ha_one, hb_one]
  exact ⟨ha_one, hb_one, hc_four⟩

/-- With the forced coefficients and lepton offset `c = 0`, the lepton value is fixed. -/
theorem lepton_value_with_forced_coeffs :
    Zpoly 0 1 1 (-6) = 1332 := by
  norm_num [Zpoly]

/-- Quark values with forced coefficients are exactly the two family anchors. -/
theorem quark_values_with_forced_coeffs :
    Zpoly 4 1 1 4 = 276 ∧ Zpoly 4 1 1 (-2) = 24 := by
  constructor <;> norm_num [Zpoly]

end ZMapConstraintPass2
end Verification
end IndisputableMonolith
