import Mathlib
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.RSBridge.Anchor

/-!
# Z-Map Derivation: Z = 1332 from Polynomial Minimality

This module derives the lepton charge index Z_ℓ = 1332 from:

1. **Charge integerization**: k = F(3) = cube_faces(3) = 6
   (one independent 2D symmetry channel per face of Q₃)

2. **Integerized charge**: Q̃_e = k · Q_e = 6 · (-1) = -6

3. **Even polynomial ansatz**: Z(Q̃) = a·Q̃² + b·Q̃⁴
   (charge-conjugation invariance + neutral vanishing + non-negativity)

4. **Coefficient minimality**: (a,b) = (1,1) is the unique pair with
   a ≥ 1, b ≥ 1 minimizing a + b

5. **Result**: Z_ℓ = 1·(-6)² + 1·(-6)⁴ = 36 + 1296 = 1332

## Charge Integerization

The face count k = F(3) = 6 is a structural choice: each face of Q₃
provides one independent 2D symmetry channel for charge quantization.
This is documented as a geometric structural input, not derived from
T0–T8 alone.
-/

namespace IndisputableMonolith
namespace RSBridge
namespace ZMapDerivation

open Constants.AlphaDerivation

/-! ## Charge Integerization -/

/-- The integerization scale: one channel per cube face. -/
def integerization_scale : ℕ := cube_faces 3

theorem integerization_scale_eq : integerization_scale = 6 := by native_decide

/-- The integerized electron charge: Q̃_e = k · Q_e = 6 · (-1) = -6. -/
def Q_tilde_e : ℤ := -(integerization_scale : ℤ)

theorem Q_tilde_e_eq : Q_tilde_e = -6 := by
  simp [Q_tilde_e, integerization_scale_eq]

/-! ## Even Polynomial Ansatz -/

/-- The charge index polynomial: Z(Q̃) = a·Q̃² + b·Q̃⁴.
    Even in Q̃ (charge-conjugation invariance), no constant term
    (neutral vanishing), non-negative coefficients. -/
def Z_poly (a b : ℕ) (q : ℤ) : ℤ := (a : ℤ) * q ^ 2 + (b : ℤ) * q ^ 4

/-- Z is even: Z(Q̃) = Z(-Q̃). -/
theorem Z_poly_even (a b : ℕ) (q : ℤ) :
    Z_poly a b q = Z_poly a b (-q) := by
  unfold Z_poly; ring

/-- Z vanishes at neutral: Z(0) = 0. -/
theorem Z_poly_zero (a b : ℕ) : Z_poly a b 0 = 0 := by
  unfold Z_poly; ring

/-! ## Coefficient Minimality -/

/-- The minimal choice: both terms present, minimum a + b. -/
theorem minimal_coefficients :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 2 ≤ a + b :=
  fun _ _ ha hb => by omega

/-- (1,1) achieves the minimum. -/
theorem unit_coefficients_minimal :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → 1 + 1 ≤ a + b :=
  fun _ _ ha hb => by omega

/-! ## The Derivation: Z_ℓ = 1332 -/

/-- Z_poly with (a,b) = (1,1) at Q̃ = -6 gives 1332. -/
theorem Z_lepton_eq : Z_poly 1 1 (-6) = 1332 := by native_decide

/-- Decomposition: 36 + 1296 = 1332. -/
theorem Z_lepton_decomposition :
    (1 : ℤ) * (-6) ^ 2 = 36 ∧
    (1 : ℤ) * (-6) ^ 4 = 1296 ∧
    (36 : ℤ) + 1296 = 1332 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Consistency: the derived Z equals 1332, matching Anchor.lean's hardcoded value. -/
theorem Z_lepton_matches_anchor_value :
    Z_poly 1 1 Q_tilde_e = 1332 := by
  simp [Z_poly, Q_tilde_e, integerization_scale_eq]

/-- The hardcoded ZOf for the electron is 1332. -/
theorem anchor_electron_Z : RSBridge.ZOf .e = 1332 := rfl

/-- All three leptons share the same charge index. -/
theorem leptons_same_Z :
    RSBridge.ZOf .e = RSBridge.ZOf .mu ∧
    RSBridge.ZOf .mu = RSBridge.ZOf .tau := by
  exact ⟨rfl, rfl⟩

/-! ## Z is strictly increasing (for hierarchy ordering) -/

theorem Z_poly_strictly_increasing (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (q₁ q₂ : ℕ) (hq : q₂ < q₁) (_hq₂ : 0 < q₂) :
    Z_poly a b q₂ < Z_poly a b q₁ := by
  unfold Z_poly
  have h2 : (q₂ : ℤ) ^ 2 < (q₁ : ℤ) ^ 2 := by
    exact_mod_cast Nat.pow_lt_pow_left hq (by omega)
  have h4 : (q₂ : ℤ) ^ 4 < (q₁ : ℤ) ^ 4 := by
    exact_mod_cast Nat.pow_lt_pow_left hq (by omega)
  have ha' : (0 : ℤ) < a := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  have hb' : (0 : ℤ) < b := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hb
  linarith [mul_lt_mul_of_pos_left h2 ha', mul_lt_mul_of_pos_left h4 hb']

/-! ## Summary

The lepton charge index Z_ℓ = 1332 is determined by:
1. k = F(3) = 6 (cube faces — structural input)
2. Q̃_e = -6 (integerized electron charge)
3. (a,b) = (1,1) (minimal complete even polynomial)
4. Z = Q̃² + Q̃⁴ = 36 + 1296 = 1332
-/

end ZMapDerivation
end RSBridge
end IndisputableMonolith
