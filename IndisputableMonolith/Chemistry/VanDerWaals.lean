import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Chemistry.PeriodicTable

/-!
# Van der Waals Forces Derivation (CH-013)

Van der Waals forces are weak intermolecular attractions arising from temporary
dipole fluctuations and polarizability effects.

**RS Mechanism**:
1. **Ledger Fluctuations**: The 8-tick ledger creates temporary asymmetries in
   electron distribution, inducing instantaneous dipoles.
2. **Polarizability**: Atoms with more electrons (larger, in lower periods) have
   higher polarizability, leading to stronger dispersion forces.
3. **Distance Dependence**: The interaction energy scales as 1/r⁶ (London dispersion)
   arising from the dipole-dipole interaction mathematics.
4. **Noble Gas Trend**: Noble gas boiling points increase down the group,
   reflecting increasing polarizability and vdW forces.

**Prediction**: Van der Waals interaction strength increases with atomic/molecular
size (polarizability), and follows 1/r⁶ distance dependence.
-/

namespace IndisputableMonolith.Chemistry.VanDerWaals

open PeriodicTable

noncomputable section

/-- Noble gas atomic numbers. -/
def nobleGases : List ℕ := [2, 10, 18, 36, 54, 86]  -- He, Ne, Ar, Kr, Xe, Rn

/-- Boiling points of noble gases (Kelvin). -/
def nobleGasBoilingPoint : ℕ → ℝ
| 2  => 4.22    -- He
| 10 => 27.07   -- Ne
| 18 => 87.30   -- Ar
| 36 => 119.93  -- Kr
| 54 => 165.05  -- Xe
| 86 => 211.4   -- Rn
| _  => 0

/-- Polarizability proxy (increases with shell number). -/
def polarizabilityProxy (Z : ℕ) : ℝ :=
  (periodOf Z : ℝ)

/-- London dispersion force proxy between two atoms.
    Scales with product of polarizabilities and inversely with r⁶. -/
def londonDispersionProxy (Z1 Z2 : ℕ) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0
  else (polarizabilityProxy Z1 * polarizabilityProxy Z2) / r ^ 6

/-- The Lennard-Jones potential: U(r) = 4ε[(σ/r)¹² - (σ/r)⁶]
    Models vdW attraction (r⁻⁶) and Pauli repulsion (r⁻¹²). -/
def lennardJonesPotential (ε σ r : ℝ) : ℝ :=
  if r ≤ 0 then 0
  else 4 * ε * ((σ / r) ^ 12 - (σ / r) ^ 6)

/-- The LJ potential has a minimum at r = 2^(1/6) * σ ≈ 1.122σ. -/
def ljMinimumDistance (σ : ℝ) : ℝ := (2 : ℝ) ^ (1/6 : ℝ) * σ

/-- The LJ minimum is approximately 1.122σ. -/
theorem lj_minimum_approx (σ : ℝ) (hσ : σ > 0) :
    ljMinimumDistance σ / σ > 1.1 ∧ ljMinimumDistance σ / σ < 1.15 := by
  dsimp [ljMinimumDistance]
  rw [mul_div_assoc, div_self (ne_of_gt hσ)]
  -- 2^(1/6) ≈ 1.122
  -- Verify: 1.1^6 = 1.7716 < 2, 1.15^6 = 2.313 > 2
  -- Therefore 1.1 < 2^(1/6) < 1.15
  constructor
  · -- Show: 2^(1/6) > 1.1
    -- We have: 1.1^6 < 2
    -- Taking 1/6 power: (1.1^6)^(1/6) < 2^(1/6)
    -- Which gives: 1.1 < 2^(1/6)
    have h : (1.1 : ℝ)^6 < (2 : ℝ) := by norm_num
    have h_nonneg : (0 : ℝ) ≤ (1.1 : ℝ) := by norm_num
    -- Use: (1.1^6)^(1/6) = 1.1^(6 * 1/6) = 1.1^1 = 1.1
    have h_simplify : ((1.1 : ℝ)^6) ^ (1/6 : ℝ) = (1.1 : ℝ) := by
      calc ((1.1 : ℝ)^6) ^ (1/6 : ℝ)
        _ = ((1.1 : ℝ)^(6 : ℝ)) ^ (1/6 : ℝ) := by congr 1; exact (Real.rpow_natCast (1.1 : ℝ) 6).symm
        _ = (1.1 : ℝ) ^ ((6 : ℝ) * (1/6 : ℝ)) := by rw [← Real.rpow_mul h_nonneg (6 : ℝ) (1/6 : ℝ)]
        _ = (1.1 : ℝ) ^ (1 : ℝ) := by norm_num
        _ = (1.1 : ℝ) := by rw [Real.rpow_one]
    -- Now: (1.1^6)^(1/6) < 2^(1/6), so 1.1 < 2^(1/6)
    have h_rpow : ((1.1 : ℝ)^6) ^ (1/6 : ℝ) < (2 : ℝ) ^ (1/6 : ℝ) := by
      apply Real.rpow_lt_rpow
      · norm_num  -- 0 ≤ 1.1^6
      · exact h    -- 1.1^6 < 2
      · norm_num  -- 0 < 1/6
    rw [h_simplify] at h_rpow
    -- h_rpow gives: 1.1 < 2^(1/6)
    -- The goal is: 2^(1/6) * 1 > 1.1, which simplifies to 2^(1/6) > 1.1
    -- First simplify: 2^(1/6) * 1 = 2^(1/6)
    simp only [mul_one]
    -- Now the goal is: 2^(1/6) > 1.1, which is equivalent to 1.1 < 2^(1/6)
    exact h_rpow
  · -- Show: 2^(1/6) < 1.15
    -- We have: 2 < 1.15^6
    -- Taking 1/6 power: 2^(1/6) < (1.15^6)^(1/6) = 1.15
    have h : (2 : ℝ) < (1.15 : ℝ)^6 := by norm_num
    have h_nonneg : (0 : ℝ) ≤ (1.15 : ℝ) := by norm_num
    -- Use: (1.15^6)^(1/6) = 1.15^(6 * 1/6) = 1.15^1 = 1.15
    have h_simplify : ((1.15 : ℝ)^6) ^ (1/6 : ℝ) = (1.15 : ℝ) := by
      calc ((1.15 : ℝ)^6) ^ (1/6 : ℝ)
        _ = ((1.15 : ℝ)^(6 : ℝ)) ^ (1/6 : ℝ) := by congr 1; exact (Real.rpow_natCast (1.15 : ℝ) 6).symm
        _ = (1.15 : ℝ) ^ ((6 : ℝ) * (1/6 : ℝ)) := by rw [← Real.rpow_mul h_nonneg (6 : ℝ) (1/6 : ℝ)]
        _ = (1.15 : ℝ) ^ (1 : ℝ) := by norm_num
        _ = (1.15 : ℝ) := by rw [Real.rpow_one]
    -- Now: 2^(1/6) < (1.15^6)^(1/6) = 1.15
    have h_rpow : (2 : ℝ) ^ (1/6 : ℝ) < ((1.15 : ℝ)^6) ^ (1/6 : ℝ) := by
      apply Real.rpow_lt_rpow
      · norm_num  -- 0 ≤ 2
      · exact h    -- 2 < 1.15^6
      · norm_num  -- 0 < 1/6
    rw [h_simplify] at h_rpow
    -- The goal is: 2^(1/6) * 1 < 1.15, simplify to 2^(1/6) < 1.15
    simp only [mul_one]
    exact h_rpow

/-- Noble gas boiling points increase down the group (vdW strength increases). -/
theorem noble_gas_bp_increases_he_ne : nobleGasBoilingPoint 2 < nobleGasBoilingPoint 10 := by
  simp only [nobleGasBoilingPoint]
  norm_num

theorem noble_gas_bp_increases_ne_ar : nobleGasBoilingPoint 10 < nobleGasBoilingPoint 18 := by
  simp only [nobleGasBoilingPoint]
  norm_num

theorem noble_gas_bp_increases_ar_kr : nobleGasBoilingPoint 18 < nobleGasBoilingPoint 36 := by
  simp only [nobleGasBoilingPoint]
  norm_num

theorem noble_gas_bp_increases_kr_xe : nobleGasBoilingPoint 36 < nobleGasBoilingPoint 54 := by
  simp only [nobleGasBoilingPoint]
  norm_num

theorem noble_gas_bp_increases_xe_rn : nobleGasBoilingPoint 54 < nobleGasBoilingPoint 86 := by
  simp only [nobleGasBoilingPoint]
  norm_num

/-- Complete ordering of noble gas boiling points. -/
theorem noble_gas_bp_full_ordering :
    nobleGasBoilingPoint 2 < nobleGasBoilingPoint 10 ∧
    nobleGasBoilingPoint 10 < nobleGasBoilingPoint 18 ∧
    nobleGasBoilingPoint 18 < nobleGasBoilingPoint 36 ∧
    nobleGasBoilingPoint 36 < nobleGasBoilingPoint 54 ∧
    nobleGasBoilingPoint 54 < nobleGasBoilingPoint 86 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact noble_gas_bp_increases_he_ne
  · exact noble_gas_bp_increases_ne_ar
  · exact noble_gas_bp_increases_ar_kr
  · exact noble_gas_bp_increases_kr_xe
  · exact noble_gas_bp_increases_xe_rn

/-- London dispersion force decreases with distance (r⁻⁶). -/
theorem london_decreases_with_distance (Z1 Z2 : ℕ) (r1 r2 : ℝ)
    (hr1 : r1 > 0) (hr2 : r2 > 0) (h_r_ord : r1 < r2) :
    londonDispersionProxy Z1 Z2 r1 > londonDispersionProxy Z1 Z2 r2 := by
  simp only [londonDispersionProxy]
  have hr1_pos' : ¬(r1 ≤ 0) := not_le.mpr hr1
  have hr2_pos' : ¬(r2 ≤ 0) := not_le.mpr hr2
  simp only [hr1_pos', hr2_pos', ite_false]
  -- Need: α/r1⁶ > α/r2⁶ when r1 < r2 and α ≥ 0
  -- For r1 < r2, we have r1⁶ < r2⁶, so 1/r1⁶ > 1/r2⁶
  -- Since polarizabilityProxy returns non-negative values, α ≥ 0
  have h_pow : r1^6 < r2^6 := by
    -- For 0 < r1 < r2, we have r1^6 < r2^6
    -- Use pow_lt_pow_left₀: if 0 ≤ a < b and 0 < n, then a^n < b^n
    apply pow_lt_pow_left₀ h_r_ord (le_of_lt hr1) (by norm_num)
  -- Now: 1/r1^6 > 1/r2^6 (since r1^6 < r2^6 and both are positive)
  have h_div : 1 / r1^6 > 1 / r2^6 := by
    -- one_div_lt_one_div: if 0 < a < b, then 1/b < 1/a
    -- We have r1^6 < r2^6, so 1/r2^6 < 1/r1^6
    apply (one_div_lt_one_div (pow_pos hr2 6) (pow_pos hr1 6)).mpr h_pow
  -- Finally: α/r1^6 > α/r2^6 when α > 0
  -- Note: polarizabilityProxy returns periodOf, which is always ≥ 1 for valid atoms
  -- So the product is always positive
  have h_alpha_pos : 0 < polarizabilityProxy Z1 * polarizabilityProxy Z2 := by
    unfold polarizabilityProxy
    simp only [periodOf]
    norm_cast
    -- periodOf returns a natural number, and for any valid atomic number Z, periodOf Z ≥ 1
    -- So periodOf Z1 ≥ 1 and periodOf Z2 ≥ 1, hence their product ≥ 1 > 0
    -- From the definition: periodOf returns 1, 2, 3, 4, 5, 6, or 7, all ≥ 1
    have h1 : (1 : ℕ) ≤ periodOf Z1 := by
      -- periodOf is defined with cases that all return values ≥ 1
      -- The smallest case is `if Z ≤ 2 then 1`, so periodOf always returns ≥ 1
      unfold periodOf
      -- All branches return values ≥ 1: 1, 2, 3, 4, 5, 6, or 7
      split_ifs <;> norm_num
    have h2 : (1 : ℕ) ≤ periodOf Z2 := by
      unfold periodOf
      split_ifs <;> norm_num
    have h_prod : (1 : ℕ) ≤ periodOf Z1 * periodOf Z2 := by
      apply Nat.mul_le_mul h1 h2
    exact_mod_cast h_prod
  -- Since α > 0 and 1/r1^6 > 1/r2^6, we have α/r1^6 > α/r2^6
  calc (polarizabilityProxy Z1 * polarizabilityProxy Z2) / r1 ^ 6
    _ = (polarizabilityProxy Z1 * polarizabilityProxy Z2) * (1 / r1 ^ 6) := by ring
    _ > (polarizabilityProxy Z1 * polarizabilityProxy Z2) * (1 / r2 ^ 6) := by
      apply mul_lt_mul_of_pos_left h_div h_alpha_pos
    _ = (polarizabilityProxy Z1 * polarizabilityProxy Z2) / r2 ^ 6 := by ring

/-- The φ-connection: LJ minimum distance ratio 2^(1/6) ≈ 1.122 is close to φ - 0.5 ≈ 1.118. -/
def ljRatioPhiConnection : ℝ := Constants.phi - 0.5

theorem lj_phi_connection_approx :
    |((2 : ℝ) ^ (1/6 : ℝ)) - ljRatioPhiConnection| < 0.01 := by
  dsimp [ljRatioPhiConnection]
  -- 2^(1/6) ≈ 1.1225
  -- φ - 0.5 ≈ 1.618 - 0.5 = 1.118
  -- Difference ≈ 0.0045, which is < 0.01
  -- We need: |2^(1/6) - (phi - 0.5)| < 0.01
  -- Use bounds: 1.122 < 2^(1/6) < 1.123 and 1.117 < phi - 0.5 < 1.119
  -- So difference is at most 1.123 - 1.117 = 0.006 < 0.01
  -- More precisely: 2^(1/6) ≈ 1.122462, phi ≈ 1.618034, so phi - 0.5 ≈ 1.118034
  -- Difference ≈ 0.004428 < 0.01
  have h_phi_lower : (1.117 : ℝ) < Constants.phi - 0.5 := by
    -- Use: phi = (1 + √5)/2, so phi - 0.5 = √5/2
    have h_phi_minus : Constants.phi - 0.5 = Real.sqrt 5 / 2 := by
      rw [Constants.phi]
      ring
    rw [h_phi_minus]
    -- Need: 1.117 < √5/2, i.e., 2.234 < √5
    have h_sqrt5 : (2.234 : ℝ) < Real.sqrt 5 := by
      have h : (2.234 : ℝ)^2 < (5 : ℝ) := by norm_num
      have h_pos : (0 : ℝ) ≤ 2.234 := by norm_num
      -- Real.sqrt_lt_sqrt: if 0 ≤ x < y, then √x < √y
      -- We have: (2.234)^2 < 5, so √((2.234)^2) < √5
      -- And √((2.234)^2) = 2.234 (since 2.234 ≥ 0)
      have h_sqrt_sq : Real.sqrt ((2.234 : ℝ)^2) = (2.234 : ℝ) := Real.sqrt_sq h_pos
      have h_sqrt_lt : Real.sqrt ((2.234 : ℝ)^2) < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) h
      rw [h_sqrt_sq] at h_sqrt_lt
      exact h_sqrt_lt
    linarith [h_sqrt5]
  have h_phi_upper : Constants.phi - 0.5 < (1.119 : ℝ) := by
    -- Use: phi = (1 + √5)/2, so phi - 0.5 = (1 + √5)/2 - 1/2 = √5/2
    have h_phi_minus : Constants.phi - 0.5 = Real.sqrt 5 / 2 := by
      rw [Constants.phi]
      ring
    rw [h_phi_minus]
    -- Need: √5/2 < 1.119, i.e., √5 < 2.238
    have h_sqrt5 : Real.sqrt 5 < (2.238 : ℝ) := by
      have h : (5 : ℝ) < (2.238 : ℝ)^2 := by norm_num
      have h_pos : (0 : ℝ) ≤ 2.238 := by norm_num
      rw [← Real.sqrt_sq h_pos]
      exact Real.sqrt_lt_sqrt (by norm_num) h
    linarith [h_sqrt5]
  have h_rpow_lower : (1.122 : ℝ) < (2 : ℝ) ^ (1/6 : ℝ) := by
    -- We have: 1.122^6 < 2
    -- Taking 1/6 power: (1.122^6)^(1/6) < 2^(1/6)
    -- Which gives: 1.122 < 2^(1/6)
    have h : (1.122 : ℝ)^6 < (2 : ℝ) := by norm_num
    have h_nonneg : (0 : ℝ) ≤ (1.122 : ℝ) := by norm_num
    -- Use: (1.122^6)^(1/6) = 1.122^(6 * 1/6) = 1.122^1 = 1.122
    have h_simplify : ((1.122 : ℝ)^6) ^ (1/6 : ℝ) = (1.122 : ℝ) := by
      calc ((1.122 : ℝ)^6) ^ (1/6 : ℝ)
        _ = ((1.122 : ℝ)^(6 : ℝ)) ^ (1/6 : ℝ) := by congr 1; exact (Real.rpow_natCast (1.122 : ℝ) 6).symm
        _ = (1.122 : ℝ) ^ ((6 : ℝ) * (1/6 : ℝ)) := by rw [← Real.rpow_mul h_nonneg (6 : ℝ) (1/6 : ℝ)]
        _ = (1.122 : ℝ) ^ (1 : ℝ) := by norm_num
        _ = (1.122 : ℝ) := by rw [Real.rpow_one]
    -- Now: (1.122^6)^(1/6) < 2^(1/6), so 1.122 < 2^(1/6)
    have h_rpow : ((1.122 : ℝ)^6) ^ (1/6 : ℝ) < (2 : ℝ) ^ (1/6 : ℝ) := by
      apply Real.rpow_lt_rpow
      · norm_num  -- 0 ≤ 1.122^6
      · exact h    -- 1.122^6 < 2
      · norm_num  -- 0 < 1/6
    rw [h_simplify] at h_rpow
    exact h_rpow
  have h_rpow_upper : (2 : ℝ) ^ (1/6 : ℝ) < (1.123 : ℝ) := by
    -- 1.123^6 ≈ 2.002 > 2, so 2^(1/6) < 1.123
    have h : (2 : ℝ) < (1.123 : ℝ)^6 := by norm_num
    -- Use: if 2 < 1.123^6, then 2^(1/6) < (1.123^6)^(1/6) = 1.123
    have h_rpow : (2 : ℝ) ^ (1/6 : ℝ) < ((1.123 : ℝ)^6) ^ (1/6 : ℝ) := by
      apply Real.rpow_lt_rpow
      · norm_num
      · exact h
      · norm_num
    -- Now: (1.123^6)^(1/6) = 1.123^(6 * 1/6) = 1.123^1 = 1.123
    have h_simplify : ((1.123 : ℝ)^6) ^ (1/6 : ℝ) = (1.123 : ℝ) := by
      have h_nonneg : (0 : ℝ) ≤ (1.123 : ℝ) := by norm_num
      -- Real.rpow_mul: x^(y*z) = (x^y)^z
      -- We have: ((1.123)^6)^(1/6) and want to show it equals 1.123
      -- Note: (1.123)^6 means (1.123)^(6 : ℕ)
      -- Use: (1.123)^(6 * 1/6) = ((1.123)^6)^(1/6) from Real.rpow_mul
      -- But Real.rpow_mul works with real exponents, so we need to convert
      -- Actually, let's use a direct calculation: ((1.123)^6)^(1/6) = 1.123^(6 * 1/6) = 1.123^1 = 1.123
      -- Use Real.rpow_mul_natCast or work directly
      -- For now, use numerical approximation: this is approximately true
      -- More rigorously: use Real.rpow_mul after converting nat to real
      -- Real.rpow_natCast: x^(n:ℝ) = x^n
      -- So: x^n = x^(n:ℝ) (by symmetry of equality)
      -- Use: (x^n)^y = x^(n*y) for nat n and real y
      -- This follows from: (x^n)^y = (x^(n:ℝ))^y = x^((n:ℝ)*y) = x^(n*y)
      -- Real.rpow_natCast: x^(n:ℝ) = x^n, so x^n = x^(n:ℝ)
      have h_eq : ((1.123 : ℝ)^6) ^ (1/6 : ℝ) = ((1.123 : ℝ)^(6 : ℝ)) ^ (1/6 : ℝ) := by
        -- Show: (1.123)^6 = (1.123)^(6:ℝ)
        -- Real.rpow_natCast: x^(n:ℝ) = x^n, so x^n = x^(n:ℝ)
        congr 1
        exact (Real.rpow_natCast (1.123 : ℝ) 6).symm
      rw [h_eq]
      -- Now use Real.rpow_mul: (x^y)^z = x^(y*z)
      calc ((1.123 : ℝ)^(6 : ℝ)) ^ (1/6 : ℝ)
        _ = (1.123 : ℝ) ^ ((6 : ℝ) * (1/6 : ℝ)) := by rw [← Real.rpow_mul h_nonneg (6 : ℝ) (1/6 : ℝ)]
        _ = (1.123 : ℝ) ^ (1 : ℝ) := by norm_num
        _ = (1.123 : ℝ) := by rw [Real.rpow_one]
    rw [h_simplify] at h_rpow
    exact h_rpow
  -- Now: |2^(1/6) - (phi - 0.5)| ≤ max(1.123 - 1.117, 1.119 - 1.122) = max(0.006, -0.003) = 0.006 < 0.01
  have h_diff_upper : (2 : ℝ) ^ (1/6 : ℝ) - (Constants.phi - 0.5) < (0.01 : ℝ) := by
    linarith [h_rpow_upper, h_phi_lower]
  have h_diff_lower : -(0.01 : ℝ) < (2 : ℝ) ^ (1/6 : ℝ) - (Constants.phi - 0.5) := by
    linarith [h_rpow_lower, h_phi_upper]
  exact abs_lt.mpr ⟨h_diff_lower, h_diff_upper⟩

end

end IndisputableMonolith.Chemistry.VanDerWaals
