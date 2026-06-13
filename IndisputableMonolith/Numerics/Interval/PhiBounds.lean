import IndisputableMonolith.Numerics.Interval.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rigorous Bounds on the Golden Ratio

This module provides rigorous bounds on φ = (1 + √5)/2 using algebraic properties.

## Strategy

We use the fact that:
- 2.236² = 4.999696 < 5 < 5.001956 = 2.237²
- Therefore 2.236 < √5 < 2.237
- Therefore (1 + 2.236)/2 < φ < (1 + 2.237)/2
- i.e., 1.618 < φ < 1.6185

For tighter bounds, we use more decimal places.
-/

namespace IndisputableMonolith.Numerics

open Real

/-- 2.236² < 5 -/
theorem sq_2236_lt_5 : (2.236 : ℝ)^2 < 5 := by norm_num

/-- 5 < 2.237² -/
theorem five_lt_sq_2237 : (5 : ℝ) < (2.237 : ℝ)^2 := by norm_num

/-- 2.236 < √5 -/
theorem sqrt5_gt_2236 : (2.236 : ℝ) < sqrt 5 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.236)]
  exact sqrt_lt_sqrt (by norm_num) sq_2236_lt_5

/-- √5 < 2.237 -/
theorem sqrt5_lt_2237 : sqrt 5 < (2.237 : ℝ) := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.237)]
  exact sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) five_lt_sq_2237

/-- 1.618 < φ -/
theorem phi_gt_1618 : (1.618 : ℝ) < goldenRatio := by
  unfold goldenRatio
  have h : (2.236 : ℝ) < sqrt 5 := sqrt5_gt_2236
  linarith

/-- φ < 1.6185 -/
theorem phi_lt_16185 : goldenRatio < (1.6185 : ℝ) := by
  unfold goldenRatio
  have h : sqrt 5 < (2.237 : ℝ) := sqrt5_lt_2237
  linarith

-- For tighter bounds, we need more precision

/-- 2.2360679² < 5 -/
theorem sq_22360679_lt_5 : (2.2360679 : ℝ)^2 < 5 := by norm_num

/-- 5 < 2.2360680² -/
theorem five_lt_sq_22360680 : (5 : ℝ) < (2.2360680 : ℝ)^2 := by norm_num

/-- 2.2360679 < √5 -/
theorem sqrt5_gt_22360679 : (2.2360679 : ℝ) < sqrt 5 := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.2360679)]
  exact sqrt_lt_sqrt (by norm_num) sq_22360679_lt_5

/-- √5 < 2.2360680 -/
theorem sqrt5_lt_22360680 : sqrt 5 < (2.2360680 : ℝ) := by
  rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.2360680)]
  exact sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) five_lt_sq_22360680

/-- 1.61803395 < φ -/
theorem phi_gt_161803395 : (1.61803395 : ℝ) < goldenRatio := by
  unfold goldenRatio
  have h : (2.2360679 : ℝ) < sqrt 5 := sqrt5_gt_22360679
  linarith

/-- φ < 1.6180340 -/
theorem phi_lt_16180340 : goldenRatio < (1.6180340 : ℝ) := by
  unfold goldenRatio
  have h : sqrt 5 < (2.2360680 : ℝ) := sqrt5_lt_22360680
  linarith

/-- Convenience: a bundled “tight enough” φ bound.

This replaces the legacy `Numerics/Interval.lean` `phi_tight_bounds` lemma and is the
canonical bound used across the codebase going forward. -/
theorem phi_tight_bounds : (1.61803395 : ℝ) < goldenRatio ∧ goldenRatio < (1.6180340 : ℝ) :=
  ⟨phi_gt_161803395, phi_lt_16180340⟩

/-- Interval containing φ with tight bounds -/
def phiIntervalTight : Interval where
  lo := 161803395 / 100000000  -- 1.61803395
  hi := 16180340 / 10000000    -- 1.6180340
  valid := by norm_num

/-- φ is contained in phiIntervalTight - PROVEN -/
theorem phi_in_phiIntervalTight : phiIntervalTight.contains goldenRatio := by
  simp only [Interval.contains, phiIntervalTight]
  constructor
  · have h := phi_gt_161803395
    have h1 : ((161803395 / 100000000 : ℚ) : ℝ) < goldenRatio := by
      calc ((161803395 / 100000000 : ℚ) : ℝ) = (1.61803395 : ℝ) := by norm_num
        _ < goldenRatio := h
    exact le_of_lt h1
  · have h := phi_lt_16180340
    have h1 : goldenRatio < ((16180340 / 10000000 : ℚ) : ℝ) := by
      calc goldenRatio < (1.6180340 : ℝ) := h
        _ = ((16180340 / 10000000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-! ## Quarter-root bounds (needed for quarter/half-ladder rungs) -/

/-- A certified lower rational bound for \(φ^{1/4}\). -/
noncomputable def phi_quarter_lo : ℝ := 1.12783847

/-- A certified upper rational bound for \(φ^{1/4}\). -/
noncomputable def phi_quarter_hi : ℝ := 1.12783849

lemma phi_quarter_lo_pow4_lt_phi_lo : phi_quarter_lo ^ (4 : ℕ) < (1.61803395 : ℝ) := by
  simp [phi_quarter_lo]
  norm_num

lemma phi_hi_lt_phi_quarter_hi_pow4 : (1.6180340 : ℝ) < phi_quarter_hi ^ (4 : ℕ) := by
  simp [phi_quarter_hi]
  norm_num

/-- Lower bound: `phi_quarter_lo < φ^(1/4)` (proved via monotonicity of `x ↦ x^4`). -/
theorem phi_quarter_gt : phi_quarter_lo < goldenRatio ^ (1/4 : ℝ) := by
  have hx : (0 : ℝ) ≤ phi_quarter_lo := by simp [phi_quarter_lo]; norm_num
  have hy : (0 : ℝ) ≤ goldenRatio ^ (1/4 : ℝ) := by
    exact Real.rpow_nonneg (le_of_lt (by simpa using Real.goldenRatio_pos)) _
  have hz : (0 : ℝ) < (4 : ℝ) := by norm_num
  -- Normalize `1/4` to `4⁻¹` to match simp-normal form in `rpow_mul`.
  have hright : (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ) = goldenRatio := by
    have hg0 : (0 : ℝ) ≤ goldenRatio := le_of_lt (by simpa using Real.goldenRatio_pos)
    calc (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ)
        = goldenRatio ^ ((4⁻¹ : ℝ) * (4 : ℝ)) := by
            simpa using (Real.rpow_mul hg0 (4⁻¹ : ℝ) (4 : ℝ)).symm
      _ = goldenRatio ^ (1 : ℝ) := by norm_num
      _ = goldenRatio := by simp
  have hleft : phi_quarter_lo ^ (4 : ℝ) = phi_quarter_lo ^ (4 : ℕ) := by
    simpa using (Real.rpow_natCast phi_quarter_lo 4)
  have hq : phi_quarter_lo ^ (4 : ℝ) < goldenRatio := by
    have h1 : phi_quarter_lo ^ (4 : ℕ) < (1.61803395 : ℝ) := phi_quarter_lo_pow4_lt_phi_lo
    have h2 : (1.61803395 : ℝ) < goldenRatio := phi_gt_161803395
    have h1' : phi_quarter_lo ^ (4 : ℝ) < (1.61803395 : ℝ) := by simpa [hleft] using h1
    exact lt_trans h1' h2
  have hpow : phi_quarter_lo ^ (4 : ℝ) < (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ) := by
    simpa [hright] using hq
  have hlt : phi_quarter_lo < goldenRatio ^ (4⁻¹ : ℝ) :=
    (Real.rpow_lt_rpow_iff hx (by
      exact Real.rpow_nonneg (le_of_lt (by simpa using Real.goldenRatio_pos)) _) hz).1 hpow
  -- `simp` normalizes `(1/4 : ℝ)` to `4⁻¹`, so this closes.
  simpa using hlt

/-- Upper bound: `φ^(1/4) < phi_quarter_hi` (proved via monotonicity of `x ↦ x^4`). -/
theorem phi_quarter_lt : goldenRatio ^ (1/4 : ℝ) < phi_quarter_hi := by
  -- Work in the simp-normal form `4⁻¹` (Lean normalizes `1/4` to `4⁻¹`).
  have hx : (0 : ℝ) ≤ goldenRatio ^ (4⁻¹ : ℝ) := by
    exact Real.rpow_nonneg (le_of_lt (by simpa using Real.goldenRatio_pos)) _
  have hy : (0 : ℝ) ≤ phi_quarter_hi := by simp [phi_quarter_hi]; norm_num
  have hz : (0 : ℝ) < (4 : ℝ) := by norm_num
  have hright : (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ) = goldenRatio := by
    have hg0 : (0 : ℝ) ≤ goldenRatio := le_of_lt (by simpa using Real.goldenRatio_pos)
    calc (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ)
        = goldenRatio ^ ((4⁻¹ : ℝ) * (4 : ℝ)) := by
            simpa using (Real.rpow_mul hg0 (4⁻¹ : ℝ) (4 : ℝ)).symm
      _ = goldenRatio ^ (1 : ℝ) := by norm_num
      _ = goldenRatio := by simp
  have hleft : phi_quarter_hi ^ (4 : ℝ) = phi_quarter_hi ^ (4 : ℕ) := by
    simpa using (Real.rpow_natCast phi_quarter_hi 4)
  have hq : goldenRatio < phi_quarter_hi ^ (4 : ℝ) := by
    have h1 : goldenRatio < (1.6180340 : ℝ) := phi_lt_16180340
    have h2 : (1.6180340 : ℝ) < phi_quarter_hi ^ (4 : ℕ) := phi_hi_lt_phi_quarter_hi_pow4
    have h2' : (1.6180340 : ℝ) < phi_quarter_hi ^ (4 : ℝ) := by simpa [hleft] using h2
    exact lt_trans h1 h2'
  have hpow : (goldenRatio ^ (4⁻¹ : ℝ)) ^ (4 : ℝ) < phi_quarter_hi ^ (4 : ℝ) := by
    simpa [hright] using hq
  have hlt : goldenRatio ^ (4⁻¹ : ℝ) < phi_quarter_hi :=
    (Real.rpow_lt_rpow_iff hx hy hz).1 hpow
  -- convert back to the displayed exponent `1/4`
  simpa using hlt

/-- Consolidated quarter-root bounds. -/
theorem phi_quarter_bounds : phi_quarter_lo < goldenRatio ^ (1/4 : ℝ) ∧ goldenRatio ^ (1/4 : ℝ) < phi_quarter_hi :=
  ⟨phi_quarter_gt, phi_quarter_lt⟩

/-- Bounds for \(φ^{-1/4}\) derived from the quarter-root bounds by inversion. -/
theorem phi_neg_quarter_bounds :
    (1 / phi_quarter_hi) < goldenRatio ^ (-(1/4 : ℝ)) ∧ goldenRatio ^ (-(1/4 : ℝ)) < (1 / phi_quarter_lo) := by
  have hq := phi_quarter_bounds
  have hg0 : (0 : ℝ) ≤ goldenRatio := le_of_lt (by simpa using Real.goldenRatio_pos)
  have hpos : (0 : ℝ) < goldenRatio ^ (4⁻¹ : ℝ) := by
    have : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
    exact Real.rpow_pos_of_pos this _
  have hneg : goldenRatio ^ (-(4⁻¹ : ℝ)) = (goldenRatio ^ (4⁻¹ : ℝ))⁻¹ := by
    simpa using (Real.rpow_neg hg0 (4⁻¹ : ℝ))
  have hlo : phi_quarter_lo < goldenRatio ^ (4⁻¹ : ℝ) := by
    simpa using hq.1
  have hhi : goldenRatio ^ (4⁻¹ : ℝ) < phi_quarter_hi := by
    simpa using hq.2
  have h_lower : (1 / phi_quarter_hi) < 1 / (goldenRatio ^ (4⁻¹ : ℝ)) :=
    one_div_lt_one_div_of_lt hpos hhi
  have h_upper : (1 / (goldenRatio ^ (4⁻¹ : ℝ))) < (1 / phi_quarter_lo) :=
    one_div_lt_one_div_of_lt (by
      have : (0 : ℝ) < phi_quarter_lo := by simp [phi_quarter_lo]; norm_num
      exact this) hlo
  -- `simp` normalizes `-(1/4)` to `-(4⁻¹)`
  constructor
  · simpa [hneg, one_div] using h_lower
  · simpa [hneg, one_div] using h_upper

/-! ## Powers of φ using the recurrence φ² = φ + 1 -/

/-- φ² = φ + 1, so 2.618 < φ² < 2.619 -/
theorem phi_sq_gt : (2.618 : ℝ) < goldenRatio ^ 2 := by
  have h := phi_gt_1618
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  linarith

theorem phi_sq_lt : goldenRatio ^ 2 < (2.619 : ℝ) := by
  have h := phi_lt_16185
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  linarith

/-! ## φ^(-2) bounds (for quark masses) -/

/-- φ^(-2) > 0.3818 (using φ² < 2.619) -/
theorem phi_neg2_gt : (0.3818 : ℝ) < goldenRatio ^ (-2 : ℤ) := by
  have h := phi_sq_lt  -- φ² < 2.619
  have hpos : (0 : ℝ) < goldenRatio ^ 2 := by positivity
  have heq : goldenRatio ^ (-2 : ℤ) = (goldenRatio ^ 2)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 2)
  rw [heq]
  have h1 : (0.3818 : ℝ) < 1 / (2.619 : ℝ) := by norm_num
  have h2 : 1 / (2.619 : ℝ) < 1 / goldenRatio ^ 2 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 2 = (goldenRatio ^ 2)⁻¹ := one_div _
  linarith

/-- φ^(-2) < 0.382 (using φ² > 2.618) -/
theorem phi_neg2_lt : goldenRatio ^ (-2 : ℤ) < (0.382 : ℝ) := by
  have h := phi_sq_gt  -- 2.618 < φ²
  have hpos_bound : (0 : ℝ) < 2.618 := by norm_num
  have heq : goldenRatio ^ (-2 : ℤ) = (goldenRatio ^ 2)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 2)
  rw [heq]
  have h1 : (goldenRatio ^ 2)⁻¹ < (2.618 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (2.618 : ℝ)⁻¹ < (0.382 : ℝ) := by norm_num
  linarith

/-! ## Negative powers of φ (using φ⁻¹ = φ - 1) -/

/-- φ⁻¹ = φ - 1 ≈ 0.618 -/
theorem phi_inv_eq : goldenRatio⁻¹ = goldenRatio - 1 := by
  -- φ⁻¹ = -ψ = -(1 - √5)/2 = (√5 - 1)/2 = (1 + √5)/2 - 1 = φ - 1
  rw [inv_goldenRatio]
  unfold goldenRatio goldenConj
  ring

theorem phi_inv_gt : (0.618 : ℝ) < goldenRatio⁻¹ := by
  rw [phi_inv_eq]
  have h := phi_gt_1618
  linarith

theorem phi_inv_lt : goldenRatio⁻¹ < (0.6186 : ℝ) := by
  rw [phi_inv_eq]
  have h := phi_lt_16185
  linarith

/-- Interval containing φ⁻¹ - PROVEN -/
def phi_inv_interval_proven : Interval where
  lo := 618 / 1000
  hi := 6186 / 10000
  valid := by norm_num

theorem phi_inv_in_interval_proven : phi_inv_interval_proven.contains goldenRatio⁻¹ := by
  simp only [Interval.contains, phi_inv_interval_proven]
  constructor
  · have h := phi_inv_gt
    exact le_of_lt (by calc ((618 / 1000 : ℚ) : ℝ) = (0.618 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ := h)
  · have h := phi_inv_lt
    exact le_of_lt (by calc goldenRatio⁻¹ < (0.6186 : ℝ) := h
      _ = ((6186 / 10000 : ℚ) : ℝ) := by norm_num)

/-! ## Higher powers using Fibonacci recurrence φ^(n+2) = φ^(n+1) + φ^n -/

/-- φ³ = φ² + φ = (φ + 1) + φ = 2φ + 1 -/
theorem phi_cubed_eq : goldenRatio ^ 3 = 2 * goldenRatio + 1 := by
  have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  calc goldenRatio ^ 3 = goldenRatio ^ 2 * goldenRatio := by ring
    _ = (goldenRatio + 1) * goldenRatio := by rw [h]
    _ = goldenRatio ^ 2 + goldenRatio := by ring
    _ = (goldenRatio + 1) + goldenRatio := by rw [h]
    _ = 2 * goldenRatio + 1 := by ring

theorem phi_cubed_gt : (4.236 : ℝ) < goldenRatio ^ 3 := by
  rw [phi_cubed_eq]
  have h := phi_gt_1618
  linarith

theorem phi_cubed_lt : goldenRatio ^ 3 < (4.237 : ℝ) := by
  rw [phi_cubed_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁴ = φ³ + φ² = (2φ + 1) + (φ + 1) = 3φ + 2 -/
theorem phi_pow4_eq : goldenRatio ^ 4 = 3 * goldenRatio + 2 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h3 : goldenRatio ^ 3 = 2 * goldenRatio + 1 := phi_cubed_eq
  calc goldenRatio ^ 4 = goldenRatio ^ 3 * goldenRatio := by ring
    _ = (2 * goldenRatio + 1) * goldenRatio := by rw [h3]
    _ = 2 * goldenRatio ^ 2 + goldenRatio := by ring
    _ = 2 * (goldenRatio + 1) + goldenRatio := by rw [h2]
    _ = 3 * goldenRatio + 2 := by ring

theorem phi_pow4_gt : (6.854 : ℝ) < goldenRatio ^ 4 := by
  rw [phi_pow4_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow4_lt : goldenRatio ^ 4 < (6.856 : ℝ) := by
  rw [phi_pow4_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁵ = φ⁴ + φ³ = (3φ + 2) + (2φ + 1) = 5φ + 3 -/
theorem phi_pow5_eq : goldenRatio ^ 5 = 5 * goldenRatio + 3 := by
  have h3 : goldenRatio ^ 3 = 2 * goldenRatio + 1 := phi_cubed_eq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := phi_pow4_eq
  calc goldenRatio ^ 5 = goldenRatio ^ 4 * goldenRatio := by ring
    _ = (3 * goldenRatio + 2) * goldenRatio := by rw [h4]
    _ = 3 * goldenRatio ^ 2 + 2 * goldenRatio := by ring
    _ = 3 * (goldenRatio + 1) + 2 * goldenRatio := by rw [goldenRatio_sq]
    _ = 5 * goldenRatio + 3 := by ring

theorem phi_pow5_gt : (11.09 : ℝ) < goldenRatio ^ 5 := by
  rw [phi_pow5_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow5_lt : goldenRatio ^ 5 < (11.1 : ℝ) := by
  rw [phi_pow5_eq]
  have h := phi_lt_16185
  linarith

/-- φ⁶ = 8φ + 5 -/
theorem phi_pow6_eq : goldenRatio ^ 6 = 8 * goldenRatio + 5 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := phi_pow4_eq
  calc goldenRatio ^ 6 = goldenRatio ^ 4 * goldenRatio ^ 2 := by ring
    _ = (3 * goldenRatio + 2) * (goldenRatio + 1) := by rw [h4, h2]
    _ = 3 * goldenRatio ^ 2 + 5 * goldenRatio + 2 := by ring
    _ = 3 * (goldenRatio + 1) + 5 * goldenRatio + 2 := by rw [h2]
    _ = 8 * goldenRatio + 5 := by ring

/-- φ⁷ = 13φ + 8 -/
theorem phi_pow7_eq : goldenRatio ^ 7 = 13 * goldenRatio + 8 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h5 : goldenRatio ^ 5 = 5 * goldenRatio + 3 := phi_pow5_eq
  calc goldenRatio ^ 7 = goldenRatio ^ 5 * goldenRatio ^ 2 := by ring
    _ = (5 * goldenRatio + 3) * (goldenRatio + 1) := by rw [h5, h2]
    _ = 5 * goldenRatio ^ 2 + 8 * goldenRatio + 3 := by ring
    _ = 5 * (goldenRatio + 1) + 8 * goldenRatio + 3 := by rw [h2]
    _ = 13 * goldenRatio + 8 := by ring

/-- φ⁸ = F₈·φ + F₇ = 21φ + 13 (where F_n is Fibonacci) -/
theorem phi_pow8_eq : goldenRatio ^ 8 = 21 * goldenRatio + 13 := by
  -- φ⁶ = 8φ + 5, φ⁷ = 13φ + 8, φ⁸ = 21φ + 13
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h4 : goldenRatio ^ 4 = 3 * goldenRatio + 2 := phi_pow4_eq
  calc goldenRatio ^ 8 = goldenRatio ^ 4 * goldenRatio ^ 4 := by ring
    _ = (3 * goldenRatio + 2) * (3 * goldenRatio + 2) := by rw [h4]
    _ = 9 * goldenRatio ^ 2 + 12 * goldenRatio + 4 := by ring
    _ = 9 * (goldenRatio + 1) + 12 * goldenRatio + 4 := by rw [h2]
    _ = 21 * goldenRatio + 13 := by ring

theorem phi_pow8_gt : (46.97 : ℝ) < goldenRatio ^ 8 := by
  rw [phi_pow8_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow8_lt : goldenRatio ^ 8 < (46.99 : ℝ) := by
  rw [phi_pow8_eq]
  have h := phi_lt_16185
  linarith

/-- Interval containing φ⁸ - PROVEN -/
def phi_pow8_interval_proven : Interval where
  lo := 4697 / 100
  hi := 4699 / 100
  valid := by norm_num

theorem phi_pow8_in_interval_proven : phi_pow8_interval_proven.contains (goldenRatio ^ 8) := by
  simp only [Interval.contains, phi_pow8_interval_proven]
  constructor
  · have h := phi_pow8_gt
    exact le_of_lt (by calc ((4697 / 100 : ℚ) : ℝ) = (46.97 : ℝ) := by norm_num
      _ < goldenRatio ^ 8 := h)
  · have h := phi_pow8_lt
    exact le_of_lt (by calc goldenRatio ^ 8 < (46.99 : ℝ) := h
      _ = ((4699 / 100 : ℚ) : ℝ) := by norm_num)

/-! ## Negative powers using (φ⁻¹)^n -/

/-- (φ⁻¹)² bounds -/
theorem phi_inv2_gt : (0.381 : ℝ) < goldenRatio⁻¹ ^ 2 := by
  have h := phi_inv_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

theorem phi_inv2_lt : goldenRatio⁻¹ ^ 2 < (0.383 : ℝ) := by
  have h := phi_inv_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

/-- (φ⁻¹)³ bounds -/
theorem phi_inv3_gt : (0.2359 : ℝ) < goldenRatio⁻¹ ^ 3 := by
  have h1 := phi_inv_gt
  have h2 := phi_inv2_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  nlinarith [sq_nonneg goldenRatio⁻¹]

theorem phi_inv3_lt : goldenRatio⁻¹ ^ 3 < (0.237 : ℝ) := by
  have h1 := phi_inv_lt
  have h2 := phi_inv2_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  nlinarith [sq_nonneg goldenRatio⁻¹]

/-- Interval containing (φ⁻¹)³ - PROVEN -/
def phi_inv3_interval_proven : Interval where
  lo := 2359 / 10000
  hi := 237 / 1000
  valid := by norm_num

theorem phi_inv3_in_interval_proven : phi_inv3_interval_proven.contains (goldenRatio⁻¹ ^ 3) := by
  simp only [Interval.contains, phi_inv3_interval_proven]
  constructor
  · have h := phi_inv3_gt
    exact le_of_lt (by calc ((2359 / 10000 : ℚ) : ℝ) = (0.2359 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ ^ 3 := h)
  · have h := phi_inv3_lt
    exact le_of_lt (by calc goldenRatio⁻¹ ^ 3 < (0.237 : ℝ) := h
      _ = ((237 / 1000 : ℚ) : ℝ) := by norm_num)

/-! ## Direct bounds for φ^(-3) (zpow form)

Some physics modules use `phi ^ (-3 : ℤ)` directly (rather than `(phi⁻¹)^3`), so we provide
an explicit, proven envelope in zpow form.

This replaces the legacy `Numerics/Interval.lean` theorem `phi_inv3_zpow_bounds`. -/

theorem phi_inv3_zpow_bounds :
    (0.2360 : ℝ) < goldenRatio ^ (-3 : ℤ) ∧ goldenRatio ^ (-3 : ℤ) < (0.2361 : ℝ) := by
  -- Rewrite φ^(-3) as the inverse of φ^3 and use φ^3 = 2φ + 1.
  have h3 : goldenRatio ^ (3 : ℕ) = 2 * goldenRatio + 1 := phi_cubed_eq
  have hz : goldenRatio ^ (-3 : ℤ) = (goldenRatio ^ (3 : ℕ))⁻¹ := by
    simpa using (zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < (3 : ℕ)))
  have hz' : goldenRatio ^ (-3 : ℤ) = (2 * goldenRatio + 1)⁻¹ := by
    rw [hz, h3]

  -- Bounds on 2φ + 1 from the bundled φ bounds.
  have hlo : (4.2360679 : ℝ) < 2 * goldenRatio + 1 := by
    have hφ := phi_tight_bounds.1
    linarith
  have hhi : 2 * goldenRatio + 1 < (4.2360680 : ℝ) := by
    have hφ := phi_tight_bounds.2
    linarith
  have hpos : (0 : ℝ) < 2 * goldenRatio + 1 := lt_trans (by norm_num) hlo

  -- Invert the inequalities.
  have h_lower : (1 / (4.2360680 : ℝ)) < (2 * goldenRatio + 1)⁻¹ := by
    have := one_div_lt_one_div_of_lt hpos hhi
    simpa [one_div] using this
  have h_upper : (2 * goldenRatio + 1)⁻¹ < (1 / (4.2360679 : ℝ)) := by
    have hpos_lo : (0 : ℝ) < (4.2360679 : ℝ) := by norm_num
    have := one_div_lt_one_div_of_lt hpos_lo hlo
    simpa [one_div] using this

  constructor
  · have hnum : (0.2360 : ℝ) < 1 / (4.2360680 : ℝ) := by norm_num
    have : (0.2360 : ℝ) < (2 * goldenRatio + 1)⁻¹ := lt_trans hnum h_lower
    simpa [hz'] using this
  · have hnum : (1 / (4.2360679 : ℝ)) < (0.2361 : ℝ) := by norm_num
    have : (2 * goldenRatio + 1)⁻¹ < (0.2361 : ℝ) := lt_trans h_upper hnum
    simpa [hz'] using this

/-- (φ⁻¹)⁵ bounds - using 0.381 * 0.2359 ≈ 0.0899 -/
theorem phi_inv5_gt : (0.089 : ℝ) < goldenRatio⁻¹ ^ 5 := by
  have h2 := phi_inv2_gt
  have h3 := phi_inv3_gt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  have hpos3 : 0 < goldenRatio⁻¹ ^ 3 := pow_pos hpos 3
  have h : goldenRatio⁻¹ ^ 5 = goldenRatio⁻¹ ^ 2 * goldenRatio⁻¹ ^ 3 := by ring
  nlinarith

theorem phi_inv5_lt : goldenRatio⁻¹ ^ 5 < (0.091 : ℝ) := by
  have h2 := phi_inv2_lt
  have h3 := phi_inv3_lt
  have hpos : 0 < goldenRatio⁻¹ := inv_pos.mpr goldenRatio_pos
  have hpos2 : 0 < goldenRatio⁻¹ ^ 2 := sq_pos_of_pos hpos
  have hpos3 : 0 < goldenRatio⁻¹ ^ 3 := pow_pos hpos 3
  have h : goldenRatio⁻¹ ^ 5 = goldenRatio⁻¹ ^ 2 * goldenRatio⁻¹ ^ 3 := by ring
  nlinarith

/-- Interval containing (φ⁻¹)⁵ - PROVEN -/
def phi_inv5_interval_proven : Interval where
  lo := 89 / 1000
  hi := 91 / 1000
  valid := by norm_num

theorem phi_inv5_in_interval_proven : phi_inv5_interval_proven.contains (goldenRatio⁻¹ ^ 5) := by
  simp only [Interval.contains, phi_inv5_interval_proven]
  constructor
  · have h := phi_inv5_gt
    exact le_of_lt (by calc ((89 / 1000 : ℚ) : ℝ) = (0.089 : ℝ) := by norm_num
      _ < goldenRatio⁻¹ ^ 5 := h)
  · have h := phi_inv5_lt
    exact le_of_lt (by calc goldenRatio⁻¹ ^ 5 < (0.091 : ℝ) := h
      _ = ((91 / 1000 : ℚ) : ℝ) := by norm_num)

/-! ## Higher powers for φ^16 -/

/-- φ^16 = F₁₆·φ + F₁₅ = 987φ + 610 -/
theorem phi_pow16_eq : goldenRatio ^ 16 = 987 * goldenRatio + 610 := by
  have h2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h8 : goldenRatio ^ 8 = 21 * goldenRatio + 13 := phi_pow8_eq
  calc goldenRatio ^ 16 = goldenRatio ^ 8 * goldenRatio ^ 8 := by ring
    _ = (21 * goldenRatio + 13) * (21 * goldenRatio + 13) := by rw [h8]
    _ = 441 * goldenRatio ^ 2 + 546 * goldenRatio + 169 := by ring
    _ = 441 * (goldenRatio + 1) + 546 * goldenRatio + 169 := by rw [h2]
    _ = 987 * goldenRatio + 610 := by ring

theorem phi_pow16_gt : (2206.9 : ℝ) < goldenRatio ^ 16 := by
  rw [phi_pow16_eq]
  have h := phi_gt_1618
  linarith

theorem phi_pow16_lt : goldenRatio ^ 16 < (2207.5 : ℝ) := by
  rw [phi_pow16_eq]
  have h := phi_lt_16185
  linarith

/-- φ^51 = F₅₁·φ + F₅₀ = 20365011074·φ + 12586269025 -/
theorem phi_pow51_eq : goldenRatio ^ 51 = 20365011074 * goldenRatio + 12586269025 := by
  have h :=
    (Real.goldenRatio_mul_fib_succ_add_fib 50 :
        goldenRatio * (Nat.fib 51 : ℝ) + Nat.fib 50 = goldenRatio ^ 51)
  have fib51 : (Nat.fib 51 : ℝ) = 20365011074 := by norm_num
  have fib50 : (Nat.fib 50 : ℝ) = 12586269025 := by norm_num
  simpa [fib51, fib50, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h.symm

theorem phi_pow51_gt : (45537548334 : ℝ) < goldenRatio ^ 51 := by
  rw [phi_pow51_eq]
  have hphi := phi_gt_161803395
  linarith

theorem phi_pow51_lt : goldenRatio ^ 51 < (45537549354 : ℝ) := by
  rw [phi_pow51_eq]
  have h := phi_lt_16180340
  linarith

def phi_pow51_interval_proven : Interval where
  lo := 45537548334
  hi := 45537549354
  valid := by norm_num

theorem phi_pow51_in_interval_proven :
    phi_pow51_interval_proven.contains (goldenRatio ^ 51) := by
  simp [Interval.contains, phi_pow51_interval_proven, phi_pow51_gt, phi_pow51_lt, le_of_lt]

/-! ## φ^54 bounds (for neutrino mass predictions) -/

/-- φ^54 = φ^51 × φ^3 -/
theorem phi_pow54_eq : goldenRatio ^ 54 = goldenRatio ^ 51 * goldenRatio ^ 3 := by
  ring_nf

/-- φ^54 > 192894126000 (using φ^51 > 45536856942 and φ^3 > 4.236) -/
theorem phi_pow54_gt : (192894126000 : ℝ) < goldenRatio ^ 54 := by
  rw [phi_pow54_eq]
  have h51 := phi_pow51_gt  -- 45536856942 < φ^51
  have h3 := phi_cubed_gt   -- 4.236 < φ^3
  have hpos51 : (0 : ℝ) < goldenRatio ^ 51 := by positivity
  have hpos3 : (0 : ℝ) < goldenRatio ^ 3 := by positivity
  -- 45536856942 * 4.236 = 192894126006.312 > 192894126000
  calc (192894126000 : ℝ) < (45536856942 : ℝ) * (4.236 : ℝ) := by norm_num
    _ < goldenRatio ^ 51 * (4.236 : ℝ) := by nlinarith
    _ < goldenRatio ^ 51 * goldenRatio ^ 3 := by nlinarith

/-- φ^54 < 192983018016 (using φ^51 < 45547089449 and φ^3 < 4.237) -/
theorem phi_pow54_lt : goldenRatio ^ 54 < (192983018016 : ℝ) := by
  rw [phi_pow54_eq]
  have h51 := phi_pow51_lt  -- φ^51 < 45547089449
  have h3 := phi_cubed_lt   -- φ^3 < 4.237
  have hpos51 : (0 : ℝ) < goldenRatio ^ 51 := by positivity
  have hpos3 : (0 : ℝ) < goldenRatio ^ 3 := by positivity
  -- 45547089449 * 4.237 = 192983018015.413 < 192983018016
  calc goldenRatio ^ 51 * goldenRatio ^ 3 < (45547089449 : ℝ) * goldenRatio ^ 3 := by nlinarith
    _ < (45547089449 : ℝ) * (4.237 : ℝ) := by nlinarith
    _ < (192983018016 : ℝ) := by norm_num

/-! ## φ^(-54) bounds (for neutrino mass predictions) -/

/-- φ^(-54) > 5.181e-12 (using φ^54 < 192983018016) -/
theorem phi_neg54_gt : (5.181e-12 : ℝ) < goldenRatio ^ (-54 : ℤ) := by
  have h := phi_pow54_lt  -- φ^54 < 192983018016
  have hpos : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have heq : goldenRatio ^ (-54 : ℤ) = (goldenRatio ^ 54)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 54)
  rw [heq]
  -- 1/192983018016 > 5.181e-12
  have h1 : (5.181e-12 : ℝ) < 1 / (192983018016 : ℝ) := by norm_num
  have h2 : 1 / (192983018016 : ℝ) < 1 / goldenRatio ^ 54 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 54 = (goldenRatio ^ 54)⁻¹ := one_div _
  linarith

/-- φ^(-54) < 5.185e-12 (using φ^54 > 192894126000) -/
theorem phi_neg54_lt : goldenRatio ^ (-54 : ℤ) < (5.185e-12 : ℝ) := by
  have h := phi_pow54_gt  -- 192894126000 < φ^54
  have hpos_bound : (0 : ℝ) < 192894126000 := by norm_num
  have heq : goldenRatio ^ (-54 : ℤ) = (goldenRatio ^ 54)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 54)
  rw [heq]
  -- 1/192894126000 < 5.185e-12
  have h1 : (goldenRatio ^ 54)⁻¹ < (192894126000 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (192894126000 : ℝ)⁻¹ < (5.185e-12 : ℝ) := by norm_num
  linarith

/-! ## φ^58 bounds (for neutrino mass predictions) -/

/-- φ^58 = φ^54 × φ^4 -/
theorem phi_pow58_eq : goldenRatio ^ 58 = goldenRatio ^ 54 * goldenRatio ^ 4 := by
  ring_nf

/-- φ^58 > 1.3219e12 (using φ^54 > 192894126000 and φ^4 > 6.854) -/
theorem phi_pow58_gt : (1.3219e12 : ℝ) < goldenRatio ^ 58 := by
  rw [phi_pow58_eq]
  have h54 := phi_pow54_gt  -- 192894126000 < φ^54
  have h4 := phi_pow4_gt    -- 6.854 < φ^4
  have hpos54 : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have hpos4 : (0 : ℝ) < goldenRatio ^ 4 := by positivity
  -- 192894126000 * 6.854 = 1321900000000.0
  calc (1.3219e12 : ℝ) ≤ (192894126000 : ℝ) * (6.854 : ℝ) := by norm_num
    _ < goldenRatio ^ 54 * (6.854 : ℝ) := by nlinarith
    _ < goldenRatio ^ 54 * goldenRatio ^ 4 := by nlinarith

/-- φ^58 < 1.324e12 (using φ^54 < 192983018016 and φ^4 < 6.86) -/
theorem phi_pow58_lt : goldenRatio ^ 58 < (1.324e12 : ℝ) := by
  rw [phi_pow58_eq]
  have h54 := phi_pow54_lt  -- φ^54 < 192983018016
  have h4 := phi_pow4_lt    -- φ^4 < 6.86
  have hpos54 : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  have hpos4 : (0 : ℝ) < goldenRatio ^ 4 := by positivity
  calc goldenRatio ^ 54 * goldenRatio ^ 4 < (192983018016 : ℝ) * goldenRatio ^ 4 := by nlinarith
    _ < (192983018016 : ℝ) * (6.86 : ℝ) := by nlinarith
    _ < (1.324e12 : ℝ) := by norm_num

/-! ## φ^(-58) bounds (for neutrino mass predictions) -/

/-- φ^(-58) > 7.55e-13 (using φ^58 < 1.324e12) -/
theorem phi_neg58_gt : (7.55e-13 : ℝ) < goldenRatio ^ (-58 : ℤ) := by
  have h := phi_pow58_lt  -- φ^58 < 1.324e12
  have hpos : (0 : ℝ) < goldenRatio ^ 58 := by positivity
  have heq : goldenRatio ^ (-58 : ℤ) = (goldenRatio ^ 58)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 58)
  rw [heq]
  have h1 : (7.55e-13 : ℝ) < 1 / (1.324e12 : ℝ) := by norm_num
  have h2 : 1 / (1.324e12 : ℝ) < 1 / goldenRatio ^ 58 :=
    one_div_lt_one_div_of_lt hpos h
  have h3 : 1 / goldenRatio ^ 58 = (goldenRatio ^ 58)⁻¹ := one_div _
  linarith

/-- φ^(-58) < 7.57e-13 (using φ^58 > 1.3219e12) -/
theorem phi_neg58_lt : goldenRatio ^ (-58 : ℤ) < (7.57e-13 : ℝ) := by
  have h := phi_pow58_gt  -- 1.3219e12 < φ^58
  have hpos_bound : (0 : ℝ) < 1.3219e12 := by norm_num
  have heq : goldenRatio ^ (-58 : ℤ) = (goldenRatio ^ 58)⁻¹ :=
    zpow_neg_coe_of_pos goldenRatio (by norm_num : 0 < 58)
  rw [heq]
  have h1 : (goldenRatio ^ 58)⁻¹ < (1.3219e12 : ℝ)⁻¹ :=
    inv_strictAnti₀ hpos_bound h
  have h2 : (1.3219e12 : ℝ)⁻¹ < (7.57e-13 : ℝ) := by norm_num
  linarith

/-! ## Quarter-step derived bounds (φ^(-217/4), φ^(-231/4))

These are the first interval-style lemmas needed to support **quarter/half-ladder**
neutrino rungs without numeric axioms.

Strategy:
- use proven integer-power bounds (e.g. `phi_neg54_gt/lt`, `phi_neg58_gt/lt`)
- use proven quarter-root bounds (`phi_quarter_bounds`, `phi_neg_quarter_bounds`)
- combine via `Real.rpow_add` and monotone multiplication
-/

private lemma qhi_pos : (0 : ℝ) < phi_quarter_hi := by
  simp [phi_quarter_hi]; norm_num

private lemma qlo_pos : (0 : ℝ) < phi_quarter_lo := by
  simp [phi_quarter_lo]; norm_num

/-- Lower bound for \(φ^{-217/4} = φ^{-54}·φ^{-1/4}\). -/
theorem phi_neg2174_gt : (4.593e-12 : ℝ) < goldenRatio ^ (((-217 : ℚ) / 4 : ℚ) : ℝ) := by
  -- Split exponent: -217/4 = -54 - 1/4 (in simp-normal form: -54 + -(4⁻¹))
  have hexp : (((-217 : ℚ) / 4 : ℚ) : ℝ) = (-54 : ℝ) + (-(4⁻¹ : ℝ)) := by
    norm_num
  have hposφ : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
  have hsplit :
      goldenRatio ^ (((-217 : ℚ) / 4 : ℚ) : ℝ)
        = goldenRatio ^ (-54 : ℝ) * goldenRatio ^ (-(4⁻¹ : ℝ)) := by
    simpa [hexp] using (Real.rpow_add hposφ (-54 : ℝ) (-(4⁻¹ : ℝ)))
  -- Convert φ^(-54:ℝ) to zpow for reuse of existing bounds.
  have hz54 : goldenRatio ^ (-54 : ℝ) = goldenRatio ^ (-54 : ℤ) := by
    rw [← Real.rpow_intCast]
    norm_cast
  have h54_lo : (5.181e-12 : ℝ) < goldenRatio ^ (-54 : ℝ) := by
    simpa [hz54] using phi_neg54_gt
  have hq := phi_neg_quarter_bounds
  have hq_lo : (1 / phi_quarter_hi) < goldenRatio ^ (-(4⁻¹ : ℝ)) := by
    -- `simp` normalizes `-(1/4)` to `-(4⁻¹)`
    simpa using hq.1
  have hq_pos : (0 : ℝ) < (1 / phi_quarter_hi) := by
    exact one_div_pos.2 qhi_pos
  have hφ54_pos : (0 : ℝ) < goldenRatio ^ (-54 : ℝ) := by
    linarith [h54_lo]
  -- Numeric: 4.593e-12 < 5.181e-12 * (1/phi_quarter_hi)
  have hnum : (4.593e-12 : ℝ) < (5.181e-12 : ℝ) * (1 / phi_quarter_hi) := by
    simp [phi_quarter_hi]
    norm_num
  -- Propagate bounds to the product.
  have hstep1 : (5.181e-12 : ℝ) * (1 / phi_quarter_hi) < (goldenRatio ^ (-54 : ℝ)) * (1 / phi_quarter_hi) :=
    mul_lt_mul_of_pos_right h54_lo hq_pos
  have hstep2 : (goldenRatio ^ (-54 : ℝ)) * (1 / phi_quarter_hi) < (goldenRatio ^ (-54 : ℝ)) * (goldenRatio ^ (-(4⁻¹ : ℝ))) :=
    mul_lt_mul_of_pos_left hq_lo hφ54_pos
  -- Finish.
  rw [hsplit]
  exact lt_trans hnum (lt_trans hstep1 hstep2)

/-- Upper bound for \(φ^{-217/4} = φ^{-54}·φ^{-1/4}\). -/
theorem phi_neg2174_lt : goldenRatio ^ (((-217 : ℚ) / 4 : ℚ) : ℝ) < (4.598e-12 : ℝ) := by
  have hexp : (((-217 : ℚ) / 4 : ℚ) : ℝ) = (-54 : ℝ) + (-(4⁻¹ : ℝ)) := by
    norm_num
  have hposφ : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
  have hsplit :
      goldenRatio ^ (((-217 : ℚ) / 4 : ℚ) : ℝ)
        = goldenRatio ^ (-54 : ℝ) * goldenRatio ^ (-(4⁻¹ : ℝ)) := by
    simpa [hexp] using (Real.rpow_add hposφ (-54 : ℝ) (-(4⁻¹ : ℝ)))
  have hz54 : goldenRatio ^ (-54 : ℝ) = goldenRatio ^ (-54 : ℤ) := by
    rw [← Real.rpow_intCast]
    norm_cast
  have h54_hi : goldenRatio ^ (-54 : ℝ) < (5.185e-12 : ℝ) := by
    simpa [hz54] using phi_neg54_lt
  have hq := phi_neg_quarter_bounds
  have hq_hi : goldenRatio ^ (-(4⁻¹ : ℝ)) < (1 / phi_quarter_lo) := by
    simpa using hq.2
  have hφq_pos : (0 : ℝ) < goldenRatio ^ (-(4⁻¹ : ℝ)) := by
    have : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
    exact Real.rpow_pos_of_pos this _
  -- bound product
  have hstep1 : (goldenRatio ^ (-54 : ℝ)) * (goldenRatio ^ (-(4⁻¹ : ℝ))) < (5.185e-12 : ℝ) * (goldenRatio ^ (-(4⁻¹ : ℝ))) :=
    mul_lt_mul_of_pos_right h54_hi hφq_pos
  have hstep2 : (5.185e-12 : ℝ) * (goldenRatio ^ (-(4⁻¹ : ℝ))) < (5.185e-12 : ℝ) * (1 / phi_quarter_lo) :=
    mul_lt_mul_of_pos_left hq_hi (by norm_num : (0 : ℝ) < (5.185e-12 : ℝ))
  have hnum : (5.185e-12 : ℝ) * (1 / phi_quarter_lo) < (4.598e-12 : ℝ) := by
    simp [phi_quarter_lo]
    norm_num
  rw [hsplit]
  exact lt_trans (lt_trans hstep1 hstep2) hnum

/-- Lower bound for \(φ^{-231/4} = φ^{-58}·φ^{1/4}\). -/
theorem phi_neg2314_gt : (8.514e-13 : ℝ) < goldenRatio ^ (((-231 : ℚ) / 4 : ℚ) : ℝ) := by
  have hexp : (((-231 : ℚ) / 4 : ℚ) : ℝ) = (-58 : ℝ) + (4⁻¹ : ℝ) := by
    norm_num
  have hposφ : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
  have hsplit :
      goldenRatio ^ (((-231 : ℚ) / 4 : ℚ) : ℝ)
        = goldenRatio ^ (-58 : ℝ) * goldenRatio ^ (4⁻¹ : ℝ) := by
    simpa [hexp] using (Real.rpow_add hposφ (-58 : ℝ) (4⁻¹ : ℝ))
  have hz58 : goldenRatio ^ (-58 : ℝ) = goldenRatio ^ (-58 : ℤ) := by
    rw [← Real.rpow_intCast]
    norm_cast
  have h58_lo : (7.55e-13 : ℝ) < goldenRatio ^ (-58 : ℝ) := by
    simpa [hz58] using phi_neg58_gt
  have hq := phi_quarter_bounds
  have hq_lo : phi_quarter_lo < goldenRatio ^ (4⁻¹ : ℝ) := by
    simpa using hq.1
  have hq_pos : (0 : ℝ) < phi_quarter_lo := qlo_pos
  have hφ58_pos : (0 : ℝ) < goldenRatio ^ (-58 : ℝ) := by
    linarith [h58_lo]
  -- 7.55e-13 * 1.12783847 = 8.5151804485e-13 > 8.514e-13
  have hnum : (8.514e-13 : ℝ) < (7.55e-13 : ℝ) * phi_quarter_lo := by
    simp [phi_quarter_lo]
    norm_num
  have hstep1 : (7.55e-13 : ℝ) * phi_quarter_lo < (goldenRatio ^ (-58 : ℝ)) * phi_quarter_lo :=
    mul_lt_mul_of_pos_right h58_lo hq_pos
  have hstep2 : (goldenRatio ^ (-58 : ℝ)) * phi_quarter_lo < (goldenRatio ^ (-58 : ℝ)) * (goldenRatio ^ (4⁻¹ : ℝ)) :=
    mul_lt_mul_of_pos_left hq_lo hφ58_pos
  rw [hsplit]
  exact lt_trans hnum (lt_trans hstep1 hstep2)

/-- Upper bound for \(φ^{-231/4} = φ^{-58}·φ^{1/4}\). -/
theorem phi_neg2314_lt : goldenRatio ^ (((-231 : ℚ) / 4 : ℚ) : ℝ) < (8.538e-13 : ℝ) := by
  have hexp : (((-231 : ℚ) / 4 : ℚ) : ℝ) = (-58 : ℝ) + (4⁻¹ : ℝ) := by
    norm_num
  have hposφ : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
  have hsplit :
      goldenRatio ^ (((-231 : ℚ) / 4 : ℚ) : ℝ)
        = goldenRatio ^ (-58 : ℝ) * goldenRatio ^ (4⁻¹ : ℝ) := by
    simpa [hexp] using (Real.rpow_add hposφ (-58 : ℝ) (4⁻¹ : ℝ))
  have hz58 : goldenRatio ^ (-58 : ℝ) = goldenRatio ^ (-58 : ℤ) := by
    rw [← Real.rpow_intCast]
    norm_cast
  have h58_hi : goldenRatio ^ (-58 : ℝ) < (7.57e-13 : ℝ) := by
    simpa [hz58] using phi_neg58_lt
  have hq := phi_quarter_bounds
  have hq_hi : goldenRatio ^ (4⁻¹ : ℝ) < phi_quarter_hi := by
    simpa using hq.2
  have hφq_pos : (0 : ℝ) < goldenRatio ^ (4⁻¹ : ℝ) := by
    have : (0 : ℝ) < goldenRatio := by simpa using Real.goldenRatio_pos
    exact Real.rpow_pos_of_pos this _
  have hstep1 : (goldenRatio ^ (-58 : ℝ)) * (goldenRatio ^ (4⁻¹ : ℝ)) < (7.57e-13 : ℝ) * (goldenRatio ^ (4⁻¹ : ℝ)) :=
    mul_lt_mul_of_pos_right h58_hi hφq_pos
  have hstep2 : (7.57e-13 : ℝ) * (goldenRatio ^ (4⁻¹ : ℝ)) < (7.57e-13 : ℝ) * phi_quarter_hi :=
    mul_lt_mul_of_pos_left hq_hi (by norm_num : (0 : ℝ) < (7.57e-13 : ℝ))
  have hnum : (7.57e-13 : ℝ) * phi_quarter_hi < (8.538e-13 : ℝ) := by
    simp [phi_quarter_hi]
    norm_num
  rw [hsplit]
  exact lt_trans (lt_trans hstep1 hstep2) hnum

/-! ## φ⁶ bounds (mass verification) -/

theorem phi_pow6_gt : (17.944 : ℝ) < goldenRatio ^ 6 := by
  rw [phi_pow6_eq]; linarith [phi_gt_1618]

theorem phi_pow6_lt : goldenRatio ^ 6 < (17.948 : ℝ) := by
  rw [phi_pow6_eq]; linarith [phi_lt_16185]

/-! ## φ^32 bounds (proton mass verification)

φ^32 = (φ^16)². -/

theorem phi_pow32_gt : (4870400 : ℝ) < goldenRatio ^ 32 := by
  have heq : goldenRatio ^ 32 = goldenRatio ^ 16 * goldenRatio ^ 16 := by ring_nf
  rw [heq]
  have h16 := phi_pow16_gt
  have hpos : (0 : ℝ) < goldenRatio ^ 16 := by positivity
  calc (4870400 : ℝ) < (2206.9 : ℝ) * (2206.9 : ℝ) := by norm_num
    _ < goldenRatio ^ 16 * (2206.9 : ℝ) := by nlinarith
    _ < goldenRatio ^ 16 * goldenRatio ^ 16 := by nlinarith

theorem phi_pow32_lt : goldenRatio ^ 32 < (4873100 : ℝ) := by
  have heq : goldenRatio ^ 32 = goldenRatio ^ 16 * goldenRatio ^ 16 := by ring_nf
  rw [heq]
  have h16 := phi_pow16_lt
  have hpos : (0 : ℝ) < goldenRatio ^ 16 := by positivity
  calc goldenRatio ^ 16 * goldenRatio ^ 16
      < (2207.5 : ℝ) * goldenRatio ^ 16 := by nlinarith
    _ < (2207.5 : ℝ) * (2207.5 : ℝ) := by nlinarith
    _ < (4873100 : ℝ) := by norm_num

/-! ## φ^43 bounds (proton mass verification)

φ^43 = φ^32 × φ^8 × φ^3. -/

theorem phi_pow43_gt : (969030000 : ℝ) < goldenRatio ^ 43 := by
  have heq : goldenRatio ^ 43 = goldenRatio ^ 32 * goldenRatio ^ 8 * goldenRatio ^ 3 := by ring_nf
  rw [heq]
  have h32 := phi_pow32_gt
  have h8 := phi_pow8_gt
  have h3 := phi_cubed_gt
  have hpos32 : (0 : ℝ) < goldenRatio ^ 32 := by positivity
  have hpos32x8 : (0 : ℝ) < goldenRatio ^ 32 * goldenRatio ^ 8 := by positivity
  have h40 : (4870400 : ℝ) * (46.97 : ℝ) < goldenRatio ^ 32 * goldenRatio ^ 8 :=
    mul_lt_mul h32 (le_of_lt h8) (by norm_num) (le_of_lt hpos32)
  have h43 : (4870400 : ℝ) * (46.97 : ℝ) * (4.236 : ℝ) <
      goldenRatio ^ 32 * goldenRatio ^ 8 * goldenRatio ^ 3 :=
    mul_lt_mul h40 (le_of_lt h3) (by norm_num) (le_of_lt hpos32x8)
  have hnum : (969030000 : ℝ) < (4870400 : ℝ) * (46.97 : ℝ) * (4.236 : ℝ) := by norm_num
  linarith

theorem phi_pow43_lt : goldenRatio ^ 43 < (970320000 : ℝ) := by
  have heq : goldenRatio ^ 43 = goldenRatio ^ 32 * goldenRatio ^ 8 * goldenRatio ^ 3 := by ring_nf
  rw [heq]
  have h32 := phi_pow32_lt
  have h8 := phi_pow8_lt
  have h3 := phi_cubed_lt
  have hpos8 : (0 : ℝ) < goldenRatio ^ 8 := by positivity
  have hpos3 : (0 : ℝ) < goldenRatio ^ 3 := by positivity
  have h40 : goldenRatio ^ 32 * goldenRatio ^ 8 < (4873100 : ℝ) * (46.99 : ℝ) :=
    mul_lt_mul h32 (le_of_lt h8) hpos8 (by norm_num)
  have h43 : goldenRatio ^ 32 * goldenRatio ^ 8 * goldenRatio ^ 3 <
      (4873100 : ℝ) * (46.99 : ℝ) * (4.237 : ℝ) :=
    mul_lt_mul h40 (le_of_lt h3) hpos3 (by norm_num)
  have hnum : (4873100 : ℝ) * (46.99 : ℝ) * (4.237 : ℝ) < (970320000 : ℝ) := by norm_num
  linarith

/-! ## φ^59 bounds (electron mass verification)

φ^59 = φ^51 × φ^8. We compose existing bounds on each factor. -/

theorem phi_pow59_gt : (2138898000000 : ℝ) < goldenRatio ^ 59 := by
  have heq : goldenRatio ^ 59 = goldenRatio ^ 51 * goldenRatio ^ 8 := by ring_nf
  rw [heq]
  have h51 := phi_pow51_gt
  have h8 := phi_pow8_gt
  have hpos51 : (0 : ℝ) < goldenRatio ^ 51 := by positivity
  calc (2138898000000 : ℝ) < (45537548334 : ℝ) * (46.97 : ℝ) := by norm_num
    _ < goldenRatio ^ 51 * (46.97 : ℝ) := by nlinarith
    _ < goldenRatio ^ 51 * goldenRatio ^ 8 := by nlinarith

theorem phi_pow59_lt : goldenRatio ^ 59 < (2139810000000 : ℝ) := by
  have heq : goldenRatio ^ 59 = goldenRatio ^ 51 * goldenRatio ^ 8 := by ring_nf
  rw [heq]
  have h51 := phi_pow51_lt
  have h8 := phi_pow8_lt
  have hpos8 : (0 : ℝ) < goldenRatio ^ 8 := by positivity
  calc goldenRatio ^ 51 * goldenRatio ^ 8
      < (45537549354 : ℝ) * goldenRatio ^ 8 := by nlinarith
    _ < (45537549354 : ℝ) * (46.99 : ℝ) := by nlinarith
    _ < (2139810000000 : ℝ) := by norm_num

/-! ## φ^70 bounds (muon mass verification)

φ^70 = φ^54 × φ^16. -/

theorem phi_pow70_gt : (425698000000000 : ℝ) < goldenRatio ^ 70 := by
  have heq : goldenRatio ^ 70 = goldenRatio ^ 54 * goldenRatio ^ 16 := by ring_nf
  rw [heq]
  have h54 := phi_pow54_gt
  have h16 := phi_pow16_gt
  have hpos54 : (0 : ℝ) < goldenRatio ^ 54 := by positivity
  calc (425698000000000 : ℝ)
      < (192894126000 : ℝ) * (2206.9 : ℝ) := by norm_num
    _ < goldenRatio ^ 54 * (2206.9 : ℝ) := by nlinarith
    _ < goldenRatio ^ 54 * goldenRatio ^ 16 := by nlinarith

theorem phi_pow70_lt : goldenRatio ^ 70 < (426011000000000 : ℝ) := by
  have heq : goldenRatio ^ 70 = goldenRatio ^ 54 * goldenRatio ^ 16 := by ring_nf
  rw [heq]
  have h54 := phi_pow54_lt
  have h16 := phi_pow16_lt
  have hpos16 : (0 : ℝ) < goldenRatio ^ 16 := by positivity
  calc goldenRatio ^ 54 * goldenRatio ^ 16
      < (192983018016 : ℝ) * goldenRatio ^ 16 := by nlinarith
    _ < (192983018016 : ℝ) * (2207.5 : ℝ) := by nlinarith
    _ < (426011000000000 : ℝ) := by norm_num

/-! ## φ^76 bounds (tau mass verification)

φ^76 = φ^70 × φ^6. -/

theorem phi_pow76_gt : (7638724000000000 : ℝ) < goldenRatio ^ 76 := by
  have heq : goldenRatio ^ 76 = goldenRatio ^ 70 * goldenRatio ^ 6 := by ring_nf
  rw [heq]
  have h70 := phi_pow70_gt
  have h6 := phi_pow6_gt
  have hpos70 : (0 : ℝ) < goldenRatio ^ 70 := by positivity
  calc (7638724000000000 : ℝ)
      < (425698000000000 : ℝ) * (17.944 : ℝ) := by norm_num
    _ < goldenRatio ^ 70 * (17.944 : ℝ) := by nlinarith
    _ < goldenRatio ^ 70 * goldenRatio ^ 6 := by nlinarith

theorem phi_pow76_lt : goldenRatio ^ 76 < (7646046000000000 : ℝ) := by
  have heq : goldenRatio ^ 76 = goldenRatio ^ 70 * goldenRatio ^ 6 := by ring_nf
  rw [heq]
  have h70 := phi_pow70_lt
  have h6 := phi_pow6_lt
  have hpos6 : (0 : ℝ) < goldenRatio ^ 6 := by positivity
  calc goldenRatio ^ 70 * goldenRatio ^ 6
      < (426011000000000 : ℝ) * goldenRatio ^ 6 := by nlinarith
    _ < (426011000000000 : ℝ) * (17.948 : ℝ) := by nlinarith
    _ < (7646046000000000 : ℝ) := by norm_num

/-! ## φ − 1 bounds (preparation for log φ analysis) -/

lemma phi_sub_one_pos : 0 < goldenRatio - 1 := by
  have h := phi_gt_1618
  linarith

lemma phi_sub_one_lt_one : goldenRatio - 1 < 1 := by
  have h := Real.goldenRatio_lt_two
  linarith

lemma phi_sub_one_mem_Icc : goldenRatio - 1 ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_of_lt phi_sub_one_pos, le_of_lt phi_sub_one_lt_one⟩

end IndisputableMonolith.Numerics
