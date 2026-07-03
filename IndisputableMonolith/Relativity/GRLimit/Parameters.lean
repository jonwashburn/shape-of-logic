import Mathlib
import IndisputableMonolith.Constants

/-!
# Parameter Limits and Recognition Spine Connection

ACTUALLY PROVES that ILG parameters (α, C_lag) from RS are small and perturbative.

From Source.txt line 26:
- α = (1 - 1/φ)/2 (derived from RS geometry)
- C_lag = φ^(-5) (derived from coherence quantum E_coh = φ^(-5) eV)

We PROVE (not assume):
1. Both < 1 (straightforward)
2. Product < 0.1 (requires showing φ^5 > 10)
3. Product < 0.02 (STATUS: needs tighter bounds - see below)
-/

namespace IndisputableMonolith
namespace Relativity
namespace GRLimit

/-- ILG exponent α from RS: α = (1 - 1/φ)/2 ≈ 0.191 -/
noncomputable def alpha_from_phi : ℝ :=
  (1 - 1 / Constants.phi) / 2

/-- ILG lag constant C_lag from RS: C_lag = φ^(-5) ≈ 0.090 -/
noncomputable def cLag_from_phi : ℝ :=
  Constants.phi ^ (-5 : ℝ)

/-- PROVEN: Both parameters are positive. -/
theorem rs_params_positive :
  0 < alpha_from_phi ∧ 0 < cLag_from_phi := by
  constructor
  · unfold alpha_from_phi
    have hφ_pos : 0 < Constants.phi := Constants.phi_pos
    have hφ_gt_one : 1 < Constants.phi := Constants.one_lt_phi
    have : 0 < 1 - 1 / Constants.phi := by
      have : 1 / Constants.phi < 1 := (div_lt_one hφ_pos).mpr hφ_gt_one
      linarith
    linarith
  · unfold cLag_from_phi
    exact Real.rpow_pos_of_pos Constants.phi_pos _

/-- PROVEN: α < 1 (straightforward from φ > 1). -/
theorem alpha_lt_one : alpha_from_phi < 1 := by
  unfold alpha_from_phi
  have hφ_pos : 0 < Constants.phi := Constants.phi_pos
  have : 1 - 1 / Constants.phi < 1 := by
    have : 0 < 1 / Constants.phi := div_pos (by norm_num) hφ_pos
    linarith
  have : (1 - 1 / Constants.phi) / 2 < 1 / 2 := by
    exact div_lt_div_of_pos_right this (by norm_num)
  linarith

/- PROVEN: α < 1/2 (since 1 − 1/φ < 1). -/
theorem alpha_lt_half : alpha_from_phi < 1 / 2 := by
  unfold alpha_from_phi
  have hφ_pos : 0 < Constants.phi := Constants.phi_pos
  have : 1 - 1 / Constants.phi < 1 := by
    have : 0 < 1 / Constants.phi := div_pos (by norm_num) hφ_pos
    linarith
  exact div_lt_div_of_pos_right this (by norm_num)

-- (helper lemma removed)

/-- φ > 3/2. -/
theorem phi_gt_three_halves : Constants.phi > 3 / 2 := by
  -- First show √5 > 11/5, hence φ = (1+√5)/2 > (1+11/5)/2 = 8/5 > 3/2
  have hy : 0 ≤ (11 : ℝ) / 5 := by norm_num
  have hnot_le : ¬ (Real.sqrt 5 ≤ (11 : ℝ) / 5) := by
    -- If √5 ≤ 11/5 then 5 ≤ (11/5)^2, contradiction
    have hcontra : ¬ (5 : ℝ) ≤ ((11 : ℝ) / 5) ^ 2 := by norm_num
    exact fun hle => hcontra ((Real.sqrt_le_left hy).mp hle)
  have h11lt : (11 : ℝ) / 5 < Real.sqrt 5 := lt_of_not_ge hnot_le
  have hsum : 1 + (11 : ℝ) / 5 < 1 + Real.sqrt 5 := by linarith
  have hdiv : (1 + (11 : ℝ) / 5) / 2 < (1 + Real.sqrt 5) / 2 :=
    div_lt_div_of_pos_right hsum (by norm_num)
  have h8over5 : (8 : ℝ) / 5 = (1 + (11 : ℝ) / 5) / 2 := by norm_num
  have hphi : (1 + Real.sqrt 5) / 2 = Constants.phi := by simp [Constants.phi]
  have h8ltphi : (8 : ℝ) / 5 < Constants.phi := by
    simpa [h8over5, hphi] using hdiv
  have : (3 : ℝ) / 2 < (8 : ℝ) / 5 := by norm_num
  exact lt_trans this h8ltphi

-- φ^2 = φ + 1 (reference)

-- φ^5 = 5φ + 3 (reference)

-- φ^5 > 10 (reference); not needed since we bound C_lag via rpow monotonicity

/-- PROVEN: φ^(-5) < 1/10. -/
theorem cLag_lt_one_tenth : cLag_from_phi < 1 / 10 := by
  -- Use φ ≥ 8/5 and negative exponent monotonicity: φ^(−5) ≤ (8/5)^(−5) = 3125/32768 < 1/10
  unfold cLag_from_phi
  have hphi_ge : (8 : ℝ) / 5 ≤ Constants.phi := le_of_lt (by
    -- φ > 8/5
    unfold Constants.phi
    have hy : 0 ≤ (11 : ℝ) / 5 := by norm_num
    have hnot_le : ¬ (Real.sqrt 5 ≤ (11 : ℝ) / 5) := by
      have hcontra : ¬ (5 : ℝ) ≤ ((11 : ℝ) / 5) ^ 2 := by norm_num
      exact fun hle => hcontra ((Real.sqrt_le_left hy).mp hle)
    have h11lt : (11 : ℝ) / 5 < Real.sqrt 5 := lt_of_not_ge hnot_le
    have hsum : 1 + (11 : ℝ) / 5 < 1 + Real.sqrt 5 := by linarith
    have hdiv : (1 + (11 : ℝ) / 5) / 2 < (1 + Real.sqrt 5) / 2 :=
      div_lt_div_of_pos_right hsum (by norm_num)
    have h8over5 : (8 : ℝ) / 5 = (1 + (11 : ℝ) / 5) / 2 := by norm_num
    have hphi : (1 + Real.sqrt 5) / 2 = Constants.phi := by simp [Constants.phi]
    simpa [h8over5, hphi] using hdiv)
  have hxpos : 0 < (8 : ℝ) / 5 := by norm_num
  have hmon : Constants.phi ^ ((-5) : ℝ) ≤ ((8 : ℝ) / 5) ^ ((-5) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hxpos hphi_ge (by norm_num)
  have hrpow : ((8 : ℝ) / 5) ^ ((-5) : ℝ) = 1 / ((8 : ℝ) / 5) ^ 5 := by
    rw [Real.rpow_neg (le_of_lt hxpos)]
    simp
  have hlt : 1 / ((8 : ℝ) / 5) ^ 5 < 1 / 10 := by
    -- since (8/5)^5 = 32768/3125 > 10
    have hpow : ((8 : ℝ) / 5) ^ 5 = (32768 : ℝ) / 3125 := by norm_num
    have hgt : ((8 : ℝ) / 5) ^ 5 > 10 := by simpa [hpow] using (by norm_num : (32768 : ℝ) / 3125 > 10)
    exact (div_lt_div_of_pos_left (by norm_num) (by norm_num) hgt)
  have : ((8 : ℝ) / 5) ^ ((-5) : ℝ) < 1 / 10 := by simpa [hrpow] using hlt
  exact lt_of_le_of_lt hmon this

/-- PROVEN: C_lag < 1 (from φ^5 > 10 ⇒ φ^(−5) < 1/10 < 1). -/
theorem cLag_lt_one : cLag_from_phi < 1 := by
  have hlt : cLag_from_phi < 1 / 10 := cLag_lt_one_tenth
  have : (1 / 10 : ℝ) < 1 := by norm_num
  exact lt_trans hlt this

/-- PROVEN: Product < 0.1 using algebraic bounds. -/
theorem rs_params_perturbative_proven : |alpha_from_phi * cLag_from_phi| < 0.1 := by
  have hα_pos := rs_params_positive.1
  have hC_pos := rs_params_positive.2
  rw [abs_of_nonneg (mul_nonneg (le_of_lt hα_pos) (le_of_lt hC_pos))]
  have hα_lt : alpha_from_phi < 1 / 2 := alpha_lt_half
  have hC_lt : cLag_from_phi < 1 / 10 := cLag_lt_one_tenth
  calc alpha_from_phi * cLag_from_phi
      < (1 / 2) * (1 / 10) := by
        apply mul_lt_mul'' hα_lt hC_lt (le_of_lt hα_pos) (le_of_lt hC_pos)
    _ = 1 / 20 := by norm_num
    _ < 0.1 := by norm_num

/-- STATUS: Product < 0.02 needs tighter bounds.

    PROGRESS: Proven product < 0.05 (since α < 1/2, C_lag < 1/10)
    NEEDED: Either α < 1/5 OR C_lag < 1/11 to get product < 0.02

    Current bounds:
    - α = (1-1/φ)/2 where φ = (1+√5)/2
    - Need to show α < 1/5 OR find tighter C_lag bound

    Path forward:
    - Prove φ < 1.62 ⟹ 1/φ > 0.617 ⟹ 1-1/φ < 0.383 ⟹ α < 0.192 < 1/5 ✓
    - Requires proving √5 < 2.24 ⟹ φ < (1+2.24)/2 = 1.62
    - This is doable with Mathlib's Real.sqrt inequalities
-/
theorem coupling_product_small_proven : |alpha_from_phi * cLag_from_phi| < 0.02 := by
  have hα_pos := rs_params_positive.1
  have hC_pos := rs_params_positive.2
  rw [abs_of_nonneg (mul_nonneg (le_of_lt hα_pos) (le_of_lt hC_pos))]

  -- Strategy: Prove α < 1/5
  -- Need: (1 - 1/φ)/2 < 1/5
  -- ⟺ 1 - 1/φ < 2/5
  -- ⟺ 1 - 2/5 < 1/φ
  -- ⟺ 3/5 < 1/φ
  -- ⟺ φ < 5/3

  have hα_lt_one_fifth : alpha_from_phi < 1 / 5 := by
    unfold alpha_from_phi
    have hφ_pos : 0 < Constants.phi := Constants.phi_pos

    -- Need to prove φ < 5/3
    have hφ_lt_5_3 : Constants.phi < 5 / 3 := by
      unfold Constants.phi
      -- (1+√5)/2 < 5/3
      -- ⟺ 3(1+√5) < 10
      -- ⟺ 3 + 3√5 < 10
      -- ⟺ 3√5 < 7
      -- ⟺ √5 < 7/3
      -- ⟺ 5 < 49/9
      -- 5 = 45/9 < 49/9 ✓
      have h_sqrt5_lt : Real.sqrt 5 < 7 / 3 := by
        -- use sqrt_lt equivalence: √x < y ↔ x < y^2
        have hx : 0 ≤ (5 : ℝ) := by norm_num
        have hy : 0 ≤ (7 / 3 : ℝ) := by norm_num
        have hxy : (5 : ℝ) < (7 / 3 : ℝ) ^ 2 := by norm_num
        exact (Real.sqrt_lt hx hy).2 hxy
      have : 1 + Real.sqrt 5 < 1 + 7 / 3 := by linarith
      have : (1 + Real.sqrt 5) / 2 < (1 + 7 / 3) / 2 := by
        exact div_lt_div_of_pos_right this (by norm_num)
      calc (1 + Real.sqrt 5) / 2
          < (1 + 7 / 3) / 2 := this
        _ = 10 / 6 := by norm_num
        _ = 5 / 3 := by norm_num

    -- Now: φ < 5/3 ⟹ 1/φ > 3/5 ⟹ 1 - 1/φ < 2/5 ⟹ α < 1/5
    have : 1 / Constants.phi > 3 / 5 := by
      -- From φ < 5/3 and φ > 0, we get 1/(5/3) < 1/φ i.e., 3/5 < 1/φ
      have hpos : 0 < Constants.phi := hφ_pos
      have : 1 / (5 / 3 : ℝ) < 1 / Constants.phi :=
        one_div_lt_one_div_of_lt hpos hφ_lt_5_3
      simpa using this
    have : 1 - 1 / Constants.phi < 2 / 5 := by linarith
    have : (1 - 1 / Constants.phi) / 2 < (2 / 5) / 2 := by
      exact div_lt_div_of_pos_right this (by norm_num)
    calc (1 - 1 / Constants.phi) / 2
        < (2 / 5) / 2 := this
      _ = 1 / 5 := by norm_num

  have hC_lt : cLag_from_phi < 1 / 10 := cLag_lt_one_tenth

  calc alpha_from_phi * cLag_from_phi
      < (1 / 5) * (1 / 10) := by
        apply mul_lt_mul'' hα_lt_one_fifth hC_lt (le_of_lt hα_pos) (le_of_lt hC_pos)
    _ = 1 / 50 := by norm_num
    _ = 0.02 := by norm_num

/-- PROVEN: Both parameters < 1. -/
theorem rs_params_small_proven : alpha_from_phi < 1 ∧ cLag_from_phi < 1 :=
  ⟨alpha_lt_one, cLag_lt_one⟩

/-- Recognition spine parameters are small (for perturbation theory). -/
class GRLimitParameterFacts : Prop where
  rs_params_small : alpha_from_phi < 1 ∧ cLag_from_phi < 1
  coupling_product_small : |alpha_from_phi * cLag_from_phi| < 0.02
  rs_params_perturbative : (|alpha_from_phi * cLag_from_phi|) < 0.1

/-- Rigorous instance providing GRLimitParameterFacts with ACTUAL PROOFS. -/
instance grLimitParameterFacts_proven : GRLimitParameterFacts where
  rs_params_small := rs_params_small_proven
  coupling_product_small := coupling_product_small_proven
  rs_params_perturbative := rs_params_perturbative_proven

end GRLimit
end Relativity
end IndisputableMonolith
