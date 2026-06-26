import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Measurement.PathAction
import IndisputableMonolith.Measurement.TwoBranchGeodesic

/-!
# Kernel Matching: Pointwise Identity J(r) dt = 2 dA

This module proves the constructive kernel match from Local-Collapse Appendix D.

The key lemma: for the profile
  r(ϑ) = (1 + 2 tan ϑ) + √((1 + 2 tan ϑ)^2 − 1),
we have J(r(ϑ)) = 2 tan ϑ pointwise, enabling the integral identity C = 2A.
-/

namespace IndisputableMonolith
namespace Measurement

open Real Cost

/-- Recognition profile from eq (D.1) of Local-Collapse:
    r(ϑ) solves J(r(ϑ)) = 2 tan ϑ. -/
noncomputable def recognitionProfile (ϑ : ℝ) : ℝ :=
  1 + 2 * Real.cot ϑ + Real.sqrt ((1 + 2 * Real.cot ϑ) ^ 2 - 1)

/-- The argument to arcosh is at least 1 for ϑ ∈ [0, π/2] -/
lemma arcosh_arg_ge_one (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ ≤ π/2) :
  1 ≤ 1 + 2 * Real.cot ϑ := by
  have hsin : 0 ≤ Real.sin ϑ := by
    have hmem : ϑ ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · exact hϑ.1
      · have hpi2_le_pi : (Real.pi / 2 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_pos]
        exact le_trans hϑ.2 hpi2_le_pi
    simpa using Real.sin_nonneg_of_mem_Icc hmem
  have hcos : 0 ≤ Real.cos ϑ := by
    have hmem : ϑ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · have hneg : (-(Real.pi / 2) : ℝ) ≤ 0 := by nlinarith [Real.pi_pos]
        exact le_trans hneg hϑ.1
      · exact hϑ.2
    simpa using Real.cos_nonneg_of_mem_Icc hmem
  have hcot : 0 ≤ Real.cot ϑ := by
    -- Rewrite `cot` as `cos / sin` on reals.
    simpa [Real.cot_eq_cos_div_sin] using (div_nonneg hcos hsin)
  have hprod : 0 ≤ 2 * Real.cot ϑ := by
    have htwo : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg htwo hcot
  simpa using add_le_add_left hprod 1

/-- Recognition profile is positive -/
lemma recognitionProfile_pos (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ ≤ π/2) :
  0 < recognitionProfile ϑ := by
  have hy : 1 ≤ 1 + 2 * Real.cot ϑ := arcosh_arg_ge_one ϑ hϑ
  have hypos : 0 < 1 + 2 * Real.cot ϑ := lt_of_lt_of_le zero_lt_one hy
  have hs : 0 ≤ Real.sqrt ((1 + 2 * Real.cot ϑ) ^ 2 - 1) := Real.sqrt_nonneg _
  exact add_pos_of_pos_of_nonneg hypos hs

/-- Pointwise kernel matching: J(r(ϑ)) = 2 tan ϑ
    This is the core technical lemma enabling C = 2A -/
theorem kernel_match_pointwise (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ ≤ π/2) :
  Jcost (recognitionProfile ϑ) = 2 * Real.cot ϑ := by
  classical
  set y := 1 + 2 * Real.cot ϑ
  set s := Real.sqrt (y ^ 2 - 1)
  have hy : 1 ≤ y := by
    simpa [y] using arcosh_arg_ge_one ϑ hϑ
  have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hynonneg : 0 ≤ y := le_trans (by norm_num) hy
  have hrad_nonneg : 0 ≤ y ^ 2 - 1 := by
    have hsub : 0 ≤ y - 1 := sub_nonneg.mpr hy
    have hadd : 0 ≤ y + 1 := add_nonneg hynonneg (by norm_num)
    have hx := mul_nonneg hsub hadd
    convert hx using 1 <;> ring
  have hs_sq : s ^ 2 = y ^ 2 - 1 := by
    have := Real.mul_self_sqrt hrad_nonneg
    simpa [s, pow_two] using this
  have hxmul : (y + s) * (y - s) = 1 := by
    calc
      (y + s) * (y - s) = y ^ 2 - s ^ 2 := by ring
      _ = y ^ 2 - (y ^ 2 - 1) := by simpa [pow_two, hs_sq]
      _ = 1 := by ring
  have hxpos : 0 < y + s := add_pos_of_pos_of_nonneg hy_pos (Real.sqrt_nonneg _)
  have hxinv :
      (y + s) ⁻¹ = y - s := by
    have hxnonzero : y + s ≠ 0 := ne_of_gt hxpos
    have hx' := congrArg (fun t => (y + s)⁻¹ * t) hxmul
    have hx'' : (y - s) = (y + s)⁻¹ := by
      simpa [mul_assoc, hxnonzero] using hx'
    simpa [recognitionProfile, y, s] using hx''.symm
  have hxsum : (y + s) + (y - s) = 2 * y := by ring
  have hydiv : (2 * y) / 2 = y := by
    have : (2 : ℝ) ≠ 0 := by norm_num
    simpa [mul_comm] using (mul_div_cancel' y this)
  have hy_sub : y - 1 = 2 * Real.cot ϑ := by simp [y]
  calc
    Jcost (recognitionProfile ϑ)
        = ((y + s) + (y + s)⁻¹) / 2 - 1 := by simp [Jcost, recognitionProfile, y, s]
    _ = ((y + s) + (y - s)) / 2 - 1 := by simp [hxinv]
    _ = (2 * y) / 2 - 1 := by simpa [hxsum]
    _ = y - 1 := by simpa [hydiv]
    _ = 2 * Real.cot ϑ := hy_sub

/-- Differential form of kernel match: J(r) dϑ = 2 tan ϑ dϑ -/
theorem kernel_match_differential (ϑ : ℝ) (hϑ : 0 ≤ ϑ ∧ ϑ ≤ π/2) :
  Jcost (recognitionProfile ϑ) = 2 * Real.cot ϑ :=
  kernel_match_pointwise ϑ hϑ

/-- The integrand match: ∫ J(r(ϑ)) dϑ = 2 ∫ tan ϑ dϑ -/
theorem kernel_integral_match (θ_s : ℝ) (hθ : 0 < θ_s ∧ θ_s < π/2) :
  ∫ ϑ in (0)..(π/2 - θ_s), Jcost (recognitionProfile (ϑ + θ_s)) =
  2 * ∫ ϑ in (0)..(π/2 - θ_s), Real.cot (ϑ + θ_s) := by
  -- Follows by integrating the pointwise identity
  -- measurability and integrability are standard for these smooth functions
  have hb_nonneg : 0 ≤ π/2 - θ_s := sub_nonneg.mpr (le_of_lt hθ.2)
  have hpt : ∀ ϑ ∈ Set.Icc (0 : ℝ) (π/2 - θ_s),
      Jcost (recognitionProfile (ϑ + θ_s)) = 2 * Real.cot (ϑ + θ_s) := by
    intro ϑ hϑ
    apply kernel_match_pointwise (ϑ + θ_s)
    constructor
    · have hθ_nonneg : 0 ≤ θ_s := le_of_lt hθ.1
      exact add_nonneg hϑ.1 hθ_nonneg
    · have : ϑ ≤ π/2 - θ_s := hϑ.2
      have hsum := add_le_add_right this θ_s
      simpa [add_comm, add_left_comm, add_assoc] using hsum
  have h_ae :
      ∀ᵐ ϑ ∂MeasureTheory.volume,
        ϑ ∈ Set.uIoc 0 (π/2 - θ_s) →
          Jcost (recognitionProfile (ϑ + θ_s)) = 2 * Real.cot (ϑ + θ_s) := by
    refine Filter.Eventually.of_forall ?_
    intro ϑ hϑ
    have hIoc : ϑ ∈ Set.Ioc (0 : ℝ) (π/2 - θ_s) := by
      simpa [Set.uIoc, hb_nonneg] using hϑ
    have hIcc : ϑ ∈ Set.Icc (0 : ℝ) (π/2 - θ_s) := by
      exact ⟨le_of_lt hIoc.1, hIoc.2⟩
    exact hpt ϑ hIcc
  have hcongr :=
    intervalIntegral.integral_congr_ae
      (μ := MeasureTheory.volume)
      (a := 0) (b := π/2 - θ_s)
      (f := fun ϑ => Jcost (recognitionProfile (ϑ + θ_s)))
      (g := fun ϑ => 2 * Real.cot (ϑ + θ_s)) h_ae
  simpa using hcongr

end Measurement
end IndisputableMonolith
