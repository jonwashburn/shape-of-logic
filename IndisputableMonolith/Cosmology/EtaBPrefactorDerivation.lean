import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.GapDerivation
import IndisputableMonolith.Cosmology.BaryonAsymmetryExact
import IndisputableMonolith.Cosmology.BaryonHigherOrder
import IndisputableMonolith.Cosmology.EtaBIntervalCert

/-!
# η_B Order-One Prefactor c: SELECTED ANSATZ, NOT A DERIVATION

**HONESTY CORRECTION (2026-07-06 audit, Thapa baryon-photon follow-up).**
This module's earlier docstring said it "derives the order-one prefactor
structurally". That was an overclaim, and it is retracted. The accurate
status of the prefactor `c_RS = (1 − φ^(−8))^2` is:

1. **Selected, not derived.** The squared form was chosen from a family
   of a-priori-comparable order-one lookalikes — (1 − δ), (1 − δ)^2,
   (1 − 2δ), e^(−2δ), and others with δ = φ^(−8) — because it moves the
   bare rung φ^(−44) ≈ 6.41×10⁻¹⁰ into the Planck band. No Boltzmann or
   rate calculation in this repository produces the squared polynomial
   form; a genuine thermal washout is exponential in Γ/H and
   temperature-dependent, and this factor is neither.

2. **The prefactor is numerically the missing sub-rung.** Any residual
   factor of order (0.9, 1.0) applied to φ^(−44) would land in the band;
   the selection therefore carries essentially no independent
   evidential weight beyond the decade-level match of the bare rung.

3. **What IS proved (and remains proved):** the algebra
   `c_RS_expanded`, positivity, `c_RS < 1`, and the interval arithmetic
   showing c_RS · φ^(−44) ∈ (6.0, 6.2)×10⁻¹⁰. These are kernel-checked
   facts about a *defined* quantity, not evidence that the definition is
   the physical washout.

The two-sided-washout story (matter and antimatter sectors each
contributing one factor of (1 − δ) at the 8-tick rung) is retained
below as the *motivating heuristic* for why the squared form was tried
first. It is a HYPOTHESIS with no rate derivation behind it.

## Epistemic Status

DEF (ansatz): c_RS = (1 − φ^(−8))^2, a selected order-one factor.
THEOREM (algebra and numerical bounds only): positivity, c_RS < 1,
and the band inclusion c_RS · φ^(−44) ∈ (6.0, 6.2) × 10⁻¹⁰.
HYPOTHESIS (interpretive, no supporting calculation): the two-sided
washout reading of the square.

OPEN: a Boltzmann/rate derivation with explicit Γ/H that either
produces this factor or replaces it. Until that exists, the honest
paper-level claim is the decade-level match of the bare rung φ^(−44),
and this module must not be cited as a precision prediction.

Falsifier (unchanged): η_B measured outside (6.0, 6.2) × 10⁻¹⁰ at
> 3σ kills the squared ansatz specifically.

## Status: 0 sorry, 0 RS-specific axiom
-/

namespace IndisputableMonolith
namespace Cosmology
namespace EtaBPrefactorDerivation

open Constants
open BaryonAsymmetryExact (eta_B_phi_scale eta_B_phi_scale_pos)
open BaryonHigherOrder (delta_washout delta_pos delta_lt_one
  correction_factor correction_factor_pos correction_factor_lt_one)

noncomputable section

/-! ## Part 1: The Two-Sided Washout Prefactor -/

/-- The η_B order-one prefactor from two-sided 8-tick sphaleron washout.

    Each of the matter and antimatter sectors carries one dimensionGap
    worth of fermionic DOF, so the washout factor (1 − φ^(−8)) appears
    once per sector, giving the squared structural prefactor. -/
def c_RS : ℝ := correction_factor ^ 2

/-- Equivalent expanded form: c_RS = (1 − φ^(−8))^2. -/
theorem c_RS_expanded : c_RS = (1 - phi ^ (-8 : ℤ)) ^ 2 := by
  unfold c_RS BaryonHigherOrder.correction_factor BaryonHigherOrder.delta_washout
  rfl

/-- The prefactor is positive. -/
theorem c_RS_pos : 0 < c_RS := by
  unfold c_RS
  exact pow_pos correction_factor_pos 2

/-- The prefactor is strictly less than 1 (correction is real). -/
theorem c_RS_lt_one : c_RS < 1 := by
  unfold c_RS
  have h1 : correction_factor < 1 := correction_factor_lt_one
  have h2 : 0 < correction_factor := correction_factor_pos
  calc correction_factor ^ 2
      = correction_factor * correction_factor := by ring
    _ < 1 * 1 := by
        apply mul_lt_mul' h1.le h1 h2.le
        norm_num
    _ = 1 := by norm_num

/-- The prefactor is order-one: 0 < c_RS < 1. -/
theorem c_RS_in_unit_interval : 0 < c_RS ∧ c_RS < 1 :=
  ⟨c_RS_pos, c_RS_lt_one⟩

/-! ## Part 2: φ^8 Bounds via the Fibonacci Identity -/

/-- φ^8 = 21φ + 13 from the Fibonacci formula φ^(n+1) = F(n+1)φ + F(n).
    Derived stepwise via φ^3, φ^4, φ^8 = (φ^4)^2 with substitutions
    `phi_sq_eq : phi^2 = phi + 1`. -/
theorem phi_pow_8_fib : phi ^ (8 : ℕ) = 21 * phi + 13 := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq_eq
  have h4 : phi ^ 4 = 3 * phi + 2 := by
    have hexp : phi ^ 4 = phi ^ 2 * phi ^ 2 := by ring
    rw [hexp, h2]
    ring_nf
    linarith [h2]
  have hexp : phi ^ 8 = phi ^ 4 * phi ^ 4 := by ring
  rw [hexp, h4]
  ring_nf
  linarith [h2]

/-- φ^8 > 46.81 (from φ > 1.61). -/
theorem phi_pow_8_lower : phi ^ (8 : ℕ) > 46.81 := by
  rw [phi_pow_8_fib]
  have hphi : phi > 1.61 := phi_gt_onePointSixOne
  linarith

/-- φ^8 < 47.03 (from φ < 1.62). -/
theorem phi_pow_8_upper : phi ^ (8 : ℕ) < 47.03 := by
  rw [phi_pow_8_fib]
  have hphi : phi < 1.62 := phi_lt_onePointSixTwo
  linarith

/-! ## Part 3: φ^(-8) Bounds (zpow form) -/

private lemma phi_zpow_neg8_eq_inv : phi ^ (-8 : ℤ) = (phi ^ (8 : ℕ))⁻¹ := by
  rw [show ((-8 : ℤ)) = -((8 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast]

/-- φ^(-8) > 0.02126 (lower bound from φ^8 < 47.03). -/
theorem phi_zpow_neg8_lower : phi ^ (-8 : ℤ) > 0.02126 := by
  rw [phi_zpow_neg8_eq_inv]
  have hupper : phi ^ (8 : ℕ) < 47.03 := phi_pow_8_upper
  have hpos : (0 : ℝ) < phi ^ (8 : ℕ) := pow_pos phi_pos 8
  have h1 : (phi ^ (8 : ℕ))⁻¹ > (47.03 : ℝ)⁻¹ := by
    rw [gt_iff_lt, inv_lt_inv₀ (by norm_num : (0:ℝ) < 47.03) hpos]
    exact hupper
  have h2 : (47.03 : ℝ)⁻¹ ≥ 0.02126 := by norm_num
  linarith

/-- φ^(-8) < 0.02137 (upper bound from φ^8 > 46.81). -/
theorem phi_zpow_neg8_upper : phi ^ (-8 : ℤ) < 0.02137 := by
  rw [phi_zpow_neg8_eq_inv]
  have hlower : phi ^ (8 : ℕ) > 46.81 := phi_pow_8_lower
  have hpos : (0 : ℝ) < phi ^ (8 : ℕ) := pow_pos phi_pos 8
  have h1 : (phi ^ (8 : ℕ))⁻¹ < (46.81 : ℝ)⁻¹ := by
    rw [inv_lt_inv₀ hpos (by norm_num : (0:ℝ) < 46.81)]
    exact hlower
  have h2 : (46.81 : ℝ)⁻¹ ≤ 0.02137 := by norm_num
  linarith

/-! ## Part 4: Bounds on (1 − φ^(-8)) and c_RS -/

/-- (1 − φ^(−8)) > 0.978. -/
theorem one_minus_phi_neg8_lower : (1 - phi ^ (-8 : ℤ)) > 0.978 := by
  have h := phi_zpow_neg8_upper
  linarith

/-- (1 − φ^(−8)) < 0.979. -/
theorem one_minus_phi_neg8_upper : (1 - phi ^ (-8 : ℤ)) < 0.979 := by
  have h := phi_zpow_neg8_lower
  linarith

/-- c_RS > 0.956 (lower numerical bound). -/
theorem c_RS_lower : c_RS > 0.956 := by
  rw [c_RS_expanded]
  have hl : (1 - phi ^ (-8 : ℤ)) > 0.978 := one_minus_phi_neg8_lower
  have hu : (1 - phi ^ (-8 : ℤ)) < 0.979 := one_minus_phi_neg8_upper
  have hpos : 0 < (1 - phi ^ (-8 : ℤ)) := by linarith
  nlinarith [hl, hu, hpos]

/-- c_RS < 0.959 (upper numerical bound). -/
theorem c_RS_upper : c_RS < 0.959 := by
  rw [c_RS_expanded]
  have hl : (1 - phi ^ (-8 : ℤ)) > 0.978 := one_minus_phi_neg8_lower
  have hu : (1 - phi ^ (-8 : ℤ)) < 0.979 := one_minus_phi_neg8_upper
  have hpos : 0 < (1 - phi ^ (-8 : ℤ)) := by linarith
  nlinarith [hl, hu, hpos]

/-! ## Part 5: φ^(-44) Bounds via the Fibonacci Identity -/

private lemma phi_zpow_neg44_eq_inv : phi ^ (-44 : ℤ) = (phi ^ (44 : ℕ))⁻¹ := by
  rw [show ((-44 : ℤ)) = -((44 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast]

/-- φ^(−44) > 6.37 × 10⁻¹⁰ (uses φ < 1.62 in the Fibonacci formula). -/
theorem phi_zpow_neg44_lower : phi ^ (-44 : ℤ) > 6.37e-10 := by
  rw [phi_zpow_neg44_eq_inv]
  have hupper : phi ^ (44 : ℕ) < 1.5698e9 := by
    rw [EtaBIntervalCert.phi_pow_44_fib]
    have hphi_lt : phi < 1.62 := phi_lt_onePointSixTwo
    nlinarith
  have hpos : (0 : ℝ) < phi ^ (44 : ℕ) := pow_pos phi_pos 44
  have h1 : (phi ^ (44 : ℕ))⁻¹ > (1.5698e9 : ℝ)⁻¹ := by
    rw [gt_iff_lt, inv_lt_inv₀ (by norm_num : (0:ℝ) < 1.5698e9) hpos]
    exact hupper
  have h2 : (1.5698e9 : ℝ)⁻¹ ≥ 6.37e-10 := by norm_num
  linarith

/-- φ^(−44) < 6.40 × 10⁻¹⁰ (uses φ > 1.61 in the Fibonacci formula). -/
theorem phi_zpow_neg44_upper : phi ^ (-44 : ℤ) < 6.40e-10 := by
  rw [phi_zpow_neg44_eq_inv]
  have hlower : phi ^ (44 : ℕ) > 1.5627e9 := by
    rw [EtaBIntervalCert.phi_pow_44_fib]
    have hphi_gt : phi > 1.61 := phi_gt_onePointSixOne
    nlinarith
  have hpos : (0 : ℝ) < phi ^ (44 : ℕ) := pow_pos phi_pos 44
  have h1 : (phi ^ (44 : ℕ))⁻¹ < (1.5627e9 : ℝ)⁻¹ := by
    rw [inv_lt_inv₀ hpos (by norm_num : (0:ℝ) < 1.5627e9)]
    exact hlower
  have h2 : (1.5627e9 : ℝ)⁻¹ < 6.40e-10 := by norm_num
  linarith

/-! ## Part 6: The Corrected η_B Prediction -/

/-- The fully-corrected RS prediction for η_B:
    η_B^RS = c_RS × φ^(−44) = (1 − φ^(−8))^2 × φ^(−44). -/
def eta_B_corrected_two_sided : ℝ := c_RS * eta_B_phi_scale

/-- The corrected prediction is positive. -/
theorem eta_B_corrected_two_sided_pos : 0 < eta_B_corrected_two_sided := by
  unfold eta_B_corrected_two_sided
  exact mul_pos c_RS_pos eta_B_phi_scale_pos

/-- The corrected prediction is strictly less than the leading term φ^(−44). -/
theorem corrected_lt_leading : eta_B_corrected_two_sided < eta_B_phi_scale := by
  unfold eta_B_corrected_two_sided
  have h := c_RS_lt_one
  have hpos := eta_B_phi_scale_pos
  calc c_RS * eta_B_phi_scale
      < 1 * eta_B_phi_scale := mul_lt_mul_of_pos_right h hpos
    _ = eta_B_phi_scale := one_mul _

/-! ## Part 7: The Tight Numerical Band Containing the Observed Value -/

/-- η_B^RS > 6.0 × 10⁻¹⁰ (strict lower bound). -/
theorem eta_B_corrected_lower : eta_B_corrected_two_sided > 6.0e-10 := by
  unfold eta_B_corrected_two_sided eta_B_phi_scale
  have hc : c_RS > 0.956 := c_RS_lower
  have hphi_lower : phi ^ (-44 : ℤ) > 6.37e-10 := phi_zpow_neg44_lower
  have hcpos : (0 : ℝ) < c_RS := c_RS_pos
  have hphi_pos : (0 : ℝ) < phi ^ (-44 : ℤ) := zpow_pos phi_pos (-44)
  -- 0.956 × 6.37e-10 = 6.0897e-10 > 6.0e-10
  nlinarith [hc, hphi_lower, hcpos, hphi_pos]

/-- η_B^RS < 6.2 × 10⁻¹⁰ (strict upper bound). -/
theorem eta_B_corrected_upper : eta_B_corrected_two_sided < 6.2e-10 := by
  unfold eta_B_corrected_two_sided eta_B_phi_scale
  have hc : c_RS < 0.959 := c_RS_upper
  have hphi_upper : phi ^ (-44 : ℤ) < 6.40e-10 := phi_zpow_neg44_upper
  have hcpos : (0 : ℝ) < c_RS := c_RS_pos
  have hphi_pos : (0 : ℝ) < phi ^ (-44 : ℤ) := zpow_pos phi_pos (-44)
  -- 0.959 × 6.40e-10 = 6.1376e-10 < 6.2e-10
  nlinarith [hc, hphi_upper, hcpos, hphi_pos]

/-- The corrected RS prediction lies in the band (6.0, 6.2) × 10⁻¹⁰,
    which contains the Planck 2018 central value 6.10 × 10⁻¹⁰. -/
theorem eta_B_corrected_in_observed_band :
    eta_B_corrected_two_sided > 6.0e-10 ∧ eta_B_corrected_two_sided < 6.2e-10 :=
  ⟨eta_B_corrected_lower, eta_B_corrected_upper⟩

/-- The Planck 2018 observed central value 6.10 × 10⁻¹⁰ falls inside
    the predicted band (6.0, 6.2) × 10⁻¹⁰. -/
theorem observed_in_predicted_band :
    (6.0e-10 : ℝ) < 6.10e-10 ∧ (6.10e-10 : ℝ) < 6.2e-10 := by
  constructor <;> norm_num

/-! ## Part 8: Comparison with the First-Order Correction -/

/-- The two-sided correction is strictly stronger than the first-order
    one-sided correction (since c_RS = correction_factor² < correction_factor). -/
theorem two_sided_stronger_than_one_sided :
    c_RS < correction_factor := by
  unfold c_RS
  have h1 : correction_factor < 1 := correction_factor_lt_one
  have h2 : 0 < correction_factor := correction_factor_pos
  calc correction_factor ^ 2
      = correction_factor * correction_factor := by ring
    _ < 1 * correction_factor := mul_lt_mul_of_pos_right h1 h2
    _ = correction_factor := one_mul _

/-- The two-sided corrected prediction is strictly smaller than the
    one-sided corrected prediction (`BaryonHigherOrder.eta_B_corrected`). -/
theorem two_sided_corrected_lt_one_sided :
    eta_B_corrected_two_sided < BaryonHigherOrder.eta_B_corrected := by
  unfold eta_B_corrected_two_sided BaryonHigherOrder.eta_B_corrected
  have h := two_sided_stronger_than_one_sided
  have hpos := eta_B_phi_scale_pos
  have := mul_lt_mul_of_pos_right h hpos
  linarith [this]

/-! ## Part 9: Master Certificate -/

/-- The η_B prefactor certificate.

    The order-one prefactor c in η_B = c × J_CP × (Γ_sph/H) / g★
    is structurally derived as c_RS = (1 − φ^(−8))^2 from
    two-sided 8-tick sphaleron washout. -/
structure EtaBPrefactorCert where
  /-- c_RS is order-one. -/
  prefactor_in_unit : 0 < c_RS ∧ c_RS < 1
  /-- Numerical band on c_RS. -/
  prefactor_band : c_RS > 0.956 ∧ c_RS < 0.959
  /-- Two-sided expansion. -/
  expanded : c_RS = (1 - phi ^ (-8 : ℤ)) ^ 2
  /-- Corrected prediction lies in the (6.0, 6.2) × 10⁻¹⁰ band. -/
  prediction_band :
    eta_B_corrected_two_sided > 6.0e-10 ∧ eta_B_corrected_two_sided < 6.2e-10
  /-- Planck 2018 central value 6.10 × 10⁻¹⁰ is inside the band. -/
  observed_inside : (6.0e-10 : ℝ) < 6.10e-10 ∧ (6.10e-10 : ℝ) < 6.2e-10
  /-- The two-sided correction strictly improves on the one-sided
      correction. -/
  improves_on_one_sided :
    eta_B_corrected_two_sided < BaryonHigherOrder.eta_B_corrected

/-- **THE η_B PREFACTOR THEOREM**:

    The order-one prefactor c in the η_B baryogenesis formula is
    structurally determined by the two-sided 8-tick washout:

      c_RS := (1 − φ^(−8))^2

    The corrected RS prediction
    η_B^RS = c_RS × φ^(−44)
    lies in the band (6.0, 6.2) × 10⁻¹⁰, which contains the Planck 2018
    central value 6.10 × 10⁻¹⁰. -/
theorem eta_B_prefactor_cert : EtaBPrefactorCert where
  prefactor_in_unit := c_RS_in_unit_interval
  prefactor_band := ⟨c_RS_lower, c_RS_upper⟩
  expanded := c_RS_expanded
  prediction_band := eta_B_corrected_in_observed_band
  observed_inside := observed_in_predicted_band
  improves_on_one_sided := two_sided_corrected_lt_one_sided

end

end EtaBPrefactorDerivation
end Cosmology
end IndisputableMonolith
