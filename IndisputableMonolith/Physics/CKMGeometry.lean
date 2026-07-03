import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.PhiSupport
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Numerics.Interval.AlphaBounds
import IndisputableMonolith.Physics.MixingGeometry

/-!
# T11: The CKM Matrix Geometry

This module formalizes the derivation of the CKM mixing angles from the
ledger geometry and the fine-structure constant.

## The Hypothesis

The CKM matrix elements $|V_{us}|, |V_{cb}|, |V_{ub}|$ are not arbitrary parameters.
They are determined by geometric couplings on the cubic ledger:

1. **Theta 13 ($V_{ub}$)**: The "Fine Structure Coupling".
   $$ |V_{ub}| = \frac{\alpha}{2} $$
   Prediction: 0.00365. Observation: 0.00369(11). Match: < 1 sigma.

2. **Theta 23 ($V_{cb}$)**: The "Edge-Dual Coupling".
   $$ |V_{cb}| = \frac{1}{2 E_{total}} = \frac{1}{24} $$
   Prediction: 0.04167. Observation: 0.04182(85). Match: < 0.2 sigma.

3. **Theta 12 ($V_{us}$, Cabibbo)**: The "Golden Projection".
   $$ |V_{us}| = \phi^{-3} - \frac{3}{2}\alpha $$
   Prediction: 0.2251. Observation: 0.2250(7). Match: < 0.2 sigma.

## Verification Status

T11 V_cb theorem is now PROVEN (1/24 is exact rational).
V_ub and V_us depend on α and φ which require interval arithmetic for full proofs.

-/

namespace IndisputableMonolith
namespace Physics
namespace CKMGeometry

open Real Constants AlphaDerivation MixingGeometry

/-! ## Experimental Values (PDG 2022) -/

def V_us_exp : ℝ := 0.22500
def V_us_err : ℝ := 0.00067

def V_cb_exp : ℝ := 0.04182
def V_cb_err : ℝ := 0.00085

def V_ub_exp : ℝ := 0.00369
def V_ub_err : ℝ := 0.00011

/-! ## Theoretical Predictions -/

/-- V_ub is half the fine-structure constant (fine_structure_leakage). -/
noncomputable def V_ub_pred : ℝ := fine_structure_leakage

/-- V_cb geometric ratio: 1/vertex_edge_slots = 1/24. -/
def V_cb_geom : ℚ := edge_dual_ratio

/-- V_cb is the inverse of twice the total edge count (1/24). -/
noncomputable def V_cb_pred : ℝ := (V_cb_geom : ℝ)

/-- V_us is the golden projection (torsion_overlap) minus a radiative correction. -/
noncomputable def V_us_pred : ℝ := torsion_overlap - cabibbo_radiative_correction

/-! ## Geometric Derivation -/

/-- V_cb derives from cube edge geometry: 1/(2 * 12) = 1/24. -/
theorem V_cb_from_cube_edges :
    V_cb_geom = 1 / (2 * cube_edges 3) := by
  simp only [V_cb_geom, edge_dual_ratio, cube_edges]
  norm_num

/-! ## Verification Theorems -/

/-- V_cb matches within 1 sigma.

    pred = 1/24 ≈ 0.04166666...
    obs  = 0.04182
    err  = 0.00085
    |pred - obs| = |0.04166 - 0.04182| = 0.00016 < 0.00085 ✓

    This is now PROVEN, not axiomatized. -/
theorem V_cb_match : abs (V_cb_pred - V_cb_exp) < V_cb_err := by
  simp only [V_cb_pred, V_cb_geom, V_cb_exp, V_cb_err, edge_dual_ratio]
  norm_num

/-- Bounds on alpha needed for CKM proofs.
    alphaInv ≈ 137.036 so alpha ≈ 0.00730
    NOTE: These bounds are verified numerically but require transcendental
    computation (involving π and ln(φ)) that norm_num cannot handle. -/
theorem alpha_lower_bound : (0.00729 : ℝ) < Constants.alpha := by
  -- From the rigorous interval proof: alphaInv < 137.039 ⇒ 1/137.039 < alpha
  have h_inv_lt : Constants.alphaInv < (137.039 : ℝ) := by
    simpa [Constants.alphaInv] using (IndisputableMonolith.Numerics.alphaInv_lt)
  have h_inv_pos : (0 : ℝ) < Constants.alphaInv := by
    have h := IndisputableMonolith.Numerics.alphaInv_gt
    linarith
  -- Invert inequality (antitone on positive reals).
  have h_one_div : (1 / (137.039 : ℝ)) < 1 / Constants.alphaInv := by
    exact one_div_lt_one_div_of_lt h_inv_pos h_inv_lt
  -- Translate to alpha = 1/alphaInv and weaken the numeric constant to 0.00729.
  have h_num : (0.00729 : ℝ) < (1 / (137.039 : ℝ)) := by norm_num
  simpa [Constants.alpha, one_div] using lt_trans h_num h_one_div

theorem alpha_upper_bound : Constants.alpha < (0.00731 : ℝ) := by
  -- From the rigorous interval proof: 137.030 < alphaInv ⇒ alpha < 1/137.030
  have h_inv_gt : (137.030 : ℝ) < Constants.alphaInv := by
    simpa [Constants.alphaInv] using (IndisputableMonolith.Numerics.alphaInv_gt)
  have h_pos : (0 : ℝ) < (137.030 : ℝ) := by norm_num
  -- Invert inequality (antitone on positive reals): 1/alphaInv < 1/137.030
  have h_one_div : (1 / Constants.alphaInv) < 1 / (137.030 : ℝ) := by
    exact one_div_lt_one_div_of_lt h_pos h_inv_gt
  -- Translate to alpha = 1/alphaInv and weaken the numeric constant to 0.00731.
  have h_num : (1 / (137.030 : ℝ)) < (0.00731 : ℝ) := by norm_num
  have : Constants.alpha < 1 / (137.030 : ℝ) := by
    simpa [Constants.alpha, one_div] using h_one_div
  exact lt_trans this h_num

/-- V_ub matches within 1 sigma.

    V_ub_pred = alpha/2 ≈ 0.00365
    V_ub_exp = 0.00369
    |V_ub_pred - V_ub_exp| ≈ 0.00004 < 0.00011 ✓

    Proof: From alpha bounds (0.00729, 0.00731), we get
    alpha/2 ∈ (0.003645, 0.003655), and
    |0.00365 - 0.00369| = 0.00004 < 0.00011. -/
theorem V_ub_match : abs (V_ub_pred - V_ub_exp) < V_ub_err := by
  have h_alpha_lower := alpha_lower_bound
  have h_alpha_upper := alpha_upper_bound
  simp only [V_ub_pred, V_ub_exp, V_ub_err, fine_structure_leakage]
  -- alpha/2 ∈ (0.003645, 0.003655)
  have h_lower : (0.003645 : ℝ) < Constants.alpha / 2 := by linarith
  have h_upper : Constants.alpha / 2 < (0.003655 : ℝ) := by linarith
  -- |alpha/2 - 0.00369| ≤ max(|0.003645 - 0.00369|, |0.003655 - 0.00369|)
  --                     = max(0.000045, 0.000035) = 0.000045 < 0.00011
  rw [abs_lt]
  constructor <;> linarith

/-- Bounds on phi^(-3) needed for V_us proof.
    φ^(-3) ≈ 0.2360679...

    These bounds are derived from phi_tight_bounds via antitonicity. -/
theorem phi_inv3_lower_bound : (0.2360 : ℝ) < phi ^ (-3 : ℤ) :=
  Numerics.phi_inv3_zpow_bounds.1

theorem phi_inv3_upper_bound : phi ^ (-3 : ℤ) < (0.2361 : ℝ) :=
  Numerics.phi_inv3_zpow_bounds.2

/-- V_us matches within 1 sigma.

    V_us_pred = φ^(-3) - (3/2)*α
              ≈ 0.2360679 - 0.01095
              ≈ 0.2251
    V_us_exp = 0.22500
    |V_us_pred - V_us_exp| ≈ 0.0001 < 0.00067 ✓

    Proof: From bounds on φ^(-3) and α, we establish the match. -/
theorem V_us_match : abs (V_us_pred - V_us_exp) < V_us_err := by
  have h_alpha_lower := alpha_lower_bound
  have h_alpha_upper := alpha_upper_bound
  have h_phi3_lower := phi_inv3_lower_bound
  have h_phi3_upper := phi_inv3_upper_bound
  simp only [V_us_pred, V_us_exp, V_us_err, torsion_overlap, cabibbo_radiative_correction]
  -- V_us_pred = phi^(-3) - 1.5*alpha
  -- phi^(-3) ∈ (0.2360, 0.2361)
  -- 1.5*alpha ∈ (0.010935, 0.010965)
  -- V_us_pred ∈ (0.2360 - 0.010965, 0.2361 - 0.010935) = (0.225035, 0.225165)
  have h_correction_lower : (0.010935 : ℝ) < (3/2) * Constants.alpha := by linarith
  have h_correction_upper : (3/2) * Constants.alpha < (0.010965 : ℝ) := by linarith
  have h_pred_lower : (0.225035 : ℝ) < Constants.phi ^ (-3 : ℤ) - (3/2) * Constants.alpha := by linarith
  have h_pred_upper : Constants.phi ^ (-3 : ℤ) - (3/2) * Constants.alpha < (0.225165 : ℝ) := by linarith
  -- |V_us_pred - 0.22500| ≤ max(|0.225035 - 0.22500|, |0.225165 - 0.22500|)
  --                      = max(0.000035, 0.000165) = 0.000165 < 0.00067
  rw [abs_lt]
  constructor <;> linarith

/-! ## Certificate -/

/-- T11 Certificate: V_cb from cube edge geometry. -/
structure T11Cert where
  /-- V_cb = 1/(2*12) = 1/24 from cube edges. -/
  geometric_origin : V_cb_geom = 1 / (2 * cube_edges 3)
  /-- The prediction matches experiment within uncertainty. -/
  matches_pdg : abs (V_cb_pred - V_cb_exp) < V_cb_err

/-- The T11 certificate (for V_cb) is verified. -/
def t11_V_cb_verified : T11Cert where
  geometric_origin := V_cb_from_cube_edges
  matches_pdg := V_cb_match

end CKMGeometry
end Physics
end IndisputableMonolith
