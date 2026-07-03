import Mathlib
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Foundation.JCostHessianC7
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Alpha Genesis M12: the genuine J-cost of cube curvature vs the seed (verdict)

This module records the decisive finding from the "derive α the right way" pass:
the seed `4π·11` is a **category error**, not a recognition cost. Two facts
settle it.

## 1. `4π` is a topological integral, not a cost

The factor `4π` in the seed is the discrete Gauss-Bonnet total curvature
`∑ deficits = 2π·χ(S²) = 4π` of `∂Q₃` (`AlphaDerivation.gauss_bonnet_Q3`). That
is a **linear** topological invariant. The recognition cost is the canonical
reciprocal cost `J`, which is **quadratic** at equilibrium: `J(1+ε) = ε²/(2(1+ε))`,
quadratic coefficient `1/2` (`JCostHessianC7`). A linear curvature integral and
a quadratic displacement cost are different objects; one cannot multiply `4π` by
an edge count and call the product a cost.

## 2. The genuine quadratic J-cost of the cube's curvature is `π²`, not `4π·11`

If one computes the actual recognition cost of the cube's curvature, summing the
quadratic J-cost `½·δ²` of each of the `8` vertex deficits `δ = π/2`:
`8 · ½ · (π/2)² = π² ≈ 9.87` (`cubeCurvatureJCost_eq_pi_sq`). This is the honest
forced quantity. It is below the topological `4π ≈ 12.57`
(`genuine_cost_lt_gaussBonnet`) and nowhere near the seed `4π·11 ≈ 138.23`
(`seed_far_above_genuine_cost`).

## Verdict

The seed `4π·11` is neither the genuine quadratic J-cost (`π²`) nor the
gauge-invariant photon count (`5`, see `U1Normalization`). It is an
identification, and its exact equality with `α⁻¹(0) = 137.035999` is falsified
(`MeasurementVerdict`, `ScaleIdentification`). The calibration-free content that
survives is an `O(4π)` UV-scale recognition cost; the exact infrared value of
`α` is OPEN.

This does NOT touch the forced *dressing* `g(t) = φ⁻ᵗ` (`CalibrationForcing`,
zero α-input) or the forced spectral weight `w₈` (`GapWeight`, zero α-input). It
isolates the SEED as the locus of the overclaim.

STATUS: THEOREM (the cost computation and inequalities); QUARANTINE.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis
namespace CurvatureJCostVerdict

open Constants.AlphaDerivation

noncomputable section

/-- The genuine quadratic recognition cost of the cube's curvature: the J-cost
quadratic coefficient `1/2` (`JCostHessianC7.jcostTaylorQuadraticCoefficient`)
applied to each of the `8` vertex deficits `δ = π/2`, summed:
`8 · ½ · (π/2)²`. -/
def cubeCurvatureJCost : ℝ :=
  (cube_vertices D : ℝ)
    * Foundation.JCostHessianC7.jcostTaylorQuadraticCoefficient
    * (vertex_angular_deficit) ^ 2

/-- **The genuine J-cost of the cube curvature is `π²`.** `8 · ½ · (π/2)² = π²`.
This is the honest quadratic recognition cost, contrasted with the seed's
`4π·11`. -/
theorem cubeCurvatureJCost_eq_pi_sq : cubeCurvatureJCost = Real.pi ^ 2 := by
  unfold cubeCurvatureJCost
  rw [vertex_deficit_eq, Foundation.JCostHessianC7.jcostTaylorQuadraticCoefficient_eq]
  have h8 : (cube_vertices D : ℝ) = 8 := by exact_mod_cast vertices_at_D3
  rw [h8]; ring

/-- The genuine quadratic J-cost `π² ≈ 9.87` is strictly below the topological
Gauss-Bonnet integral `4π ≈ 12.57`: a quadratic cost and a linear topological
invariant are different objects, and they do not even agree numerically. -/
theorem genuine_cost_lt_gaussBonnet :
    cubeCurvatureJCost < 4 * Real.pi := by
  rw [cubeCurvatureJCost_eq_pi_sq]
  nlinarith [Real.pi_pos, Real.pi_lt_four]

/-- The seed `4π·11` is far above the genuine quadratic J-cost `π²` of the cube
curvature: `π² < 4π < 4π·11`. The seed is not a recognition cost. -/
theorem seed_far_above_genuine_cost :
    cubeCurvatureJCost < Constants.alpha_seed := by
  have h1 : cubeCurvatureJCost < 4 * Real.pi := genuine_cost_lt_gaussBonnet
  have h2 : (4 : ℝ) * Real.pi < Constants.alpha_seed := by
    simp only [Constants.alpha_seed]
    nlinarith [Real.pi_pos]
  linarith

/-- The genuine quadratic J-cost is also far below the measured `α⁻¹`:
`π² < 137.030 < alphaInv`. So even the honest cost is not `α⁻¹(0)`; the cube
forces only an `O(4π)` UV-scale quantity. -/
theorem genuine_cost_far_below_alphaInv :
    cubeCurvatureJCost < Constants.alphaInv := by
  rw [cubeCurvatureJCost_eq_pi_sq]
  have h1 : Real.pi ^ 2 < 4 * Real.pi := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have h2 : (4 : ℝ) * Real.pi < 13 := by nlinarith [Real.pi_lt_d6]
  have h3 : (137.030 : ℝ) < Constants.alphaInv := Numerics.alphaInv_gt
  linarith

/-! ## The verdict -/

/-- **Curvature-cost verdict.** The seed `4π·11` is a category error: `4π` is a
linear topological invariant (Gauss-Bonnet), not a quadratic recognition cost;
the genuine quadratic J-cost of the cube curvature is `π²`; and the seed exceeds
both the genuine cost and the topological invariant. The exact value of `α⁻¹(0)`
is not produced by any of these forced quantities; it is OPEN. -/
structure CurvatureCostVerdict : Prop where
  genuine_cost_is_pi_sq : cubeCurvatureJCost = Real.pi ^ 2
  cost_below_topological : cubeCurvatureJCost < 4 * Real.pi
  seed_above_genuine_cost : cubeCurvatureJCost < Constants.alpha_seed
  genuine_cost_not_alphaInv : cubeCurvatureJCost < Constants.alphaInv

def curvatureCostVerdict : CurvatureCostVerdict where
  genuine_cost_is_pi_sq := cubeCurvatureJCost_eq_pi_sq
  cost_below_topological := genuine_cost_lt_gaussBonnet
  seed_above_genuine_cost := seed_far_above_genuine_cost
  genuine_cost_not_alphaInv := genuine_cost_far_below_alphaInv

end

end CurvatureJCostVerdict
end AlphaGenesis
end Constants
end IndisputableMonolith
