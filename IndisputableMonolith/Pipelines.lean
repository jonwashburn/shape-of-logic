import Mathlib

namespace IndisputableMonolith
namespace Pipelines

open Real

/-- Golden ratio φ as a concrete real number. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

namespace GapSeries

/-- Gap-series coefficient (1-indexed by design via `n.succ`).
The conventional closed-form uses the series of `log(1+x)` at `x = z/φ`.
This definition is dimensionless and self-contained. -/
noncomputable def coeff (n : ℕ) : ℝ :=
  let k := n.succ
  ((-1 : ℝ) ^ k) / (k : ℝ) / (phi ^ k)

/-- Finite partial sum (0..n-1) of the gap coefficients (evaluated at z=1).
This stays purely algebraic here; convergence and identification with
`log(1 + 1/φ)` can be proved in a companion module that imports analysis. -/
noncomputable def partialSum (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun i => coeff i)

/-- Generating functional F(z) := log(1 + z/φ).  -/
noncomputable def F (z : ℝ) : ℝ := Real.log (1 + z / phi)

/-- The master gap value as the generator at z=1. -/
noncomputable def f_gap : ℝ := F 1
@[simp] lemma f_gap_def : f_gap = Real.log (1 + 1 / phi) := rfl

end GapSeries

namespace Curvature

/-- Curvature-closure constant δ_κ used in the α pipeline.
Defined here as the exact rational/π expression from the voxel seam count. -/
noncomputable def deltaKappa : ℝ := - (103 : ℝ) / (102 * Real.pi ^ 5)

/-- The predicted dimensionless inverse fine-structure constant
α^{-1} = 4π·11 − (ln φ + δ_κ).
This is a pure expression-level definition (no numerics here). -/
noncomputable def alphaInvPrediction : ℝ := 4 * Real.pi * 11 - (Real.log phi + deltaKappa)

end Curvature

end Pipelines
end IndisputableMonolith
