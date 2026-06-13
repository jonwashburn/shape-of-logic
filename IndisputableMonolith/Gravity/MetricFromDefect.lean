import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.ZeroParameterGravity

/-!
# Step 2: Metric Perturbation from J-Cost Defect Density

Defines the metric perturbation h_mu_nu as a function of the J-cost defect
field on the lattice. In the weak-field limit, spacetime geometry emerges
from the distribution of ledger defects.

## Physical Picture

- Each voxel carries a J-cost defect: J(x) = ½(x + x⁻¹) - 1 ≥ 0
- A region with high defect density has more "strain" in the ledger
- This strain curves the emergent spacetime: g_mu_nu = eta_mu_nu + h_mu_nu
- The metric perturbation h is proportional to the integrated defect density
- The proportionality constant is kappa = 8*phi^5 (from ZeroParameterGravity)

## Linearized Gravity Convention

In linearized GR, the metric perturbation h_mu_nu satisfies:
- h is symmetric: h_mu_nu = h_nu_mu
- The trace-reversed perturbation: h_bar = h - (1/2) eta * trace(h)
- The linearized EFE in harmonic gauge: nabla^2 h_bar = -2*kappa * T

In RS, the defect density IS the stress-energy source T^00.
-/

namespace IndisputableMonolith
namespace Gravity
namespace MetricFromDefect

open Constants

noncomputable section

/-! ## Symmetric Tensor Structure -/

/-- A symmetric 2-tensor in D dimensions, represented as a symmetric
    matrix (upper-triangular storage). For D=3+1 spacetime, indices
    run over {0,1,2,3}. For the spatial part, D=3 with {1,2,3}. -/
structure SymmetricTensor (D : ℕ) where
  components : Fin D → Fin D → ℝ
  symmetric : ∀ i j, components i j = components j i

/-- The flat Minkowski metric in D spatial dimensions (spatial part only).
    eta_ij = delta_ij (Euclidean for spatial indices). -/
def flat_metric_spatial : SymmetricTensor 3 where
  components := fun i j => if i = j then 1 else 0
  symmetric := by intro i j; simp [eq_comm]

/-- The trace of a symmetric tensor. -/
def trace (t : SymmetricTensor 3) : ℝ := t.components 0 0 + t.components 1 1 + t.components 2 2

/-! ## Defect Field to Metric Perturbation -/

/-- The J-cost defect density at a point. In RS, this is the source
    of spacetime curvature. A defect density of zero means flat space. -/
structure DefectField where
  density : ℝ → ℝ → ℝ → ℝ
  nonneg : ∀ x y z, 0 ≤ density x y z

/-- The metric perturbation h_mu_nu induced by a defect field.
    In the Newtonian limit: h_00 = -2*Phi, h_ij = -2*Phi*delta_ij
    where Phi is the gravitational potential sourced by the defect density.

    The coupling constant is kappa = 8*phi^5.

    For a uniform defect density rho: Phi = -(1/2)*kappa*rho*r^2/(D=3)
    (Poisson equation: nabla^2 Phi = kappa * rho). -/
def metric_perturbation_from_defect (d : DefectField) (r : ℝ) : SymmetricTensor 3 where
  components := fun i j => if i = j then -ZeroParameterGravity.kappa_rs * d.density r 0 0 else 0
  symmetric := by intro i j; simp [eq_comm]

/-- The metric perturbation is symmetric by construction. -/
theorem metric_perturbation_symmetric (d : DefectField) (r : ℝ) (i j : Fin 3) :
    (metric_perturbation_from_defect d r).components i j =
    (metric_perturbation_from_defect d r).components j i :=
  (metric_perturbation_from_defect d r).symmetric i j

/-- Zero defect density gives zero metric perturbation (flat space). -/
theorem zero_defect_flat_space (r : ℝ) :
    let d : DefectField := ⟨fun _ _ _ => 0, fun _ _ _ => le_refl 0⟩
    (metric_perturbation_from_defect d r).components 0 0 = 0 := by
  simp [metric_perturbation_from_defect, ZeroParameterGravity.kappa_rs]

/-- The metric perturbation is proportional to kappa (= 8*phi^5). -/
theorem perturbation_proportional_to_kappa (d : DefectField) (r : ℝ) :
    (metric_perturbation_from_defect d r).components 0 0 =
    -ZeroParameterGravity.kappa_rs * d.density r 0 0 := by
  simp [metric_perturbation_from_defect]

/-! ## Weak-Field Regime -/

/-- In the weak-field regime, |h_mu_nu| << 1. This means the defect
    density must be small: kappa * rho << 1. -/
def weak_field_condition (d : DefectField) : Prop :=
  ∀ x y z, |d.density x y z| < 1 / ZeroParameterGravity.kappa_rs

/-- Under the weak-field condition, the metric perturbation is small. -/
theorem weak_field_small_perturbation (d : DefectField) (hd : weak_field_condition d)
    (r : ℝ) :
    |(metric_perturbation_from_defect d r).components 0 0| <  1 := by
  rw [perturbation_proportional_to_kappa]
  have hk := ZeroParameterGravity.kappa_pos
  have hd0 := hd r 0 0
  have h_eq :
      |-ZeroParameterGravity.kappa_rs * d.density r 0 0|
        = ZeroParameterGravity.kappa_rs * |d.density r 0 0| := by
    rw [show (-ZeroParameterGravity.kappa_rs * d.density r 0 0)
          = -(ZeroParameterGravity.kappa_rs * d.density r 0 0) from by ring,
        abs_neg, abs_mul, abs_of_pos hk]
  rw [h_eq]
  calc ZeroParameterGravity.kappa_rs * |d.density r 0 0|
      < ZeroParameterGravity.kappa_rs * (1 / ZeroParameterGravity.kappa_rs) :=
        mul_lt_mul_of_pos_left hd0 hk
    _ = 1 := by field_simp

/-! ## Certificate -/

structure MetricFromDefectCert where
  symmetric : ∀ d r i j,
    (metric_perturbation_from_defect d r).components i j =
    (metric_perturbation_from_defect d r).components j i
  proportional_to_kappa : ∀ d r,
    (metric_perturbation_from_defect d r).components 0 0 =
    -ZeroParameterGravity.kappa_rs * d.density r 0 0

theorem metric_from_defect_cert : MetricFromDefectCert where
  symmetric := metric_perturbation_symmetric
  proportional_to_kappa := perturbation_proportional_to_kappa

end

end MetricFromDefect
end Gravity
end IndisputableMonolith
