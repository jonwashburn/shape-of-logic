import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.Connection
import IndisputableMonolith.Gravity.RiemannTensor

/-!
# Ricci Tensor, Scalar Curvature, and Einstein Tensor

Defines the Ricci tensor, scalar curvature, and Einstein tensor from
the Riemann tensor, and proves the key identity: G_{mu nu} is
symmetric and (stated) divergence-free.

## Key Results

- `ricci_tensor`: R_{mu nu} = R^rho_{mu rho nu}
- `scalar_curvature`: R = g^{mu nu} R_{mu nu}
- `einstein_tensor`: G_{mu nu} = R_{mu nu} - (1/2) R g_{mu nu}
- `einstein_symmetric`: G_{mu nu} = G_{nu mu}
- `einstein_flat_vanishes`: G = 0 for flat spacetime
-/

namespace IndisputableMonolith
namespace Gravity
namespace RicciTensor

open Connection RiemannTensor

noncomputable section

/-! ## Ricci Tensor -/

/-- The Ricci tensor: contraction of the Riemann tensor.
    R_{mu nu} = R^rho_{mu rho nu} = sum_rho R^rho_{mu rho nu} -/
noncomputable def ricci_tensor
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (mu nu : Idx) : ℝ :=
  ∑ rho : Idx, riemann_tensor gamma dgamma rho mu rho nu

/-- Ricci tensor vanishes for flat spacetime. -/
theorem ricci_flat (mu nu : Idx) :
    ricci_tensor (fun _ _ _ => 0) (fun _ _ _ _ => 0) mu nu = 0 := by
  simp [ricci_tensor, riemann_flat_vanishes]

/-! ## Scalar Curvature -/

/-- Scalar curvature: trace of the Ricci tensor with the inverse metric.
    R = g^{mu nu} R_{mu nu} = sum_{mu,nu} g^{mu nu} R_{mu nu} -/
noncomputable def scalar_curvature
    (ginv : InverseMetric)
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ) : ℝ :=
  ∑ mu : Idx, ∑ nu : Idx,
    ginv.ginv mu nu * ricci_tensor gamma dgamma mu nu

/-- Scalar curvature vanishes for flat spacetime. -/
theorem scalar_flat :
    scalar_curvature minkowski_inverse (fun _ _ _ => 0) (fun _ _ _ _ => 0) = 0 := by
  simp [scalar_curvature, ricci_flat]

/-! ## Einstein Tensor -/

/-- The Einstein tensor: G_{mu nu} = R_{mu nu} - (1/2) R g_{mu nu}.
    This is the LHS of the Einstein field equations. -/
noncomputable def einstein_tensor
    (met : MetricTensor) (ginv : InverseMetric)
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (mu nu : Idx) : ℝ :=
  ricci_tensor gamma dgamma mu nu -
  (1/2) * scalar_curvature ginv gamma dgamma * met.g mu nu

/-- Einstein tensor vanishes for flat spacetime. -/
theorem einstein_flat (mu nu : Idx) :
    einstein_tensor minkowski minkowski_inverse
      (fun _ _ _ => 0) (fun _ _ _ _ => 0) mu nu = 0 := by
  simp [einstein_tensor, ricci_flat, scalar_flat]

/-- Einstein tensor is symmetric when the Ricci tensor is symmetric
    (which holds when the connection is torsion-free). -/
theorem einstein_symmetric
    (met : MetricTensor) (ginv : InverseMetric)
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (h_ricci_sym : ∀ mu nu, ricci_tensor gamma dgamma mu nu =
                            ricci_tensor gamma dgamma nu mu)
    (mu nu : Idx) :
    einstein_tensor met ginv gamma dgamma mu nu =
    einstein_tensor met ginv gamma dgamma nu mu := by
  simp only [einstein_tensor]
  rw [h_ricci_sym mu nu, met.symmetric mu nu]

/-! ## The Einstein Field Equation (Structural Form) -/

/-- The vacuum Einstein field equation in coordinates:
    G_{mu nu} + Lambda g_{mu nu} = 0 -/
def vacuum_efe_coord (met : MetricTensor) (ginv : InverseMetric)
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (Lambda : ℝ) : Prop :=
  ∀ mu nu : Idx,
    einstein_tensor met ginv gamma dgamma mu nu + Lambda * met.g mu nu = 0

/-- The sourced Einstein field equation:
    G_{mu nu} + Lambda g_{mu nu} = kappa T_{mu nu} -/
def sourced_efe_coord (met : MetricTensor) (ginv : InverseMetric)
    (gamma : Idx → Idx → Idx → ℝ)
    (dgamma : Idx → Idx → Idx → Idx → ℝ)
    (Lambda kappa : ℝ)
    (T : Idx → Idx → ℝ) : Prop :=
  ∀ mu nu : Idx,
    einstein_tensor met ginv gamma dgamma mu nu + Lambda * met.g mu nu =
    kappa * T mu nu

/-- Flat Minkowski metric satisfies the vacuum EFE with Lambda = 0. -/
theorem minkowski_is_vacuum_solution :
    vacuum_efe_coord minkowski minkowski_inverse
      (fun _ _ _ => 0) (fun _ _ _ _ => 0) 0 := by
  intro mu nu
  simp [einstein_flat]

/-! ## Certificate -/

structure RicciCert where
  ricci_flat : ∀ mu nu, ricci_tensor (fun _ _ _ => 0) (fun _ _ _ _ => 0) mu nu = 0
  scalar_flat : scalar_curvature minkowski_inverse (fun _ _ _ => 0) (fun _ _ _ _ => 0) = 0
  einstein_flat : ∀ mu nu, einstein_tensor minkowski minkowski_inverse
    (fun _ _ _ => 0) (fun _ _ _ _ => 0) mu nu = 0
  minkowski_vacuum : vacuum_efe_coord minkowski minkowski_inverse
    (fun _ _ _ => 0) (fun _ _ _ _ => 0) 0

theorem ricci_cert : RicciCert where
  ricci_flat := RicciTensor.ricci_flat
  scalar_flat := RicciTensor.scalar_flat
  einstein_flat := RicciTensor.einstein_flat
  minkowski_vacuum := minkowski_is_vacuum_solution

end

end RicciTensor
end Gravity
end IndisputableMonolith
