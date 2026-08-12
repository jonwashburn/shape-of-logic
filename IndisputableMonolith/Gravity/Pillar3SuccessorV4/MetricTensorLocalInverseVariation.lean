import IndisputableMonolith.Relativity.Variation.Functional

/-!
# Local inverse-metric variation without the legacy axiom

`Variation.perturbed_metric` is defined by adding a symmetric matrix line to
the inverse metric and then inverting that line to obtain a covariant metric.
Near zero, nondegeneracy is open.  The inverse of the resulting covariant
metric is therefore exactly the matrix line used in the definition.

This module proves that local identity and differentiates it.  In particular,
`functionalDeriv_inverseMetric_provedLocally` has the same conclusion as the
legacy `functional_deriv_inverse_metric` axiom but does not reference it.

THEOREM: local inverse-metric perturbation and its Gateaux derivative.
No `sorry`, `admit`, or new axiom.
-/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

namespace IndisputableMonolith
namespace Gravity
namespace Pillar3SuccessorV4
namespace MetricTensorLocalInverseVariation

open Relativity.Geometry
open Relativity.Variation
open Matrix
open scoped Topology

/--
At a nondegenerate metric, the inverse metric of `perturbed_metric` agrees in
a neighborhood of zero with the affine inverse-metric line used to define the
perturbation.
-/
theorem inverseMetric_perturbedMetric_eventuallyEq_inverseLine
    (g : MetricTensor)
    (mu nu rho sigma : Fin 4)
    (x : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x) :
    (fun e : ℝ =>
        inverse_metric (perturbed_metric g mu nu x e) x
          (fun i => if i = 0 then rho else sigma)
          (fun _ => 0)) =ᶠ[nhds 0]
      (fun e : ℝ =>
        ((metric_to_matrix g x)⁻¹ + e • delta_matrix mu nu) rho sigma) := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := metric_to_matrix g x
  letI : Invertible A := metric_matrix_invertible g x h_inv
  have hAunit : IsUnit A.det :=
    Matrix.isUnit_det_of_invertible A
  have hAinvunit : IsUnit A⁻¹.det :=
    Matrix.isUnit_nonsing_inv_det A hAunit
  have hcontinuous :
      Continuous (fun e : ℝ => A⁻¹ + e • delta_matrix mu nu) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hdet_zero :
      (A⁻¹ + (0 : ℝ) • delta_matrix mu nu).det ≠ 0 := by
    simpa using (isUnit_iff_ne_zero.mp hAinvunit)
  have heventually_nondegenerate :
      ∀ᶠ e : ℝ in nhds 0,
        (A⁻¹ + e • delta_matrix mu nu).det ≠ 0 :=
    hcontinuous.matrix_det.continuousAt.eventually_ne hdet_zero
  filter_upwards [heventually_nondegenerate] with e he
  have hunit :
      IsUnit (A⁻¹ + e • delta_matrix mu nu).det :=
    isUnit_iff_ne_zero.mpr he
  unfold inverse_metric perturbed_metric metric_to_matrix
  dsimp only
  simp only [ite_true]
  change (((A⁻¹ + e • delta_matrix mu nu)⁻¹)⁻¹ rho sigma) = _
  rw [Matrix.nonsing_inv_nonsing_inv _ hunit]
  rfl

/--
The locally perturbed inverse-metric component has the expected symmetrized
Kronecker derivative.
-/
theorem inverseMetric_perturbedMetric_hasDerivAt
    (g : MetricTensor)
    (mu nu rho sigma : Fin 4)
    (x : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x) :
    HasDerivAt
      (fun e : ℝ =>
        inverse_metric (perturbed_metric g mu nu x e) x
          (fun i => if i = 0 then rho else sigma)
          (fun _ => 0))
      (delta_matrix mu nu rho sigma)
      0 := by
  have hline :
      HasDerivAt
        (fun e : ℝ =>
          ((metric_to_matrix g x)⁻¹ + e • delta_matrix mu nu) rho sigma)
        (delta_matrix mu nu rho sigma)
        0 := by
    convert
        ((hasDerivAt_const
          (0 : ℝ) ((metric_to_matrix g x)⁻¹ rho sigma)).add
        ((hasDerivAt_id (0 : ℝ)).mul_const
          (delta_matrix mu nu rho sigma))) using 1
    all_goals simp
  exact hline.congr_of_eventuallyEq
    (inverseMetric_perturbedMetric_eventuallyEq_inverseLine
      g mu nu rho sigma x h_inv)

/--
The existing differentiability predicate follows from local nondegeneracy; it
does not need to be supplied as a separate hypothesis.
-/
theorem differentiableAt_inverseMetric_provedLocally
    (g : MetricTensor)
    (mu nu rho sigma : Fin 4)
    (x : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x) :
    differentiableAt_inverse_metric g mu nu rho sigma x :=
  (inverseMetric_perturbedMetric_hasDerivAt
    g mu nu rho sigma x h_inv).differentiableAt

/--
Local theorem replacing `functional_deriv_inverse_metric`.  The legacy axiom
is deliberately not used.
-/
theorem functionalDeriv_inverseMetric_provedLocally
    (rho sigma : Fin 4)
    (g : MetricTensor)
    (mu nu : Fin 4)
    (x : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x) :
    functional_deriv
        (fun g' y =>
          inverse_metric g' y
            (fun i => if i = 0 then rho else sigma)
            (fun _ => 0))
        g mu nu x =
      delta_matrix mu nu rho sigma := by
  unfold functional_deriv
  exact
    (inverseMetric_perturbedMetric_hasDerivAt
      g mu nu rho sigma x h_inv).deriv

end MetricTensorLocalInverseVariation
end Pillar3SuccessorV4
end Gravity
end IndisputableMonolith
