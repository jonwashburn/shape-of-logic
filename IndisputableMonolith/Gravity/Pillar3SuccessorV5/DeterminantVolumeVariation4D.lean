import Mathlib
import IndisputableMonolith.Gravity.Pillar3SuccessorV4.MetricTensorLocalInverseVariation

/-!
# Pillar-3 Successor V5: proved determinant and volume variation

This module replaces the determinant witnesses used by the older variational
scaffold with an ordinary Lean proof.  The proof factors an affine matrix line
through `1 + ε C` and uses Mathlib's proved first-order determinant expansion.
No `SqrtAbsInvDetDerivWitness` or `jacobi_det_hypothesis` is accepted.

The final specialization is four-dimensional and uses V4's locally proved
identity for the inverse metric of `perturbed_metric`.
-/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

namespace IndisputableMonolith
namespace Gravity
namespace Pillar3SuccessorV5
namespace DeterminantVolumeVariation4D

open scoped Topology

open Matrix
open Relativity.Geometry
open Relativity.Variation
open Pillar3SuccessorV4.MetricTensorLocalInverseVariation

/-- The derivative of `det (1 + ε M)` at zero is `trace M`.

Mathlib proves the exact polynomial expansion in
`Matrix.det_one_add_smul`; this theorem turns that algebraic result into the
analytic `HasDerivAt` statement needed by the action calculation. -/
theorem detOneAddSMul_hasDerivAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    HasDerivAt (fun e : ℝ => (1 + e • M).det) M.trace 0 := by
  let q : Polynomial ℝ :=
    (Matrix.det
      (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hq :
      HasDerivAt (fun e : ℝ => q.eval e) (q.derivative.eval 0) 0 :=
    q.hasDerivAt 0
  have he2 : HasDerivAt (fun e : ℝ => e ^ 2) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).pow 2
  have hrem :
      HasDerivAt (fun e : ℝ => q.eval e * e ^ 2) 0 0 := by
    convert hq.mul he2 using 1 <;> simp
  have hlinear :
      HasDerivAt (fun e : ℝ => 1 + M.trace * e) M.trace 0 := by
    convert
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        ((hasDerivAt_id (0 : ℝ)).const_mul M.trace) using 1 <;> ring
  have hrhs :
      HasDerivAt
        (fun e : ℝ => 1 + M.trace * e + q.eval e * e ^ 2)
        M.trace 0 := by
    convert hlinear.add hrem using 1 <;> ring
  exact hrhs.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun e => by
      simpa [q] using (Matrix.det_one_add_smul e M))

/-- Proved Jacobi formula for an affine matrix line. -/
theorem detAffine_hasDerivAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A) :
    HasDerivAt
      (fun e : ℝ => (A + e • B).det)
      (A.det * (A⁻¹ * B).trace) 0 := by
  letI : Invertible A := hA
  let C : Matrix n n ℝ := A⁻¹ * B
  have hfactor : ∀ e : ℝ, A + e • B = A * (1 + e • C) := by
    intro e
    simp [C, Matrix.mul_add, Matrix.mul_inv_cancel_left_of_invertible]
  have hdet :
      (fun e : ℝ => (A + e • B).det) =
        (fun e : ℝ => A.det * (1 + e • C).det) := by
    funext e
    rw [hfactor e, Matrix.det_mul]
  rw [hdet]
  simpa [C] using (detOneAddSMul_hasDerivAt C).const_mul A.det

/-- Proved derivative of the reciprocal determinant. -/
theorem invDetAffine_hasDerivAt
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A) :
    HasDerivAt
      (fun e : ℝ => (A + e • B).det⁻¹)
      (-(A.det⁻¹ * (A⁻¹ * B).trace)) 0 := by
  letI : Invertible A := hA
  have hdet_ne : A.det ≠ 0 :=
    isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible A)
  have h :=
    (detAffine_hasDerivAt A B hA).inv (by simpa using hdet_ne)
  have hcoeff :
      -(A.det * (A⁻¹ * B).trace) / A.det ^ 2 =
        -(A.det⁻¹ * (A⁻¹ * B).trace) := by
    field_simp
  simpa [hcoeff] using h

/-- Proved derivative of `sqrt |det(A + εB)⁻¹|` on the negative-determinant
component.  This is the Lorentzian component used below. -/
theorem sqrtAbsInvDetAffine_hasDerivAt_of_det_neg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : Invertible A)
    (hdet_neg : A.det < 0) :
    HasDerivAt
      (fun e : ℝ => Real.sqrt (abs (A + e • B).det⁻¹))
      (-(1 / 2 : ℝ) * Real.sqrt (abs A.det⁻¹) *
        (A⁻¹ * B).trace) 0 := by
  letI : Invertible A := hA
  let tr : ℝ := (A⁻¹ * B).trace
  have hdet_ne : A.det ≠ 0 := ne_of_lt hdet_neg
  have hinv_neg : A.det⁻¹ < 0 := inv_lt_zero.mpr hdet_neg
  have hinv_ne : A.det⁻¹ ≠ 0 := inv_ne_zero hdet_ne
  have hinv :
      HasDerivAt
        (fun e : ℝ => (A + e • B).det⁻¹)
        (-(A.det⁻¹ * tr)) 0 := by
    simpa [tr] using invDetAffine_hasDerivAt A B hA
  have habs :
      HasDerivAt
        (fun e : ℝ => abs (A + e • B).det⁻¹)
        (A.det⁻¹ * tr) 0 := by
    convert
      (hasDerivAt_abs_neg (by simpa using hinv_neg)).comp 0 hinv
      using 1 <;> simp <;> ring
  have hsqrt :=
    habs.sqrt (by simpa using (abs_ne_zero.mpr hinv_ne))
  let s : ℝ := Real.sqrt (abs A.det⁻¹)
  have hs_pos : 0 < s := by
    exact Real.sqrt_pos.2 (abs_pos.mpr hinv_ne)
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = abs A.det⁻¹ := by
    exact Real.sq_sqrt (abs_nonneg A.det⁻¹)
  have hinv_eq : A.det⁻¹ = -(s ^ 2) := by
    rw [hs_sq, abs_of_neg hinv_neg]
    ring
  have hcoeff :
      A.det⁻¹ * tr / (2 * s) = -(1 / 2 : ℝ) * s * tr := by
    rw [div_eq_iff (mul_ne_zero (by norm_num) hs_ne)]
    rw [hinv_eq]
    ring
  convert hsqrt using 1
  simpa only [s, tr, zero_smul, add_zero] using hcoeff.symm

/-! ## Four-dimensional metric specialization -/

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Matrix of inverse-metric components at a point. -/
def inverseMetricMatrixAt
    (g : MetricTensor) (x : Fin 4 → ℝ) : Matrix4 :=
  fun rho sigma =>
    inverse_metric g x
      (fun i => if i = 0 then rho else sigma)
      (fun _ => 0)

theorem inverseMetricMatrixAt_eq
    (g : MetricTensor) (x : Fin 4 → ℝ) :
    inverseMetricMatrixAt g x = (metric_to_matrix g x)⁻¹ :=
  rfl

/-- The Lorentzian component used by the V5 action calculation: a
nondegenerate symmetric metric with negative determinant.  In four
dimensions every metric of signature `(1,3)` lies in this component. -/
def LorentzianVolumeDomain
    (g : MetricTensor) (x : Fin 4 → ℝ) : Prop :=
  metric_matrix_invertible_hypothesis g x ∧ metric_det g x < 0

/-- V4's locally proved inverse identity, lifted entrywise to a matrix
identity.  This is the bridge from the repository's `perturbed_metric` API to
the affine inverse-metric line used by the determinant proof. -/
theorem inverseMetricMatrixAt_perturbed_eventuallyEq_inverseLine
    (g : MetricTensor) (mu nu : Fin 4) (x : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x) :
    (fun e : ℝ => inverseMetricMatrixAt (perturbed_metric g mu nu x e) x)
      =ᶠ[nhds 0]
    (fun e : ℝ =>
      (metric_to_matrix g x)⁻¹ + e • delta_matrix mu nu) := by
  refine
    (Filter.eventually_all.mpr fun rho : Fin 4 =>
      Filter.eventually_all.mpr fun sigma : Fin 4 =>
        inverseMetric_perturbedMetric_eventuallyEq_inverseLine
          g mu nu rho sigma x h_inv).mono ?_
  intro e he
  funext rho sigma
  exact he rho sigma

/-- Taking the determinant inverse of the actual inverse metric recovers the
covariant metric determinant.  Over `ℝ` this remains true even at a singular
matrix because the nonsingular inverse and field inverse both return zero. -/
theorem inverseMetricMatrixAt_det_inv
    (g : MetricTensor) (x : Fin 4 → ℝ) :
    (inverseMetricMatrixAt g x).det⁻¹ = metric_det g x := by
  unfold inverseMetricMatrixAt metric_det inverse_metric
  simp

/-- The repository covariant volume density. -/
def covariantVolumeDensity :
    MetricTensor → (Fin 4 → ℝ) → ℝ :=
  fun g x => Real.sqrt (abs (metric_det g x))

/-- The same density written entirely in inverse-metric coordinates. -/
def inverseMetricVolumeDensity :
    MetricTensor → (Fin 4 → ℝ) → ℝ :=
  fun g x =>
    Real.sqrt (abs (inverseMetricMatrixAt g x).det⁻¹)

theorem inverseMetricVolumeDensity_eq_covariantVolumeDensity
    (g : MetricTensor) (x : Fin 4 → ℝ) :
    inverseMetricVolumeDensity g x = covariantVolumeDensity g x := by
  rw [inverseMetricVolumeDensity, covariantVolumeDensity,
    inverseMetricMatrixAt_det_inv]

/-- The trace contraction with the symmetrized inverse-metric coordinate
variation is exactly the selected covariant metric component. -/
theorem trace_metric_mul_delta
    (g : MetricTensor) (x : Fin 4 → ℝ) (mu nu : Fin 4) :
    ((metric_to_matrix g x) * delta_matrix mu nu).trace =
      metric_to_matrix g x mu nu := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∑ i : Fin 4, ∑ j : Fin 4,
        metric_to_matrix g x i j * delta_matrix mu nu j i)
        =
      ∑ i : Fin 4, ∑ j : Fin 4,
        metric_to_matrix g x i j * delta_matrix mu nu i j := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [symmetric_matrix_apply (delta_matrix_symmetric mu nu) j i]
    _ = metric_to_matrix g x mu nu :=
      sum_delta_matrix_apply_matrix mu nu (metric_to_matrix g x)
        (metric_to_matrix_symmetric g x)

/-- The inverse-metric-coordinate volume path has the standard Lorentzian
variation, proved without either legacy determinant witness. -/
theorem inverseMetricVolumeDensity_hasDerivAt
    (g : MetricTensor) (mu nu : Fin 4) (x : Fin 4 → ℝ)
    (hdom : LorentzianVolumeDomain g x) :
    HasDerivAt
      (fun e : ℝ =>
        inverseMetricVolumeDensity (perturbed_metric g mu nu x e) x)
      (-(1 / 2 : ℝ) * covariantVolumeDensity g x *
        metric_to_matrix g x mu nu) 0 := by
  let G : Matrix4 := metric_to_matrix g x
  let H : Matrix4 := G⁻¹
  let D : Matrix4 := delta_matrix mu nu
  let hG : Invertible G := metric_matrix_invertible g x hdom.1
  letI : Invertible G := hG
  let hH : Invertible H := by
    dsimp [H]
    infer_instance
  have hGunit : IsUnit G.det := Matrix.isUnit_det_of_invertible G
  have hHdet_neg : H.det < 0 := by
    dsimp [H]
    simpa [Matrix.det_nonsing_inv] using (inv_lt_zero.mpr hdom.2)
  have hline :=
    sqrtAbsInvDetAffine_hasDerivAt_of_det_neg H D hH hHdet_neg
  have hpath :
      (fun e : ℝ =>
        inverseMetricVolumeDensity (perturbed_metric g mu nu x e) x)
        =ᶠ[nhds 0]
      (fun e : ℝ => Real.sqrt (abs (H + e • D).det⁻¹)) := by
    have hm :=
      inverseMetricMatrixAt_perturbed_eventuallyEq_inverseLine
        g mu nu x hdom.1
    filter_upwards [hm] with e he
    rw [inverseMetricVolumeDensity, he]
  have hderived := hline.congr_of_eventuallyEq hpath
  have hHinv : H⁻¹ = G := by
    dsimp [H]
    exact Matrix.nonsing_inv_nonsing_inv G hGunit
  have htrace : (H⁻¹ * D).trace = G mu nu := by
    rw [hHinv]
    exact trace_metric_mul_delta g x mu nu
  have hvolume :
      Real.sqrt (abs H.det⁻¹) = covariantVolumeDensity g x := by
    change
      Real.sqrt (abs (inverseMetricMatrixAt g x).det⁻¹) =
        covariantVolumeDensity g x
    exact inverseMetricVolumeDensity_eq_covariantVolumeDensity g x
  rw [htrace, hvolume] at hderived
  exact hderived

/-- The functional derivative of the actual covariant volume element, with
respect to the repository's inverse-metric perturbation, is proved for every
metric in the four-dimensional Lorentzian domain. -/
theorem functionalDeriv_covariantVolumeDensity
    (g : MetricTensor) (mu nu : Fin 4) (x : Fin 4 → ℝ)
    (hdom : LorentzianVolumeDomain g x) :
    functional_deriv covariantVolumeDensity g mu nu x =
      -(1 / 2 : ℝ) * covariantVolumeDensity g x *
        metric_to_matrix g x mu nu := by
  unfold functional_deriv
  have h :=
    inverseMetricVolumeDensity_hasDerivAt g mu nu x hdom
  have heq :
      (fun e : ℝ =>
        covariantVolumeDensity (perturbed_metric g mu nu x e) x) =
      (fun e : ℝ =>
        inverseMetricVolumeDensity (perturbed_metric g mu nu x e) x) := by
    funext e
    exact
      (inverseMetricVolumeDensity_eq_covariantVolumeDensity
        (perturbed_metric g mu nu x e) x).symm
  rw [heq]
  exact h.deriv

end DeterminantVolumeVariation4D
end Pillar3SuccessorV5
end Gravity
end IndisputableMonolith
