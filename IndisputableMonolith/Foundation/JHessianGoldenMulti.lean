import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.CostProjectorGolden

/-!
# The multi-coordinate J-Hessian forces the golden operator (Phase 4 closure)

`JHessianGolden` closed the Phase 4 φ-forcing for the one-dimensional recognition
scaling ray.  This module extends it to the genuine multi-coordinate recognition
cost manifold, following Washburn-Zlatanović, *Golden and Metallic Structures on
Hessian Manifolds* (arXiv:2606.02150).

The `n`-dimensional reciprocal cost is

  `J(x₁,…,xₙ) = ½(R + R⁻¹) − 1`,   `R = ∏ xᵢ^αᵢ`,   `α ∈ ℝⁿ \ {0}`,

which in logarithmic coordinates `tᵢ = log xᵢ` is `J(t) = cosh(α·t) − 1`.  Its
Hessian is the rank-one tensor (paper, §2.1 and §6)

  `∇²J = cosh(α·t) · (α ⊗ α)`,

positive semidefinite of rank one *in every dimension*.  Pairing the rank-one
tensor with the nondegenerate reference Hessian metric `h₀ = ∇²(Σⱼ J(xⱼ))`
(equivalently, on the inner-product model, with the identity metric) gives the
`(1,1)`-tensor `A = h₀⁻¹ ∇²J`, which by the paper's Lemma 3.1 satisfies

  `A² = μ A`,   `μ = cosh(α·t) · ‖α‖² = tr A`,

so `A` normalizes to a projector `P = A/μ` (Corollary 3.1), and the induced
golden operator `G = φP + (1−φ)(I−P)` satisfies `G² = G + I` (§4), forcing the
positive eigenvalue to be `φ`.

The decisive point for Phase 4 is the **nondegeneracy source**: the eigenvalue
`μ = cosh(α·t)·‖α‖²` is strictly positive precisely because `cosh > 0` (strict
convexity of the recognition well in the comparison direction) and `α ≠ 0` (a
genuine recognition comparison exists).  This is the multi-coordinate version of
the unit positive curvature `J''(1) = 1` used in `JHessianGolden`, and it holds
in arbitrary finite or infinite dimension because the construction is carried out
over an arbitrary real inner-product space.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace JHessianGoldenMulti

open CostProjectorGolden

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The inner-product comparison functional -/

/-- The comparison one-form `ω(X) = ⟪α, X⟫` of the recognition cost, as a real
linear functional.  On the inner-product model this is the metric dual of the
distinguished comparison direction `α` (paper: `ω = Σ αᵢ dxᵢ/xᵢ`, `V = h⁻¹ω`). -/
noncomputable def innerForm (α : V) : V →ₗ[ℝ] ℝ where
  toFun := fun x => inner ℝ α x
  map_add' := by intro x y; simp only [inner_add_right]
  map_smul' := by
    intro a x
    simp only [RingHom.id_apply, smul_eq_mul, real_inner_smul_right]

@[simp] lemma innerForm_apply (α x : V) : innerForm α x = inner ℝ α x := rfl

/-! ## The cost-Hessian curvature scalar and rank-one operator -/

/-- The recognition-cost curvature scalar along the comparison direction:
`cosh(α·t)`.  This is the (rank-one) Hessian eigenvalue density of
`J(t) = cosh(α·t) − 1` at the log-coordinate point `t`. -/
noncomputable def costHessianScalar (α t : V) : ℝ := Real.cosh (inner ℝ α t)

/-- The recognition well is strictly curved in every comparison direction:
`cosh(α·t) > 0`.  This is the multi-coordinate strict convexity that supplies
the golden route's nondegeneracy. -/
lemma costHessianScalar_pos (α t : V) : 0 < costHessianScalar α t :=
  Real.cosh_pos _

/-- The cost-Hessian functional `ℓ(X) = cosh(α·t) · ⟪α, X⟫`, i.e. the rank-one
Hessian tensor `cosh(α·t) (α ⊗ α)` with one index lowered. -/
noncomputable def costHessianForm (α t : V) : V →ₗ[ℝ] ℝ :=
  (costHessianScalar α t) • innerForm α

@[simp] lemma costHessianForm_apply (α t x : V) :
    costHessianForm α t x = costHessianScalar α t * inner ℝ α x := by
  simp [costHessianForm, LinearMap.smul_apply, smul_eq_mul]

/-- The multi-coordinate cost-Hessian rank-one operator
`A X = cosh(α·t) · ⟪α, X⟫ · α` (paper eq. (6.3) with reference metric the
identity). -/
noncomputable def costHessianOperator (α t : V) : Module.End ℝ V :=
  rankOneEnd (costHessianForm α t) α

/-- The rank-one eigenvalue is `μ = cosh(α·t) · ⟪α, α⟫ = cosh(α·t) · ‖α‖²`
(paper: `μ = g(V,V) = tr A`). -/
lemma costHessianForm_self (α t : V) :
    costHessianForm α t α = costHessianScalar α t * inner ℝ α α := by
  simp [costHessianForm_apply]

/-- **Nondegeneracy of the multi-coordinate J-Hessian.**  For a genuine
comparison direction `α ≠ 0`, the eigenvalue `μ = cosh(α·t)·‖α‖²` is strictly
positive: `cosh > 0` and `⟪α, α⟫ > 0`.  This is the exact multi-coordinate
analogue of `J''(1) = 1 > 0`. -/
lemma costHessianForm_self_pos (α t : V) (hα : α ≠ 0) :
    0 < costHessianForm α t α := by
  rw [costHessianForm_self]
  have hself : 0 < (inner ℝ α α : ℝ) := by
    have hne : (inner ℝ α α : ℝ) ≠ 0 := fun h => hα (inner_self_eq_zero.mp h)
    exact lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hne)
  exact mul_pos (costHessianScalar_pos α t) hself

/-- The eigenvalue is nonzero for a genuine comparison direction. -/
lemma costHessianForm_self_ne_zero (α t : V) (hα : α ≠ 0) :
    costHessianForm α t α ≠ 0 :=
  ne_of_gt (costHessianForm_self_pos α t hα)

/-! ## The golden structure forced by the multi-coordinate J-Hessian -/

/-- The multi-coordinate cost-Hessian operator satisfies `A² = μ A`
(paper Lemma 3.1). -/
theorem costHessianOperator_square (α t : V) :
    costHessianOperator α t * costHessianOperator α t
      = costHessianForm α t α • costHessianOperator α t :=
  rankOneEnd_square (costHessianForm α t) α

/-- The multi-coordinate cost-Hessian operator normalizes to a projector
(paper Corollary 3.1). -/
theorem costHessianOperator_normalized_isProjector (α t : V) (hα : α ≠ 0) :
    IsProjector
      (normalizedProjector (costHessianForm α t α) (costHessianOperator α t)) :=
  rankOneEnd_normalized_isProjector (costHessianForm α t) α
    (costHessianForm_self_ne_zero α t hα)

/-- **Multi-coordinate Phase 4 φ-forcing.**  The golden operator induced by the
`n`-dimensional recognition cost's Hessian satisfies `G² = G + I` (paper §4,
eq. (6.7)), for an arbitrary comparison direction `α ≠ 0` at an arbitrary
log-coordinate point `t`, over an arbitrary real inner-product space. -/
theorem costHessianOperator_goldenOperator_sq (α t : V) (hα : α ≠ 0) :
    goldenOperator
        (normalizedProjector (costHessianForm α t α) (costHessianOperator α t)) *
      goldenOperator
        (normalizedProjector (costHessianForm α t α) (costHessianOperator α t)) =
        goldenOperator
          (normalizedProjector (costHessianForm α t α)
            (costHessianOperator α t)) + 1 :=
  rankOneEnd_goldenOperator_sq (costHessianForm α t) α
    (costHessianForm_self_ne_zero α t hα)

/-- The golden scalar equation forces `φ` (re-exported). -/
theorem goldenScalar_forces_phi {lam : ℝ}
    (h_lam_pos : 0 < lam) (h_lam : lam ^ 2 = lam + 1) :
    lam = Constants.phi :=
  CostProjectorGolden.goldenScalar_forces_phi h_lam_pos h_lam

/-! ## Multi-coordinate certificate -/

/-- The multi-coordinate concrete-J-Hessian φ-forcing certificate: the
`n`-dimensional recognition cost's own Hessian supplies the nondegenerate
rank-one operator the golden route needs, in arbitrary dimension, so φ-forcing
no longer rests on either a supplied operator or a single-coordinate
restriction. -/
structure JHessianGoldenMultiCertificate
    (α t : V) (hα : α ≠ 0) : Prop where
  /-- The curvature scalar `cosh(α·t)` is strictly positive. -/
  curvature_pos : 0 < costHessianScalar α t
  /-- The rank-one eigenvalue `μ = cosh(α·t)·⟪α,α⟫` is strictly positive. -/
  eigenvalue_pos : 0 < costHessianForm α t α
  /-- `A² = μ A` for the concrete multi-coordinate operator. -/
  operator_square :
    costHessianOperator α t * costHessianOperator α t
      = costHessianForm α t α • costHessianOperator α t
  /-- The operator normalizes to a projector. -/
  normalized_is_projector :
    IsProjector
      (normalizedProjector (costHessianForm α t α) (costHessianOperator α t))
  /-- The induced golden operator satisfies `G² = G + I`. -/
  golden_structure :
    goldenOperator
        (normalizedProjector (costHessianForm α t α) (costHessianOperator α t)) *
      goldenOperator
        (normalizedProjector (costHessianForm α t α) (costHessianOperator α t)) =
        goldenOperator
          (normalizedProjector (costHessianForm α t α)
            (costHessianOperator α t)) + 1
  /-- The golden scalar equation forces `φ`. -/
  golden_scalar_forces_phi :
    ∀ {lam : ℝ}, 0 < lam → lam ^ 2 = lam + 1 → lam = Constants.phi

/-- The multi-coordinate concrete RS J-Hessian discharges the golden-structure
φ-forcing hypotheses in arbitrary dimension. -/
theorem jHessianGoldenMultiCertificate (α t : V) (hα : α ≠ 0) :
    JHessianGoldenMultiCertificate α t hα where
  curvature_pos := costHessianScalar_pos α t
  eigenvalue_pos := costHessianForm_self_pos α t hα
  operator_square := costHessianOperator_square α t
  normalized_is_projector := costHessianOperator_normalized_isProjector α t hα
  golden_structure := costHessianOperator_goldenOperator_sq α t hα
  golden_scalar_forces_phi := @goldenScalar_forces_phi

end JHessianGoldenMulti
end Foundation
end IndisputableMonolith
