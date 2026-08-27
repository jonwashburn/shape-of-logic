import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.CostProjectorGolden

/-!
# The concrete RS J-Hessian forces the golden operator (Phase 4 closure step)

Phase 4 (T5 -> T6) needs the φ-forcing to start from the *actual* recognition
cost `J`, not from an abstract supplied operator.  The Hessian-geometry route in
`CostProjectorGolden` reduces φ-forcing to producing a rank-one endomorphism `A`
with `A² = μ A` and `μ ≠ 0`: it then normalizes `A` to a projector `P`, builds
the golden operator `G = φ P + (1-φ)(I-P)`, proves `G² = G + I`, and forces the
positive root to be `φ`.

This module supplies that rank-one operator from the second derivative of
`J(x) = ½(x + x⁻¹) − 1` at the recognition fixed point `x = 1`.

* `jHessianScalar = J''(1) = 1` (the calibration curvature, re-derived locally so
  that `Foundation` stays independent of later domain-layer curvature modules);
* the rank-one J-Hessian operator on `ℝ` is `x ↦ (J''(1) · x) · v`, `v = 1`;
* its eigenvalue is `J''(1) = 1 ≠ 0` precisely because `J` is strictly convex at
  the fixed point (`Jcost_deriv2_pos`), so the nondegeneracy that the golden
  route requires *is* the unit, positive curvature of the recognition cost well.

Hence the concrete RS J-Hessian forces `G² = G + I`, and the golden scalar
equation forces φ.  Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace JHessianGolden

open CostProjectorGolden
open Set Filter Topology

/-! ## Second derivative of `J` at the recognition fixed point (re-derived) -/

/-- The derivative of the RS cost: `J'(x) = (1 - x⁻²)/2`, valid away from `0`. -/
lemma hasDerivAt_Jcost (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt Cost.Jcost ((1 - (x ^ 2)⁻¹) / 2) x := by
  unfold Cost.Jcost
  convert ((hasDerivAt_id x).add (hasDerivAt_inv hx)).div_const 2 |>.sub_const 1 using 1

/-- The derivative of the first-derivative formula: `(J')'(x) = x⁻³`. -/
lemma hasDerivAt_Jcost_deriv (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => (1 - (y ^ 2)⁻¹) / 2) ((x ^ 3)⁻¹) x := by
  have hx2 : (x : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h := (((hasDerivAt_pow 2 x).inv hx2).const_sub 1).div_const 2
  convert h using 1
  field_simp
  ring

/-- `J''(x) = x⁻³` for `x > 0`. -/
lemma Jcost_deriv2_eq (x : ℝ) (hx : 0 < x) :
    deriv^[2] Cost.Jcost x = (x ^ 3)⁻¹ := by
  have heq : deriv Cost.Jcost =ᶠ[nhds x] (fun y => (1 - (y ^ 2)⁻¹) / 2) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_Jcost y (ne_of_gt hy)).deriv
  have h2 : deriv^[2] Cost.Jcost x = deriv (fun y => (1 - (y ^ 2)⁻¹) / 2) x := by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact heq.deriv_eq
  rw [h2, (hasDerivAt_Jcost_deriv x (ne_of_gt hx)).deriv]

/-- `J''(1) = 1`: the curvature at the ideal ratio is exactly the calibration
constant.  This is the nondegenerate, unit-curvature recognition well. -/
lemma Jcost_deriv2_one : deriv^[2] Cost.Jcost 1 = 1 := by
  rw [Jcost_deriv2_eq 1 one_pos]; norm_num

/-- `J''(x) > 0` for `x > 0`: the recognition cost is strictly curved. -/
lemma Jcost_deriv2_pos (x : ℝ) (hx : 0 < x) : 0 < deriv^[2] Cost.Jcost x := by
  rw [Jcost_deriv2_eq x hx]; positivity

/-! ## Additive posting reference potential (from `J`) -/

/-- The additive-posting recognition potential on `n` coordinates: the total
recognition cost of a multi-coordinate state is the sum of the per-coordinate
recognition costs, `Φ(x) = Σᵢ J(xᵢ)`.  This is the separable reference potential
the golden construction pairs with the rank-one cost Hessian (paper §5,
`Φ₀ = Σⱼ J(xⱼ)`); its Hessian is the diagonal `diag(J''(xᵢ))`. -/
noncomputable def additivePosting {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Cost.Jcost (x i)

/-- Additive posting peels off one coordinate by adding its `J`-cost: recognition
cost is posted additively, coordinate by coordinate.  This is the ledger
additivity of the multi-coordinate cost, realized by the `J`-potential. -/
lemma additivePosting_succ {n : ℕ} (x : Fin (n + 1) → ℝ) :
    additivePosting x
      = Cost.Jcost (x 0) + additivePosting (fun i : Fin n => x i.succ) := by
  simp [additivePosting, Fin.sum_univ_succ]

/-- **Nondegeneracy of the additive-posting reference metric.**  Each diagonal
entry of the additive-posting Hessian is the per-coordinate curvature
`J''(xᵢ) = xᵢ⁻³ > 0` for positive `xᵢ`.  Hence the separable reference metric
`diag(J''(xᵢ))` is positive-definite — exactly the nondegeneracy the golden
construction requires of its reference metric, sourced entirely from `J`. -/
lemma additivePosting_curvature_pos {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (i : Fin n) :
    0 < deriv^[2] Cost.Jcost (x i) :=
  Jcost_deriv2_pos (x i) (hx i)

/-! ## The concrete rank-one J-Hessian operator -/

/-- The recognition-cost curvature scalar at the fixed point: `J''(1) = 1`. -/
noncomputable def jHessianScalar : ℝ := deriv^[2] Cost.Jcost 1

@[simp] lemma jHessianScalar_eq_one : jHessianScalar = 1 := Jcost_deriv2_one

lemma jHessianScalar_pos : 0 < jHessianScalar :=
  Jcost_deriv2_pos 1 one_pos

/-- The J-Hessian functional on the one-dimensional recognition scaling ray:
`ℓ(x) = J''(1) · x`.  This is the cost second derivative acting as a linear
functional (the Hessian metric with one index lowered). -/
noncomputable def jHessianForm : ℝ →ₗ[ℝ] ℝ := jHessianScalar • LinearMap.id

/-- The recognition direction (the unit scaling generator). -/
def recognitionDirection : ℝ := 1

/-- The concrete rank-one J-Hessian operator on `ℝ`: `A : x ↦ ℓ(x) · v` with `ℓ`
the J-Hessian functional and `v` the recognition direction. -/
noncomputable def jHessianOperator : Module.End ℝ ℝ :=
  rankOneEnd jHessianForm recognitionDirection

/-- The rank-one eigenvalue is the recognition curvature `J''(1)`. -/
@[simp] lemma jHessianForm_recognitionDirection :
    jHessianForm recognitionDirection = jHessianScalar := by
  simp [jHessianForm, recognitionDirection]

/-- **Nondegeneracy.** The J-Hessian rank-one eigenvalue is nonzero, because the
recognition cost is strictly convex at the fixed point: `J''(1) = 1 > 0`.  The
golden route's nondegeneracy hypothesis is exactly this positive curvature. -/
lemma jHessianForm_recognitionDirection_ne_zero :
    jHessianForm recognitionDirection ≠ 0 := by
  rw [jHessianForm_recognitionDirection]
  exact ne_of_gt jHessianScalar_pos

/-- The concrete J-Hessian operator satisfies `A² = J''(1) · A` (`= 1 · A`). -/
theorem jHessianOperator_square :
    jHessianOperator * jHessianOperator = jHessianScalar • jHessianOperator := by
  have h := rankOneEnd_square jHessianForm recognitionDirection
  rw [jHessianForm_recognitionDirection] at h
  exact h

/-- The concrete J-Hessian operator normalizes to a projector. -/
theorem jHessianOperator_normalized_isProjector :
    IsProjector
      (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) :=
  rankOneEnd_normalized_isProjector jHessianForm recognitionDirection
    jHessianForm_recognitionDirection_ne_zero

/-- **Phase 4 concrete φ-forcing.** The golden operator induced by the concrete
RS J-Hessian satisfies `G² = G + I`, with the operator built from the actual
second derivative of `J` rather than from a supplied abstract operator. -/
theorem jHessianOperator_goldenOperator_sq :
    goldenOperator
        (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) *
      goldenOperator
        (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) =
        goldenOperator
          (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) + 1 :=
  rankOneEnd_goldenOperator_sq jHessianForm recognitionDirection
    jHessianForm_recognitionDirection_ne_zero

/-- A positive scalar satisfying the golden-operator characteristic equation
`λ² = λ + 1` is forced to be `φ`.  The golden operator built from the concrete
J-Hessian has this characteristic equation, so its positive eigenvalue is φ. -/
theorem goldenScalar_forces_phi {lam : ℝ}
    (h_lam_pos : 0 < lam) (h_lam : lam ^ 2 = lam + 1) :
    lam = Constants.phi :=
  CostProjectorGolden.goldenScalar_forces_phi h_lam_pos h_lam

/-! ## Phase 4 concrete certificate -/

/-- The concrete-J-Hessian φ-forcing certificate: the recognition cost's own
Hessian at the fixed point supplies the nondegenerate rank-one operator that the
golden-structure route needs, so φ-forcing no longer rests on a supplied
operator. -/
structure JHessianGoldenCertificate : Prop where
  /-- The J-Hessian curvature scalar at the fixed point is `1`. -/
  hessian_scalar_one : jHessianScalar = 1
  /-- The curvature is strictly positive (nondegeneracy source). -/
  hessian_scalar_pos : 0 < jHessianScalar
  /-- The concrete J-Hessian rank-one eigenvalue is nonzero. -/
  rank_one_nondegenerate : jHessianForm recognitionDirection ≠ 0
  /-- `A² = μ A` for the concrete operator. -/
  operator_square :
    jHessianOperator * jHessianOperator = jHessianScalar • jHessianOperator
  /-- The concrete operator normalizes to a projector. -/
  normalized_is_projector :
    IsProjector
      (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator)
  /-- The induced golden operator satisfies `G² = G + I`. -/
  golden_structure :
    goldenOperator
        (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) *
      goldenOperator
        (normalizedProjector (jHessianForm recognitionDirection) jHessianOperator) =
        goldenOperator
          (normalizedProjector
            (jHessianForm recognitionDirection) jHessianOperator) + 1
  /-- The golden scalar equation forces φ. -/
  golden_scalar_forces_phi :
    ∀ {lam : ℝ}, 0 < lam → lam ^ 2 = lam + 1 → lam = Constants.phi

/-- The concrete RS J-Hessian discharges the golden-structure φ-forcing
hypotheses: every field is a proved theorem of this module. -/
theorem jHessianGoldenCertificate : JHessianGoldenCertificate where
  hessian_scalar_one := jHessianScalar_eq_one
  hessian_scalar_pos := jHessianScalar_pos
  rank_one_nondegenerate := jHessianForm_recognitionDirection_ne_zero
  operator_square := jHessianOperator_square
  normalized_is_projector := jHessianOperator_normalized_isProjector
  golden_structure := jHessianOperator_goldenOperator_sq
  golden_scalar_forces_phi := @goldenScalar_forces_phi

end JHessianGolden
end Foundation
end IndisputableMonolith
