import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.PhiForcingDerived

/-!
# Projectors force golden operators

The paper `Golden and Metallic Structures on Hessian Manifolds` uses the
rank-one Hessian tensor of reciprocal cost geometry to construct a normalized
projector `P`.  The theorem needed by the forcing stack is algebraic: once
`P² = P`, the almost-product operator `F = 2P - I` satisfies `F² = I`, and the
golden operator

`G = φ P + (1 - φ)(I - P)`

satisfies `G² = G + I`.

This module proves that projector-to-golden step for endomorphisms over a real
module.  It is deliberately the algebraic core, not a full Hessian-manifold
formalization.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CostProjectorGolden

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A projector endomorphism. -/
def IsProjector (P : Module.End ℝ V) : Prop :=
  P * P = P

/-- The almost-product operator induced by a projector. -/
noncomputable def almostProduct (P : Module.End ℝ V) : Module.End ℝ V :=
  2 • P - 1

/-- The golden operator induced by a projector. -/
noncomputable def goldenOperator (P : Module.End ℝ V) : Module.End ℝ V :=
  Constants.phi • P + (1 - Constants.phi) • (1 - P)

/-- Normalize an operator satisfying `A² = μA` by its trace scalar `μ`. -/
noncomputable def normalizedProjector (μ : ℝ) (A : Module.End ℝ V) : Module.End ℝ V :=
  μ⁻¹ • A

/-- Rank-one endomorphism `x ↦ ℓ(x) v`.  This is the algebraic shape of the
rank-one Hessian projector construction used by the golden-structure route. -/
noncomputable def rankOneEnd (ell : V →ₗ[ℝ] ℝ) (v : V) : Module.End ℝ V where
  toFun := fun x => ell x • v
  map_add' := by
    intro x y
    simp [map_add, add_smul]
  map_smul' := by
    intro a x
    simp [map_smul, smul_smul]

/-- A rank-one endomorphism squares to a scalar multiple of itself:
`A² = ℓ(v) A`. -/
theorem rankOneEnd_square (ell : V →ₗ[ℝ] ℝ) (v : V) :
    rankOneEnd ell v * rankOneEnd ell v = ell v • rankOneEnd ell v := by
  ext x
  simp [rankOneEnd, smul_smul, mul_comm]

/-- The algebraic projector step from the Hessian-geometry paper:
`A² = μA` and `μ ≠ 0` imply `P = μ⁻¹A` is a projector. -/
theorem normalizedProjector_isProjector
    {μ : ℝ} {A : Module.End ℝ V}
    (hA : A * A = μ • A) (hμ : μ ≠ 0) :
    IsProjector (normalizedProjector μ A) := by
  ext v
  have hAv : A (A v) = μ • A v := by
    have h := congrArg (fun Q : Module.End ℝ V => Q v) hA
    simpa using h
  have hscalar : μ⁻¹ * μ⁻¹ * μ = μ⁻¹ := by
    field_simp [hμ]
  simp [normalizedProjector, smul_smul, hAv]
  rw [hscalar]

/-- `P²=P` implies `(2P-I)²=I`, the algebraic almost-product structure. -/
theorem almostProduct_sq {P : Module.End ℝ V} (hP : IsProjector P) :
    almostProduct P * almostProduct P = 1 := by
  ext v
  have hPv : P (P v) = P v := by
    have h := congrArg (fun Q : Module.End ℝ V => Q v) hP
    simpa [IsProjector] using h
  simp [almostProduct, sub_eq_add_neg, hPv]
  module

/-- A projector induces a golden operator: `G² = G + I`. -/
theorem goldenOperator_sq {P : Module.End ℝ V} (hP : IsProjector P) :
    goldenOperator P * goldenOperator P = goldenOperator P + 1 := by
  ext v
  have hPv : P (P v) = P v := by
    have h := congrArg (fun Q : Module.End ℝ V => Q v) hP
    simpa [IsProjector] using h
  have hphi : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq_eq
  have hphi_compl :
      1 - Constants.phi * 2 + Constants.phi ^ 2 = 2 - Constants.phi := by
    rw [hphi]
    ring
  have hphi_mul : Constants.phi * Constants.phi = Constants.phi + 1 := by
    simpa [pow_two] using hphi
  have hphi_compl_mul :
      (1 + -Constants.phi) * (1 + -Constants.phi) = 2 - Constants.phi := by
    nlinarith [hphi_compl]
  simp [goldenOperator, sub_eq_add_neg, map_add, map_smul, smul_smul, hPv]
  rw [hphi_mul, hphi_compl_mul]
  module

/-- Normalizing an operator with `A² = μA` and `μ ≠ 0` gives a golden
operator satisfying `G² = G + I`. -/
theorem normalizedProjector_goldenOperator_sq
    {μ : ℝ} {A : Module.End ℝ V}
    (hA : A * A = μ • A) (hμ : μ ≠ 0) :
    goldenOperator (normalizedProjector μ A) *
      goldenOperator (normalizedProjector μ A) =
        goldenOperator (normalizedProjector μ A) + 1 :=
  goldenOperator_sq (normalizedProjector_isProjector hA hμ)

/-- A nondegenerate rank-one endomorphism normalizes to a projector. -/
theorem rankOneEnd_normalized_isProjector
    (ell : V →ₗ[ℝ] ℝ) (v : V) (hμ : ell v ≠ 0) :
    IsProjector (normalizedProjector (ell v) (rankOneEnd ell v)) :=
  normalizedProjector_isProjector (rankOneEnd_square ell v) hμ

/-- A nondegenerate rank-one endomorphism induces the golden-operator equation
after normalization. -/
theorem rankOneEnd_goldenOperator_sq
    (ell : V →ₗ[ℝ] ℝ) (v : V) (hμ : ell v ≠ 0) :
    goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) *
      goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) =
        goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) + 1 :=
  normalizedProjector_goldenOperator_sq (rankOneEnd_square ell v) hμ

/-- A positive scalar satisfying the golden-operator characteristic equation is
forced to be the RS golden ratio. -/
theorem goldenScalar_forces_phi {lam : ℝ}
    (h_lam_pos : 0 < lam) (h_lam : lam ^ 2 = lam + 1) :
    lam = Constants.phi := by
  have h_lam_ne_one : lam ≠ 1 := by
    intro h1
    rw [h1] at h_lam
    norm_num at h_lam
  have hclosure : 1 + lam = lam ^ 2 := by
    linarith
  exact PhiForcingDerived.phi_forcing_complete lam h_lam_pos h_lam_ne_one hclosure

/-- The algebraic projector package supplied by the cost-induced projector
construction in the Hessian-geometry paper. -/
structure ProjectorGoldenCertificate : Prop where
  almost_product :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (P : Module.End ℝ V),
      IsProjector P → almostProduct P * almostProduct P = 1
  golden_structure :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (P : Module.End ℝ V),
      IsProjector P → goldenOperator P * goldenOperator P = goldenOperator P + 1
  normalized_operator_is_projector :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (μ : ℝ) (A : Module.End ℝ V),
      A * A = μ • A → μ ≠ 0 → IsProjector (normalizedProjector μ A)
  normalized_operator_golden_structure :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (μ : ℝ) (A : Module.End ℝ V),
      A * A = μ • A → μ ≠ 0 →
        goldenOperator (normalizedProjector μ A) *
          goldenOperator (normalizedProjector μ A) =
            goldenOperator (normalizedProjector μ A) + 1
  rank_one_square :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (ell : V →ₗ[ℝ] ℝ) (v : V),
      rankOneEnd ell v * rankOneEnd ell v = ell v • rankOneEnd ell v
  rank_one_normalized_projector :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (ell : V →ₗ[ℝ] ℝ) (v : V),
      ell v ≠ 0 → IsProjector (normalizedProjector (ell v) (rankOneEnd ell v))
  rank_one_golden_structure :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] (ell : V →ₗ[ℝ] ℝ) (v : V),
      ell v ≠ 0 →
        goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) *
          goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) =
            goldenOperator (normalizedProjector (ell v) (rankOneEnd ell v)) + 1
  golden_scalar_forces_phi :
    ∀ {lam : ℝ}, 0 < lam → lam ^ 2 = lam + 1 → lam = Constants.phi

/-- Any cost-induced normalized projector carries the golden-operator equation.
The cost geometry supplies the projector; this theorem supplies the polynomial
structure forced by being a projector. -/
theorem projector_golden_certificate : ProjectorGoldenCertificate where
  almost_product := @almostProduct_sq
  golden_structure := @goldenOperator_sq
  normalized_operator_is_projector := @normalizedProjector_isProjector
  normalized_operator_golden_structure := @normalizedProjector_goldenOperator_sq
  rank_one_square := @rankOneEnd_square
  rank_one_normalized_projector := @rankOneEnd_normalized_isProjector
  rank_one_golden_structure := @rankOneEnd_goldenOperator_sq
  golden_scalar_forces_phi := @goldenScalar_forces_phi

end CostProjectorGolden
end Foundation
end IndisputableMonolith
