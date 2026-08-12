import IndisputableMonolith.Gravity.NullConeQuadraticTensorClass

/-!
# Projective-section null-quadratic class (Phase 5 algebra)

Finite-dimensional real linear algebra on the canonical future projective
null section `k₀ = 1`.  No Recognition imports, no affine-rescaling law,
and no stress ancestry.

Derivation path:

* quadratic contraction is homogeneous of degree 2 in the vector argument;
* agreement of two symmetric matrices on every Minkowski-null covector with
  `k 0 = 1` therefore extends, by projective normalization `k ↦ k / k 0`,
  to every future nonzero null covector, then to the full null cone;
* the symmetric representative `G₀ = diag(-1,0,0,0)` has
  `quadContr G₀ k = -(k 0)²`, hence contraction `-1` on every canonical
  section;
* any symmetric matrix with the same canonical-section values differs from
  `G₀` by a scalar multiple of Minkowski `η`.

Honesty tags:

* THEOREM: vector homogeneity of `quadContr`; the canonical-section-to-cone
  bridge; `G₀` symmetry and section contraction; uniqueness modulo `η` from
  canonical-section agreement.
* This module supplies no Recognition ancestry and does not claim that the
  physical focusing scalar `-1` is forced.  Attaching Recognition cut data
  is the job of a separate MODEL package.  Continuum Ricci, EFE, C-gap1,
  Unruh/KMS, and LocalNullPatch remain untouched.

Forbidden shortcuts: no `sorry`, no new axioms, no physical `stepSq / c²`
premise, no import of the affine-rescaling wall tower, and no claim that
`G₀` is independently forced geometry beyond being the unique class
representative realizing the projective scalar `-1`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace ProjectiveSectionNullQuadraticClass

open ClausiusEinsteinBridge
open NullConeQuadraticTensorClass
open scoped BigOperators

/-! ## Canonical future projective null section -/

/-- Future projective null section with time component normalized to `1`. -/
def CanonicalFutureNullSection (k : Fin 4 → ℝ) : Prop :=
  MinkowskiNull k ∧ k 0 = 1

theorem CanonicalFutureNullSection.minkowskiNull
    {k : Fin 4 → ℝ} (hk : CanonicalFutureNullSection k) :
    MinkowskiNull k :=
  hk.1

theorem CanonicalFutureNullSection.time
    {k : Fin 4 → ℝ} (hk : CanonicalFutureNullSection k) :
    k 0 = 1 :=
  hk.2

theorem CanonicalFutureNullSection.nonzero
    {k : Fin 4 → ℝ} (hk : CanonicalFutureNullSection k) :
    k ≠ 0 := by
  intro hzero
  have ht := hk.2
  simp [hzero] at ht

/-! ## Vector homogeneity of quadratic contraction -/

/-- Quadratic contraction is homogeneous of degree 2 in the covector. -/
theorem quadContr_smul_vector
    (A : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (k : Fin 4 → ℝ) :
    quadContr A (fun i => c * k i) = c ^ 2 * quadContr A k := by
  simp only [quadContr]
  calc
    (∑ i, ∑ j, A i j * (c * k i) * (c * k j))
        = ∑ i, ∑ j, c ^ 2 * (A i j * k i * k j) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, c ^ 2 * ∑ j, A i j * k i * k j := by
          refine Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum _ _ _).symm
    _ = c ^ 2 * ∑ i, ∑ j, A i j * k i * k j :=
      (Finset.mul_sum _ _ _).symm

theorem minkowskiNull_smul
    {k : Fin 4 → ℝ} (hk : MinkowskiNull k) (c : ℝ) :
    MinkowskiNull (fun i => c * k i) := by
  simp only [MinkowskiNull] at hk ⊢
  have :
      -(c * k 0) ^ 2 + (c * k 1) ^ 2 + (c * k 2) ^ 2 + (c * k 3) ^ 2 =
        c ^ 2 * (-(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2) := by
    ring
  simp [this, hk]

/-! ## Projective normalization bridge -/

/--
Normalize a future nonzero null covector to the canonical section
`k / k₀`.
-/
def normalizeToCanonicalSection (k : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => k i / k 0

theorem normalizeToCanonicalSection_time
    (k : Fin 4 → ℝ) (hk0 : k 0 ≠ 0) :
    normalizeToCanonicalSection k 0 = 1 := by
  simp [normalizeToCanonicalSection, div_self hk0]

theorem normalizeToCanonicalSection_minkowskiNull
    (k : Fin 4 → ℝ) (hk : MinkowskiNull k) (_hk0 : k 0 ≠ 0) :
    MinkowskiNull (normalizeToCanonicalSection k) := by
  have hsmul :
      MinkowskiNull (fun i => (k 0)⁻¹ * k i) :=
    minkowskiNull_smul hk (k 0)⁻¹
  convert hsmul using 1
  funext i
  simp [normalizeToCanonicalSection, div_eq_inv_mul]

theorem normalizeToCanonicalSection_canonical
    (k : Fin 4 → ℝ) (hk : MinkowskiNull k) (hk0 : k 0 ≠ 0) :
    CanonicalFutureNullSection (normalizeToCanonicalSection k) :=
  ⟨normalizeToCanonicalSection_minkowskiNull k hk hk0,
    normalizeToCanonicalSection_time k hk0⟩

theorem quadContr_eq_scale_sq_normalize
    (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) (hk0 : k 0 ≠ 0) :
    quadContr A k =
      (k 0) ^ 2 * quadContr A (normalizeToCanonicalSection k) := by
  have hEq :
      quadContr A k =
        quadContr A (fun i => (k 0) * normalizeToCanonicalSection k i) := by
    congr 1
    funext i
    simp [normalizeToCanonicalSection, mul_div_cancel₀ _ hk0]
  rw [hEq, quadContr_smul_vector]

/--
Canonical-section agreement of two matrices extends to every future nonzero
null covector by quadratic homogeneity and projective normalization.  This
bridge is pure algebra; it does not use a physical affine-step law.
-/
theorem future_nonzero_null_quad_eq_of_canonical_section_quad_eq
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hsec :
      ∀ k, CanonicalFutureNullSection k →
        quadContr A k = quadContr B k) :
    ∀ k, MinkowskiNull k → k ≠ 0 → 0 < k 0 →
      quadContr A k = quadContr B k := by
  intro k hk _hkne hk0pos
  have hk0 : k 0 ≠ 0 := ne_of_gt hk0pos
  have hcan := normalizeToCanonicalSection_canonical k hk hk0
  have hsecEq := hsec _ hcan
  rw [quadContr_eq_scale_sq_normalize A k hk0,
    quadContr_eq_scale_sq_normalize B k hk0, hsecEq]

/--
Canonical-section agreement of symmetric matrices determines their difference
as a scalar multiple of Minkowski `η`.
-/
theorem canonical_section_quad_eq_implies_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : Symmetric4 A) (hB : Symmetric4 B)
    (hsec :
      ∀ k, CanonicalFutureNullSection k →
        quadContr A k = quadContr B k) :
    ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j := by
  apply future_null_quadratic_eq_implies_diff_scalar_eta A B hA hB
  exact future_nonzero_null_quad_eq_of_canonical_section_quad_eq A B hsec

/-! ## Symmetric representative `G₀` -/

/-- Geometric class representative `G₀ = diag(-1,0,0,0)`. -/
def geometricG0 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = 0 ∧ j = 0 then (-1 : ℝ) else 0

theorem geometricG0_symmetric : Symmetric4 geometricG0 := by
  intro i j
  simp only [geometricG0]
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · subst hi; subst hj; simp
    · simp [hi, hj]
  · by_cases hj : j = 0
    · simp [hi, hj]
    · simp [hi, hj]

theorem quadContr_geometricG0 (k : Fin 4 → ℝ) :
    quadContr geometricG0 k = -(k 0) ^ 2 := by
  simp only [quadContr, geometricG0]
  have hu : Finset.univ = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  rw [hu]
  simp
  ring

/-- On every canonical future null section, `G₀` contracts to `-1`. -/
theorem quadContr_geometricG0_canonical
    (k : Fin 4 → ℝ) (hk : CanonicalFutureNullSection k) :
    quadContr geometricG0 k = -1 := by
  rw [quadContr_geometricG0, hk.2]
  ring

/-! ## Uniqueness of the class from canonical-section scalar `-1` -/

/--
Any symmetric matrix agreeing with `G₀` on every canonical section differs
from `G₀` by a multiple of `η`.  Stated matrix-to-matrix: no bare scalar is
extended by fiat homogeneity.
-/
theorem geometricG0_unique_mod_eta_of_canonical_section_eq
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : Symmetric4 B)
    (hsec :
      ∀ k, CanonicalFutureNullSection k →
        quadContr geometricG0 k = quadContr B k) :
    ∃ lam : ℝ, ∀ i j, geometricG0 i j - B i j = lam * minkowskiEta4 i j :=
  canonical_section_quad_eq_implies_diff_scalar_eta
    geometricG0 B geometricG0_symmetric hB hsec

/--
Any symmetric matrix with canonical-section contraction `-1` lies in the
null-quadratic class of `G₀`.
-/
theorem geometricG0_unique_mod_eta_of_section_scalar_neg_one
    (B : Matrix (Fin 4) (Fin 4) ℝ) (hB : Symmetric4 B)
    (hsec :
      ∀ k, CanonicalFutureNullSection k → quadContr B k = -1) :
    ∃ lam : ℝ, ∀ i j, geometricG0 i j - B i j = lam * minkowskiEta4 i j := by
  apply geometricG0_unique_mod_eta_of_canonical_section_eq B hB
  intro k hk
  rw [quadContr_geometricG0_canonical k hk, hsec k hk]

/--
`G₀` determines the algebraic null-quadratic class of the constant
projective scalar `-1` on the canonical section (extended to the cone by
the algebraic bridge above, not by a physical rescaling law).
-/
theorem geometricG0_determinesAlgebraicNullQuadraticClass_sectionNegOne :
    DeterminesAlgebraicNullQuadraticClass
      (fun k => -(k 0) ^ 2) geometricG0 := by
  refine ⟨geometricG0_symmetric, ?_, ?_⟩
  · intro k hk
    exact (quadContr_geometricG0 k).symm
  · intro B hB hφ
    have hnull :
        ∀ k, MinkowskiNull k →
          quadContr geometricG0 k = quadContr B k := by
      intro k hk
      rw [quadContr_geometricG0 k]
      exact hφ k hk
    exact null_quadratic_eq_implies_diff_scalar_eta
      geometricG0 B geometricG0_symmetric hB hnull

/-! ## Certificate (all fields substantive) -/

/--
Load-bearing algebraic certificate for the projective-section route.
Every field is a proved Prop.  No vacuous `True` honesty placeholders.
-/
structure ProjectiveSectionNullQuadraticClassCert : Prop where
  vector_homogeneity :
    ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (c : ℝ) (k : Fin 4 → ℝ),
      quadContr A (fun i => c * k i) = c ^ 2 * quadContr A k
  g0_symmetric : Symmetric4 geometricG0
  g0_contraction :
    ∀ k, quadContr geometricG0 k = -(k 0) ^ 2
  g0_canonical_section :
    ∀ k, CanonicalFutureNullSection k → quadContr geometricG0 k = -1
  section_bridge :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ),
      (∀ k, CanonicalFutureNullSection k →
        quadContr A k = quadContr B k) →
      ∀ k, MinkowskiNull k → k ≠ 0 → 0 < k 0 →
        quadContr A k = quadContr B k
  section_uniqueness :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ),
      Symmetric4 A → Symmetric4 B →
      (∀ k, CanonicalFutureNullSection k →
        quadContr A k = quadContr B k) →
        ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j
  g0_class_from_section_neg_one :
    ∀ (B : Matrix (Fin 4) (Fin 4) ℝ),
      Symmetric4 B →
      (∀ k, CanonicalFutureNullSection k → quadContr B k = -1) →
        ∃ lam : ℝ, ∀ i j, geometricG0 i j - B i j = lam * minkowskiEta4 i j

theorem projectiveSectionNullQuadraticClassCert :
    ProjectiveSectionNullQuadraticClassCert where
  vector_homogeneity := quadContr_smul_vector
  g0_symmetric := geometricG0_symmetric
  g0_contraction := quadContr_geometricG0
  g0_canonical_section := quadContr_geometricG0_canonical
  section_bridge :=
    future_nonzero_null_quad_eq_of_canonical_section_quad_eq
  section_uniqueness :=
    canonical_section_quad_eq_implies_diff_scalar_eta
  g0_class_from_section_neg_one :=
    geometricG0_unique_mod_eta_of_section_scalar_neg_one

end ProjectiveSectionNullQuadraticClass
end Gravity
end IndisputableMonolith
