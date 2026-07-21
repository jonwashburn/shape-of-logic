import IndisputableMonolith.Gravity.ClausiusEinsteinBridge

/-!
# Null-cone quadratic tensor class (Phase 5 algebraic prerequisite)

Finite-dimensional real linear algebra: the values of a symmetric quadratic
form on all Minkowski-null covectors determine the symmetric matrix modulo a
scalar multiple of the Minkowski metric `η = diag(-1,1,1,1)`.

This is a rigidity package and algebraic prerequisite for Phase 5.  It is not
the independently geometric tensor `G` required by that phase.  Tier A remains
OPEN until a symmetric `G` is constructed from Recognition area/focusing
ancestry independently of the fixed stress tensor.  This module does **not**
identify a matrix with Ricci or stress-energy, construct horizons or Unruh
temperature, or close the Einstein field equation.

Honesty tags:

* THEOREM: null-cone reconstruction of symmetric matrices modulo `η`;
  converse; antisymmetry is invisible to `quadContr`; the general class is
  symmetrization modulo `η`; every fixed symmetric stress scalar map
  instantiates an algebraic null-quadratic class (including
  `witnessFixedStress` once its
  `Symmetric4` fact from `HorizonIndexedRecordFlux` is supplied).
* OPEN: an independently constructed symmetric `G` with Recognition
  area/focusing ancestry; geometric curvature; continuum Ricci; C-gap1; EFE.

Forbidden shortcuts: no `sorry`, no new axioms, no renaming finite responses
into Ricci/stress, no `G := T`, no use of a shared MODEL chart as geometric
ancestry, and no claim that Phase 5 or EFE is closed.

Dependency note: this module imports only `ClausiusEinsteinBridge`.  It does
not pull `HorizonIndexedRecordFlux`, so the witness matrix itself is not
re-imported here; the fixed-stress instantiation is stated for every
symmetric `T` with the same scalar map shape as `fixedStressFlux`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace NullConeQuadraticTensorClass

open ClausiusEinsteinBridge
open scoped BigOperators

/-! ## Symmetrization -/

/-- Componentwise symmetrization of a real 4×4 matrix. -/
def symmetrize4 (A : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (A i j + A j i) / 2

theorem symmetrize4_symmetric (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Symmetric4 (symmetrize4 A) := by
  intro i j
  unfold symmetrize4
  ring

theorem symmetrize4_of_symmetric
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Symmetric4 A) :
    symmetrize4 A = A := by
  ext i j
  unfold symmetrize4
  have := hA i j
  linarith

/-- Antisymmetric part relative to the transpose. -/
def antisymmetrize4 (A : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (A i j - A j i) / 2

private lemma sum_fin_four {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  have hu : Finset.univ = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  rw [hu]
  simp
  abel

/-- Quadratic contraction sees only the symmetric part. -/
theorem quadContr_eq_quadContr_symmetrize4
    (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quadContr A k = quadContr (symmetrize4 A) k := by
  simp only [quadContr, symmetrize4, sum_fin_four]
  ring

theorem quadContr_antisymmetrize4_eq_zero
    (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quadContr (antisymmetrize4 A) k = 0 := by
  have hA :
      A = symmetrize4 A + antisymmetrize4 A := by
    ext i j
    simp only [symmetrize4, antisymmetrize4, Matrix.add_apply]
    ring
  have hadd :
      quadContr A k =
        quadContr (symmetrize4 A) k + quadContr (antisymmetrize4 A) k := by
    have hcongr := congrArg (fun M => quadContr M k) hA
    change quadContr A k =
      quadContr (symmetrize4 A + antisymmetrize4 A) k at hcongr
    have hsum :
        quadContr (symmetrize4 A + antisymmetrize4 A) k =
          quadContr (symmetrize4 A) k +
            quadContr (antisymmetrize4 A) k := by
      simp only [quadContr, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    exact hcongr.trans hsum
  linarith [quadContr_eq_quadContr_symmetrize4 A k, hadd]

/-! ## Future nonzero null data determines all null data -/

/-- Quadratic contraction is even in its vector argument. -/
theorem quadContr_neg
    (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quadContr A (-k) = quadContr A k := by
  unfold quadContr
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply]
  ring

/--
Agreement on every future nonzero Minkowski-null vector extends to the whole
null cone.  Negative-time vectors are handled by quadratic evenness.  A null
vector with zero time component is the zero vector.
-/
theorem all_null_quad_eq_of_future_nonzero_null_quad_eq
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hfuture :
      ∀ k, MinkowskiNull k → k ≠ 0 → 0 < k 0 →
        quadContr A k = quadContr B k) :
    ∀ k, MinkowskiNull k → quadContr A k = quadContr B k := by
  intro k hk
  by_cases hzero : k = 0
  · subst k
    simp [quadContr]
  have htime : k 0 ≠ 0 := by
    intro hk0
    have hkEq := hk
    unfold MinkowskiNull at hkEq
    norm_num [hk0] at hkEq
    have h1 : k 1 = 0 := by
      nlinarith [sq_nonneg (k 1), sq_nonneg (k 2), sq_nonneg (k 3)]
    have h2 : k 2 = 0 := by
      nlinarith [sq_nonneg (k 1), sq_nonneg (k 2), sq_nonneg (k 3)]
    have h3 : k 3 = 0 := by
      nlinarith [sq_nonneg (k 1), sq_nonneg (k 2), sq_nonneg (k 3)]
    apply hzero
    funext i
    fin_cases i
    · exact hk0
    · exact h1
    · exact h2
    · exact h3
  rcases lt_or_gt_of_ne htime with hneg | hpos
  · have hkneg : MinkowskiNull (-k) := by
      simpa [MinkowskiNull] using hk
    have hnegzero : (-k) ≠ 0 := neg_ne_zero.mpr hzero
    have hfutureNeg :=
      hfuture (-k) hkneg hnegzero (by simpa using neg_pos.mpr hneg)
    simpa only [quadContr_neg] using hfutureNeg
  · exact hfuture k hk hzero hpos

/-! ## Metric term on the null cone -/

theorem quadContr_smul
    (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) :
    quadContr (c • A) k = c * quadContr A k := by
  unfold quadContr
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, c * A i j * k i * k j)
        = ∑ i, ∑ j, c * (A i j * k i * k j) := by
          refine Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, c * ∑ j, A i j * k i * k j := by
          refine Finset.sum_congr rfl fun i _ =>
            (Finset.mul_sum _ _ _).symm
    _ = c * ∑ i, ∑ j, A i j * k i * k j :=
      (Finset.mul_sum _ _ _).symm

theorem quadContr_smul_eta
    (lam : ℝ) (k : Fin 4 → ℝ) :
    quadContr (lam • minkowskiEta4) k =
      lam * (-(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2) := by
  rw [quadContr_smul, quadContr_minkowskiEta4]

theorem quadContr_smul_eta_of_null
    (lam : ℝ) (k : Fin 4 → ℝ) (hk : MinkowskiNull k) :
    quadContr (lam • minkowskiEta4) k = 0 := by
  rw [quadContr_smul_eta]
  have hk' :
      -(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2 = 0 := by
    simpa [MinkowskiNull] using hk
  simp [hk']

/-! ## Core reconstruction (componentwise form) -/

/--
If a symmetric matrix has vanishing null-cone quadratic form, it is a scalar
multiple of `η`, stated componentwise.
-/
theorem symmetric_null_zero_eq_scalar_eta_components
    (D : Matrix (Fin 4) (Fin 4) ℝ)
    (hD : Symmetric4 D)
    (hnull : ∀ k, MinkowskiNull k → quadContr D k = 0) :
    ∃ lam : ℝ, ∀ i j, D i j = lam * minkowskiEta4 i j := by
  obtain ⟨lam, hlam⟩ := null_quadratic_zero_eq_scalar_eta D hD hnull
  refine ⟨lam, ?_⟩
  intro i j
  have hij := congrFun (congrFun hlam i) j
  simpa [Matrix.smul_apply, smul_eq_mul] using hij

/--
Null-cone agreement of two symmetric quadratic forms determines their
difference as a scalar multiple of the Minkowski metric.
-/
theorem null_quadratic_eq_implies_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : Symmetric4 A)
    (hB : Symmetric4 B)
    (hnull : ∀ k, MinkowskiNull k → quadContr A k = quadContr B k) :
    ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j := by
  obtain ⟨lam, hlam⟩ := null_quadratic_eq_of_diff_scalar_eta A B hA hB hnull
  refine ⟨lam, ?_⟩
  intro i j
  have hij := congrFun (congrFun hlam i) j
  -- `A = B + lam • η` at `(i,j)`.
  change A i j = B i j + (lam • minkowskiEta4) i j at hij
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  linarith

/--
Future nonzero null agreement is sufficient for the symmetric rigidity
conclusion.  This is the algebraic handoff from future-section data; it does
not supply the independently constructed `G` required by Phase 5.
-/
theorem future_null_quadratic_eq_implies_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : Symmetric4 A)
    (hB : Symmetric4 B)
    (hfuture :
      ∀ k, MinkowskiNull k → k ≠ 0 → 0 < k 0 →
        quadContr A k = quadContr B k) :
    ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j := by
  apply null_quadratic_eq_implies_diff_scalar_eta A B hA hB
  exact all_null_quad_eq_of_future_nonzero_null_quad_eq A B hfuture

/-- Converse: a pure metric difference is invisible on the null cone. -/
theorem diff_scalar_eta_implies_null_quadratic_eq
    (A B : Matrix (Fin 4) (Fin 4) ℝ) (lam : ℝ)
    (hlam : ∀ i j, A i j - B i j = lam * minkowskiEta4 i j) :
    ∀ k, MinkowskiNull k → quadContr A k = quadContr B k := by
  intro k hk
  have hAB : A = B + lam • minkowskiEta4 := by
    ext i j
    have hij := hlam i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  have hcontr := congrArg (fun M => quadContr M k) hAB
  change quadContr A k = quadContr (B + lam • minkowskiEta4) k at hcontr
  have hadd :
      quadContr (B + lam • minkowskiEta4) k =
        quadContr B k + quadContr (lam • minkowskiEta4) k := by
    simp only [quadContr, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hadd, quadContr_smul_eta_of_null lam k hk, add_zero] at hcontr
  exact hcontr

/-- Biconditional for symmetric matrices. -/
theorem null_quadratic_eq_iff_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : Symmetric4 A)
    (hB : Symmetric4 B) :
    (∀ k, MinkowskiNull k → quadContr A k = quadContr B k) ↔
      ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j := by
  constructor
  · exact null_quadratic_eq_implies_diff_scalar_eta A B hA hB
  · intro h
    obtain ⟨lam, hlam⟩ := h
    exact diff_scalar_eta_implies_null_quadratic_eq A B lam hlam

/-! ## General (not necessarily symmetric) matrices -/

/--
For general matrices, null-cone quadratic data determines the symmetrization
modulo `η`.  Antisymmetric parts are invisible.
-/
theorem null_quadratic_eq_iff_symmetrize_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ k, MinkowskiNull k → quadContr A k = quadContr B k) ↔
      ∃ lam : ℝ, ∀ i j,
        symmetrize4 A i j - symmetrize4 B i j = lam * minkowskiEta4 i j := by
  constructor
  · intro hnull
    have hsym :
        ∀ k, MinkowskiNull k →
          quadContr (symmetrize4 A) k = quadContr (symmetrize4 B) k := by
      intro k hk
      rw [← quadContr_eq_quadContr_symmetrize4 A k,
        ← quadContr_eq_quadContr_symmetrize4 B k]
      exact hnull k hk
    exact null_quadratic_eq_implies_diff_scalar_eta
      (symmetrize4 A) (symmetrize4 B)
      (symmetrize4_symmetric A) (symmetrize4_symmetric B) hsym
  · intro h
    obtain ⟨lam, hlam⟩ := h
    intro k hk
    have hsymEq :=
      diff_scalar_eta_implies_null_quadratic_eq
        (symmetrize4 A) (symmetrize4 B) lam hlam k hk
    rw [quadContr_eq_quadContr_symmetrize4 A k,
      quadContr_eq_quadContr_symmetrize4 B k, hsymEq]

/-! ## Algebraic null-quadratic class interface -/

/--
Null-cone equivalence of two matrices: they induce the same quadratic
scalar on every Minkowski-null covector.
-/
def NullConeEquivalent
    (A B : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ k, MinkowskiNull k → quadContr A k = quadContr B k

theorem NullConeEquivalent.refl (A : Matrix (Fin 4) (Fin 4) ℝ) :
    NullConeEquivalent A A := by
  intro _ _
  rfl

theorem NullConeEquivalent.symm
    {A B : Matrix (Fin 4) (Fin 4) ℝ}
    (h : NullConeEquivalent A B) :
    NullConeEquivalent B A := by
  intro k hk
  exact (h k hk).symm

theorem NullConeEquivalent.trans
    {A B C : Matrix (Fin 4) (Fin 4) ℝ}
    (hAB : NullConeEquivalent A B) (hBC : NullConeEquivalent B C) :
    NullConeEquivalent A C := by
  intro k hk
  exact (hAB k hk).trans (hBC k hk)

/--
A scalar map `φ` on covectors determines a unique symmetric matrix class
modulo `η` when it arises as a null-cone quadratic form.
This is only an algebraic equivalence class, theorem-backed without a quotient
type.  It supplies no geometric ancestry.
-/
def DeterminesAlgebraicNullQuadraticClass
    (φ : (Fin 4 → ℝ) → ℝ)
    (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Symmetric4 A ∧
  (∀ k, MinkowskiNull k → φ k = quadContr A k) ∧
  (∀ B : Matrix (Fin 4) (Fin 4) ℝ,
    Symmetric4 B →
    (∀ k, MinkowskiNull k → φ k = quadContr B k) →
      ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j)

/-- Every symmetric matrix determines its algebraic null-quadratic class. -/
theorem determinesAlgebraicNullQuadraticClass_quadContr
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Symmetric4 A) :
    DeterminesAlgebraicNullQuadraticClass (quadContr A) A := by
  refine ⟨hA, fun _ _ => rfl, ?_⟩
  intro B hB hφ
  exact null_quadratic_eq_implies_diff_scalar_eta A B hA hB hφ

/--
Adding a metric multiple does not change the algebraic null-quadratic class of a
symmetric representative.
-/
theorem determinesAlgebraicNullQuadraticClass_add_eta
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : Symmetric4 A) (lam : ℝ) :
    DeterminesAlgebraicNullQuadraticClass (quadContr A)
      (A + lam • minkowskiEta4) := by
  have hSym : Symmetric4 (A + lam • minkowskiEta4) := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hA i j]
    have hη : minkowskiEta4 i j = minkowskiEta4 j i := by
      simp only [minkowskiEta4]
      by_cases hij : i = j
      · subst j; simp
      · have hji : j ≠ i := fun h => hij h.symm
        simp [hij, hji]
    rw [hη]
  have hφ :
      ∀ k, MinkowskiNull k →
        quadContr A k = quadContr (A + lam • minkowskiEta4) k := by
    intro k hk
    have hadd :
        quadContr (A + lam • minkowskiEta4) k =
          quadContr A k + quadContr (lam • minkowskiEta4) k := by
      simp only [quadContr, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hadd, quadContr_smul_eta_of_null lam k hk, add_zero]
  refine ⟨hSym, hφ, ?_⟩
  intro B hB hBφ
  have hnull :
      ∀ k, MinkowskiNull k →
        quadContr (A + lam • minkowskiEta4) k = quadContr B k := by
    intro k hk
    exact (hφ k hk).symm.trans (hBφ k hk)
  exact null_quadratic_eq_implies_diff_scalar_eta
    (A + lam • minkowskiEta4) B hSym hB hnull

/-! ## Fixed-stress scalar-map instantiation -/

/--
Direction-indexed flux of a fixed stress matrix.  Matches the
`fixedStressFlux` packaging in `HorizonIndexedRecordFlux` (definitionally
`quadContr`), kept local so this module stays free of that heavy import.
-/
def fixedStressFlux
    (T : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) : ℝ :=
  quadContr T k

/--
Any fixed symmetric stress scalar map determines its algebraic
null-quadratic class modulo `η`.  Specializes immediately to
`HorizonIndexedRecordFlux.witnessFixedStress` once `Symmetric4` is known.
This statement supplies no independently geometric `G`.
-/
theorem fixedSymmetricStress_determinesAlgebraicNullQuadraticClass
    (T : Matrix (Fin 4) (Fin 4) ℝ) (hT : Symmetric4 T) :
    DeterminesAlgebraicNullQuadraticClass (fixedStressFlux T) T := by
  simpa [fixedStressFlux] using
    determinesAlgebraicNullQuadraticClass_quadContr T hT

theorem fixedSymmetricStress_null_class_unique
    (T B : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : Symmetric4 T) (hB : Symmetric4 B)
    (hnull :
      ∀ k, MinkowskiNull k →
        fixedStressFlux T k = fixedStressFlux B k) :
    ∃ lam : ℝ, ∀ i j, T i j - B i j = lam * minkowskiEta4 i j :=
  null_quadratic_eq_implies_diff_scalar_eta T B hT hB hnull

/-!
## OPEN Phase 5 residual

The remaining Phase 5 object is an independently constructed symmetric matrix
`G` whose entries descend from Recognition area/focusing ancestry, together
with a proved future-null quadratic comparison to the relevant scalar data.
The theorem `future_null_quadratic_eq_implies_diff_scalar_eta` would then
identify its algebraic class modulo `η`.  This module intentionally defines no
Prop that pretends to encode "independently constructed": that requirement must
be discharged by the actual construction and its dependency graph.  Taking
`G := T` or reusing the shared MODEL chart is forbidden and leaves Tier A OPEN.
-/

/-! ## Certificate -/

/--
Certificate for the Phase-5 algebraic prerequisite.  It records rigidity and
future-to-all extension only.  It does not contain or claim the independently
geometric `G`, Ricci identification, Unruh, C-gap1, Tier A, or EFE closure.
-/
structure NullConeQuadraticTensorClassCert : Prop where
  future_to_all :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ),
      (∀ k, MinkowskiNull k → k ≠ 0 → 0 < k 0 →
        quadContr A k = quadContr B k) →
      ∀ k, MinkowskiNull k → quadContr A k = quadContr B k
  reconstruction :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ),
      Symmetric4 A → Symmetric4 B →
      (∀ k, MinkowskiNull k → quadContr A k = quadContr B k) →
        ∃ lam : ℝ, ∀ i j, A i j - B i j = lam * minkowskiEta4 i j
  converse :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ) (lam : ℝ),
      (∀ i j, A i j - B i j = lam * minkowskiEta4 i j) →
        ∀ k, MinkowskiNull k → quadContr A k = quadContr B k
  antisym_invisible :
    ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ),
      quadContr A k = quadContr (symmetrize4 A) k
  general_class :
    ∀ (A B : Matrix (Fin 4) (Fin 4) ℝ),
      (∀ k, MinkowskiNull k → quadContr A k = quadContr B k) ↔
        ∃ lam : ℝ, ∀ i j,
          symmetrize4 A i j - symmetrize4 B i j = lam * minkowskiEta4 i j
  fixed_stress_algebraic_class :
    ∀ (T : Matrix (Fin 4) (Fin 4) ℝ),
      Symmetric4 T →
        DeterminesAlgebraicNullQuadraticClass (fixedStressFlux T) T

theorem nullConeQuadraticTensorClassCert :
    NullConeQuadraticTensorClassCert where
  future_to_all := all_null_quad_eq_of_future_nonzero_null_quad_eq
  reconstruction := null_quadratic_eq_implies_diff_scalar_eta
  converse := diff_scalar_eta_implies_null_quadratic_eq
  antisym_invisible := quadContr_eq_quadContr_symmetrize4
  general_class := null_quadratic_eq_iff_symmetrize_diff_scalar_eta
  fixed_stress_algebraic_class :=
    fixedSymmetricStress_determinesAlgebraicNullQuadraticClass

end NullConeQuadraticTensorClass
end Gravity
end IndisputableMonolith
