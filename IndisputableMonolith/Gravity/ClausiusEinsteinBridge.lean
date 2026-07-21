import Mathlib

/-!
# The algebraic Clausius-to-Einstein hinge

This module isolates the finite-dimensional linear algebra used in Jacobson's
thermodynamic derivation.  Equality of two symmetric quadratic forms on every
Minkowski-null direction determines their difference only up to a scalar
multiple of the metric.  Thus an all-null local Clausius balance has the
algebraic shape of the Einstein equation, with the metric term left free.

The result is deliberately independent of the repository's refuted raw
ledger-deficit-to-signed-hinge bridge.  It does not construct local horizons,
identify posted record heat with stress-energy flux, prove continuum focusing,
or fix the free scalar by a conservation law.
-/

namespace IndisputableMonolith
namespace Gravity
namespace ClausiusEinsteinBridge

/-- A componentwise symmetry predicate for real covariant 2-tensors in four dimensions. -/
def Symmetric4 (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ i j, A i j = A j i

/-- The `(-,+,+,+)` Minkowski metric in the standard basis. -/
def minkowskiEta4 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then if i = 0 then -1 else 1 else 0

/-- The quadratic contraction `A_{\mu nu} k^mu k^nu`. -/
def quadContr (A : Matrix (Fin 4) (Fin 4) ℝ) (k : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * k i * k j

/-- Nullness for the standard `(-,+,+,+)` Minkowski metric. -/
def MinkowskiNull (k : Fin 4 → ℝ) : Prop :=
  -(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2 = 0

/-- A four-vector with named components, used for the finite null probes below. -/
def vec4 (a b c d : ℝ) : Fin 4 → ℝ :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

@[simp] lemma vec4_zero (a b c d : ℝ) : vec4 a b c d 0 = a := by
  simp [vec4]

@[simp] lemma vec4_one (a b c d : ℝ) : vec4 a b c d 1 = b := by
  rw [vec4, if_neg (by decide), if_pos rfl]

@[simp] lemma vec4_two (a b c d : ℝ) : vec4 a b c d 2 = c := by
  rw [vec4, if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp] lemma vec4_three (a b c d : ℝ) : vec4 a b c d 3 = d := by
  rw [vec4, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

private lemma sum_fin_four {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  have hu : Finset.univ = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  rw [hu]
  simp
  abel

/-- The matrix definition of `minkowskiEta4` has the expected quadratic form. -/
theorem quadContr_minkowskiEta4 (k : Fin 4 → ℝ) :
    quadContr minkowskiEta4 k =
      -(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2 := by
  simp only [quadContr, sum_fin_four]
  simp [minkowskiEta4]
  ring

/-- Pointwise tensor equality implies equality on every null cut. -/
theorem pointwise_eq_implies_null_cut_eq
    (A B : Matrix (Fin 4) (Fin 4) ℝ) (hAB : A = B) :
    ∀ k, MinkowskiNull k → quadContr A k = quadContr B k := by
  subst B
  simp

/--
Null-cut equality is strictly weaker than pointwise equality: the Minkowski
metric and zero agree quadratically on every Minkowski-null vector.
-/
theorem null_cut_eq_not_pointwise_eq :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ,
      Symmetric4 A ∧ Symmetric4 B ∧
      (∀ k, MinkowskiNull k → quadContr A k = quadContr B k) ∧
      A ≠ B := by
  refine ⟨minkowskiEta4, 0, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [minkowskiEta4]
    by_cases hij : i = j
    · subst j
      simp
    · have hji : j ≠ i := fun h => hij h.symm
      simp [hij, hji]
  · intro i j
    simp
  · intro k hk
    rw [quadContr_minkowskiEta4]
    simpa [quadContr, MinkowskiNull] using hk
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
    norm_num [minkowskiEta4] at h00

/--
Four-dimensional Lorentzian null-contraction rigidity.

If a symmetric covariant tensor has zero quadratic contraction on every
Minkowski-null vector, it is a scalar multiple of the Minkowski metric.
-/
theorem null_quadratic_zero_eq_scalar_eta
    (D : Matrix (Fin 4) (Fin 4) ℝ)
    (hD : Symmetric4 D)
    (hnull : ∀ k, MinkowskiNull k → quadContr D k = 0) :
    ∃ f : ℝ, D = f • minkowskiEta4 := by
  have h01p := hnull (vec4 1 1 0 0) (by norm_num [MinkowskiNull])
  have h01m := hnull (vec4 1 (-1) 0 0) (by norm_num [MinkowskiNull])
  have h02p := hnull (vec4 1 0 1 0) (by norm_num [MinkowskiNull])
  have h02m := hnull (vec4 1 0 (-1) 0) (by norm_num [MinkowskiNull])
  have h03p := hnull (vec4 1 0 0 1) (by norm_num [MinkowskiNull])
  have h03m := hnull (vec4 1 0 0 (-1)) (by norm_num [MinkowskiNull])
  simp only [quadContr, sum_fin_four] at h01p h01m h02p h02m h03p h03m
  norm_num at h01p h01m h02p h02m h03p h03m

  have hs01 : D 1 0 = D 0 1 := hD 1 0
  have hs02 : D 2 0 = D 0 2 := hD 2 0
  have hs03 : D 3 0 = D 0 3 := hD 3 0
  have hz01 : D 0 1 = 0 := by linarith
  have hz02 : D 0 2 = 0 := by linarith
  have hz03 : D 0 3 = 0 := by linarith
  have hd11 : D 1 1 = -D 0 0 := by linarith
  have hd22 : D 2 2 = -D 0 0 := by linarith
  have hd33 : D 3 3 = -D 0 0 := by linarith

  have h12 := hnull (vec4 5 3 4 0) (by norm_num [MinkowskiNull])
  have h13 := hnull (vec4 5 3 0 4) (by norm_num [MinkowskiNull])
  have h23 := hnull (vec4 5 0 3 4) (by norm_num [MinkowskiNull])
  simp only [quadContr, sum_fin_four] at h12 h13 h23
  norm_num at h12 h13 h23

  have hs10 : D 1 0 = D 0 1 := hD 1 0
  have hs20 : D 2 0 = D 0 2 := hD 2 0
  have hs30 : D 3 0 = D 0 3 := hD 3 0
  have hs21 : D 2 1 = D 1 2 := hD 2 1
  have hs31 : D 3 1 = D 1 3 := hD 3 1
  have hs32 : D 3 2 = D 2 3 := hD 3 2
  have hz12 : D 1 2 = 0 := by linarith
  have hz13 : D 1 3 = 0 := by linarith
  have hz23 : D 2 3 = 0 := by linarith

  refine ⟨-D 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minkowskiEta4] <;>
    linarith [hD 0 1, hD 0 2, hD 0 3, hD 1 2, hD 1 3, hD 2 3]

/--
Equality of symmetric quadratic contractions on every null direction
determines the two tensors up to a scalar metric term.
-/
theorem null_quadratic_eq_of_diff_scalar_eta
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : Symmetric4 A)
    (hB : Symmetric4 B)
    (hnull : ∀ k, MinkowskiNull k → quadContr A k = quadContr B k) :
    ∃ f : ℝ, A = B + f • minkowskiEta4 := by
  let D : Matrix (Fin 4) (Fin 4) ℝ := A - B
  have hD : Symmetric4 D := by
    intro i j
    simp only [D, Matrix.sub_apply]
    rw [hA i j, hB i j]
  have hDnull : ∀ k, MinkowskiNull k → quadContr D k = 0 := by
    intro k hk
    specialize hnull k hk
    simpa [D, quadContr, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr hnull
  obtain ⟨f, hf⟩ := null_quadratic_zero_eq_scalar_eta D hD hDnull
  refine ⟨f, ?_⟩
  ext i j
  have hij := congrFun (congrFun hf i) j
  change A i j = B i j + (f • minkowskiEta4) i j
  simp only [D, Matrix.sub_apply] at hij
  linarith

/--
The algebraic Einstein-shaped consequence of local Clausius balance.

Here "Clausius" names an assumed null-cut interface: a stress-like symmetric
tensor and a Ricci-like symmetric tensor have equal contractions on every
local null direction.  The theorem does not derive that interface from
thermodynamics.  Its conclusion leaves a free scalar metric term, as in
Jacobson's argument before conservation fixes the cosmological term.
-/
theorem einstein_equation_shaped_of_local_clausius
    (coupling : ℝ)
    (T Ric : Matrix (Fin 4) (Fin 4) ℝ)
    (hT : Symmetric4 T)
    (hRic : Symmetric4 Ric)
    (hClausius :
      ∀ k, MinkowskiNull k →
        quadContr (coupling • T) k = quadContr Ric k) :
    ∃ f : ℝ, coupling • T = Ric + f • minkowskiEta4 := by
  apply null_quadratic_eq_of_diff_scalar_eta
  · intro i j
    change coupling * T i j = coupling * T j i
    rw [hT i j]
  · exact hRic
  · exact hClausius

end ClausiusEinsteinBridge
end Gravity
end IndisputableMonolith
