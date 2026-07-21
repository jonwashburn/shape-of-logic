import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.ClausiusEinsteinBridge

/-!
# RS null scalar reduction from an assumed matrix source

This module proves the algebraic step from an independently supplied
Einstein-shaped matrix equation to its null-contracted scalar equation.

If

`κ T = Ric + f η`

and `k` is Minkowski-null, then the metric term vanishes and

`Ric(k,k) = κ T(k,k)`.

The RS specialization selects the coupling parameter
`κ = kappa_einstein`.

Honesty tags:

* THEOREM: all matrix and null-contraction algebra below.
* OPEN / external input: inhabiting `EinsteinShapedSource` from the RS action.
* This module does not construct a horizon patch, identify cut channels with
  spacetime covectors, or derive a sourced field equation from the ledger.
* The file name is retained for import compatibility; every public declaration
  is named as a conditional reduction rather than a derived field equation.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace RSNullFieldReduction

open ClausiusEinsteinBridge
open IndisputableMonolith.Constants

/-- Quadratic contraction is additive in its matrix argument. -/
theorem quadContr_add
    (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) :
    quadContr (A + B) k = quadContr A k + quadContr B k := by
  unfold quadContr
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

/-- Quadratic contraction is homogeneous in its matrix argument. -/
theorem quadContr_smul
    (c : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ)
    (k : Fin 4 → ℝ) :
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

/-- Every scalar Minkowski metric term vanishes on a null probe. -/
theorem quadContr_metric_term_eq_zero
    (f : ℝ) (k : Fin 4 → ℝ)
    (hk : MinkowskiNull k) :
    quadContr (f • minkowskiEta4) k = 0 := by
  rw [quadContr_smul, quadContr_minkowskiEta4]
  rw [show -(k 0) ^ 2 + (k 1) ^ 2 + (k 2) ^ 2 + (k 3) ^ 2 = 0 by
    simpa [MinkowskiNull] using hk]
  ring

/--
An Einstein-shaped sourced equation at the matrix layer.  This is an explicit
input interface, not an in-tree derivation from the RS action.
-/
def EinsteinShapedSource
    (coupling : ℝ)
    (T Ric : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∃ f : ℝ, coupling • T = Ric + f • minkowskiEta4

/--
Null reduction of one Einstein-shaped equation.  The undetermined scalar
metric term disappears on every Minkowski-null direction.
-/
theorem null_scalar_of_einstein_shaped
    (coupling : ℝ)
    (T Ric : Matrix (Fin 4) (Fin 4) ℝ)
    (f : ℝ)
    (h : coupling • T = Ric + f • minkowskiEta4)
    (k : Fin 4 → ℝ)
    (hk : MinkowskiNull k) :
    quadContr Ric k = coupling * quadContr T k := by
  have hcontract := congrArg (fun A => quadContr A k) h
  change quadContr (coupling • T) k =
    quadContr (Ric + f • minkowskiEta4) k at hcontract
  rw [quadContr_smul, quadContr_add,
    quadContr_metric_term_eq_zero f k hk, add_zero] at hcontract
  exact hcontract.symm

/-- Bundled null reduction from `EinsteinShapedSource`. -/
theorem null_scalar_of_source
    {coupling : ℝ}
    {T Ric : Matrix (Fin 4) (Fin 4) ℝ}
    (h : EinsteinShapedSource coupling T Ric) :
    ∀ k, MinkowskiNull k →
      quadContr Ric k = coupling * quadContr T k := by
  obtain ⟨f, hf⟩ := h
  intro k hk
  exact null_scalar_of_einstein_shaped coupling T Ric f hf k hk

/--
RS-normalized specialization: an independently inhabited Einstein-shaped
source with the RS coupling yields its null-contracted scalar form.
-/
theorem rs_null_scalar_of_source
    {T Ric : Matrix (Fin 4) (Fin 4) ℝ}
    (h : EinsteinShapedSource kappa_einstein T Ric) :
    ∀ k, MinkowskiNull k →
      quadContr Ric k = kappa_einstein * quadContr T k :=
  null_scalar_of_source h

/--
Componentwise source equations can be transported into the matrix interface.
-/
theorem source_of_componentwise
    (coupling f : ℝ)
    (T Ric : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ i j,
      coupling * T i j = Ric i j + f * minkowskiEta4 i j) :
    EinsteinShapedSource coupling T Ric := by
  refine ⟨f, ?_⟩
  ext i j
  simpa [Matrix.smul_apply, smul_eq_mul] using h i j

/--
The null equation does not recover the scalar metric term: adding a nonzero
multiple of `η` changes the matrix while preserving every null contraction.
-/
theorem scalar_metric_term_is_null_invisible :
    ∃ D : Matrix (Fin 4) (Fin 4) ℝ,
      D ≠ 0 ∧
      ∀ k, MinkowskiNull k → quadContr D k = 0 := by
  refine ⟨minkowskiEta4, ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
    norm_num [minkowskiEta4] at h00
  · intro k hk
    simpa using quadContr_metric_term_eq_zero 1 k hk

/-- Certificate for the matrix-level RS null reduction. -/
structure RSNullFieldReductionCert : Prop where
  metric_term_vanishes :
    ∀ (f : ℝ) (k : Fin 4 → ℝ), MinkowskiNull k →
      quadContr (f • minkowskiEta4) k = 0
  source_reduces :
    ∀ {T Ric : Matrix (Fin 4) (Fin 4) ℝ},
      EinsteinShapedSource kappa_einstein T Ric →
      ∀ k, MinkowskiNull k →
        quadContr Ric k = kappa_einstein * quadContr T k
  metric_term_not_recovered :
    ∃ D : Matrix (Fin 4) (Fin 4) ℝ,
      D ≠ 0 ∧
      ∀ k, MinkowskiNull k → quadContr D k = 0

theorem rsNullFieldReductionCert : RSNullFieldReductionCert where
  metric_term_vanishes := quadContr_metric_term_eq_zero
  source_reduces := rs_null_scalar_of_source
  metric_term_not_recovered := scalar_metric_term_is_null_invisible

end RSNullFieldReduction
end Gravity
end IndisputableMonolith
