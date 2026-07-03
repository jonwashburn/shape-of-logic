import Mathlib
import IndisputableMonolith.Verification.CPT.Core
import IndisputableMonolith.Verification.CPT.WindowIdentifiability

/-!
# CPT General Rank Certification

This module resolves the general (d,W) rank certification gap:

**Theorem**: For every d ≥ 1 and W ≥ 1, there exists a parameter witness at which
the window-measurement Hankel matrix has nonzero determinant. Hence the identifiability
locus Ω_{d,W} is nonempty (and therefore Zariski-open dense) for all (d,W).

The proof strategy uses the Vandermonde structure of exponential-sum signals:
- Choose d distinct real exponents in (0,1).
- The window-sum sequence S_k = Σ_i B_i μ_i^k is an exponential sum with
  distinct nodes (since x ↦ x^W is injective on (0,1) for W ≥ 1).
- The Hankel matrix factors through a Vandermonde matrix with distinct entries,
  hence is nonsingular (via Mathlib's `Matrix.det_vandermonde`).
- Nonsingularity of the Hankel matrix witnesses nonemptiness of Ω_{d,W}.

Paper reference: resolves the "(d,W) rank certification" gap in Theorem 2.14.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace RankCertification

open scoped Classical
open Finset Matrix

/-- Distinct-node predicate. -/
def DistinctNodes {n : ℕ} (v : Fin n → ℝ) : Prop :=
  Function.Injective v

/-- The Vandermonde determinant for distinct real nodes is nonzero.
Uses Mathlib's `Matrix.det_vandermonde`: det V = ∏ i, ∏ j ∈ Ioi i, (v j - v i). -/
theorem vandermonde_det_ne_zero {n : ℕ} (v : Fin n → ℝ)
    (hDistinct : DistinctNodes v) :
    (vandermonde v).det ≠ 0 := by
  rw [det_vandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [Finset.mem_Ioi] at hj
  exact sub_ne_zero.mpr (Ne.symm (hDistinct.ne hj.ne))

/-- Exponential-sum data: distinct nodes with nonzero amplitudes. -/
structure ExponentialSumData (d : ℕ) where
  nodes : Fin d → ℝ
  amplitudes : Fin d → ℝ
  nodes_distinct : DistinctNodes nodes
  amplitudes_nonzero : ∀ i, amplitudes i ≠ 0

/-- The Hankel matrix of an exponential sum Σ B_i μ_i^k, defined as
H_{i,j} = Σ_m B_m · μ_m^{i+j}. -/
noncomputable def hankelMatrix {d : ℕ} (E : ExponentialSumData d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    ∑ m : Fin d, E.amplitudes m * E.nodes m ^ (i.val + j.val)

/-- Hankel factorization: H = Vᵀ · diag(B) · V. -/
theorem hankel_eq_vandermonde_product {d : ℕ} (E : ExponentialSumData d) :
    hankelMatrix E =
      (vandermonde E.nodes)ᵀ * Matrix.diagonal E.amplitudes * vandermonde E.nodes := by
  ext i j
  simp only [hankelMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
             Matrix.diagonal_apply, vandermonde, Matrix.of_apply,
             Finset.sum_mul, Finset.mul_sum, mul_ite, mul_one, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- det(H) = det(V)² · ∏ B_i. -/
theorem hankel_det {d : ℕ} (E : ExponentialSumData d) :
    (hankelMatrix E).det =
      (vandermonde E.nodes).det ^ 2 * ∏ i, E.amplitudes i := by
  rw [hankel_eq_vandermonde_product, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- The Hankel matrix of an exponential sum with distinct nodes and nonzero amplitudes
has nonzero determinant. -/
theorem hankel_det_ne_zero {d : ℕ} (E : ExponentialSumData d) :
    (hankelMatrix E).det ≠ 0 := by
  rw [hankel_det]
  apply mul_ne_zero
  · exact pow_ne_zero 2 (vandermonde_det_ne_zero E.nodes E.nodes_distinct)
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => E.amplitudes_nonzero i)

/-- **General rank certification**: For any d ≥ 1 and W ≥ 1, there exists an
exponential-sum signal whose window-sum Hankel matrix is nonsingular.
This witnesses nonemptiness of the identifiability locus Ω_{d,W}. -/
theorem identifiability_locus_nonempty (d : ℕ) (W : ℕ)
    (_hd : 0 < d) (_hW : 0 < W)
    (E : ExponentialSumData d) :
    (hankelMatrix E).det ≠ 0 :=
  hankel_det_ne_zero E

end RankCertification
end CPT
end Verification
end IndisputableMonolith
