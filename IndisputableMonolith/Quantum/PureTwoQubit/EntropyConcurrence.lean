import Mathlib

/-!
# Pure Two-Qubit Concurrence and Entanglement Entropy (Track 2.B)

## Status: STRUCTURAL THEOREM (Track 2.B closed; no proof holes, no new RS assumptions).

This module discharges Track 2.B of the master
plan: the chain from the Wootters concurrence of a pure two-qubit
amplitude matrix to strict positivity of the von Neumann entanglement
entropy. The full reduction
`E_VN(ρ₁) = h((1 + √(1 − C²)) / 2)` is proved by combining:

(i) the **algebraic core**: for `C ∈ (0, 1]`, the value
    `(1 + √(1 − C²)) / 2` lies in the open unit interval `(1/2, 1]`
    (strictly less than `1` when `C > 0`), and the binary entropy
    `h(p) = -p log p - (1-p) log(1-p)` is strictly positive on
    `(0, 1)` and zero at the endpoints `0, 1`.

(ii) the **reduced-density-matrix step**: for a
     pure two-qubit state `|ψ⟩ = Σᵢⱼ Aᵢⱼ |ij⟩`, the reduced density
     matrix `ρ₁ = tr_2 |ψ⟩⟨ψ|` has eigenvalues
     `(1 ± √(1 − 4|det A|²)) / 2 = (1 ± √(1 − C²)) / 2`, hence
     `E_VN(ρ₁) = h((1 − √(1 − C²)) / 2)
     = h((1 + √(1 − C²)) / 2)` (binary entropy is symmetric about
     `p = 1/2`). This is captured as a Prop-shaped sub-target
     `PureTwoQubitReducedEntropyTarget` and composed with the algebraic
     core to give the full entropy-positivity theorem.

## Concurrence convention

For a pure two-qubit amplitude matrix `A : Fin 2 × Fin 2 → ℂ`
representing a normalized state, the Wootters concurrence is
`C(A) := 2 · |det A|`. (This is the standard pure-state simplification;
the general mixed-state Wootters formula reduces to this in the pure
case.) Strict positivity of `C` is equivalent to nonzero determinant,
matching the algebraic entanglement witness already proved in
`Gravity.QuantumChannel.BMVPositive.det_branchAmplitude_factored`.

## What this module proves

* `concurrence`: the Wootters concurrence of a `2×2` amplitude matrix.
* `concurrence_nonneg`, `concurrence_eq_zero_iff_det_zero`.
* `binaryEntropy`: `h(p) = -p · log p - (1-p) · log(1-p)`.
* `binaryEntropy_zero_left`, `binaryEntropy_zero_right`: `h(0) = h(1) = 0`.
* `binaryEntropy_pos_of_open_unit_interval`: `0 < p < 1 → 0 < h(p)`.
* `inner_radius_pos_of_pos_concurrence`: for `0 < C ≤ 1`,
  `(1 + √(1 − C²)) / 2 ∈ (1/2, 1)`.
* `pureTwoQubitReducedEntropyTarget_holds`: the spectral reduced-entropy
  target for `reducedDensityVonNeumannEntropy`.
* `pure_two_qubit_entropy_positive_unconditional`: for normalized states
  with `0 < C`,
  `E_VN(ρ₁) > 0`.
-/

namespace IndisputableMonolith
namespace Quantum
namespace PureTwoQubit
namespace EntropyConcurrence

open Real Complex

noncomputable section

/-! ## §1. Concurrence of a pure two-qubit amplitude matrix -/

/-- The Wootters concurrence of a pure two-qubit amplitude matrix:
`C(A) = 2 · ‖det A‖`. (For pure two-qubit states, the general
Wootters formula simplifies to twice the absolute value of the
determinant of the amplitude matrix.) -/
def concurrence (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  2 * ‖Matrix.det A‖

/-- Concurrence is non-negative. -/
theorem concurrence_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ concurrence A := by
  unfold concurrence
  have h : 0 ≤ ‖Matrix.det A‖ := norm_nonneg _
  linarith

/-- Concurrence vanishes if and only if the amplitude matrix has
zero determinant. -/
theorem concurrence_eq_zero_iff_det_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    concurrence A = 0 ↔ Matrix.det A = 0 := by
  unfold concurrence
  constructor
  · intro h
    have : ‖Matrix.det A‖ = 0 := by linarith [norm_nonneg (Matrix.det A)]
    exact norm_eq_zero.mp this
  · intro h
    rw [h]
    simp

/-- Concurrence is positive iff determinant is nonzero. -/
theorem concurrence_pos_iff_det_ne_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    0 < concurrence A ↔ Matrix.det A ≠ 0 := by
  rw [show (0 : ℝ) < concurrence A ↔ concurrence A ≠ 0 from
    ⟨fun h => h.ne', fun h => lt_of_le_of_ne (concurrence_nonneg A) (Ne.symm h)⟩,
    Ne, concurrence_eq_zero_iff_det_zero]

/-! ## §1b. Reduced density matrix of a pure two-qubit amplitude matrix -/

/-- Frobenius norm-squared of a pure two-qubit amplitude matrix:
`Σᵢⱼ ‖Aᵢⱼ‖²`, written using `Complex.normSq` so the normalization
condition is algebraic. -/
def frobeniusNormSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- The first-qubit reduced density matrix of the pure two-qubit state
with amplitude matrix `A`. This is the partial trace over the second
qubit:

`ρ₁(i,k) = Σⱼ Aᵢⱼ · conj(Aₖⱼ)`.

Equivalently, it is `A · A†` in matrix notation. -/
def reducedDensity (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i k => ∑ j, A i j * (starRingEnd ℂ) (A k j)

/-- The reduced-density trace equals the Frobenius normalization,
as a complex number. -/
theorem reducedDensity_trace_eq_frobenius
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    reducedDensity A 0 0 + reducedDensity A 1 1 =
      (frobeniusNormSq A : ℂ) := by
  unfold reducedDensity frobeniusNormSq
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [Complex.mul_conj]

/-- If the amplitude matrix is normalized, the reduced density matrix
has trace one. -/
theorem reducedDensity_trace_eq_one_of_normalized
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    reducedDensity A 0 0 + reducedDensity A 1 1 = 1 := by
  rw [reducedDensity_trace_eq_frobenius A, hNorm]
  norm_num

/-- Determinant of the first-qubit reduced density matrix:
`det(ρ₁) = normSq(det A)`.

This is the key pure-two-qubit algebraic identity behind Wootters'
formula: the non-product witness `det A ≠ 0` is exactly the positive
determinant of the reduced density matrix. -/
theorem reducedDensity_det_eq_normSq_det
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (reducedDensity A) = (Complex.normSq (Matrix.det A) : ℂ) := by
  rw [Matrix.det_fin_two]
  unfold reducedDensity
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [Matrix.det_fin_two A]
  change
    (A 0 0 * (starRingEnd ℂ) (A 0 0) + A 0 1 * (starRingEnd ℂ) (A 0 1)) *
          (A 1 0 * (starRingEnd ℂ) (A 1 0) + A 1 1 * (starRingEnd ℂ) (A 1 1)) -
        (A 0 0 * (starRingEnd ℂ) (A 1 0) + A 0 1 * (starRingEnd ℂ) (A 1 1)) *
          (A 1 0 * (starRingEnd ℂ) (A 0 0) + A 1 1 * (starRingEnd ℂ) (A 0 1)) =
      ((Complex.normSq (A 0 0 * A 1 1 - A 0 1 * A 1 0) : ℝ) : ℂ)
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sub, map_mul]
  ring

/-- Determinant of the first-qubit reduced density matrix:
`det(ρ₁) = ‖det A‖²`. -/
theorem reducedDensity_det_eq_norm_det_sq
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (reducedDensity A) = (‖Matrix.det A‖ ^ 2 : ℂ) := by
  rw [reducedDensity_det_eq_normSq_det]
  rw [Complex.normSq_eq_norm_sq]
  norm_cast

/-- Determinant of the reduced density matrix in concurrence form:
`det(ρ₁) = C(A)^2 / 4`. -/
theorem reducedDensity_det_eq_concurrence_sq_div_four
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (reducedDensity A) = ((concurrence A) ^ 2 / 4 : ℝ) := by
  rw [reducedDensity_det_eq_norm_det_sq]
  unfold concurrence
  norm_num
  ring

/-- If the pure two-qubit amplitude matrix has nonzero determinant, the
first-qubit reduced density matrix has nonzero determinant. -/
theorem reducedDensity_det_ne_zero_of_concurrence_pos
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hC : 0 < concurrence A) :
    Matrix.det (reducedDensity A) ≠ 0 := by
  rw [reducedDensity_det_eq_concurrence_sq_div_four]
  have hC_ne : concurrence A ≠ 0 := hC.ne'
  have hsq_ne : (concurrence A) ^ 2 ≠ 0 := pow_ne_zero 2 hC_ne
  exact_mod_cast div_ne_zero hsq_ne (by norm_num : (4 : ℝ) ≠ 0)

/-- The trace-one characteristic discriminant of the reduced density
matrix, written in terms of concurrence:
`tr(ρ₁)^2 - 4 det(ρ₁) = 1 - C(A)^2`.

This is the algebraic bridge from the partial trace to the standard
eigenvalue expression `(1 ± √(1 - C²))/2`. -/
theorem reducedDensity_discriminant_eq_one_sub_concurrence_sq
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (_hNorm : frobeniusNormSq A = 1) :
    (1 : ℂ) - 4 * Matrix.det (reducedDensity A) =
      ((1 - (concurrence A) ^ 2 : ℝ) : ℂ) := by
  rw [reducedDensity_det_eq_concurrence_sq_div_four]
  norm_num
  ring

/-! ## §1c. Spectral weights from concurrence -/

/-- The upper reduced-density eigenvalue candidate:
`λ₊(C) = (1 + √(1 - C²)) / 2`. -/
def lambdaPlus (C : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - C ^ 2)) / 2

/-- The lower reduced-density eigenvalue candidate:
`λ₋(C) = (1 - √(1 - C²)) / 2`. -/
def lambdaMinus (C : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - C ^ 2)) / 2

/-- The two concurrence spectral weights sum to one. -/
theorem lambdaPlus_add_lambdaMinus (C : ℝ) :
    lambdaPlus C + lambdaMinus C = 1 := by
  unfold lambdaPlus lambdaMinus
  ring

/-- If `0 ≤ 1 - C²`, the two concurrence spectral weights multiply to
`C²/4`, matching the determinant of the reduced density matrix. -/
theorem lambdaPlus_mul_lambdaMinus
    {C : ℝ} (hdisc : 0 ≤ 1 - C ^ 2) :
    lambdaPlus C * lambdaMinus C = C ^ 2 / 4 := by
  unfold lambdaPlus lambdaMinus
  have hs : (Real.sqrt (1 - C ^ 2)) ^ 2 = 1 - C ^ 2 := by
    exact Real.sq_sqrt hdisc
  nlinarith

/-- For `0 ≤ C ≤ 1`, the concurrence spectral weights have the same
trace and determinant invariants as a normalized reduced density matrix:
sum `1`, product `C²/4`. -/
theorem lambdaPair_sum_product_of_concurrence_unit_interval
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hC_le : C ≤ 1) :
    lambdaPlus C + lambdaMinus C = 1 ∧
      lambdaPlus C * lambdaMinus C = C ^ 2 / 4 := by
  refine ⟨lambdaPlus_add_lambdaMinus C, ?_⟩
  have hdisc : 0 ≤ 1 - C ^ 2 := by
    nlinarith [sq_nonneg C, hC_nonneg, hC_le]
  exact lambdaPlus_mul_lambdaMinus hdisc

/-! ## §2. Binary entropy -/

/-- The binary entropy function `h(p) = -p · log p - (1-p) · log(1-p)`,
extended by continuity at the endpoints with `h(0) = h(1) = 0`
(`Real.log 0 = 0` in Mathlib, so the formula evaluates correctly at
the endpoints). -/
def binaryEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- `h(0) = 0`. -/
theorem binaryEntropy_zero_left : binaryEntropy 0 = 0 := by
  unfold binaryEntropy
  simp [Real.log_one]

/-- `h(1) = 0`. -/
theorem binaryEntropy_zero_right : binaryEntropy 1 = 0 := by
  unfold binaryEntropy
  simp [Real.log_one]

/-- Binary entropy is symmetric about `p = 1/2`. -/
theorem binaryEntropy_symm (p : ℝ) : binaryEntropy (1 - p) = binaryEntropy p := by
  unfold binaryEntropy
  ring_nf

/-- Strict positivity of binary entropy on the open unit interval.

For `0 < p < 1`, both `-p · log p` and `-(1-p) · log(1-p)` are
non-negative (since `log` of a number in `(0, 1)` is negative), and at
least one is strictly positive (since `p ≠ 0` and `1 - p ≠ 0`). -/
theorem binaryEntropy_pos_of_open_unit_interval
    {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    0 < binaryEntropy p := by
  unfold binaryEntropy
  -- Show that both terms `-p · log p` and `-(1-p) · log(1-p)` are ≥ 0,
  -- with the first being > 0 (since 0 < p < 1).
  have h1mp : 0 < 1 - p := by linarith
  have hpt1 : p < 1 := h1
  have hpt2 : 1 - p ≤ 1 := by linarith
  have hp_log_neg : Real.log p < 0 := Real.log_neg h0 h1
  have h_first_pos : 0 < -p * Real.log p := by
    have : Real.log p < 0 := hp_log_neg
    nlinarith [h0, this]
  -- Second term `-(1-p) · log(1-p)`: with 0 < 1-p ≤ 1, log(1-p) ≤ 0.
  -- Its negation times a positive scalar is ≥ 0.
  have h1mp_log_le : Real.log (1 - p) ≤ 0 := by
    by_cases h_eq : 1 - p = 1
    · rw [h_eq]; simp [Real.log_one]
    · have h1mp_lt : 1 - p < 1 := lt_of_le_of_ne hpt2 h_eq
      exact (Real.log_neg h1mp h1mp_lt).le
  have h_second_nonneg : 0 ≤ -(1 - p) * Real.log (1 - p) := by
    nlinarith [h1mp, h1mp_log_le]
  linarith [h_first_pos, h_second_nonneg]

/-! ## §3. Inner radius from concurrence -/

/-- For `0 < C ≤ 1`, the value `(1 + √(1 − C²)) / 2` lies strictly
between `1/2` and `1`. The strict upper bound `< 1` is exactly the
condition for binary entropy to be positive. -/
theorem inner_radius_lt_one_of_pos_concurrence
    {C : ℝ} (hC_pos : 0 < C) (hC_le : C ≤ 1) :
    (1 + Real.sqrt (1 - C ^ 2)) / 2 < 1 := by
  -- Need √(1 - C²) < 1, i.e., 1 - C² < 1, i.e., 0 < C².
  have hC_sq_pos : 0 < C ^ 2 := by positivity
  have h_arg_lt_one : 1 - C ^ 2 < 1 := by linarith
  have h_arg_nonneg : 0 ≤ 1 - C ^ 2 := by
    have : C ^ 2 ≤ 1 := by
      have : C ^ 2 ≤ 1 ^ 2 := by
        apply sq_le_sq'
        · linarith
        · exact hC_le
      simpa using this
    linarith
  have h_sqrt_lt_one : Real.sqrt (1 - C ^ 2) < 1 := by
    have h_sqrt_lt_sqrt : Real.sqrt (1 - C ^ 2) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt h_arg_nonneg h_arg_lt_one
    simpa [Real.sqrt_one] using h_sqrt_lt_sqrt
  linarith

/-- For `0 < C ≤ 1`, the inner radius `(1 + √(1 − C²)) / 2` lies in
`[1/2, 1)` (lower bound non-strict — equality holds at `C = 1`; upper
bound strict — the entropy positivity argument needs the upper bound to
be strict). -/
theorem inner_radius_in_unit_interval_of_pos_concurrence
    {C : ℝ} (hC_pos : 0 < C) (hC_le : C ≤ 1) :
    (1 : ℝ) / 2 ≤ (1 + Real.sqrt (1 - C ^ 2)) / 2 ∧
      (1 + Real.sqrt (1 - C ^ 2)) / 2 < 1 := by
  refine ⟨?_, inner_radius_lt_one_of_pos_concurrence hC_pos hC_le⟩
  have h_arg_nonneg : 0 ≤ 1 - C ^ 2 := by
    have hCsq_le_one : C ^ 2 ≤ 1 := by
      have : C ^ 2 ≤ 1 ^ 2 := by
        apply sq_le_sq'
        · linarith
        · exact hC_le
      simpa using this
    linarith
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 - C ^ 2) := Real.sqrt_nonneg _
  linarith

/-- Composing §2 and §3: for `0 < C ≤ 1`, the binary entropy of the
inner radius is strictly positive. -/
theorem binaryEntropy_inner_radius_pos_of_concurrence
    {C : ℝ} (hC_pos : 0 < C) (hC_le : C ≤ 1) :
    0 < binaryEntropy ((1 + Real.sqrt (1 - C ^ 2)) / 2) := by
  obtain ⟨h_lo, h_hi⟩ := inner_radius_in_unit_interval_of_pos_concurrence hC_pos hC_le
  apply binaryEntropy_pos_of_open_unit_interval
  · linarith
  · exact h_hi

/-! ## §3b. Spectral closure of the reduced-density-matrix step -/

/-- The manual partial-trace formula agrees with `A · A†`. -/
theorem reducedDensity_eq_mul_conjTranspose
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    reducedDensity A = A * A.conjTranspose := by
  ext i k
  simp only [reducedDensity, Matrix.mul_apply, Matrix.conjTranspose_apply, starRingEnd_apply]

/-- The reduced density matrix is Hermitian. -/
theorem reducedDensity_isHermitian
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (reducedDensity A).IsHermitian := by
  rw [reducedDensity_eq_mul_conjTranspose]
  exact Matrix.isHermitian_mul_conjTranspose_self A

/-- Trace of the reduced density matrix equals the Frobenius normalization. -/
theorem reducedDensity_trace_eq_frobenius_complex
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (reducedDensity A).trace = (frobeniusNormSq A : ℂ) := by
  rw [Matrix.trace_fin_two, reducedDensity_trace_eq_frobenius A]

theorem reducedDensity_trace_eq_one_of_normalized_complex
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    (reducedDensity A).trace = 1 := by
  rw [reducedDensity_trace_eq_frobenius_complex A, hNorm]
  norm_num

private theorem lambdaPlus_sub_lambdaMinus (C : ℝ) :
    lambdaPlus C - lambdaMinus C = Real.sqrt (1 - C ^ 2) := by
  unfold lambdaPlus lambdaMinus
  ring

private theorem lambdaPlus_ge_lambdaMinus {C : ℝ} (_hdisc : 0 ≤ 1 - C ^ 2) :
    lambdaMinus C ≤ lambdaPlus C := by
  unfold lambdaPlus lambdaMinus
  linarith [Real.sqrt_nonneg (1 - C ^ 2)]

private theorem sum_product_implies_quadratic
    {x y p : ℝ} (hsum : x + y = 1) (hprod : x * y = p) :
    x ^ 2 - x + p = 0 := by
  have hy : y = 1 - x := by linarith
  rw [hy] at hprod
  nlinarith

private theorem eq_lambdaPlus_or_lambdaMinus_of_quadratic
    {C x : ℝ} (hdisc : 0 ≤ 1 - C ^ 2)
    (hx : x ^ 2 - x + C ^ 2 / 4 = 0) :
    x = lambdaPlus C ∨ x = lambdaMinus C := by
  unfold lambdaPlus lambdaMinus
  have hs : Real.sqrt (1 - C ^ 2) ^ 2 = 1 - C ^ 2 := Real.sq_sqrt hdisc
  have hfac :
      (x - (1 + Real.sqrt (1 - C ^ 2)) / 2) *
          (x - (1 - Real.sqrt (1 - C ^ 2)) / 2) = 0 := by
    nlinarith [Real.sqrt_nonneg (1 - C ^ 2), hs]
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private theorem eigenvalues_fin_two_sum_eq_of_complex_sum
    {e0 e1 t : ℝ} (h : (e0 : ℂ) + (e1 : ℂ) = (t : ℂ)) :
    e0 + e1 = t := by
  rw [← Complex.ofReal_add] at h
  exact Complex.ofReal_injective h

private theorem eigenvalues_fin_two_prod_eq_of_complex_prod
    {e0 e1 p : ℝ} (h : (e0 : ℂ) * (e1 : ℂ) = (p : ℂ)) :
    e0 * e1 = p := by
  rw [← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

private theorem reducedDensity_eigenvalues_sum_eq_one
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    let hρ := reducedDensity_isHermitian A
    hρ.eigenvalues 0 + hρ.eigenvalues 1 = 1 := by
  intro hρ
  have htrace := hρ.trace_eq_sum_eigenvalues
  rw [reducedDensity_trace_eq_one_of_normalized_complex A hNorm, Fin.sum_univ_two] at htrace
  exact eigenvalues_fin_two_sum_eq_of_complex_sum htrace.symm

private theorem reducedDensity_eigenvalues_prod_eq_concurrence_sq_div_four
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    let hρ := reducedDensity_isHermitian A
    hρ.eigenvalues 0 * hρ.eigenvalues 1 = (concurrence A) ^ 2 / 4 := by
  intro hρ
  have hdet := hρ.det_eq_prod_eigenvalues
  rw [reducedDensity_det_eq_concurrence_sq_div_four A, Fin.prod_univ_two] at hdet
  exact eigenvalues_fin_two_prod_eq_of_complex_prod hdet.symm

private theorem concurrence_sq_le_one_of_normalized
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    (concurrence A) ^ 2 ≤ 1 := by
  let hρ := reducedDensity_isHermitian A
  have hsum := reducedDensity_eigenvalues_sum_eq_one A hNorm
  have hprod := reducedDensity_eigenvalues_prod_eq_concurrence_sq_div_four A
  nlinarith [sq_nonneg (hρ.eigenvalues 0 - hρ.eigenvalues 1), hsum, hprod]

theorem concurrence_le_one_of_normalized
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    concurrence A ≤ 1 := by
  nlinarith [sq_nonneg (concurrence A), concurrence_nonneg A,
    concurrence_sq_le_one_of_normalized A hNorm]

private theorem reducedDensity_eigenvalues_eq_lambda_or_swap
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : frobeniusNormSq A = 1) :
    let hρ := reducedDensity_isHermitian A
    let C := concurrence A
    (hρ.eigenvalues 0 = lambdaPlus C ∧ hρ.eigenvalues 1 = lambdaMinus C) ∨
      (hρ.eigenvalues 0 = lambdaMinus C ∧ hρ.eigenvalues 1 = lambdaPlus C) := by
  intro hρ C
  have hC := concurrence_le_one_of_normalized A hNorm
  have hdisc : 0 ≤ 1 - C ^ 2 := by
    nlinarith [sq_nonneg C, concurrence_nonneg A, hC]
  have hsum := reducedDensity_eigenvalues_sum_eq_one A hNorm
  have hprod := reducedDensity_eigenvalues_prod_eq_concurrence_sq_div_four A
  have h0q :
      hρ.eigenvalues 0 ^ 2 - hρ.eigenvalues 0 + C ^ 2 / 4 = 0 :=
    sum_product_implies_quadratic hsum hprod
  have h0 := eq_lambdaPlus_or_lambdaMinus_of_quadratic hdisc h0q
  rcases h0 with h0plus | h0minus
  · exact Or.inl ⟨h0plus, by linarith [hsum, lambdaPlus_add_lambdaMinus C]⟩
  · exact Or.inr ⟨h0minus, by linarith [hsum, lambdaPlus_add_lambdaMinus C]⟩

/-- Von Neumann entropy of the first-qubit reduced density matrix, defined
from the spectral theorem as `-∑ᵢ λᵢ log λᵢ`. -/
def reducedDensityVonNeumannEntropy
    (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  let hρ := reducedDensity_isHermitian A
  (-∑ i : Fin 2, hρ.eigenvalues i * Real.log (hρ.eigenvalues i))

private theorem binaryEntropy_eq_neg_sum_lambda
    {C : ℝ} (_hC_nonneg : 0 ≤ C) (_hC_le : C ≤ 1) :
    binaryEntropy (lambdaPlus C) =
      -(lambdaPlus C * Real.log (lambdaPlus C) +
          lambdaMinus C * Real.log (lambdaMinus C)) := by
  have h1 : lambdaMinus C = 1 - lambdaPlus C := by
    linarith [lambdaPlus_add_lambdaMinus C]
  unfold binaryEntropy
  rw [h1]
  ring

/-- Sub-target capturing the reduced-density-matrix step. It is discharged
by `pureTwoQubitReducedEntropyTarget_holds` for the canonical spectral
definition `reducedDensityVonNeumannEntropy`. -/
def PureTwoQubitReducedEntropyTarget
    (vonNeumannEntropy : Matrix (Fin 2) (Fin 2) ℂ → ℝ) : Prop :=
  ∀ (A : Matrix (Fin 2) (Fin 2) ℂ),
    (∑ i, ∑ j, Complex.normSq (A i j)) = 1 →
    vonNeumannEntropy A =
      binaryEntropy ((1 + Real.sqrt (1 - (concurrence A) ^ 2)) / 2)

theorem pureTwoQubitReducedEntropyTarget_holds :
    PureTwoQubitReducedEntropyTarget reducedDensityVonNeumannEntropy := by
  intro A hNorm
  have hNorm' : frobeniusNormSq A = 1 := by
    simpa [frobeniusNormSq] using hNorm
  have hC := concurrence_le_one_of_normalized A hNorm'
  rcases reducedDensity_eigenvalues_eq_lambda_or_swap A hNorm' with h | h
  · simp only [reducedDensityVonNeumannEntropy]
    rw [Fin.sum_univ_two, h.1, h.2]
    rw [← binaryEntropy_eq_neg_sum_lambda (concurrence_nonneg A) hC]
    unfold lambdaPlus
    rfl
  · simp only [reducedDensityVonNeumannEntropy]
    rw [Fin.sum_univ_two, h.1, h.2]
    have hneg := binaryEntropy_eq_neg_sum_lambda (concurrence_nonneg A) hC
    have hadd :
        lambdaMinus (concurrence A) * Real.log (lambdaMinus (concurrence A)) +
            lambdaPlus (concurrence A) * Real.log (lambdaPlus (concurrence A)) =
          lambdaPlus (concurrence A) * Real.log (lambdaPlus (concurrence A)) +
            lambdaMinus (concurrence A) * Real.log (lambdaMinus (concurrence A)) := by
      ac_rfl
    rw [hadd, ← hneg]
    unfold lambdaPlus
    rfl

theorem pure_two_qubit_entropy_eq_binaryEntropy_inner_radius
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : (∑ i, ∑ j, Complex.normSq (A i j)) = 1) :
    reducedDensityVonNeumannEntropy A =
      binaryEntropy ((1 + Real.sqrt (1 - (concurrence A) ^ 2)) / 2) :=
  pureTwoQubitReducedEntropyTarget_holds A hNorm

/-! ## §4. Reduced-density entropy target (reference) -/

/-- Alias namespace anchor for the reduced-density-matrix sub-target,
already defined and discharged in §3b. -/
abbrev PureTwoQubitReducedEntropyTargetDef :=
  PureTwoQubitReducedEntropyTarget

/-! ## §5. Composite: pure two-qubit entropy positivity -/

/-- **CONDITIONAL CLOSURE: pure two-qubit entropy positivity from
concurrence positivity.** Given an abstract von Neumann-entropy
functional satisfying the reduced-density-matrix sub-target, strict
positivity of the Wootters concurrence implies strict positivity of
the von Neumann entanglement entropy. -/
theorem pure_two_qubit_entropy_positive_of_concurrence_positive
    {vonNeumannEntropy : Matrix (Fin 2) (Fin 2) ℂ → ℝ}
    (hVN : PureTwoQubitReducedEntropyTarget vonNeumannEntropy)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : (∑ i, ∑ j, Complex.normSq (A i j)) = 1)
    (hC_pos : 0 < concurrence A)
    (hC_le : concurrence A ≤ 1) :
    0 < vonNeumannEntropy A := by
  rw [hVN A hNorm]
  exact binaryEntropy_inner_radius_pos_of_concurrence hC_pos hC_le

/-- **UNCONDITIONAL CLOSURE: pure two-qubit entropy positivity from
concurrence positivity.** Uses the discharged reduced-density-matrix
sub-target at the canonical spectral definition. -/
theorem pure_two_qubit_entropy_positive_unconditional
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hNorm : (∑ i, ∑ j, Complex.normSq (A i j)) = 1)
    (hC_pos : 0 < concurrence A) :
    0 < reducedDensityVonNeumannEntropy A := by
  have hNorm' : frobeniusNormSq A = 1 := by simpa [frobeniusNormSq] using hNorm
  exact pure_two_qubit_entropy_positive_of_concurrence_positive
    pureTwoQubitReducedEntropyTarget_holds A hNorm hC_pos
    (concurrence_le_one_of_normalized A hNorm')

/-! ## §6. Master certificate -/

/-- **PURE TWO-QUBIT CONCURRENCE-ENTROPY CERTIFICATE.**

Five clauses establishing the algebraic core of Track 2.B:

1. `concurrence_nonneg`: the Wootters concurrence is non-negative.
2. `concurrence_zero_iff_det_zero`: concurrence vanishes iff
   determinant vanishes.
3. `reduced_trace`: the reduced-density trace is the Frobenius norm.
4. `reduced_det`: `det(ρ₁) = C(A)^2 / 4`.
5. `lambda_pair_sum_product`: the concurrence spectral candidates
   `λ±(C)` have sum `1` and product `C²/4`.
6. `binary_entropy_pos`: binary entropy is strictly positive on
   `(0, 1)`.
7. `inner_radius_in_unit_interval`: for `0 < C ≤ 1`, the inner radius
   lies in `[1/2, 1)`.
8. `entropy_pos_unconditional`: strict concurrence positivity implies
   strict entropy positivity at `reducedDensityVonNeumannEntropy`.
9. `reduced_entropy_target`: the canonical spectral entropy functional
   satisfies `PureTwoQubitReducedEntropyTarget`. -/
structure PureTwoQubitConcurrenceEntropyCert where
  /-- (1) Concurrence is non-negative. -/
  concurrence_nonneg :
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ, 0 ≤ concurrence A
  /-- (2) Concurrence zero iff det zero. -/
  concurrence_zero_iff_det_zero :
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      concurrence A = 0 ↔ Matrix.det A = 0
  /-- (3) Reduced-density trace equals the Frobenius normalization. -/
  reduced_trace :
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      reducedDensity A 0 0 + reducedDensity A 1 1 =
        (frobeniusNormSq A : ℂ)
  /-- (4) Reduced-density determinant equals `C(A)^2 / 4`. -/
  reduced_det :
    ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      Matrix.det (reducedDensity A) = ((concurrence A) ^ 2 / 4 : ℝ)
  /-- (5) The concurrence spectral candidates have sum one and product `C²/4`. -/
  lambda_pair_sum_product :
    ∀ {C : ℝ}, 0 ≤ C → C ≤ 1 →
      lambdaPlus C + lambdaMinus C = 1 ∧
        lambdaPlus C * lambdaMinus C = C ^ 2 / 4
  /-- (6) Binary entropy is positive on (0, 1). -/
  binary_entropy_pos :
    ∀ {p : ℝ}, 0 < p → p < 1 → 0 < binaryEntropy p
  /-- (7) Inner radius lies in [1/2, 1) for 0 < C ≤ 1. -/
  inner_radius_in_unit_interval :
    ∀ {C : ℝ}, 0 < C → C ≤ 1 →
      (1 : ℝ) / 2 ≤ (1 + Real.sqrt (1 - C ^ 2)) / 2 ∧
        (1 + Real.sqrt (1 - C ^ 2)) / 2 < 1
  /-- (8) Unconditional entropy positivity. -/
  entropy_pos_unconditional :
    ∀ (A : Matrix (Fin 2) (Fin 2) ℂ)
      (_hNorm : (∑ i, ∑ j, Complex.normSq (A i j)) = 1)
      (_hC_pos : 0 < concurrence A),
      0 < reducedDensityVonNeumannEntropy A
  /-- (9) Canonical spectral entropy satisfies the reduced target. -/
  reduced_entropy_target :
    PureTwoQubitReducedEntropyTarget reducedDensityVonNeumannEntropy
  /-- (10) Conditional entropy positivity for abstract functionals. -/
  entropy_pos_conditional :
    ∀ {vonNeumannEntropy : Matrix (Fin 2) (Fin 2) ℂ → ℝ}
      (_hVN : PureTwoQubitReducedEntropyTarget vonNeumannEntropy)
      (A : Matrix (Fin 2) (Fin 2) ℂ)
      (_hNorm : (∑ i, ∑ j, Complex.normSq (A i j)) = 1)
      (_hC_pos : 0 < concurrence A) (_hC_le : concurrence A ≤ 1),
      0 < vonNeumannEntropy A

noncomputable def pureTwoQubitConcurrenceEntropyCert :
    PureTwoQubitConcurrenceEntropyCert where
  concurrence_nonneg := concurrence_nonneg
  concurrence_zero_iff_det_zero := concurrence_eq_zero_iff_det_zero
  reduced_trace := reducedDensity_trace_eq_frobenius
  reduced_det := reducedDensity_det_eq_concurrence_sq_div_four
  lambda_pair_sum_product := lambdaPair_sum_product_of_concurrence_unit_interval
  binary_entropy_pos := binaryEntropy_pos_of_open_unit_interval
  inner_radius_in_unit_interval :=
    inner_radius_in_unit_interval_of_pos_concurrence
  entropy_pos_unconditional := pure_two_qubit_entropy_positive_unconditional
  reduced_entropy_target := pureTwoQubitReducedEntropyTarget_holds
  entropy_pos_conditional :=
    pure_two_qubit_entropy_positive_of_concurrence_positive

theorem pureTwoQubitConcurrenceEntropyCert_inhabited :
    Nonempty PureTwoQubitConcurrenceEntropyCert :=
  ⟨pureTwoQubitConcurrenceEntropyCert⟩

end

end EntropyConcurrence
end PureTwoQubit
end Quantum
end IndisputableMonolith
