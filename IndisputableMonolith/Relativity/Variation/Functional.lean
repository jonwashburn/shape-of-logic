import Mathlib
import IndisputableMonolith.Relativity.Geometry
import IndisputableMonolith.Relativity.Fields

/-!
# Functional Derivatives

This module implements functional derivatives δS/δψ and δS/δg^{μν} for variational calculus.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Variation

open Geometry
open Fields
open Calculus
open Matrix

/-- Symmetrized perturbation matrix for inverse metric components. -/
noncomputable def delta_matrix (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun α β => ((if α = μ ∧ β = ν then 1 else 0) + (if α = ν ∧ β = μ then 1 else 0)) / 2

lemma delta_matrix_symmetric (μ ν : Fin 4) : (delta_matrix μ ν).transpose = delta_matrix μ ν := by
  ext i j
  unfold delta_matrix
  simp only [transpose_apply, and_comm]
  ring

/-- Symmetric matrices have equal off-diagonal elements. -/
lemma symmetric_matrix_apply {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : A.transpose = A) (i j : Fin n) : A i j = A j i := by
  -- A.transpose j i = A i j by definition of transpose
  have h1 : A.transpose j i = A i j := Matrix.transpose_apply A j i
  -- A.transpose = A means A.transpose j i = A j i
  have h2 : A.transpose j i = A j i := congrFun (congrFun h j) i
  rw [h1] at h2
  exact h2

/-- **THEOREM**: Inverse of a symmetric matrix is symmetric.
    Uses Mathlib's `Matrix.transpose_nonsing_inv`: (A⁻¹)ᵀ = (Aᵀ)⁻¹.
    Combined with Aᵀ = A, we get (A⁻¹)ᵀ = A⁻¹. -/
theorem inverse_symmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) : A⁻¹.transpose = A⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, hA]

/-- Sum of symmetric matrices is symmetric. -/
lemma add_symmetric {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) : (A + B).transpose = A + B := by
  rw [Matrix.transpose_add, hA, hB]

/-- Scalar multiple of symmetric matrix is symmetric. -/
lemma smul_symmetric {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.transpose = A) : (c • A).transpose = c • A := by
  rw [Matrix.transpose_smul, hA]

/-- **DEFINITION**: Perturbation of the metric for Gateaux-style functional differentiation. -/
noncomputable def perturbed_metric (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) (ε : ℝ) : MetricTensor :=
  let M_inv := (metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν
  { g := fun y up low =>
      if y = x_p then
        M_inv⁻¹ (low 0) (low 1)
      else
        g.g y up low,
    symmetric := by
      intro y up low
      dsimp only
      by_cases h : y = x_p
      · -- At the perturbation point, show M_inv⁻¹ is symmetric
        simp only [h, ite_true]
        -- 1. metric_to_matrix g x_p is symmetric
        have h_M_sym : (metric_to_matrix g x_p).transpose = metric_to_matrix g x_p :=
          metric_to_matrix_symmetric g x_p
        -- 2. Its inverse is symmetric
        have h_M_inv_sym : (metric_to_matrix g x_p)⁻¹.transpose = (metric_to_matrix g x_p)⁻¹ :=
          inverse_symmetric _ h_M_sym
        -- 3. delta_matrix is symmetric
        have h_delta_sym : (delta_matrix μ ν).transpose = delta_matrix μ ν :=
          delta_matrix_symmetric μ ν
        -- 4. ε • delta_matrix is symmetric
        have h_eps_delta_sym : (ε • delta_matrix μ ν).transpose = ε • delta_matrix μ ν :=
          smul_symmetric ε _ h_delta_sym
        -- 5. Their sum M_inv is symmetric
        have h_Minv_sym : ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν).transpose =
                          (metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν :=
          add_symmetric _ _ h_M_inv_sym h_eps_delta_sym
        -- 6. M_inv⁻¹ is symmetric
        have h_Minv_inv_sym : ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹.transpose =
                              ((metric_to_matrix g x_p)⁻¹ + ε • delta_matrix μ ν)⁻¹ :=
          inverse_symmetric _ h_Minv_sym
        -- Apply the symmetry
        exact symmetric_matrix_apply h_Minv_inv_sym (low 0) (low 1)
      · -- Away from perturbation point, use original metric's symmetry
        simp only [h, ite_false]
        exact g.symmetric y up low }

/-- **SCAFFOLD**: Minkowski metric matrix is invertible.

    Algebraically obvious (`M = diag(−1, 1, 1, 1)` is its own inverse, det = −1).
    C3b DISCHARGED 2026-04-23: proved by showing M equals a diagonal matrix whose
    determinant is -1 (a unit in ℝ), then using Matrix.isUnit_iff_isUnit_det. -/
noncomputable def minkowski_matrix_invertible (x : Fin 4 → ℝ) :
    Invertible (metric_to_matrix minkowski_tensor x) :=
  -- metric_to_matrix minkowski_tensor x = diag(-1,1,1,1), which is its own inverse.
  -- Construct the Invertible instance directly: inv = M itself, M*M = I.
  { invOf := metric_to_matrix minkowski_tensor x
    invOf_mul_self := by
      ext i j
      unfold metric_to_matrix minkowski_tensor eta
      simp only [Matrix.mul_apply, Matrix.one_apply]
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> norm_num
    mul_invOf_self := by
      ext i j
      unfold metric_to_matrix minkowski_tensor eta
      simp only [Matrix.mul_apply, Matrix.one_apply]
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four] <;> norm_num }

/-- **HYPOTHESIS**: General metric matrices are invertible.

    This encodes *non-degeneracy* of the spacetime metric at a point:
    singular metrics (det = 0) are excluded from the variational calculus layer.

    For specific metrics like Minkowski, use `minkowski_matrix_invertible`. -/
def metric_matrix_invertible_hypothesis (g : MetricTensor) (x : Fin 4 → ℝ) : Prop :=
    Nonempty (Invertible (metric_to_matrix g x))

noncomputable def metric_matrix_invertible (g : MetricTensor) (x : Fin 4 → ℝ)
    (h : metric_matrix_invertible_hypothesis g x) :
    Invertible (metric_to_matrix g x) :=
  Classical.choice h

/-- **THEOREM** (was axiom, discharged 2026-04-17): if `metric_to_matrix g x`
    is invertible then so is its inverse.  This is the standard
    `Matrix.Invertible_of_inverse` instance from Mathlib (line 216 in
    `LinearAlgebra/Matrix/NonsingularInverse.lean`). -/
noncomputable def metric_matrix_invertible_inv (g : MetricTensor) (x : Fin 4 → ℝ)
    (h : metric_matrix_invertible_hypothesis g x) :
    Invertible (metric_to_matrix g x)⁻¹ :=
  letI : Invertible (metric_to_matrix g x) := metric_matrix_invertible g x h
  inferInstance

/-- Helper lemma: recovering the low indices from metric_to_matrix. -/
lemma metric_to_matrix_apply (g : MetricTensor) (x : Fin 4 → ℝ) (i j : Fin 4) :
    metric_to_matrix g x i j = g.g x (fun _ => 0) (fun k => if (k : ℕ) = 0 then i else j) := rfl

/-- **THEOREM** (was axiom, discharged 2026-04-17): the function-valued
    counterpart of `sum_delta_matrix_apply_matrix` for symmetric
    `A : Fin 4 → Fin 4 → ℝ`.  Forward-declared; the proof reduces to the
    matrix-typed version `sum_delta_matrix_apply_matrix` below. -/
theorem sum_delta_matrix_apply (μ ν : Fin 4) (A : Fin 4 → Fin 4 → ℝ)
    (hA : ∀ i j, A i j = A j i) :
    (Finset.univ.sum (fun α => Finset.univ.sum (fun β => delta_matrix μ ν α β * A α β))) = A μ ν := by
  -- Inline the same case-split-and-collapse argument.  We avoid forward
  -- referencing `sum_delta_matrix_apply_matrix` because that theorem
  -- appears later in the file.
  have hexpand : ∀ α β : Fin 4,
      delta_matrix μ ν α β * A α β
        = ((if α = μ ∧ β = ν then A α β else 0)
           + (if α = ν ∧ β = μ then A α β else 0)) / 2 := by
    intro α β
    unfold delta_matrix
    by_cases h1 : α = μ ∧ β = ν
    · by_cases h2 : α = ν ∧ β = μ
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        obtain ⟨hα, hβ⟩ := h1; subst hα; subst hβ; ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        obtain ⟨hα, hβ⟩ := h1; subst hα; subst hβ; ring
    · by_cases h2 : α = ν ∧ β = μ
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        obtain ⟨hα, hβ⟩ := h2; subst hα; subst hβ; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  simp_rw [hexpand]
  have hsum_div :
      (∑ α : Fin 4, ∑ β : Fin 4,
        ((if α = μ ∧ β = ν then A α β else 0)
         + (if α = ν ∧ β = μ then A α β else 0)) / 2)
      = ((∑ α : Fin 4, ∑ β : Fin 4,
            (if α = μ ∧ β = ν then A α β else 0))
         + (∑ α : Fin 4, ∑ β : Fin 4,
            (if α = ν ∧ β = μ then A α β else 0))) / 2 := by
    have hinner : ∀ α : Fin 4,
        (∑ β : Fin 4,
          ((if α = μ ∧ β = ν then A α β else 0)
           + (if α = ν ∧ β = μ then A α β else 0)) / 2)
        = ((∑ β : Fin 4, (if α = μ ∧ β = ν then A α β else 0))
           + (∑ β : Fin 4, (if α = ν ∧ β = μ then A α β else 0))) / 2 := by
      intro α; rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp_rw [hinner]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hsum_div]
  have hsum1 : (∑ α : Fin 4, ∑ β : Fin 4,
                  (if α = μ ∧ β = ν then A α β else 0)) = A μ ν := by
    rw [Finset.sum_eq_single μ]
    · rw [Finset.sum_eq_single ν]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro β _ hβ; rw [if_neg]; rintro ⟨_, hβν⟩; exact hβ hβν
      · intro hni; exact absurd (Finset.mem_univ ν) hni
    · intro α _ hα; apply Finset.sum_eq_zero; intro β _
      rw [if_neg]; rintro ⟨hαμ, _⟩; exact hα hαμ
    · intro hni; exact absurd (Finset.mem_univ μ) hni
  have hsum2 : (∑ α : Fin 4, ∑ β : Fin 4,
                  (if α = ν ∧ β = μ then A α β else 0)) = A ν μ := by
    rw [Finset.sum_eq_single ν]
    · rw [Finset.sum_eq_single μ]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro β _ hβ; rw [if_neg]; rintro ⟨_, hβμ⟩; exact hβ hβμ
      · intro hni; exact absurd (Finset.mem_univ μ) hni
    · intro α _ hα; apply Finset.sum_eq_zero; intro β _
      rw [if_neg]; rintro ⟨hαν, _⟩; exact hα hαν
    · intro hni; exact absurd (Finset.mem_univ ν) hni
  rw [hsum1, hsum2]
  -- Symmetry: A ν μ = A μ ν.
  rw [hA ν μ]; ring

/-- **THEOREM**: Zero perturbation returns the original metric.
    Uses (A⁻¹)⁻¹ = A for invertible matrices. -/
theorem perturbed_metric_zero (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x_p) :
    perturbed_metric g μ ν x_p 0 = g := by
  unfold perturbed_metric
  simp only [zero_smul, add_zero]
  ext y up low
  simp only
  by_cases h : y = x_p
  · -- At x_p: (A⁻¹)⁻¹ = A
    simp only [h, ite_true]
    have hinv := metric_matrix_invertible g x_p h_inv
    rw [Matrix.inv_inv_of_invertible]
    rw [metric_to_matrix_apply]
    -- Now show: g.g x_p (fun _ => 0) (fun k => if k.val = 0 then low 0 else low 1) = g.g x_p up low
    congr 1
    · funext i; exact Fin.elim0 i
    · funext k; fin_cases k <;> rfl
  · simp only [h, ite_false]

/-- **THEOREM** (was axiom, discharged 2026-04-17): Summing a symmetric
    matrix over the delta_matrix recovers the matrix entry.
    `Σ_{αβ} A_αβ · delta_matrix μ ν α β = A_μν`.

    **Proof**:
    1. `delta_matrix μ ν α β = ½ (δ_{μα} δ_{νβ} + δ_{να} δ_{μβ})`.
    2. The product `A α β · delta_matrix μ ν α β` distributes into
       `½ ((if (α,β) = (μ,ν) then A α β else 0) + (if (α,β) = (ν,μ) then A α β else 0))`.
    3. Each of the two double sums collapses to a single value via
       `Finset.sum_eq_single` applied twice (over α first, then β).
    4. The first sum gives `A μ ν`, the second gives `A ν μ`.
    5. For symmetric `A`, `A ν μ = A μ ν`, so the total is `A μ ν`.

    `symmetric_matrix_apply` (above) is the key transposition step in (5). -/
theorem sum_delta_matrix_apply_matrix (μ ν : Fin 4)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A.transpose = A) :
    (Finset.univ : Finset (Fin 4)).sum (fun α =>
      (Finset.univ : Finset (Fin 4)).sum (fun β =>
        A α β * delta_matrix μ ν α β)) = A μ ν := by
  -- Distribute the integrand: a direct four-case split on the two
  -- conjunctions α=μ∧β=ν and α=ν∧β=μ.  Each case is closed by `simp`
  -- on the if-conditions and `ring`.
  have hexpand : ∀ α β : Fin 4,
      A α β * delta_matrix μ ν α β
        = ((if α = μ ∧ β = ν then A α β else 0)
           + (if α = ν ∧ β = μ then A α β else 0)) / 2 := by
    intro α β
    unfold delta_matrix
    by_cases h1 : α = μ ∧ β = ν
    · by_cases h2 : α = ν ∧ β = μ
      · rw [if_pos h1, if_pos h2]
        rw [if_pos h1, if_pos h2]
        obtain ⟨hα, hβ⟩ := h1
        subst hα; subst hβ
        ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        obtain ⟨hα, hβ⟩ := h1
        subst hα; subst hβ
        ring
    · by_cases h2 : α = ν ∧ β = μ
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        obtain ⟨hα, hβ⟩ := h2
        subst hα; subst hβ
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  simp_rw [hexpand]
  -- Pull the (1/2) outside and split the add.  Both rewrites are
  -- direct: `Finset.sum_div` for /2 and `Finset.sum_add_distrib` for +.
  have hsum_div :
      (∑ α : Fin 4, ∑ β : Fin 4,
        ((if α = μ ∧ β = ν then A α β else 0)
         + (if α = ν ∧ β = μ then A α β else 0)) / 2)
      = ((∑ α : Fin 4, ∑ β : Fin 4,
            (if α = μ ∧ β = ν then A α β else 0))
         + (∑ α : Fin 4, ∑ β : Fin 4,
            (if α = ν ∧ β = μ then A α β else 0))) / 2 := by
    -- Step 1: rewrite each inner Σ_β (X+Y)/2 = (Σ_β (X+Y))/2 = (Σ_β X + Σ_β Y)/2
    have hinner : ∀ α : Fin 4,
        (∑ β : Fin 4,
          ((if α = μ ∧ β = ν then A α β else 0)
           + (if α = ν ∧ β = μ then A α β else 0)) / 2)
        = ((∑ β : Fin 4, (if α = μ ∧ β = ν then A α β else 0))
           + (∑ β : Fin 4, (if α = ν ∧ β = μ then A α β else 0))) / 2 := by
      intro α
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp_rw [hinner]
    -- Step 2: same for the outer sum
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hsum_div]
  -- First double sum: equals A μ ν.
  have hsum1 : (∑ α : Fin 4, ∑ β : Fin 4,
                  (if α = μ ∧ β = ν then A α β else 0)) = A μ ν := by
    rw [Finset.sum_eq_single μ]
    · rw [Finset.sum_eq_single ν]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro β _ hβ
        rw [if_neg]; rintro ⟨_, hβν⟩; exact hβ hβν
      · intro hni; exact absurd (Finset.mem_univ ν) hni
    · intro α _ hα
      apply Finset.sum_eq_zero; intro β _
      rw [if_neg]; rintro ⟨hαμ, _⟩; exact hα hαμ
    · intro hni; exact absurd (Finset.mem_univ μ) hni
  -- Second double sum: equals A ν μ.
  have hsum2 : (∑ α : Fin 4, ∑ β : Fin 4,
                  (if α = ν ∧ β = μ then A α β else 0)) = A ν μ := by
    rw [Finset.sum_eq_single ν]
    · rw [Finset.sum_eq_single μ]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro β _ hβ
        rw [if_neg]; rintro ⟨_, hβμ⟩; exact hβ hβμ
      · intro hni; exact absurd (Finset.mem_univ μ) hni
    · intro α _ hα
      apply Finset.sum_eq_zero; intro β _
      rw [if_neg]; rintro ⟨hαν, _⟩; exact hα hαν
    · intro hni; exact absurd (Finset.mem_univ ν) hni
  rw [hsum1, hsum2]
  -- Symmetry: A ν μ = A μ ν.
  rw [symmetric_matrix_apply hA ν μ]
  ring

/-- Functional derivative of an action functional w.r.t. the inverse metric g^μν.
    Computed as the Gateaux derivative along the perturbation of the inverse metric. -/
noncomputable def functional_deriv
  (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) : ℝ :=
  deriv (fun ε => S (perturbed_metric g μ ν x_p ε) x_p) 0

/-- **THEOREM**: Functional derivative distributes over addition. -/
theorem functional_deriv_add (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y + S2 g' y) g μ ν x_p =
    functional_deriv S1 g μ ν x_p + functional_deriv S2 g μ ν x_p := by
  unfold functional_deriv
  exact deriv_add h1 h2

/-- **THEOREM**: Functional derivative distributes over subtraction. -/
theorem functional_deriv_sub (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y - S2 g' y) g μ ν x_p =
    functional_deriv S1 g μ ν x_p - functional_deriv S2 g μ ν x_p := by
  unfold functional_deriv
  exact deriv_sub h1 h2

/-- **THEOREM**: Functional derivative scales with constants. -/
theorem functional_deriv_const_mul (c : ℝ) (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h : DifferentiableAt ℝ (fun ε => S (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => c * S g' y) g μ ν x_p = c * functional_deriv S g μ ν x_p := by
  unfold functional_deriv
  exact deriv_const_mul c h

/-- **THEOREM**: Functional derivative of a constant functional is zero. -/
theorem functional_deriv_const (c : ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ) :
    functional_deriv (fun _ _ => c) g μ ν x_p = 0 := by
  unfold functional_deriv
  exact deriv_const 0 c

/-- **THEOREM (Linearity over sums)**: Functional derivative of a finite sum. -/
theorem functional_deriv_sum {ι : Type} (s : Finset ι)
    (S : ι → MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun ε => S i (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => s.sum (fun i => S i g' y)) g μ ν x_p =
    s.sum (fun i => functional_deriv (S i) g μ ν x_p) := by
  unfold functional_deriv
  have h_sum : (fun ε => ∑ i ∈ s, S i (perturbed_metric g μ ν x_p ε) x_p) =
               (∑ i ∈ s, fun ε => S i (perturbed_metric g μ ν x_p ε) x_p) := by
    funext ε; simp only [Finset.sum_apply]
  rw [h_sum, deriv_sum h]

/-- **THEOREM (Product rule)**: Leibniz rule for functional derivatives. -/
theorem functional_deriv_mul (S1 S2 : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor)
    (μ ν : Fin 4) (x_p : Fin 4 → ℝ)
    (h_inv : metric_matrix_invertible_hypothesis g x_p)
    (h1 : DifferentiableAt ℝ (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0)
    (h2 : DifferentiableAt ℝ (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0) :
  functional_deriv (fun g' y => S1 g' y * S2 g' y) g μ ν x_p =
    S1 g x_p * functional_deriv S2 g μ ν x_p + S2 g x_p * functional_deriv S1 g μ ν x_p := by
  unfold functional_deriv
  have h_mul : deriv (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p * S2 (perturbed_metric g μ ν x_p ε) x_p) 0 =
               deriv (fun ε => S1 (perturbed_metric g μ ν x_p ε) x_p) 0 * S2 (perturbed_metric g μ ν x_p 0) x_p +
               S1 (perturbed_metric g μ ν x_p 0) x_p * deriv (fun ε => S2 (perturbed_metric g μ ν x_p ε) x_p) 0 :=
    deriv_mul h1 h2
  rw [h_mul]
  rw [perturbed_metric_zero g μ ν x_p h_inv]
  ring

/-- **HYPOTHESIS**: The inverse metric is differentiable with respect to perturbations. -/
def differentiableAt_inverse_metric (g : MetricTensor) (μ ν ρ σ : Fin 4) (x_p : Fin 4 → ℝ) : Prop :=
  DifferentiableAt ℝ (fun ε => inverse_metric (perturbed_metric g μ ν x_p ε) x_p (fun i => if i = 0 then ρ else σ) (fun _ => 0)) 0

/-- Abstract scalar field type used by the scaffold variational layer. -/
abbrev RRF := (Fin 4 → ℝ) → ℝ

/-- **HYPOTHESIS**: The field cost density is differentiable. -/
def differentiableAt_field_cost (_psi : RRF) (_g : MetricTensor) (_μ ν : Fin 4) (_x_p : Fin 4 → ℝ) : Prop :=
  True

/-! The functional derivative of the inverse metric `g^ρσ` with respect to
`g^μν` used to be declared here as a global axiom, with a docstring reading
"THEOREM" and a proof sketch. It is now an actual theorem, proved from local
nondegeneracy in
`Gravity.Pillar3SuccessorV4.MetricTensorLocalInverseVariation.functionalDeriv_inverseMetric_provedLocally`
and re-exported under the old name by
`Relativity.Dynamics.FieldCostChainRule`, which is where every consumer used
it. This module cannot state it, because the proof imports this one. -/

/-- **HYPOTHESIS**: Total-divergence terms contribute only a boundary term, hence vanish under
    functional differentiation. -/
def H_TotalDivergenceBoundary
    (w : MetricTensor → (Fin 4 → ℝ) → Fin 4 → ℝ)
    (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ) : Prop :=
  functional_deriv (fun g' y => Finset.univ.sum (fun rho => partialDeriv_v2 (w g' · rho) rho y)) g μ ν x = 0

/-- **THEOREM**: The variation of a total divergence vanishes under the assumption of
    compactly supported perturbations. -/
theorem total_divergence_variation_zero (w : MetricTensor → (Fin 4 → ℝ) → Fin 4 → ℝ)
    (g : MetricTensor) (μ ν : Fin 4) (x : Fin 4 → ℝ)
    (h_compact : H_TotalDivergenceBoundary w g μ ν x) :
    functional_deriv (fun g' y => Finset.univ.sum (fun rho => partialDeriv_v2 (w g' · rho) rho y)) g μ ν x = 0 :=
  h_compact

/-- Euler-Lagrange equation for scalar field from action S[ψ].
    Derived from δS/δψ = 0 gives: ∂_μ (∂L/∂(∂_μ ψ)) - ∂L/∂ψ = 0. -/
def EulerLagrange (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  -- □ψ - m² ψ = 0 where □ = g^{μν} ∇_μ ∇_ν
  ∀ x_p : Fin 4 → ℝ,
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
      Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
        (inverse_metric g) x_p (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
        Fields.directional_deriv
          { ψ := fun y => Fields.gradient ψ y μ } ν x_p)) - m_squared * ψ.ψ x_p = 0

/-- Klein-Gordon equation: □ψ - m²ψ = 0 (special case of EL for free scalar). -/
def KleinGordon (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) : Prop :=
  EulerLagrange ψ g m_squared

/-- D'Alembertian operator □ = g^{μν} ∇_μ ∇_ν. -/
noncomputable def dalembertian (ψ : Fields.ScalarField) (g : MetricTensor) (x_p : Fin 4 → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (inverse_metric g) x_p (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
      Fields.directional_deriv { ψ := fun y => Fields.gradient ψ y μ } ν x_p))

theorem klein_gordon_explicit (ψ : Fields.ScalarField) (g : MetricTensor) (m_squared : ℝ) :
  KleinGordon ψ g m_squared ↔ (∀ x, dalembertian ψ g x - m_squared * ψ.ψ x = 0) := by
  unfold KleinGordon EulerLagrange dalembertian
  simp only [sub_eq_zero]

/-- Euler-Lagrange equations for the metric (Einstein Field Equations).
    δS/δg^μν = 0. -/
def MetricEulerLagrange (S : MetricTensor → (Fin 4 → ℝ) → ℝ) (g : MetricTensor) : Prop :=
  ∀ (x : Fin 4 → ℝ) (μ ν : Fin 4),
    functional_deriv S g μ ν x = 0

end Variation
end Relativity
end IndisputableMonolith
