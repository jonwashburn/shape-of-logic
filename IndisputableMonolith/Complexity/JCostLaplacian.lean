import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Complexity.RSatEncoding

/-!
# J-Cost Laplacian on the Boolean Hypercube

For a CNF formula φ on n variables, we define a weighted graph on the Boolean
hypercube {0,1}^n where:
- Vertices are assignments (Fin n → Bool)
- Edges connect Hamming-distance-1 assignments (single bit flip)
- Edge weight w(a, a') = |satJCost(φ, a) - satJCost(φ, a')|

The **J-cost Laplacian** is represented by its quadratic form:
  Q_J(x) = ½ Σ_a Σ_k w(a, flip(a,k)) · (x(a) - x(flip(a,k)))²

## Key Results

- `laplacian_form_nonneg` — PSD (Q_J ≥ 0)
- `laplacian_form_const_zero` — constants are in the kernel
- `jcostEdgeWeight_le_clauses` — edge weights bounded by clause count

## Status: 1 sorry (summand extraction lemma in zero-form implication)
-/

namespace IndisputableMonolith
namespace Complexity
namespace JCostLaplacian

open RSatEncoding

noncomputable section

/-! ## Boolean Hypercube Graph Structure -/

/-- Flip a single bit of an assignment. -/
def flipBit {n : ℕ} (a : Assignment n) (k : Fin n) : Assignment n :=
  fun j => if j = k then !a k else a j

theorem flipBit_flipBit {n : ℕ} (a : Assignment n) (k : Fin n) :
    flipBit (flipBit a k) k = a := by
  funext j; simp only [flipBit]
  split_ifs with h
  · subst h; simp
  · rfl

theorem flipBit_ne {n : ℕ} (a : Assignment n) (k : Fin n) :
    flipBit a k ≠ a := by
  intro h
  have : (flipBit a k) k = a k := congr_fun h k
  simp [flipBit] at this

/-! ## J-Cost Edge Weights -/

/-- The J-cost edge weight when flipping bit k. -/
def jcostEdgeWeight {n : ℕ} (f : CNFFormula n) (a : Assignment n) (k : Fin n) : ℝ :=
  |satJCost f a - satJCost f (flipBit a k)|

theorem jcostEdgeWeight_nonneg {n : ℕ} (f : CNFFormula n) (a : Assignment n)
    (k : Fin n) : 0 ≤ jcostEdgeWeight f a k :=
  abs_nonneg _

theorem jcostEdgeWeight_symm {n : ℕ} (f : CNFFormula n) (a : Assignment n)
    (k : Fin n) : jcostEdgeWeight f a k = jcostEdgeWeight f (flipBit a k) k := by
  unfold jcostEdgeWeight; rw [flipBit_flipBit]; exact (abs_sub_comm _ _).symm

theorem jcostEdgeWeight_le_clauses {n : ℕ} (f : CNFFormula n) (a : Assignment n)
    (k : Fin n) : jcostEdgeWeight f a k ≤ f.clauses.length := by
  unfold jcostEdgeWeight satJCost
  have h1 : (↑(f.clauses.filter (fun c => !c.satisfiedBy a)).length : ℝ) ≤
             ↑f.clauses.length := Nat.cast_le.mpr (List.length_filter_le _ _)
  have h2 : (↑(f.clauses.filter (fun c => !c.satisfiedBy (flipBit a k))).length : ℝ) ≤
             ↑f.clauses.length := Nat.cast_le.mpr (List.length_filter_le _ _)
  have h1nn : (0 : ℝ) ≤ ↑(f.clauses.filter (fun c => !c.satisfiedBy a)).length :=
    Nat.cast_nonneg _
  have h2nn : (0 : ℝ) ≤ ↑(f.clauses.filter
    (fun c => !c.satisfiedBy (flipBit a k))).length := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

/-! ## Tight Variable-Degree Bound -/

/-- Whether a clause contains a given variable (in any polarity). -/
def containsVar {n : ℕ} (c : Clause n) (j : Fin n) : Bool :=
  c.literals.any (fun lit => lit.1 == j)

/-- The variable degree: number of clauses containing variable j. -/
def varDegree {n : ℕ} (f : CNFFormula n) (j : Fin n) : ℕ :=
  (f.clauses.filter (fun c => containsVar c j)).length

/-- Flipping bit j does not change the value at any other index. -/
theorem flipBit_other {n : ℕ} (a : Assignment n) (j : Fin n) (i : Fin n) (hij : i ≠ j) :
    flipBit a j i = a i := by
  simp [flipBit, hij]

/-- A literal not involving variable j has the same truth value after flipping j. -/
theorem literal_unchanged_by_flip {n : ℕ} (a : Assignment n) (j : Fin n)
    (lit : Fin n × Bool) (hlit : lit.1 ≠ j) :
    Literal.satisfiedBy lit (flipBit a j) = Literal.satisfiedBy lit a := by
  unfold Literal.satisfiedBy
  rw [flipBit_other a j lit.1 hlit]

/-- A clause not containing variable j has the same satisfaction after flipping j. -/
theorem clause_unchanged_by_flip {n : ℕ} (a : Assignment n) (j : Fin n)
    (c : Clause n) (hc : containsVar c j = false) :
    c.satisfiedBy (flipBit a j) = c.satisfiedBy a := by
  have hne : ∀ lit ∈ c.literals, lit.fst ≠ j := by
    intro lit hmem heq
    unfold containsVar at hc
    have : c.literals.any (fun l => l.1 == j) = true :=
      List.any_eq_true.mpr ⟨lit, hmem, by rw [beq_iff_eq]; exact heq⟩
    rw [hc] at this; exact absurd this Bool.false_ne_true
  apply Bool.eq_iff_iff.mpr
  unfold Clause.satisfiedBy
  rw [List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨l, hm, hs⟩ => ⟨l, hm, by rw [← literal_unchanged_by_flip a j l (hne l hm)]; exact hs⟩,
         fun ⟨l, hm, hs⟩ => ⟨l, hm, by rw [literal_unchanged_by_flip a j l (hne l hm)]; exact hs⟩⟩

/-- The J-cost edge weight is bounded by the variable degree.
    Flipping bit j can only change clauses that contain variable j.
    Clauses not containing j have identical satisfaction (by `clause_unchanged_by_flip`),
    so only clauses containing j contribute to the cost difference.

    The formal discharge requires a list-filter symmetric difference counting lemma:
    for predicates P, Q agreeing outside a subset S,
    |filter(P).length - filter(Q).length| ≤ S.length. Recorded as a named proposition. -/
def jcostEdgeWeight_le_varDegree_prop {n : ℕ} (f : CNFFormula n) (a : Assignment n)
    (j : Fin n) : Prop :=
  jcostEdgeWeight f a j ≤ varDegree f j

/-! ## J-Cost Weighted Degree -/

def jcostDegree {n : ℕ} (f : CNFFormula n) (a : Assignment n) : ℝ :=
  Finset.univ.sum (fun k : Fin n => jcostEdgeWeight f a k)

theorem jcostDegree_nonneg {n : ℕ} (f : CNFFormula n) (a : Assignment n) :
    0 ≤ jcostDegree f a :=
  Finset.sum_nonneg (fun k _ => jcostEdgeWeight_nonneg f a k)

/-! ## J-Cost Laplacian Quadratic Form -/

/-- The J-cost Laplacian quadratic form on (Fin n → Bool) → ℝ.
    Q_J(x) = ½ Σ_a Σ_k w(a, flip(a,k)) · (x(a) - x(flip(a,k)))² -/
def JCostLaplacianForm {n : ℕ} (f : CNFFormula n)
    (x : (Fin n → Bool) → ℝ) : ℝ :=
  (1/2 : ℝ) * Finset.univ.sum (fun a : Fin n → Bool =>
    Finset.univ.sum (fun k : Fin n =>
      jcostEdgeWeight f a k * (x a - x (flipBit a k))^2))

/-- **PSD: The J-cost Laplacian form is non-negative.** -/
theorem laplacian_form_nonneg {n : ℕ} (f : CNFFormula n) (x : (Fin n → Bool) → ℝ) :
    0 ≤ JCostLaplacianForm f x := by
  unfold JCostLaplacianForm
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro k _
  exact mul_nonneg (jcostEdgeWeight_nonneg f a k) (sq_nonneg _)

/-- **Constants are in the kernel.** -/
theorem laplacian_form_const_zero {n : ℕ} (f : CNFFormula n) (c : ℝ) :
    JCostLaplacianForm f (fun _ => c) = 0 := by
  unfold JCostLaplacianForm
  norm_num

/-- **Zero form implies constant on positive-weight edges.**
    If Q_J(x) = 0, then for every (a, k) with positive weight, x(a) = x(flip(a,k)). -/
theorem laplacian_form_zero_imp {n : ℕ} (f : CNFFormula n) (x : (Fin n → Bool) → ℝ)
    (hzero : JCostLaplacianForm f x = 0) :
    ∀ (a : Fin n → Bool) (k : Fin n),
      0 < jcostEdgeWeight f a k → x a = x (flipBit a k) := by
  intro a k hpos
  unfold JCostLaplacianForm at hzero
  -- Step 1: ½ · S = 0 with S ≥ 0 implies S = 0
  have hS_nonneg : 0 ≤ Finset.univ.sum (fun a : Fin n → Bool =>
      Finset.univ.sum (fun k : Fin n =>
        jcostEdgeWeight f a k * (x a - x (flipBit a k))^2)) := by
    apply Finset.sum_nonneg; intro a' _
    apply Finset.sum_nonneg; intro k' _
    exact mul_nonneg (jcostEdgeWeight_nonneg f a' k') (sq_nonneg _)
  have hS_zero : Finset.univ.sum (fun a : Fin n → Bool =>
      Finset.univ.sum (fun k : Fin n =>
        jcostEdgeWeight f a k * (x a - x (flipBit a k))^2)) = 0 := by
    nlinarith [hS_nonneg]
  -- Step 2: outer sum = 0 with all inner sums ≥ 0 → the a-th inner sum = 0
  have hInner_nonneg : ∀ a' : Fin n → Bool, 0 ≤ Finset.univ.sum (fun k' : Fin n =>
      jcostEdgeWeight f a' k' * (x a' - x (flipBit a' k'))^2) := by
    intro a'; apply Finset.sum_nonneg; intro k' _
    exact mul_nonneg (jcostEdgeWeight_nonneg f a' k') (sq_nonneg _)
  have hInner_zero := Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => hInner_nonneg a')
    |>.mp hS_zero a (Finset.mem_univ a)
  -- Step 3: inner sum = 0 with all terms ≥ 0 → the k-th term = 0
  have hTerm_nonneg : ∀ k' : Fin n, 0 ≤
      jcostEdgeWeight f a k' * (x a - x (flipBit a k'))^2 := by
    intro k'; exact mul_nonneg (jcostEdgeWeight_nonneg f a k') (sq_nonneg _)
  have hTerm_zero := Finset.sum_eq_zero_iff_of_nonneg (fun k' _ => hTerm_nonneg k')
    |>.mp hInner_zero k (Finset.mem_univ k)
  -- Step 4: w · d² = 0 with w > 0 → d² = 0 → d = 0
  have hd_sq_zero : (x a - x (flipBit a k))^2 = 0 := by
    rcases mul_eq_zero.mp hTerm_zero with hw | hd
    · linarith
    · exact hd
  have hd_zero : x a - x (flipBit a k) = 0 := by
    exact_mod_cast sq_eq_zero_iff.mp hd_sq_zero
  linarith

/-! ## Cost Landscape Connectivity -/

/-- Two assignments are cost-connected if there is a path through positive-weight edges. -/
inductive CostConnected {n : ℕ} (f : CNFFormula n) :
    (Fin n → Bool) → (Fin n → Bool) → Prop
  | refl (a) : CostConnected f a a
  | step (a : Fin n → Bool) (k : Fin n) (hpos : 0 < jcostEdgeWeight f a k)
      {c} (hrest : CostConnected f (flipBit a k) c) : CostConnected f a c

/-- Cost-connectivity is reflexive. -/
theorem costConnected_refl {n : ℕ} (f : CNFFormula n) (a : Fin n → Bool) :
    CostConnected f a a := CostConnected.refl a

/-! ## Certificate -/

structure JCostLaplacianCert where
  psd : ∀ (n : ℕ) (f : CNFFormula n) (x : (Fin n → Bool) → ℝ),
    0 ≤ JCostLaplacianForm f x
  const_kernel : ∀ (n : ℕ) (f : CNFFormula n) (c : ℝ),
    JCostLaplacianForm f (fun _ => c) = 0
  weights_nonneg : ∀ (n : ℕ) (f : CNFFormula n) (a : Fin n → Bool) (k : Fin n),
    0 ≤ jcostEdgeWeight f a k
  weights_bounded : ∀ (n : ℕ) (f : CNFFormula n) (a : Fin n → Bool) (k : Fin n),
    jcostEdgeWeight f a k ≤ f.clauses.length

def jcostLaplacianCert : JCostLaplacianCert where
  psd := fun n f x => laplacian_form_nonneg f x
  const_kernel := fun n f c => laplacian_form_const_zero f c
  weights_nonneg := fun n f a k => jcostEdgeWeight_nonneg f a k
  weights_bounded := fun n f a k => jcostEdgeWeight_le_clauses f a k

end -- noncomputable section

end JCostLaplacian
end Complexity
end IndisputableMonolith
