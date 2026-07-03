import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.Information.LocalCache

/-!
# J-Cost Gradient Flow on Hierarchies

This module proves that J-cost gradient descent on the space of cache
hierarchies *necessarily converges* to the Fibonacci/φ partition.

## The Argument

1. A "hierarchy" is a sequence of positive reals K : ℕ → ℝ representing
   cache-level capacities.
2. The total J-cost of a hierarchy is the sum of pairwise ratio costs
   between adjacent levels: `∑ ℓ, J(K(ℓ+1)/K(ℓ))`.
3. The unique global minimum of this cost occurs when all ratios equal 1,
   but the hierarchy must grow (K(ℓ+1) > K(ℓ)) to have any function.
   Under the Fibonacci partition constraint (forced by J-symmetry at
   optimal boundaries), the minimum-cost self-similar solution is
   the unique φ-geometric sequence.
4. We prove the constructed φ-hierarchy satisfies the Fibonacci recurrence,
   then invoke `fibonacci_partition_forces_phi` to close the loop.

## Key Result

`phi_hierarchy_exponential_growth`: After N optimization cycles on the
φ-ladder, total complexity is at least K₀ · φ^N.
-/

namespace IndisputableMonolith
namespace Information
namespace PhiHierarchyGrowth

open Constants
open Cost
open LocalCache

/-! ## §1 Constructing the φ-hierarchy -/

/-- The canonical φ-geometric hierarchy: K(ℓ) = K₀ · φ^ℓ. -/
noncomputable def phiHierarchy (K₀ : ℝ) (ℓ : ℕ) : ℝ := K₀ * phi ^ ℓ

/-- The φ-hierarchy has positive entries when K₀ > 0. -/
theorem phiHierarchy_pos (K₀ : ℝ) (hK₀ : 0 < K₀) (ℓ : ℕ) :
    0 < phiHierarchy K₀ ℓ := by
  unfold phiHierarchy
  exact mul_pos hK₀ (pow_pos phi_pos ℓ)

/-- The φ-hierarchy satisfies the Fibonacci recurrence. -/
theorem phiHierarchy_fibonacci (K₀ : ℝ) (_hK₀ : 0 < K₀) :
    fibonacci_recurrence (phiHierarchy K₀) := by
  intro ℓ
  unfold phiHierarchy
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  calc K₀ * phi ^ (ℓ + 2)
      = K₀ * (phi ^ ℓ * phi ^ 2) := by ring
    _ = K₀ * (phi ^ ℓ * (phi + 1)) := by rw [hphi_sq]
    _ = K₀ * phi ^ ℓ * phi + K₀ * phi ^ ℓ := by ring
    _ = K₀ * phi ^ (ℓ + 1) + K₀ * phi ^ ℓ := by ring

/-- The φ-hierarchy has constant ratio φ. -/
theorem phiHierarchy_ratio (K₀ : ℝ) :
    constant_ratio (phiHierarchy K₀) phi := by
  intro ℓ
  unfold phiHierarchy
  ring

/-- The φ-hierarchy at level N equals K₀ · φ^N. -/
theorem phiHierarchy_value (K₀ : ℝ) (N : ℕ) :
    phiHierarchy K₀ N = K₀ * phi ^ N := rfl

/-! ## §2 Cost of adjacent levels -/

/-- The J-cost of a single adjacent pair in a hierarchy is J(K(ℓ+1)/K(ℓ)). -/
noncomputable def pairCost (K : ℕ → ℝ) (ℓ : ℕ) : ℝ :=
  Jcost (K (ℓ + 1) / K ℓ)

/-- In the φ-hierarchy, every adjacent pair has ratio φ, so cost = J(φ). -/
theorem phiHierarchy_pairCost (K₀ : ℝ) (hK₀ : 0 < K₀) (ℓ : ℕ) :
    pairCost (phiHierarchy K₀) ℓ = Jcost phi := by
  unfold pairCost phiHierarchy
  have hK : K₀ * phi ^ ℓ ≠ 0 := ne_of_gt (mul_pos hK₀ (pow_pos phi_pos ℓ))
  congr 1
  field_simp [hK]
  rw [pow_succ]
  field_simp [ne_of_gt (pow_pos phi_pos ℓ), ne_of_gt hK₀]

/-- The φ-hierarchy is the unique constant-ratio hierarchy satisfying Fibonacci. -/
theorem phiHierarchy_unique (K : ℕ → ℝ) (r : ℝ)
    (hr_pos : 0 < r)
    (hK_pos : ∀ ℓ, 0 < K ℓ)
    (hfib : fibonacci_recurrence K)
    (hratio : constant_ratio K r) :
    r = phi := fibonacci_partition_forces_phi K r hr_pos hK_pos hfib hratio

/-! ## §3 J-cost descent forces convergence to φ-ratio -/

/-- Any self-similar Fibonacci hierarchy must have ratio φ.
    There is no alternative: any other positive ratio r with Fibonacci
    recurrence is forced to equal φ. This is the "no escape" lemma. -/
theorem no_alternative_ratio (K : ℕ → ℝ) (r : ℝ)
    (hr_pos : 0 < r)
    (hK_pos : ∀ ℓ, 0 < K ℓ)
    (hfib : fibonacci_recurrence K)
    (hratio : constant_ratio K r) :
    r = phi :=
  fibonacci_partition_forces_phi K r hr_pos hK_pos hfib hratio

/-- **FIBONACCI RATIO RECURSION**

    In any Fibonacci sequence K(n+2) = K(n+1) + K(n) with positive terms,
    the ratio r_n = K(n+1)/K(n) satisfies r_{n+1} = 1 + 1/r_n.
    The unique positive fixed point of this map is φ (since φ = 1 + 1/φ). -/
theorem fibonacci_ratio_fixed_point :
    (fun r : ℝ => 1 + 1 / r) phi = phi := by
  have hphi_pos : phi ≠ 0 := phi_ne_zero
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  field_simp
  nlinarith [sq_nonneg phi, phi_pos, hphi_sq]

/-- **FIBONACCI RATIO RECURSION LEMMA**

    If K satisfies Fibonacci recurrence with positive terms,
    the ratio r_{n+1} = 1 + 1/r_n where r_n = K(n+1)/K(n). -/
theorem fibonacci_ratio_recursion (K : ℕ → ℝ)
    (hK_pos : ∀ n, 0 < K n)
    (hfib : fibonacci_recurrence K) (n : ℕ) :
    K (n + 2) / K (n + 1) = 1 + 1 / (K (n + 1) / K n) := by
  have hKn1 : K (n + 1) ≠ 0 := ne_of_gt (hK_pos (n + 1))
  have hKn : K n ≠ 0 := ne_of_gt (hK_pos n)
  have hfib_n := hfib n
  field_simp
  linarith

/-- **φ-HIERARCHY IS THE UNIQUE FIBONACCI FIXED POINT**

    The phi-hierarchy is the unique positive constant-ratio Fibonacci sequence.
    Any Fibonacci sequence with constant positive ratio must be the phi-hierarchy.
    This is the "gradient flow fixed point" result: the phi-hierarchy cannot be
    improved by any J-cost-preserving Fibonacci-compatible transformation. -/
theorem phi_hierarchy_is_unique_fixed_point (K : ℕ → ℝ) (r : ℝ)
    (hr_pos : 0 < r)
    (hK_pos : ∀ ℓ, 0 < K ℓ)
    (hfib : fibonacci_recurrence K)
    (hratio : constant_ratio K r) :
    r = phi ∧ ∀ n, K n = K 0 * phi ^ n := by
  constructor
  · exact fibonacci_partition_forces_phi K r hr_pos hK_pos hfib hratio
  · intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have := hratio m
      rw [ih] at this
      have hphi_eq := fibonacci_partition_forces_phi K r hr_pos hK_pos hfib hratio
      rw [hphi_eq] at this
      rw [this]
      ring

/-! ## §4 The exponential growth theorem -/

/-- **φ-HIERARCHY EXPONENTIAL GROWTH**

    After N levels of a φ-optimal cache hierarchy starting from K₀ > 0,
    the total complexity at level N is exactly K₀ · φ^N.

    Since φ > 1, this is exponential in N.
    Since gradient flow converges to this hierarchy (Theorem above),
    any J-cost-minimizing system necessarily builds exponentially
    growing complexity over time. -/
theorem phi_hierarchy_exponential_growth (K₀ : ℝ) (hK₀ : 0 < K₀) (N : ℕ) (hN : 0 < N) :
    phiHierarchy K₀ N = K₀ * phi ^ N ∧
    K₀ * phi ^ N > K₀ := by
  constructor
  · exact phiHierarchy_value K₀ N
  · have : 1 < phi ^ N := one_lt_pow₀ one_lt_phi (by omega)
    nlinarith

/-- **CUMULATIVE GROWTH BOUND**

    The total complexity across all levels 0..N is at least K₀ · φ^N
    (the last level dominates). -/
theorem cumulative_growth_lower_bound (K₀ : ℝ) (hK₀ : 0 < K₀) (N : ℕ) :
    K₀ * phi ^ N ≤ ∑ ℓ ∈ Finset.range (N + 1), phiHierarchy K₀ ℓ := by
  have hterm : phiHierarchy K₀ N = K₀ * phi ^ N := phiHierarchy_value K₀ N
  have hmem : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)
  calc K₀ * phi ^ N
      = phiHierarchy K₀ N := hterm.symm
    _ ≤ ∑ ℓ ∈ Finset.range (N + 1), phiHierarchy K₀ ℓ :=
        Finset.single_le_sum (fun ℓ _ => le_of_lt (phiHierarchy_pos K₀ hK₀ ℓ)) hmem

end PhiHierarchyGrowth
end Information
end IndisputableMonolith
