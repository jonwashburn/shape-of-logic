import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DiscretenessForcing
import IndisputableMonolith.NumberTheory.ZeroLocationCost
import IndisputableMonolith.NumberTheory.XiJBridge

/-!
# The Composition Law for Zeta Zeros

## The Core Discovery

The Recognition Composition Law (RCL) — the unique functional equation
satisfied by J(x) = ½(x + x⁻¹) − 1 — induces a **composition law on
zeta zero defects**.

Given a nontrivial zero ρ of ζ(s) with deviation η = Re(ρ) − 1/2, define:

  d₀ = J(e^{2η}) = cosh(2η) − 1

The functional equation ξ(s) = ξ(1−s) pairs ρ with 1−ρ. Applying the
RCL to this pair yields a **self-composition** that amplifies defect:

  d₁ = J(e^{4η}) = cosh(4η) − 1 = 2d₀(d₀ + 2)

Iterating:

  dₙ = cosh(2ⁿ⁺¹η) − 1,    dₙ₊₁ = 2dₙ(dₙ + 2)

This is the **composition law for zeta zeros**: the RCL forces each
off-critical zero to generate a cascade of exponentially growing defect.

## Main Results

1. `defectIterate_succ`: the recurrence dₙ₊₁ = 2dₙ(dₙ+2) from RCL
2. `defectIterate_four_mul_le`: dₙ₊₁ ≥ 4dₙ (amplification)
3. `defectIterate_exponential_lower`: dₙ ≥ 4ⁿ · d₀
4. `defectIterate_unbounded`: off-critical zeros produce divergent defect
-/

namespace IndisputableMonolith
namespace NumberTheory

open Real Cost

noncomputable section

/-! ## §1. The iterated defect sequence -/

/-- The iterated defect at level n: dₙ(t) = cosh(2ⁿ · t) − 1.

    For a zeta zero with deviation η = Re(ρ)−1/2, set t = 2η.
    Then d₀ = cosh(2η)−1 is the zero's defect, and dₙ is the
    n-th iterate under the RCL self-composition. -/
def defectIterate (t : ℝ) (n : ℕ) : ℝ := Real.cosh ((2 : ℝ) ^ n * t) - 1

/-- dₙ(0) = 0 for all n: on the critical line, all iterates vanish. -/
@[simp] theorem defectIterate_zero_param (n : ℕ) : defectIterate 0 n = 0 := by
  simp [defectIterate, Real.cosh_zero]

/-- d₀(t) = cosh(t) − 1 = J_log(t). -/
theorem defectIterate_zero_eq_J_log (t : ℝ) :
    defectIterate t 0 = Foundation.DiscretenessForcing.J_log t := by
  simp [defectIterate, Foundation.DiscretenessForcing.J_log]

/-- dₙ ≥ 0 for all n and t (from cosh ≥ 1). -/
theorem defectIterate_nonneg (t : ℝ) (n : ℕ) : 0 ≤ defectIterate t n := by
  simp only [defectIterate]
  linarith [Real.one_le_cosh ((2 : ℝ) ^ n * t)]

/-- d₀ > 0 for t ≠ 0 (off the critical line). -/
theorem defectIterate_zero_pos {t : ℝ} (ht : t ≠ 0) : 0 < defectIterate t 0 := by
  rw [defectIterate_zero_eq_J_log]
  exact Foundation.DiscretenessForcing.J_log_pos ht

/-! ## §2. The recurrence from the RCL -/

/-- **The composition recurrence.**

    dₙ₊₁ = 2 · dₙ · (dₙ + 2)

    This is forced by the Recognition Composition Law: applying the
    RCL to the pair (e^{2ⁿt}, e^{−2ⁿt}) yields the cosh double-angle
    formula, which is exactly this recurrence.

    Mathematical content:
      cosh(2·u) = 2cosh²(u) − 1
      ⟹ cosh(2u)−1 = 2(cosh u − 1)(cosh u + 1)
                    = 2·(cosh u − 1)·((cosh u − 1) + 2) -/
theorem defectIterate_succ (t : ℝ) (n : ℕ) :
    defectIterate t (n + 1) = 2 * defectIterate t n * (defectIterate t n + 2) := by
  simp only [defectIterate]
  rw [show (2 : ℝ) ^ (n + 1) * t = 2 * ((2 : ℝ) ^ n * t) from by rw [pow_succ]; ring]
  have hd := Real.cosh_two_mul ((2 : ℝ) ^ n * t)
  have hs := Real.cosh_sq ((2 : ℝ) ^ n * t)
  set c := Real.cosh ((2 : ℝ) ^ n * t)
  set s := Real.sinh ((2 : ℝ) ^ n * t)
  have lhs : Real.cosh (2 * ((2 : ℝ) ^ n * t)) - 1 = 2 * c ^ 2 - 2 := by linarith
  have rhs_eq : 2 * (c - 1) * (c - 1 + 2) = 2 * c ^ 2 - 2 := by ring
  linarith

/-- The recurrence in "squared ratio" form:
    dₙ₊₁ = 2(dₙ² + 2dₙ) = 2dₙ² + 4dₙ. -/
theorem defectIterate_succ' (t : ℝ) (n : ℕ) :
    defectIterate t (n + 1) = 2 * (defectIterate t n) ^ 2 + 4 * defectIterate t n := by
  rw [defectIterate_succ]; ring

/-! ## §3. Defect amplification -/

/-- **Each iteration at least quadruples the defect.**
    dₙ₊₁ ≥ 4·dₙ  (from dₙ ≥ 0 ⟹ dₙ+2 ≥ 2). -/
theorem defectIterate_four_mul_le (t : ℝ) (n : ℕ) :
    4 * defectIterate t n ≤ defectIterate t (n + 1) := by
  rw [defectIterate_succ]
  have hd : 0 ≤ defectIterate t n := defectIterate_nonneg t n
  nlinarith [sq_nonneg (defectIterate t n)]

/-- **Exponential lower bound.** dₙ ≥ 4ⁿ · d₀.

    Each iteration quadruples the defect, so after n iterations
    the defect has grown by a factor of at least 4ⁿ. -/
theorem defectIterate_exponential_lower (t : ℝ) (n : ℕ) :
    (4 : ℝ) ^ n * defectIterate t 0 ≤ defectIterate t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (4 : ℝ) ^ (n + 1) * defectIterate t 0
        = 4 * ((4 : ℝ) ^ n * defectIterate t 0) := by ring
      _ ≤ 4 * defectIterate t n := by nlinarith
      _ ≤ defectIterate t (n + 1) := defectIterate_four_mul_le t n

/-- 1 ≤ 4^n for all n. -/
private theorem one_le_four_pow (n : ℕ) : (1 : ℝ) ≤ (4 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 4 from by norm_num) k]

/-- The sequence is monotonically nondecreasing from level 0. -/
theorem defectIterate_mono {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    defectIterate t 0 ≤ defectIterate t n := by
  have h := defectIterate_exponential_lower t n
  have hd0 : 0 < defectIterate t 0 := defectIterate_zero_pos ht
  nlinarith [one_le_four_pow n]

/-! ## §4. Divergence -/

/-- Helper: n+1 ≤ 4^(n+1) for all n. -/
private theorem nat_succ_le_pow_four (m : ℕ) : (m : ℝ) + 1 ≤ (4 : ℝ) ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]; push_cast
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 4 from by norm_num) (k + 1)]

/-- **Off-critical zeros produce divergent defect cascades.**

    For any t ≠ 0 (deviation from critical line), the iterated defect
    sequence grows without bound. This is the key obstruction: the RCL
    forces an off-critical zero to generate unbounded cost, which cannot
    be accommodated by any finite carrier budget.

    Proof: dₙ ≥ 4ⁿ · d₀ with d₀ > 0, and 4ⁿ → ∞. -/
theorem defectIterate_unbounded {t : ℝ} (ht : t ≠ 0) (C : ℝ) :
    ∃ n : ℕ, C < defectIterate t n := by
  have hd0 : 0 < defectIterate t 0 := defectIterate_zero_pos ht
  have hexp := defectIterate_exponential_lower t
  suffices h : ∃ n : ℕ, C < (4 : ℝ) ^ n * defectIterate t 0 by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, lt_of_lt_of_le hn (hexp n)⟩
  set k := ⌈C / defectIterate t 0⌉₊ + 1
  refine ⟨k, ?_⟩
  have h1 : C / defectIterate t 0 ≤ ↑(⌈C / defectIterate t 0⌉₊) := Nat.le_ceil _
  have h2 : (↑(⌈C / defectIterate t 0⌉₊) : ℝ) + 1 ≤ (4 : ℝ) ^ k :=
    nat_succ_le_pow_four _
  rw [show C = C / defectIterate t 0 * defectIterate t 0 from by
    field_simp]
  exact mul_lt_mul_of_pos_right (by linarith) hd0

/-! ## §5. Connection to the zero-location defect -/

/-- For a zeta zero ρ, the iterated defect at level 0 equals the
    zero-location defect from ZeroLocationCost. -/
theorem defectIterate_zero_eq_zeroDefect (ρ : ℂ) :
    defectIterate (zeroDeviation ρ) 0 = zeroDefect ρ := by
  rw [defectIterate_zero_eq_J_log, zeroDefect_eq_J_log]

/-- **The composition law for zeta zeros, final form.**

    If ρ is off the critical line, the iterated composition defect
    diverges, generating arbitrarily large cost values from a single zero. -/
theorem zero_composition_diverges (ρ : ℂ) (hρ : ¬OnCriticalLine ρ) (C : ℝ) :
    ∃ n : ℕ, C < defectIterate (zeroDeviation ρ) n := by
  apply defectIterate_unbounded
  exact (zeroDeviation_eq_zero_iff_on_critical_line ρ).not.mpr hρ

end

end NumberTheory
end IndisputableMonolith
