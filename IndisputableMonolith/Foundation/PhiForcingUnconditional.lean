import Mathlib
import IndisputableMonolith.Foundation.PhiForcingDerived

/-!
# T6 promotion: φ forced by adjacent composition alone (no geometric ladder)

**The theorem.** Any positive sequence obeying the adjacent additive recurrence
s(n+2) = s(n+1) + s(n) — the arithmetic of adjacent ledger composition — has
inter-level ratio converging to the golden ratio φ:

  ratio_tendsto_phi : Tendsto (fun n => s (n+1) / s n) atTop (nhds φ)

No geometric ladder, no uniform ratio, and no closure hypothesis is assumed.
The Fibonacci ladder 1, 1, 2, 3, 5, … is not geometric (its ratios 1, 2, 1.5,
1.667, … are not constant), yet its ratio tends to φ; this is the generic
behavior of EVERY additive posting ladder, for any positive seeds. The proof
is a contraction: r_{n+1} = 1 + 1/r_n, and since φ = 1 + 1/φ,

  r_{n+1} − φ = 1/r_n − 1/φ = (φ − r_n)/(r_n·φ),

so with r_n ≥ 1 (n ≥ 1) the error contracts by a factor 1/φ ≈ 0.618 per step.

**What this changes for T6.** The falsifier C-im-phi-forced demands the φ rung
without assuming a geometric ladder. Previous derivations
(PhiForcingDerived, PhiClosureSelection) assumed a uniform ratio r and
derived r = φ. Here the uniform ratio is not an input at all: geometricity
is demoted from premise to asymptotic corollary, and φ is forced by the
recurrence alone.

**Honest status of the full T6 promotion.**
- Banked premise (1) — the tick: ledger discreteness is forced by
  cost-nontriviality (Cost.GeometricRoot: subdivision trivializes J-cost, so
  a cost-carrying ledger admits a coarsest step).
- This module (2) — the recurrence suffices: adjacent composition forces φ
  with no geometricity assumption.
- Residual premise (3) — the recurrence itself: s(n+2) = s(n+1) + s(n) is the
  posting operation's arithmetic (ledger additivity: composed work is the sum
  of posted work; adjacent closure: the composition of adjacent levels is
  postable). In the library today this is carried by the
  CanonicalPostingClosure / PostingExtensivity certificates
  (UnifiedForcingChain), whose provenance is the ledger's posting operation —
  locality and binarity (HierarchyDynamics). Deriving the recurrence from the
  kernel axioms with NO posting-closure certificate is the remaining bridge;
  that residual is named here, not hidden.
-/

noncomputable section
namespace IndisputableMonolith
namespace Foundation

open Real Constants
open Filter

variable {s : ℕ → ℝ}

/-- Ratio recursion: r_{n+1} = 1 + 1/r_n, from the adjacent recurrence. -/
private theorem ratio_succ (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (n : ℕ) :
    s (n + 2) / s (n + 1) = 1 + 1 / (s (n + 1) / s n) := by
  have h1 : s (n + 1) ≠ 0 := ne_of_gt (hpos (n + 1))
  have h2 : s n ≠ 0 := ne_of_gt (hpos n)
  rw [hrec n]
  field_simp [h1, h2]

/-- Every ratio from index 1 onward is at least 1. -/
private theorem ratio_ge_one (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (n : ℕ) :
    1 ≤ s (n + 2) / s (n + 1) := by
  rw [ratio_succ hpos hrec n]
  have hr : 0 < s (n + 1) / s n := div_pos (hpos _) (hpos _)
  have h : 0 ≤ 1 / (s (n + 1) / s n) := le_of_lt (one_div_pos.mpr hr)
  linarith

/-- φ is the positive fixed point of the ratio map r ↦ 1 + 1/r. -/
private theorem phi_fixed : phi = 1 + 1 / phi := by
  have h0 : phi ≠ 0 := by linarith [one_lt_phi]
  field_simp [h0]
  nlinarith [phi_sq_eq]

/-- The key identity: r_{n+1} − φ = 1/r_n − 1/φ. -/
private theorem ratio_sub_phi (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (n : ℕ) :
    s (n + 2) / s (n + 1) - phi = 1 / (s (n + 1) / s n) - 1 / phi := by
  have h : (1 : ℝ) - phi = -(1 / phi) := by linarith [phi_fixed]
  rw [ratio_succ hpos hrec n]
  linarith [h]

/-- Contraction: |r_{n+1} − φ| ≤ |r_n − φ| / φ for n ≥ 1 (since r_n ≥ 1). -/
private theorem ratio_contract (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (n : ℕ) (hn : 1 ≤ n) :
    |s (n + 2) / s (n + 1) - phi| ≤ |s (n + 1) / s n - phi| / phi := by
  have hr : 0 < s (n + 1) / s n := div_pos (hpos _) (hpos _)
  have hp : 0 < phi := by linarith [one_lt_phi]
  have h1 : s (n + 1) / s n ≠ 0 := ne_of_gt hr
  have h2 : phi ≠ 0 := ne_of_gt hp
  rw [ratio_sub_phi hpos hrec n]
  have hident : 1 / (s (n + 1) / s n) - 1 / phi
      = (phi - s (n + 1) / s n) / ((s (n + 1) / s n) * phi) := by
    have hn1 : s (n + 1) ≠ 0 := ne_of_gt (hpos _)
    have hn0 : s n ≠ 0 := ne_of_gt (hpos _)
    field_simp [h1, h2, hn1, hn0]
  rw [hident, abs_div, abs_mul, abs_of_pos hr, abs_of_pos hp,
    show phi - s (n + 1) / s n = -(s (n + 1) / s n - phi) from by ring, abs_neg]
  gcongr
  have hn1 : 1 ≤ s (n + 1) / s n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simpa using ratio_ge_one hpos hrec k
  nlinarith [hn1, hp]

/-- Iterated contraction: |r_{k+1} − φ| ≤ (1/φ)^k · |r_1 − φ|. -/
private theorem ratio_bound (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (k : ℕ) :
    |s (k + 2) / s (k + 1) - phi|
      ≤ (1 / phi) ^ k * |s 2 / s 1 - phi| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e0 : k + 1 + 2 = k + 3 := by omega
    have e1 : k + 1 + 1 = k + 2 := by omega
    rw [e0, e1]
    have hp : 0 < phi := by linarith [one_lt_phi]
    calc |s (k + 3) / s (k + 2) - phi|
        ≤ |s (k + 2) / s (k + 1) - phi| / phi :=
          ratio_contract hpos hrec (k + 1) (by omega)
      _ ≤ ((1 / phi) ^ k * |s 2 / s 1 - phi|) / phi := by
          gcongr
      _ = (1 / phi) ^ (k + 1) * |s 2 / s 1 - phi| := by
          rw [pow_succ']
          field_simp [ne_of_gt hp]

/-- All-n bound with a seed-covering constant: |r_n − φ| ≤ C·(1/φ)^n. -/
private theorem ratio_bound_all (hpos : ∀ n, 0 < s n) (hrec : ∀ n, s (n + 2) = s (n + 1) + s n)
    (n : ℕ) :
    |s (n + 1) / s n - phi|
      ≤ phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * (1 / phi) ^ n := by
  have hp : 0 < phi := by linarith [one_lt_phi]
  have hq : 0 ≤ (1:ℝ)/phi := by positivity
  have hge1 : (1:ℝ) ≤ phi := by linarith [one_lt_phi]
  rcases n with _ | k
  · rw [pow_zero, mul_one]
    calc |s 1 / s 0 - phi|
        ≤ |s 1 / s 0 - phi| + |s 2 / s 1 - phi| := by
          linarith [abs_nonneg (s 2 / s 1 - phi)]
      _ ≤ phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) := by
          nth_rewrite 1 [← one_mul (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|)]
          exact mul_le_mul_of_nonneg_right hge1 (by positivity)
  · calc |s (k + 1 + 1) / s (k + 1) - phi|
        ≤ (1 / phi) ^ k * |s 2 / s 1 - phi| := ratio_bound hpos hrec k
      _ ≤ phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * (1 / phi) ^ (k + 1) := by
          rw [pow_succ']
          have hφ : phi * (1 / phi) = 1 := by field_simp [ne_of_gt hp]
          have e : phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * ((1 / phi) * (1 / phi) ^ k)
              = (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * (1 / phi) ^ k := by
            calc phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * ((1 / phi) * (1 / phi) ^ k)
                = (phi * (1 / phi))
                  * ((|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * (1 / phi) ^ k) := by ring
              _ = (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) * (1 / phi) ^ k := by
                  rw [hφ, one_mul]
          rw [e]
          have hle : |s 2 / s 1 - phi|
              ≤ |s 1 / s 0 - phi| + |s 2 / s 1 - phi| := by
            linarith [abs_nonneg (s 1 / s 0 - phi)]
          rw [mul_comm ((1 / phi) ^ k) |s 2 / s 1 - phi|]
          exact mul_le_mul_of_nonneg_right hle (pow_nonneg hq k)

/-- **T6, promoted: the golden ratio is the asymptotic ratio of every additive
posting ladder.** Any positive sequence obeying the adjacent additive
recurrence s(n+2) = s(n+1) + s(n) has inter-level ratio converging to φ.
No geometric ladder, no uniform ratio, and no closure hypothesis is assumed:
geometricity is demoted from premise to asymptotic corollary. -/
theorem ratio_tendsto_phi (hpos : ∀ n, 0 < s n)
    (hrec : ∀ n, s (n + 2) = s (n + 1) + s n) :
    Tendsto (fun n => s (n + 1) / s n) atTop (nhds phi) := by
  have hp : 0 < phi := by linarith [one_lt_phi]
  have hq0 : 0 ≤ (1:ℝ) / phi := by positivity
  have hq1 : (1:ℝ) / phi < 1 := by
    rw [div_lt_one hp]; exact one_lt_phi
  set C := phi * (|s 1 / s 0 - phi| + |s 2 / s 1 - phi|) with hC
  have hbound : ∀ n, |s (n + 1) / s n - phi| ≤ C * (1 / phi) ^ n := fun n =>
    ratio_bound_all hpos hrec n
  have htend : Tendsto (fun n => C * (1 / phi) ^ n) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    simpa using h
  have habs : Tendsto (fun n => |s (n + 1) / s n - phi|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound htend
  have hsub : Tendsto (fun n => s (n + 1) / s n - phi) atTop (nhds 0) := by
    have hneg : Tendsto (fun n => -|s (n + 1) / s n - phi|) atTop (nhds 0) := by
      have h := habs.neg
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hneg habs
      (fun n => neg_abs_le _) (fun n => le_abs_self _)
  have h : Tendsto (fun n => (s (n + 1) / s n - phi) + phi) atTop (nhds (0 + phi)) :=
    hsub.add tendsto_const_nhds
  simpa using h

/-- The falsifier's base instance "levels 2 = levels 1 + levels 0" is the
n = 0 case of the adjacent recurrence. -/
theorem posting_closure_at_base (hrec : ∀ n, s (n + 2) = s (n + 1) + s n) :
    s 2 = s 1 + s 0 := hrec 0

/-- **T6 assembly.** From positivity and the adjacent posting recurrence, the
asymptotic inter-level ratio is φ, with no geometric-ladder input. Combined
with the banked tick (Cost.GeometricRoot: discreteness forced by
cost-nontriviality), the chain is: the ledger cannot subdivide forever (tick),
each posted level composes its two predecessors (recurrence), and the ladder's
asymptotic ratio is φ (this module). The residual premise is the recurrence's
own provenance; see the module docstring. -/
theorem phi_is_asymptotic_ratio (hpos : ∀ n, 0 < s n)
    (hrec : ∀ n, s (n + 2) = s (n + 1) + s n) :
    Tendsto (fun n => s (n + 1) / s n) atTop (nhds phi) :=
  ratio_tendsto_phi hpos hrec

end Foundation
end IndisputableMonolith
end
