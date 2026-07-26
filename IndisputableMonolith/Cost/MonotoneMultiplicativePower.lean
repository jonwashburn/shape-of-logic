/-
  Cost/MonotoneMultiplicativePower.lean

  ERDOS'S THEOREM ON MONOTONE MULTIPLICATIVE FUNCTIONS, IN THE CASE THE COST
  CLASSIFICATION NEEDS, WITH NOTHING IMPORTED.

  Statement. A completely multiplicative `f : ℕ → ℝ` that is nondecreasing on the
  positive integers is `n ↦ n ^ c` for a single real `c ≥ 0` (`exists_exponent`).

  Provenance. This is the completely multiplicative case of Erdős 1946, whose short
  proof is due to Howe (Amer. Math. Monthly 93 (1986) 593-595). The argument below is
  Howe's: squeeze `n ^ k` between consecutive powers of two, apply monotonicity on both
  the argument and the value, and let `k` grow. It is elementary and needs no
  transcendence input, which is why it can be discharged here rather than named as a
  hypothesis. The classification of the anchor-free cost ledger previously carried it as
  one of TWO external imports; after this module the only remaining import is the six
  exponentials theorem (`Cost.TraceRationalExponent.SixExponentialsTraceInput`).

  Why the exponent is real and not rational. Monotonicity alone cannot produce a rational
  exponent, and it does not need to: the arithmetic that forces an integer runs later, on
  the traces, in `Cost.TraceRationalExponent`.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Cost
namespace MonotonePower

/-- A completely multiplicative, nondecreasing function on the positive integers. The
conditions are stated only where they are meant, above zero: `f 0` is unconstrained, since
the character the cost ledger produces has no content there. -/
structure MonotoneMultiplicative (f : ℕ → ℝ) : Prop where
  unit : f 1 = 1
  mul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → f (m * n) = f m * f n
  mono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → f m ≤ f n

variable {f : ℕ → ℝ}

theorem one_le (hf : MonotoneMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ f n := by
  have h := hf.mono 1 n le_rfl hn
  rwa [hf.unit] at h

theorem pos (hf : MonotoneMultiplicative f) {n : ℕ} (hn : 1 ≤ n) : 0 < f n :=
  lt_of_lt_of_le zero_lt_one (one_le hf hn)

/-- Complete multiplicativity on powers, which is the only form the squeeze uses. -/
theorem pow_eq (hf : MonotoneMultiplicative f) {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    f (m ^ j) = f m ^ j := by
  induction j with
  | zero => simpa using hf.unit
  | succ j ih =>
      have hmj : 1 ≤ m ^ j := Nat.one_le_pow j m hm
      rw [pow_succ, hf.mul _ _ hmj hm, ih, pow_succ]

/-- The degenerate branch. If the value at two is one then every value is one, because
every integer is below a power of two and the values in between are squeezed. -/
theorem eq_one_of_two_eq_one (hf : MonotoneMultiplicative f) (h2 : f 2 = 1)
    {n : ℕ} (hn : 1 ≤ n) : f n = 1 := by
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hle := hf.mono n (2 ^ n) hn hlt.le
  rw [pow_eq hf (by norm_num) n, h2, one_pow] at hle
  exact le_antisymm hle (one_le hf hn)

/-- **The heart of Howe's argument.** For every base `n ≥ 2` the ratio
`log (f n) / log n` is the same as at the base two, stated cross-multiplied so that no
division appears. The proof squeezes `n ^ k` between `2 ^ j` and `2 ^ (j+1)`, reads the
squeeze twice (on the argument and on the value), and lets `k` grow. -/
theorem log_ratio (hf : MonotoneMultiplicative f) (h2 : 1 < f 2) {n : ℕ} (hn : 2 ≤ n) :
    Real.log (f n) * Real.log 2 = Real.log (f 2) * Real.log n := by
  set L2 := Real.log 2 with hL2def
  set Ln := Real.log n with hLndef
  set M2 := Real.log (f 2) with hM2def
  set Mn := Real.log (f n) with hMndef
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hL2 : 0 < L2 := Real.log_pos (by norm_num)
  have hLn : 0 < Ln := Real.log_pos hnR
  have hM2 : 0 < M2 := Real.log_pos h2
  have hfn : 1 < f n := lt_of_lt_of_le h2 (hf.mono 2 n (by norm_num) hn)
  have hMn : 0 < Mn := Real.log_pos hfn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have key : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * |Mn * L2 - M2 * Ln| ≤ M2 * L2 := by
    intro k hk
    set j := Nat.log 2 (n ^ k) with hjdef
    have hnkpos : 1 ≤ n ^ k := Nat.one_le_pow k n (by omega)
    have hnk0 : n ^ k ≠ 0 := by omega
    have hle : 2 ^ j ≤ n ^ k := Nat.pow_log_le_self 2 hnk0
    have hlt : n ^ k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hleR : ((2 : ℝ)) ^ j ≤ ((n : ℝ)) ^ k := by exact_mod_cast hle
    have hltR : ((n : ℝ)) ^ k ≤ ((2 : ℝ)) ^ (j + 1) := by exact_mod_cast hlt.le
    have ha : (j : ℝ) * L2 ≤ (k : ℝ) * Ln := by
      have h := Real.log_le_log (by positivity) hleR
      rwa [Real.log_pow, Real.log_pow] at h
    have hb : (k : ℝ) * Ln ≤ ((j : ℝ) + 1) * L2 := by
      have h := Real.log_le_log (by positivity) hltR
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have hf2j : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
    have hf2j1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow (j + 1) 2 (by norm_num)
    have hfa : f (2 ^ j) ≤ f (n ^ k) := hf.mono _ _ hf2j hle
    have hfb : f (n ^ k) ≤ f (2 ^ (j + 1)) := hf.mono _ _ (Nat.one_le_pow k n (by omega)) hlt.le
    rw [pow_eq hf (by norm_num) j, pow_eq hf hn1 k] at hfa
    rw [pow_eq hf hn1 k, pow_eq hf (by norm_num) (j + 1)] at hfb
    have hf2pos : (0 : ℝ) < f 2 := lt_trans zero_lt_one h2
    have hfnpos : (0 : ℝ) < f n := lt_trans zero_lt_one hfn
    have hc : (j : ℝ) * M2 ≤ (k : ℝ) * Mn := by
      have h := Real.log_le_log (by positivity) hfa
      rwa [Real.log_pow, Real.log_pow] at h
    have hd : (k : ℝ) * Mn ≤ ((j : ℝ) + 1) * M2 := by
      have h := Real.log_le_log (by positivity) hfb
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have e1 : ((k : ℝ) * Mn) * L2 ≤ (((j : ℝ) + 1) * M2) * L2 :=
      mul_le_mul_of_nonneg_right hd hL2.le
    have e2 : ((j : ℝ) * L2) * M2 ≤ ((k : ℝ) * Ln) * M2 :=
      mul_le_mul_of_nonneg_right ha hM2.le
    have e3 : ((j : ℝ) * M2) * L2 ≤ ((k : ℝ) * Mn) * L2 :=
      mul_le_mul_of_nonneg_right hc hL2.le
    have e4 : ((k : ℝ) * Ln) * M2 ≤ (((j : ℝ) + 1) * L2) * M2 :=
      mul_le_mul_of_nonneg_right hb hM2.le
    have habs : |(k : ℝ) * (Mn * L2 - M2 * Ln)| ≤ M2 * L2 := by
      rw [abs_le]
      constructor
      · nlinarith [e3, e4]
      · nlinarith [e1, e2]
    calc (k : ℝ) * |Mn * L2 - M2 * Ln|
        = |(k : ℝ) * (Mn * L2 - M2 * Ln)| := by
          rw [abs_mul, Nat.abs_cast]
      _ ≤ M2 * L2 := habs
  by_contra hne
  have hD : 0 < |Mn * L2 - M2 * Ln| := abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨k, hk⟩ := exists_nat_gt ((M2 * L2) / |Mn * L2 - M2 * Ln|)
  have hbig : M2 * L2 < (k : ℝ) * |Mn * L2 - M2 * Ln| := (div_lt_iff₀ hD).mp hk
  have hsmall := key (k + 1) (Nat.le_add_left 1 k)
  push_cast at hsmall
  nlinarith [hD, hbig, hsmall]

/-- **Erdős's theorem, completely multiplicative case (Howe's proof).** A nondecreasing
completely multiplicative function on the positive integers is a power, with a single
nonnegative real exponent. The degenerate constant function is the exponent zero. -/
theorem exists_exponent (hf : MonotoneMultiplicative f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 1 ≤ n → f n = (n : ℝ) ^ c := by
  rcases eq_or_lt_of_le (one_le hf (by norm_num : (1 : ℕ) ≤ 2)) with h2 | h2
  · refine ⟨0, le_rfl, fun n hn => ?_⟩
    rw [Real.rpow_zero, eq_one_of_two_eq_one hf h2.symm hn]
  · have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hM2 : 0 < Real.log (f 2) := Real.log_pos h2
    refine ⟨Real.log (f 2) / Real.log 2, le_of_lt (div_pos hM2 hL2), fun n hn => ?_⟩
    rcases eq_or_lt_of_le hn with h1 | h1
    · have hn1 : n = 1 := h1.symm
      subst hn1
      rw [hf.unit, Nat.cast_one, Real.one_rpow]
    · have hn2 : 2 ≤ n := h1
      have hlog := log_ratio hf h2 hn2
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
      have hfpos : 0 < f n := pos hf hn
      rw [Real.rpow_def_of_pos hnpos, ← Real.exp_log hfpos]
      congr 1
      field_simp
      linarith [hlog]

/-! ### Nonvacuity

A theorem about an empty hypothesis class proves nothing. The pack is inhabited at both
ends of the conclusion: the constant function realizes the exponent zero and the identity
realizes the exponent one. Monotonicity is what is doing the work, and it cannot be
dropped: the Liouville function is completely multiplicative and is no power. -/

theorem monotoneMultiplicative_const_one : MonotoneMultiplicative (fun _ : ℕ => (1 : ℝ)) where
  unit := rfl
  mul := by intro m n _ _; norm_num
  mono := by intro m n _ _; exact le_rfl

theorem monotoneMultiplicative_id : MonotoneMultiplicative (fun n : ℕ => (n : ℝ)) where
  unit := by norm_num
  mul := by intro m n _ _; push_cast; ring
  mono := by intro m n _ hmn; exact_mod_cast hmn

/-! ### Axiom audit -/

#print axioms exists_exponent
#print axioms log_ratio

end MonotonePower
end Cost
end IndisputableMonolith
