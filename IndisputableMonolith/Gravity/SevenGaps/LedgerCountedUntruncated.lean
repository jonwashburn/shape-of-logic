import Mathlib

/-!
# The untruncated ledger-counted chain (U15 attainment, truncation removed)

`LedgerCountedConvergence` banked attainment for the ledger-counted
birth-death chain truncated at every finite level; its honest-scope note
named the remaining THEOREM target: the UNTRUNCATED chain. This module
builds that organ.

## The object

The untruncated ledger-counted dynamics has birth rate `1` (one fresh
posting available per tick) and death rate `x` (each of the `x` posted
labels can retire) on ALL of `Nat`. The death rate is unbounded, so no
discrete-time uniformization exists; the honest untruncated object is
the continuous-time transition function. For these rates it has an
explicit closed form: after time `t`, each of the `x` initial quanta
survives with probability `p = exp (-t)` (binomial thinning) and fresh
postings arrive as a Poisson field of mean `1 - p` (immigration), so

`Kt t x y = ∑ k, bin x p k * poi (1-p) (y-k)`,  `p = exp (-t)`.

## Necessary reasons (the block for the untruncated close)

* R1 (existence): the family is a genuine dynamics: every row is a
  probability distribution (`hasSum_K`), time zero is the identity
  (`Kt_zero`), and the family composes: `Kt s * Kt t = Kt (s+t)`
  (`chapman`, `Kt_semigroup`), an honest Chapman-Kolmogorov theorem
  with the infinite intermediate-state sum.
* R2 (the counted rates): the instantaneous rates at `t = 0` are
  EXACTLY the ledger-counted rates, birth `1` and per-label death `x`
  (`hasDerivAt_Kt`): this is where the counted selection enters, and
  what makes this family THE ledger-counted chain rather than an
  arbitrary family converging to a Poisson law.
* R3 (stationarity): the normalized inverse-factorial weight, which on
  `Nat` is the Poisson(1) law `exp (-1) / y!`, is invariant at every
  time (`poi_one_stationary`).
* R4 (attainment): from EVERY finitely supported initial distribution,
  total variation to the inverse-factorial law decays like `exp (-t)`
  with the explicit constant `2 * (first moment + 1)` (`attainment`),
  and tends to zero (`attainment_tendsto`).
* R5 (decoys scored): the selection discriminates. Poisson(c) with
  `c ≠ 1` is NOT stationary (`poi_ne_one_not_stationary`): the unit
  birth rate pins the intensity. The initial distance is strictly
  positive (`initial_distance_pos`), and the bound beats the trivial
  total-variation diameter `2` in finite time (`gate_fires`), so the
  attainment gate actually fires.

## Honest scope

The kernel is pinned by generator + semigroup + identity at zero. What
is NOT formalized: that these rates admit no OTHER transition semigroup
(non-explosion/minimality); standard probability gives uniqueness for
this conservative birth-death family, but that argument is not in this
file. Attainment is stated for finitely supported initial data; the
same proof shape gives any first-moment-bounded law. The late-time
identification (nature's weight IS the late-time state) remains the
Jon-gated MODEL clause named in the census; no measure flag is flipped.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace LedgerCountedUntruncated

open Finset

noncomputable section

/-! ## The two pmf pieces: binomial survivors, Poisson immigrants -/

/-- Binomial pmf: `k` of `x` initial quanta survive, each with
probability `p`. -/
def bin (x : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (x.choose k : ℝ) * p ^ k * (1 - p) ^ (x - k)

/-- Poisson pmf: `m` fresh postings from an immigration field of mean
`a`. At `a = 1` this is the normalized inverse-factorial weight
`exp (-1) / m!`, the census's selected state. -/
def poi (a : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-a) * a ^ m / (m.factorial : ℝ)

theorem bin_nonneg (x : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ bin x p k := by
  unfold bin
  have h1 : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

theorem poi_nonneg {a : ℝ} (ha : 0 ≤ a) (m : ℕ) : 0 ≤ poi a m := by
  unfold poi
  have h1 : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast m.factorial_pos
  positivity

theorem bin_of_lt (x : ℕ) (p : ℝ) {k : ℕ} (h : x < k) : bin x p k = 0 := by
  unfold bin
  rw [Nat.choose_eq_zero_of_lt h]
  norm_num

theorem bin_zero_left (p : ℝ) (k : ℕ) :
    bin 0 p k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp [bin]
  · simp [bin_of_lt 0 p (Nat.succ_pos k)]

theorem bin_apply_zero (x : ℕ) (p : ℝ) : bin x p 0 = (1 - p) ^ x := by
  simp [bin]

theorem bin_one_eval (x k : ℕ) : bin x 1 k = if k = x then 1 else 0 := by
  rcases lt_trichotomy k x with h | h | h
  · rw [if_neg (by omega)]
    unfold bin
    rw [show (1 : ℝ) - 1 = 0 by ring, zero_pow (by omega : x - k ≠ 0)]
    ring
  · subst h
    simp [bin]
  · rw [if_neg (by omega), bin_of_lt x 1 h]

theorem poi_zero_eval (m : ℕ) : poi 0 m = if m = 0 then 1 else 0 := by
  rcases m with _ | m
  · simp [poi]
  · unfold poi
    rw [zero_pow (by omega : m + 1 ≠ 0)]
    simp

/-- Row sum of the binomial piece (the binomial theorem). -/
theorem bin_sum (x : ℕ) (p : ℝ) : ∑ k ∈ range (x + 1), bin x p k = 1 := by
  have h := add_pow p (1 - p) x
  have h1 : p + (1 - p) = 1 := by ring
  rw [h1, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold bin
  ring

theorem hasSum_bin (x : ℕ) (p : ℝ) : HasSum (bin x p) 1 := by
  have h : ∀ k ∉ range (x + 1), bin x p k = 0 := by
    intro k hk
    exact bin_of_lt x p (by simpa [Finset.mem_range] using hk)
  have h2 : HasSum (bin x p) (∑ k ∈ range (x + 1), bin x p k) :=
    hasSum_sum_of_ne_finset_zero h
  rwa [bin_sum] at h2

/-- The exponential series, in the `a^n / n!` form. -/
theorem hasSum_exp_series (a : ℝ) :
    HasSum (fun n => a ^ n / (n.factorial : ℝ)) (Real.exp a) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ a

theorem hasSum_poi (a : ℝ) : HasSum (poi a) 1 := by
  have h := (hasSum_exp_series a).mul_left (Real.exp (-a))
  have h1 : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add]
    simp
  rw [h1] at h
  have h2 : (fun n => Real.exp (-a) * (a ^ n / (n.factorial : ℝ))) = poi a := by
    funext n
    unfold poi
    ring
  rwa [h2] at h

/-! ## Convolution and shifted sums -/

/-- Convolution of two sequences (independent sum of counts). -/
def conv (f g : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑ k ∈ range (y + 1), f k * g (y - k)

/-- The shift of a sequence by `k`, zero below `k`. -/
def shift (k : ℕ) (g : ℕ → ℝ) (y : ℕ) : ℝ :=
  if k ≤ y then g (y - k) else 0

theorem hasSum_shift (k : ℕ) {g : ℕ → ℝ} {S : ℝ} (hg : HasSum g S) :
    HasSum (shift k g) S := by
  have h1 : (fun n => shift k g (n + k)) = g := by
    funext n
    simp [shift, Nat.le_add_left]
  have h2 : HasSum (fun n => shift k g (n + k)) S := by rwa [h1]
  have h3 := (hasSum_nat_add_iff k).mp h2
  have h4 : ∑ i ∈ range k, shift k g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : ¬ k ≤ i := by
      have := Finset.mem_range.mp hi
      omega
    simp [shift, this]
  rwa [h4, add_zero] at h3

/-- A convolution whose left factor is supported below `N` is the finite
sum of shifted copies of the right factor. -/
theorem conv_eq_sum_shift (f g : ℕ → ℝ) (N : ℕ)
    (hf : ∀ b, N ≤ b → f b = 0) (y : ℕ) :
    conv f g y = ∑ k ∈ range N, f k * shift k g y := by
  have hstep1 : conv f g y = ∑ k ∈ range (y + 1), f k * shift k g y := by
    unfold conv
    refine Finset.sum_congr rfl fun k hk => ?_
    have hky : k ≤ y := by
      have := Finset.mem_range.mp hk
      omega
    rw [shift, if_pos hky]
  set M := max N (y + 1) with hM
  have hsub1 : range (y + 1) ⊆ range M := by
    rw [hM]
    exact Finset.range_subset_range.mpr (le_max_right N (y + 1))
  have hsub2 : range N ⊆ range M := by
    rw [hM]
    exact Finset.range_subset_range.mpr (le_max_left N (y + 1))
  have hext1 : ∑ k ∈ range (y + 1), f k * shift k g y =
      ∑ k ∈ range M, f k * shift k g y := by
    refine Finset.sum_subset hsub1 fun k _ hk => ?_
    have hky : y + 1 ≤ k := by
      by_contra hcon
      exact hk (Finset.mem_range.mpr (by omega))
    rw [shift, if_neg (by omega)]
    ring
  have hext2 : ∑ k ∈ range N, f k * shift k g y =
      ∑ k ∈ range M, f k * shift k g y := by
    refine Finset.sum_subset hsub2 fun k _ hk => ?_
    have hkN : N ≤ k := by
      by_contra hcon
      exact hk (Finset.mem_range.mpr (by omega))
    rw [hf k hkN]
    ring
  rw [hstep1, hext1, ← hext2]

/-- Row sums of a convolution with finitely supported left factor. -/
theorem hasSum_conv_fin (f g : ℕ → ℝ) (N : ℕ)
    (hf : ∀ b, N ≤ b → f b = 0) {S : ℝ} (hg : HasSum g S) :
    HasSum (conv f g) ((∑ k ∈ range N, f k) * S) := by
  have h1 : conv f g = fun y => ∑ k ∈ range N, f k * shift k g y := by
    funext y
    exact conv_eq_sum_shift f g N hf y
  rw [h1, Finset.sum_mul]
  exact hasSum_sum fun k _ => (hasSum_shift k hg).mul_left (f k)

/-! ## Convolution algebra via power series -/

theorem conv_eq_coeff (f g : ℕ → ℝ) (y : ℕ) :
    conv f g y =
      PowerSeries.coeff y (PowerSeries.mk f * PowerSeries.mk g) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [conv]

theorem mk_conv (f g : ℕ → ℝ) :
    PowerSeries.mk (conv f g) = PowerSeries.mk f * PowerSeries.mk g := by
  ext n
  rw [PowerSeries.coeff_mk, conv_eq_coeff]

theorem conv_assoc (f g h : ℕ → ℝ) :
    conv (conv f g) h = conv f (conv g h) := by
  funext y
  rw [conv_eq_coeff, conv_eq_coeff, mk_conv, mk_conv, mul_assoc]

/-- Poisson convolution: independent Poisson fields add their means. -/
theorem poi_conv (a b : ℝ) (y : ℕ) : conv (poi a) (poi b) y = poi (a + b) y := by
  unfold conv poi
  have hterm : ∀ k ∈ range (y + 1),
      Real.exp (-a) * a ^ k / (k.factorial : ℝ) *
        (Real.exp (-b) * b ^ (y - k) / ((y - k).factorial : ℝ)) =
      Real.exp (-(a + b)) / (y.factorial : ℝ) *
        (a ^ k * b ^ (y - k) * (y.choose k : ℝ)) := by
    intro k hk
    have hky : k ≤ y := by
      have := Finset.mem_range.mp hk
      omega
    have hcast : (y.choose k : ℝ) =
        (y.factorial : ℝ) / ((k.factorial : ℝ) * ((y - k).factorial : ℝ)) :=
      Nat.cast_choose ℝ hky
    have hkf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast k.factorial_pos.ne'
    have hykf : (((y - k).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (y - k).factorial_pos.ne'
    have hyf : ((y.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast y.factorial_pos.ne'
    have hexp : Real.exp (-(a + b)) = Real.exp (-a) * Real.exp (-b) := by
      rw [neg_add, Real.exp_add]
    rw [hcast, hexp]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow a b y]
  ring

/-! ## The transition kernel -/

/-- The untruncated ledger-counted transition kernel at survival
probability `p`: binomial thinning of the initial quanta convolved with
Poisson immigration of mean `1 - p`. -/
def K (p : ℝ) (x : ℕ) : ℕ → ℝ :=
  conv (bin x p) (poi (1 - p))

/-- The kernel in physical time: `p = exp (-t)`. -/
def Kt (t : ℝ) (x : ℕ) : ℕ → ℝ :=
  K (Real.exp (-t)) x

theorem K_apply (p : ℝ) (x y : ℕ) :
    K p x y = ∑ k ∈ range (y + 1), bin x p k * poi (1 - p) (y - k) := rfl

theorem bin_support (x : ℕ) (p : ℝ) : ∀ b, x + 1 ≤ b → bin x p b = 0 :=
  fun b hb => bin_of_lt x p (by omega)

/-- Every row of the kernel is a probability distribution. -/
theorem hasSum_K (p : ℝ) (x : ℕ) : HasSum (K p x) 1 := by
  have h := hasSum_conv_fin (bin x p) (poi (1 - p)) (x + 1)
    (bin_support x p) (hasSum_poi (1 - p))
  rwa [bin_sum, one_mul] at h

theorem K_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : ℕ) :
    0 ≤ K p x y := by
  rw [K_apply]
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ ?_
  · exact bin_nonneg x hp0 hp1 k
  · exact poi_nonneg (by linarith) (y - k)

theorem hasSum_Kt (t : ℝ) (x : ℕ) : HasSum (Kt t x) 1 := hasSum_K _ x

theorem Kt_nonneg {t : ℝ} (ht : 0 ≤ t) (x y : ℕ) : 0 ≤ Kt t x y := by
  have h1 : 0 < Real.exp (-t) := Real.exp_pos _
  have h2 : Real.exp (-t) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -t ≤ 0 by linarith)
    rwa [Real.exp_zero] at h
  exact K_nonneg (le_of_lt h1) h2 x y

/-- At survival probability one the kernel is the identity. -/
theorem K_one (x y : ℕ) : K 1 x y = if x = y then 1 else 0 := by
  rw [K_apply]
  have hterm : ∀ k ∈ range (y + 1),
      bin x 1 k * poi (1 - 1) (y - k) =
        if k = x ∧ y = x then 1 else 0 := by
    intro k hk
    have hky : k ≤ y := by
      have := Finset.mem_range.mp hk
      omega
    rw [bin_one_eval, show (1 : ℝ) - 1 = 0 by ring, poi_zero_eval]
    by_cases h1 : k = x
    · subst h1
      by_cases h2 : y = k
      · rw [if_pos rfl, if_pos (by omega), if_pos ⟨rfl, h2⟩]
        norm_num
      · rw [if_pos rfl, if_neg (by omega), if_neg (by tauto)]
        norm_num
    · rw [if_neg h1,
        if_neg (show ¬(k = x ∧ y = x) from fun hc => h1 hc.1)]
      norm_num
  rw [Finset.sum_congr rfl hterm]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hclean : ∀ k ∈ range (x + 1),
        (if k = x ∧ x = x then (1 : ℝ) else 0) =
          if k = x then (1 : ℝ) else 0 := by
      intro k _
      by_cases hk : k = x
      · rw [if_pos ⟨hk, rfl⟩, if_pos hk]
      · rw [if_neg (by tauto), if_neg hk]
    rw [Finset.sum_congr rfl hclean,
      Finset.sum_ite_eq' (range (x + 1)) x (fun _ => (1 : ℝ)),
      if_pos (Finset.self_mem_range_succ x)]
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (by tauto)]

theorem Kt_zero (x y : ℕ) : Kt 0 x y = if x = y then 1 else 0 := by
  unfold Kt
  rw [neg_zero, Real.exp_zero]
  exact K_one x y

/-! ## The generator: the counted rates enter here -/

/-- The ledger-counted rate matrix: birth rate `1` (one fresh posting
per tick), death rate `x` (each posted label can retire), diagonal
`-(x+1)`. This is the same rate schedule as the truncated organ's
`step` entries, with the clipping removed. -/
def rate (x y : ℕ) : ℝ :=
  if y = x + 1 then 1
  else if y + 1 = x then (x : ℝ)
  else if y = x then -((x : ℝ) + 1)
  else 0

/-- Derivative of the binomial factor in `p` at `p = 1`. -/
def binD (x k : ℕ) : ℝ :=
  if k = x then (x : ℝ) else if x = k + 1 then -(x : ℝ) else 0

/-- Derivative of the Poisson factor (as a function of `p` through
`a = 1 - p`) at `p = 1`. -/
def poiD (m : ℕ) : ℝ :=
  if m = 0 then 1 else if m = 1 then -1 else 0

theorem hasDerivAt_bin (x k : ℕ) :
    HasDerivAt (fun p : ℝ => bin x p k) (binD x k) 1 := by
  have h1 : HasDerivAt (fun p : ℝ => p ^ k) ((k : ℝ) * (1 : ℝ) ^ (k - 1)) 1 :=
    hasDerivAt_pow k 1
  have hsub : HasDerivAt (fun p : ℝ => 1 - p) (-1) 1 :=
    (hasDerivAt_id 1).const_sub 1
  have h2 : HasDerivAt (fun p : ℝ => (1 - p) ^ (x - k))
      (((x - k : ℕ) : ℝ) * ((1 : ℝ) - 1) ^ (x - k - 1) * (-1)) 1 :=
    hsub.pow (x - k)
  have h3 := ((h1.const_mul ((x.choose k : ℝ))).mul h2)
  have hval :
      (x.choose k : ℝ) * ((k : ℝ) * (1 : ℝ) ^ (k - 1)) *
          ((1 : ℝ) - 1) ^ (x - k) +
        (x.choose k : ℝ) * (1 : ℝ) ^ k *
          (((x - k : ℕ) : ℝ) * ((1 : ℝ) - 1) ^ (x - k - 1) * (-1)) =
      binD x k := by
    rw [show (1 : ℝ) - 1 = 0 by ring]
    simp only [one_pow, mul_one]
    unfold binD
    by_cases hkx : k = x
    · subst hkx
      rw [if_pos rfl]
      simp [Nat.sub_self]
    · rw [if_neg hkx]
      by_cases hx1 : x = k + 1
      · subst hx1
        rw [if_pos rfl]
        have e2 : k + 1 - k - 1 = 0 := by omega
        have e1 : k + 1 - k = 1 := by omega
        rw [e2, e1, Nat.choose_succ_self_right]
        norm_num
      · rw [if_neg hx1]
        by_cases hlt : k < x
        · have e1 : x - k ≠ 0 := by omega
          have e2 : x - k - 1 ≠ 0 := by omega
          rw [zero_pow e1, zero_pow e2]
          ring
        · have hgt : x < k := by omega
          rw [Nat.choose_eq_zero_of_lt hgt]
          norm_num
  have hfun : (fun p : ℝ => (x.choose k : ℝ) * p ^ k * (1 - p) ^ (x - k)) =
      fun p : ℝ => bin x p k := by
    funext p
    rfl
  rw [← hval]
  have h4 : HasDerivAt (fun p : ℝ => (x.choose k : ℝ) * p ^ k * (1 - p) ^ (x - k))
      ((x.choose k : ℝ) * ((k : ℝ) * (1 : ℝ) ^ (k - 1)) *
          ((1 : ℝ) - 1) ^ (x - k) +
        (x.choose k : ℝ) * (1 : ℝ) ^ k *
          (((x - k : ℕ) : ℝ) * ((1 : ℝ) - 1) ^ (x - k - 1) * (-1))) 1 := by
    have := (h1.const_mul ((x.choose k : ℝ))).mul h2
    convert this using 1
  rw [← hfun]
  exact h4

theorem hasDerivAt_poiComp (m : ℕ) :
    HasDerivAt (fun p : ℝ => poi (1 - p) m) (poiD m) 1 := by
  have hinner : HasDerivAt (fun p : ℝ => -(1 - p)) 1 1 := by
    have h : HasDerivAt (fun p : ℝ => p - 1) 1 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).sub_const 1
    have hfun : (fun p : ℝ => p - 1) = fun p : ℝ => -(1 - p) := by
      funext p
      ring
    rwa [hfun] at h
  have hexp : HasDerivAt (fun p : ℝ => Real.exp (-(1 - p)))
      (Real.exp (-(1 - 1)) * 1) 1 := hinner.exp
  have hsub : HasDerivAt (fun p : ℝ => 1 - p) (-1) 1 :=
    (hasDerivAt_id 1).const_sub 1
  have hpow : HasDerivAt (fun p : ℝ => (1 - p) ^ m)
      ((m : ℝ) * ((1 : ℝ) - 1) ^ (m - 1) * (-1)) 1 := hsub.pow m
  have h3 := (hexp.mul hpow).div_const ((m.factorial : ℕ) : ℝ)
  have hval :
      (Real.exp (-(1 - 1)) * 1 * ((1 : ℝ) - 1) ^ m +
          Real.exp (-(1 - 1)) * ((m : ℝ) * ((1 : ℝ) - 1) ^ (m - 1) * (-1))) /
        ((m.factorial : ℕ) : ℝ) = poiD m := by
    rw [show (1 : ℝ) - 1 = 0 by ring, show -(0 : ℝ) = 0 by ring, Real.exp_zero]
    unfold poiD
    rcases m with _ | m
    · simp
    · rcases m with _ | m
      · norm_num [Nat.factorial]
      · have e1 : m + 2 ≠ 0 := by omega
        have e2 : m + 2 - 1 ≠ 0 := by omega
        rw [if_neg (by omega), if_neg (by omega), zero_pow e1, zero_pow e2]
        ring
  rw [← hval]
  have hfun : (fun p : ℝ => Real.exp (-(1 - p)) * (1 - p) ^ m /
      ((m.factorial : ℕ) : ℝ)) = fun p : ℝ => poi (1 - p) m := by
    funext p
    unfold poi
    rfl
  rw [← hfun]
  exact h3

/-- The `p`-derivative of a kernel entry at `p = 1`. -/
def KD (x y : ℕ) : ℝ :=
  ∑ k ∈ range (y + 1), (binD x k * poi 0 (y - k) + bin x 1 k * poiD (y - k))

theorem hasDerivAt_K_p (x y : ℕ) :
    HasDerivAt (fun p : ℝ => K p x y) (KD x y) 1 := by
  have hterm : ∀ k ∈ range (y + 1),
      HasDerivAt (fun p : ℝ => bin x p k * poi (1 - p) (y - k))
        (binD x k * poi (1 - 1) (y - k) + bin x 1 k * poiD (y - k)) 1 :=
    fun k _ => (hasDerivAt_bin x k).mul (hasDerivAt_poiComp (y - k))
  have h := HasDerivAt.sum hterm
  have hval : ∑ k ∈ range (y + 1),
      (binD x k * poi (1 - 1) (y - k) + bin x 1 k * poiD (y - k)) = KD x y := by
    unfold KD
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (1 : ℝ) - 1 = 0 by ring]
  rw [hval] at h
  have hfun2 : (∑ k ∈ range (y + 1),
      fun p : ℝ => bin x p k * poi (1 - p) (y - k)) =
      fun p : ℝ => K p x y := by
    funext p
    rw [Finset.sum_apply]
    exact (K_apply p x y).symm
  rwa [hfun2] at h

theorem KD_eq (x y : ℕ) : KD x y = -(rate x y) := by
  unfold KD
  rw [Finset.sum_add_distrib]
  have hS1 : ∑ k ∈ range (y + 1), binD x k * poi 0 (y - k) = binD x y := by
    rw [Finset.sum_eq_single_of_mem y (Finset.self_mem_range_succ y)]
    · rw [show y - y = 0 by omega, poi_zero_eval, if_pos rfl, mul_one]
    · intro k hk hne
      have hky : k < y := by
        have := Finset.mem_range.mp hk
        omega
      rw [poi_zero_eval, if_neg (by omega), mul_zero]
  have hS2 : ∑ k ∈ range (y + 1), bin x 1 k * poiD (y - k) =
      if x ≤ y then poiD (y - x) else 0 := by
    by_cases hxy : x ≤ y
    · rw [if_pos hxy]
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_range.mpr (by omega))]
      · rw [bin_one_eval, if_pos rfl, one_mul]
      · intro k hk hne
        rw [bin_one_eval, if_neg hne, zero_mul]
    · rw [if_neg hxy]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkx : k ≠ x := by
        have := Finset.mem_range.mp hk
        omega
      rw [bin_one_eval, if_neg hkx, zero_mul]
  rw [hS1, hS2]
  unfold binD poiD rate
  split_ifs <;> first | ring1 | (exfalso; omega)

/-- **The generator theorem (the counted rates).** The instantaneous
rates of the untruncated kernel at `t = 0` are exactly the
ledger-counted birth-death rates: birth `1`, per-label death `x`,
diagonal `-(x+1)`. This is the pinning that makes the explicit kernel
THE ledger-counted chain; the death rate proportional to the posted
count is where the counted selection enters the untruncated dynamics. -/
theorem hasDerivAt_Kt (x y : ℕ) :
    HasDerivAt (fun t : ℝ => Kt t x y) (rate x y) 0 := by
  have hp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).neg).exp
    simpa using h
  have hK : HasDerivAt (fun p : ℝ => K p x y) (KD x y) (Real.exp (-(0 : ℝ))) := by
    have := hasDerivAt_K_p x y
    simpa using this
  have h := hK.comp 0 hp
  have hcomp : ((fun p : ℝ => K p x y) ∘ fun t : ℝ => Real.exp (-t)) =
      fun t : ℝ => Kt t x y := by
    funext t
    rfl
  rw [hcomp] at h
  have hval : KD x y * (-1) = rate x y := by
    rw [KD_eq]
    ring
  rwa [hval] at h

/-! ## Stationarity: the inverse-factorial law is invariant; the unit
birth rate selects the intensity -/

/-- Thinning a Poisson field: pushing `poi a` through the binomial
kernel with survival `q` gives `poi (a * q)`. -/
theorem hasSum_thin_poi (a q : ℝ) (k : ℕ) :
    HasSum (fun x => poi a x * bin x q k) (poi (a * q) k) := by
  set F := fun x => poi a x * bin x q k with hF
  have hshift : ∀ w : ℕ, F (w + k) =
      (Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ)) *
        ((a * (1 - q)) ^ w / (w.factorial : ℝ)) := by
    intro w
    have hcast : ((w + k).choose k : ℝ) =
        ((w + k).factorial : ℝ) / ((k.factorial : ℝ) * (w.factorial : ℝ)) := by
      have h := Nat.cast_choose ℝ (Nat.le_add_left k w)
      rwa [show w + k - k = w by omega] at h
    have hwk : (((w + k).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (w + k).factorial_pos.ne'
    have hkf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast k.factorial_pos.ne'
    have hwf : ((w.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast w.factorial_pos.ne'
    show poi a (w + k) * bin (w + k) q k =
      Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ) *
        ((a * (1 - q)) ^ w / (w.factorial : ℝ))
    unfold poi bin
    rw [show w + k - k = w by omega, hcast]
    rw [show a ^ (w + k) = a ^ w * a ^ k by rw [pow_add], mul_pow a (1 - q) w]
    field_simp
    ring
  have hsum_w : HasSum (fun w => F (w + k))
      (Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ) *
        Real.exp (a * (1 - q))) := by
    have h := (hasSum_exp_series (a * (1 - q))).mul_left
      (Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ))
    have hfun : (fun w => Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ) *
        ((a * (1 - q)) ^ w / (w.factorial : ℝ))) = fun w => F (w + k) := by
      funext w
      rw [hshift w]
    rwa [hfun] at h
  have hval : Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ) *
      Real.exp (a * (1 - q)) = poi (a * q) k := by
    unfold poi
    rw [show Real.exp (-a) * (a * q) ^ k / (k.factorial : ℝ) *
        Real.exp (a * (1 - q)) =
        (Real.exp (-a) * Real.exp (a * (1 - q))) * (a * q) ^ k /
          (k.factorial : ℝ) by ring]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hval] at hsum_w
  have h := (hasSum_nat_add_iff k).mp hsum_w
  have hzero : ∑ i ∈ range k, F i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    show poi a i * bin i q k = 0
    rw [bin_of_lt i q hik]
    ring
  rwa [hzero, add_zero] at h

/-- Pushing `poi c` through one kernel step gives the Poisson law with
the interpolated intensity `c*p + (1-p)`. -/
theorem hasSum_poi_K (c p : ℝ) (y : ℕ) :
    HasSum (fun x => poi c x * K p x y) (poi (c * p + (1 - p)) y) := by
  have hfun : (fun x => poi c x * K p x y) =
      fun x => ∑ k ∈ range (y + 1),
        (poi c x * bin x p k) * poi (1 - p) (y - k) := by
    funext x
    rw [K_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  have hsum := hasSum_sum (s := range (y + 1))
    (f := fun k x => (poi c x * bin x p k) * poi (1 - p) (y - k))
    (a := fun k => poi (c * p) k * poi (1 - p) (y - k))
    (fun k _ => (hasSum_thin_poi c p k).mul_right (poi (1 - p) (y - k)))
  have hval : ∑ k ∈ range (y + 1), poi (c * p) k * poi (1 - p) (y - k) =
      poi (c * p + (1 - p)) y := poi_conv (c * p) (1 - p) y
  rwa [hval] at hsum

/-- **Stationarity.** The Poisson(1) law (the normalized
inverse-factorial weight) is invariant under the untruncated
ledger-counted kernel at every time. -/
theorem poi_one_stationary (p : ℝ) (y : ℕ) :
    HasSum (fun x => poi 1 x * K p x y) (poi 1 y) := by
  have h := hasSum_poi_K 1 p y
  rwa [show (1 : ℝ) * p + (1 - p) = 1 by ring] at h

/-- **Decoy scored: the unit birth rate selects the intensity.** For
`c ≠ 1` the Poisson(c) law is NOT stationary: one kernel step moves it
to intensity `c*p + (1-p) ≠ c`. The balance formalism is
intensity-blind; it is the unit birth rate (one fresh posting per
tick) against the per-label death rate that pins Poisson(1). -/
theorem poi_ne_one_not_stationary (c p : ℝ) (hc : c ≠ 1) (hp : p ≠ 1) :
    (fun y => ∑' x, poi c x * K p x y) ≠ poi c := by
  intro hstat
  have h0 : (∑' x, poi c x * K p x 0) = poi (c * p + (1 - p)) 0 :=
    (hasSum_poi_K c p 0).tsum_eq
  have h1 : poi (c * p + (1 - p)) 0 = poi c 0 := by
    rw [← h0]
    exact congrFun hstat 0
  unfold poi at h1
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] at h1
  have h2 : -(c * p + (1 - p)) = -c := Real.exp_injective h1
  have h3 : (c - 1) * (p - 1) = 0 := by nlinarith [h2]
  rcases mul_eq_zero.mp h3 with h | h
  · exact hc (by linarith)
  · exact hp (by linarith)

/-! ## The Chapman-Kolmogorov semigroup law -/

/-- pmf-level Pascal: peeling one trial off the binomial. -/
theorem bin_step (z : ℕ) (q : ℝ) (k : ℕ) :
    bin (z + 1) q k =
      (1 - q) * bin z q k + q * (if k = 0 then 0 else bin z q (k - 1)) := by
  rcases k with _ | k
  · rw [if_pos rfl]
    unfold bin
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero]
    rw [show z + 1 - 0 = (z - 0) + 1 by omega]
    ring
  · rw [if_neg (by omega), show k + 1 - 1 = k by omega]
    by_cases hkz : k + 1 ≤ z + 1
    · unfold bin
      rw [Nat.choose_succ_succ' z k]
      push_cast
      by_cases hkz2 : k + 1 ≤ z
      · rw [show z - k = (z - (k + 1)) + 1 by omega]
        ring
      · have hzk : z = k := by omega
        rw [hzk, Nat.choose_eq_zero_of_lt (show k < k + 1 by omega),
          show k - (k + 1) = 0 by omega, show k - k = 0 by omega]
        push_cast
        ring
    · rw [bin_of_lt (z + 1) q (by omega), bin_of_lt z q (by omega),
        bin_of_lt z q (by omega)]
      ring

/-- pmf-level Vandermonde: the convolution of two binomials with the
same survival probability is the binomial of the summed populations. -/
theorem conv_bin_bin (k w : ℕ) (q : ℝ) :
    ∀ j, conv (bin k q) (bin w q) j = bin (k + w) q j := by
  induction k with
  | zero =>
      intro j
      unfold conv
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
      · rw [bin_zero_left, if_pos rfl, one_mul, show j - 0 = j by omega,
          show 0 + w = w by omega]
      · intro i hi hne
        rw [bin_zero_left, if_neg hne, zero_mul]
  | succ k ih =>
      intro j
      have hexpand : conv (bin (k + 1) q) (bin w q) j =
          (∑ i ∈ range j, bin (k + 1) q (i + 1) * bin w q (j - (i + 1))) +
            bin (k + 1) q 0 * bin w q (j - 0) := by
        unfold conv
        rw [Finset.sum_range_succ' (fun i => bin (k + 1) q i * bin w q (j - i)) j]
      rw [hexpand]
      have hstep0 : bin (k + 1) q 0 = (1 - q) * bin k q 0 := by
        rw [bin_step, if_pos rfl]
        ring
      have hstepi : ∀ i, bin (k + 1) q (i + 1) =
          (1 - q) * bin k q (i + 1) + q * bin k q i := by
        intro i
        rw [bin_step, if_neg (by omega), show i + 1 - 1 = i by omega]
      have hsplit : ∑ i ∈ range j, bin (k + 1) q (i + 1) * bin w q (j - (i + 1)) =
          (1 - q) * ∑ i ∈ range j, bin k q (i + 1) * bin w q (j - (i + 1)) +
            q * ∑ i ∈ range j, bin k q i * bin w q (j - (i + 1)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hstepi i]
        ring
      rw [hsplit, hstep0]
      have hconvj : (1 - q) * ∑ i ∈ range j, bin k q (i + 1) * bin w q (j - (i + 1)) +
          (1 - q) * bin k q 0 * bin w q (j - 0) =
          (1 - q) * conv (bin k q) (bin w q) j := by
        unfold conv
        rw [Finset.sum_range_succ' (fun i => bin k q i * bin w q (j - i)) j]
        ring
      have hconvj1 : q * ∑ i ∈ range j, bin k q i * bin w q (j - (i + 1)) =
          q * (if j = 0 then 0 else conv (bin k q) (bin w q) (j - 1)) := by
        rcases j with _ | j
        · simp
        · rw [if_neg (by omega)]
          congr 1
          unfold conv
          rw [show j + 1 - 1 = j by omega]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [show j + 1 - (i + 1) = j - i by omega]
      calc (1 - q) * ∑ i ∈ range j, bin k q (i + 1) * bin w q (j - (i + 1)) +
            q * ∑ i ∈ range j, bin k q i * bin w q (j - (i + 1)) +
            (1 - q) * bin k q 0 * bin w q (j - 0)
          = ((1 - q) * ∑ i ∈ range j, bin k q (i + 1) * bin w q (j - (i + 1)) +
              (1 - q) * bin k q 0 * bin w q (j - 0)) +
            q * ∑ i ∈ range j, bin k q i * bin w q (j - (i + 1)) := by ring
        _ = (1 - q) * conv (bin k q) (bin w q) j +
            q * (if j = 0 then 0 else conv (bin k q) (bin w q) (j - 1)) := by
            rw [hconvj, hconvj1]
        _ = (1 - q) * bin (k + w) q j +
            q * (if j = 0 then 0 else bin (k + w) q (j - 1)) := by
            rw [ih j]
            rcases j with _ | j
            · simp
            · rw [if_neg (by omega), if_neg (by omega), ih (j + 1 - 1)]
        _ = bin (k + w + 1) q j := by rw [bin_step (k + w) q j]
        _ = bin (k + 1 + w) q j := by rw [show k + w + 1 = k + 1 + w by omega]

/-- Finite thinning: composing two binomial kernels multiplies the
survival probabilities. -/
theorem thin_bin (x : ℕ) (p q : ℝ) :
    ∀ j, ∑ z ∈ range (x + 1), bin x p z * bin z q j = bin x (p * q) j := by
  induction x with
  | zero =>
      intro j
      rw [Finset.sum_range_one]
      rw [bin_zero_left, bin_zero_left, bin_zero_left]
      by_cases hj : j = 0 <;> simp [hj]
  | succ x ih =>
      intro j
      have hexpand : ∑ z ∈ range (x + 2), bin (x + 1) p z * bin z q j =
          (∑ z ∈ range (x + 1), bin (x + 1) p (z + 1) * bin (z + 1) q j) +
            bin (x + 1) p 0 * bin 0 q j := by
        rw [Finset.sum_range_succ' (fun z => bin (x + 1) p z * bin z q j) (x + 1)]
      rw [hexpand]
      have hstepz : ∀ z, bin (x + 1) p (z + 1) =
          (1 - p) * bin x p (z + 1) + p * bin x p z := by
        intro z
        rw [bin_step, if_neg (by omega), show z + 1 - 1 = z by omega]
      have hstep0 : bin (x + 1) p 0 = (1 - p) * bin x p 0 := by
        rw [bin_step, if_pos rfl]
        ring
      have hsplit : ∑ z ∈ range (x + 1), bin (x + 1) p (z + 1) * bin (z + 1) q j =
          (1 - p) * ∑ z ∈ range (x + 1), bin x p (z + 1) * bin (z + 1) q j +
            p * ∑ z ∈ range (x + 1), bin x p z * bin (z + 1) q j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [hstepz z]
        ring
      rw [hsplit, hstep0]
      have hA : (1 - p) * ∑ z ∈ range (x + 1), bin x p (z + 1) * bin (z + 1) q j +
          (1 - p) * bin x p 0 * bin 0 q j =
          (1 - p) * ∑ z ∈ range (x + 2), bin x p z * bin z q j := by
        rw [Finset.sum_range_succ' (fun z => bin x p z * bin z q j) (x + 1)]
        ring
      have hAtrim : ∑ z ∈ range (x + 2), bin x p z * bin z q j =
          ∑ z ∈ range (x + 1), bin x p z * bin z q j := by
        rw [Finset.sum_range_succ]
        rw [bin_of_lt x p (by omega)]
        ring
      have hB : ∀ z, bin x p z * bin (z + 1) q j =
          (1 - q) * (bin x p z * bin z q j) +
            q * (if j = 0 then 0 else bin x p z * bin z q (j - 1)) := by
        intro z
        rw [bin_step z q j]
        rcases j with _ | j
        · rw [if_pos rfl, if_pos rfl]
          ring
        · rw [if_neg (by omega), if_neg (by omega)]
          ring
      have hBsum : ∑ z ∈ range (x + 1), bin x p z * bin (z + 1) q j =
          (1 - q) * bin x (p * q) j +
            q * (if j = 0 then 0 else bin x (p * q) (j - 1)) := by
        rw [Finset.sum_congr rfl fun z _ => hB z, Finset.sum_add_distrib,
          ← Finset.mul_sum]
        rcases j with _ | j
        · simp only [if_pos rfl, mul_zero, Finset.sum_const_zero, add_zero]
          rw [ih 0]
          simp
        · simp only [if_neg (Nat.succ_ne_zero j)]
          rw [← Finset.mul_sum, ih (j + 1), show j + 1 - 1 = j by omega, ih j]
      calc (1 - p) * ∑ z ∈ range (x + 1), bin x p (z + 1) * bin (z + 1) q j +
            p * ∑ z ∈ range (x + 1), bin x p z * bin (z + 1) q j +
            (1 - p) * bin x p 0 * bin 0 q j
          = ((1 - p) * ∑ z ∈ range (x + 1), bin x p (z + 1) * bin (z + 1) q j +
              (1 - p) * bin x p 0 * bin 0 q j) +
            p * ∑ z ∈ range (x + 1), bin x p z * bin (z + 1) q j := by ring
        _ = (1 - p) * ∑ z ∈ range (x + 1), bin x p z * bin z q j +
            p * ((1 - q) * bin x (p * q) j +
              q * (if j = 0 then 0 else bin x (p * q) (j - 1))) := by
            rw [hA, hAtrim, hBsum]
        _ = (1 - p) * bin x (p * q) j +
            p * ((1 - q) * bin x (p * q) j +
              q * (if j = 0 then 0 else bin x (p * q) (j - 1))) := by
            have hthin : ∑ z ∈ range (x + 1), bin x p z * bin z q j =
                bin x (p * q) j := by
              have h := ih j
              have hz : ∑ z ∈ range (x + 1), bin x p z * bin z q j =
                  ∑ z ∈ range (x + 1), bin x p z * bin z q j := rfl
              exact h
            rw [hthin]
        _ = (1 - p * q) * bin x (p * q) j +
            (p * q) * (if j = 0 then 0 else bin x (p * q) (j - 1)) := by ring
        _ = bin (x + 1) (p * q) j := by rw [bin_step x (p * q) j]

/-- Thinning one shifted Poisson block: the survivors of the `k` marked
quanta and the thinned Poisson field separate into a convolution. -/
theorem hasSum_shift_thin (k : ℕ) (a q : ℝ) (j : ℕ) :
    HasSum (fun z => shift k (poi a) z * bin z q j)
      (conv (bin k q) (poi (a * q)) j) := by
  set F := fun z => shift k (poi a) z * bin z q j with hF
  have hshift : ∀ w : ℕ, F (w + k) = poi a w * bin (w + k) q j := by
    intro w
    rw [hF]
    simp only
    rw [shift, if_pos (Nat.le_add_left k w), show w + k - k = w by omega]
  have hvander : ∀ w : ℕ, poi a w * bin (w + k) q j =
      ∑ j1 ∈ range (j + 1), bin k q j1 * (poi a w * bin w q (j - j1)) := by
    intro w
    have h := conv_bin_bin k w q j
    unfold conv at h
    rw [show w + k = k + w by omega, ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    ring
  have hsum_w : HasSum (fun w => poi a w * bin (w + k) q j)
      (∑ j1 ∈ range (j + 1), bin k q j1 * poi (a * q) (j - j1)) := by
    have hfun : (fun w => poi a w * bin (w + k) q j) =
        fun w => ∑ j1 ∈ range (j + 1), bin k q j1 * (poi a w * bin w q (j - j1)) := by
      funext w
      exact hvander w
    rw [hfun]
    exact hasSum_sum fun j1 _ =>
      (hasSum_thin_poi a q (j - j1)).mul_left (bin k q j1)
  have hsum_shifted : HasSum (fun w => F (w + k))
      (conv (bin k q) (poi (a * q)) j) := by
    have hfun : (fun w => F (w + k)) = fun w => poi a w * bin (w + k) q j := by
      funext w
      exact hshift w
    rw [hfun]
    exact hsum_w
  have h := (hasSum_nat_add_iff k).mp hsum_shifted
  have hzero : ∑ i ∈ range k, F i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    rw [hF]
    simp only
    rw [shift, if_neg (by omega)]
    ring
  rwa [hzero, add_zero] at h

/-- Thinning a kernel row: pushing `K p x` through the binomial kernel
with survival `q`. -/
theorem hasSum_K_thin (p q : ℝ) (x j : ℕ) :
    HasSum (fun z => K p x z * bin z q j)
      (conv (bin x (p * q)) (poi ((1 - p) * q)) j) := by
  have hKrow : ∀ z, K p x z =
      ∑ k ∈ range (x + 1), bin x p k * shift k (poi (1 - p)) z :=
    conv_eq_sum_shift (bin x p) (poi (1 - p)) (x + 1) (bin_support x p)
  have hfun : (fun z => K p x z * bin z q j) =
      fun z => ∑ k ∈ range (x + 1),
        bin x p k * (shift k (poi (1 - p)) z * bin z q j) := by
    funext z
    rw [hKrow z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun]
  have hsum := hasSum_sum (s := range (x + 1))
    (f := fun k z => bin x p k * (shift k (poi (1 - p)) z * bin z q j))
    (a := fun k => bin x p k * conv (bin k q) (poi ((1 - p) * q)) j)
    (fun k _ => (hasSum_shift_thin k (1 - p) q j).mul_left (bin x p k))
  have hval : ∑ k ∈ range (x + 1), bin x p k * conv (bin k q) (poi ((1 - p) * q)) j =
      conv (bin x (p * q)) (poi ((1 - p) * q)) j := by
    unfold conv
    calc ∑ k ∈ range (x + 1), bin x p k *
            ∑ j1 ∈ range (j + 1), bin k q j1 * poi ((1 - p) * q) (j - j1)
        = ∑ k ∈ range (x + 1), ∑ j1 ∈ range (j + 1),
            bin x p k * bin k q j1 * poi ((1 - p) * q) (j - j1) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j1 _ => ?_
          ring
      _ = ∑ j1 ∈ range (j + 1), ∑ k ∈ range (x + 1),
            bin x p k * bin k q j1 * poi ((1 - p) * q) (j - j1) :=
          Finset.sum_comm
      _ = ∑ j1 ∈ range (j + 1), bin x (p * q) j1 * poi ((1 - p) * q) (j - j1) := by
          refine Finset.sum_congr rfl fun j1 _ => ?_
          rw [← Finset.sum_mul, thin_bin x p q j1]
  rwa [hval] at hsum

/-- **Chapman-Kolmogorov.** Composing kernel steps with survival
probabilities `p` then `q` (an infinite sum over the intermediate
state) gives the kernel step with survival `p * q`: the family is a
genuine semigroup, not an interpolation. -/
theorem chapman (p q : ℝ) (x y : ℕ) :
    HasSum (fun z => K p x z * K q z y) (K (p * q) x y) := by
  have hfun : (fun z => K p x z * K q z y) =
      fun z => ∑ j ∈ range (y + 1),
        (K p x z * bin z q j) * poi (1 - q) (y - j) := by
    funext z
    rw [K_apply q z y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hfun]
  have hsum := hasSum_sum (s := range (y + 1))
    (f := fun j z => (K p x z * bin z q j) * poi (1 - q) (y - j))
    (a := fun j => conv (bin x (p * q)) (poi ((1 - p) * q)) j * poi (1 - q) (y - j))
    (fun j _ => (hasSum_K_thin p q x j).mul_right (poi (1 - q) (y - j)))
  have hval : ∑ j ∈ range (y + 1),
      conv (bin x (p * q)) (poi ((1 - p) * q)) j * poi (1 - q) (y - j) =
      K (p * q) x y := by
    have h1 : ∑ j ∈ range (y + 1),
        conv (bin x (p * q)) (poi ((1 - p) * q)) j * poi (1 - q) (y - j) =
        conv (conv (bin x (p * q)) (poi ((1 - p) * q))) (poi (1 - q)) y := rfl
    rw [h1, conv_assoc]
    have h2 : conv (poi ((1 - p) * q)) (poi (1 - q)) = poi (1 - p * q) := by
      funext m
      rw [poi_conv]
      congr 1
      ring
    rw [h2]
    rfl
  rwa [hval] at hsum

/-- The semigroup law in physical time. -/
theorem Kt_semigroup (s t : ℝ) (x y : ℕ) :
    HasSum (fun z => Kt s x z * Kt t z y) (Kt (s + t) x y) := by
  have h := chapman (Real.exp (-s)) (Real.exp (-t)) x y
  have h1 : Real.exp (-s) * Real.exp (-t) = Real.exp (-(s + t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1] at h
  exact h

/-! ## Attainment: the explicit total-variation bound -/

/-- **The convolution drift bound.** Convolving a probability law `f`
with a probability law `g` moves it, in the l1 (twice total-variation)
metric, by at most twice the mass `g` puts off zero. -/
theorem conv_l1_bound (g f : ℕ → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hgs : HasSum g 1)
    (hf0 : ∀ k, 0 ≤ f k) (hfs : HasSum f 1) :
    ∑' y, |conv g f y - f y| ≤ 2 * (1 - g 0) := by
  set A : ℕ → ℝ := fun y => ∑ k ∈ range y, g (k + 1) * f (y - (k + 1)) with hA
  have hg0le1 : g 0 ≤ 1 := le_hasSum hgs 0 fun b _ => hg0 b
  have hconv : ∀ y, conv g f y = A y + g 0 * f y := by
    intro y
    unfold conv
    rw [Finset.sum_range_succ' (fun k => g k * f (y - k)) y]
    rw [hA]
    simp
  have hAnn : ∀ y, 0 ≤ A y := by
    intro y
    rw [hA]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hg0 _) (hf0 _)
  have hgtail : ∀ M : ℕ, ∑ k ∈ range M, g (k + 1) ≤ 1 - g 0 := by
    intro M
    have h1 : ∑ k ∈ range (M + 1), g k ≤ 1 :=
      sum_le_hasSum (range (M + 1)) (fun k _ => hg0 k) hgs
    have h2 : ∑ k ∈ range (M + 1), g k =
        (∑ k ∈ range M, g (k + 1)) + g 0 :=
      Finset.sum_range_succ' g M
    rw [h2] at h1
    linarith
  have hAbound : ∀ M : ℕ, ∑ y ∈ range M, A y ≤ 1 - g 0 := by
    intro M
    have hpad : ∀ y ∈ range M, A y =
        ∑ k ∈ range M, (if k < y then g (k + 1) * f (y - (k + 1)) else 0) := by
      intro y hy
      have hyM : y ≤ M := le_of_lt (Finset.mem_range.mp hy)
      rw [hA]
      simp only
      rw [show (∑ k ∈ range y, g (k + 1) * f (y - (k + 1))) =
          ∑ k ∈ range y, (if k < y then g (k + 1) * f (y - (k + 1)) else 0) from
        Finset.sum_congr rfl fun k hk => by
          rw [if_pos (Finset.mem_range.mp hk)]]
      refine Finset.sum_subset (Finset.range_subset_range.mpr hyM) fun k _ hk => ?_
      rw [if_neg (by simpa [Finset.mem_range] using hk)]
    rw [Finset.sum_congr rfl hpad, Finset.sum_comm]
    have hinner : ∀ k ∈ range M,
        (∑ y ∈ range M, if k < y then g (k + 1) * f (y - (k + 1)) else 0) ≤
          g (k + 1) := by
      intro k _
      have hfilter :
          (∑ y ∈ range M, if k < y then g (k + 1) * f (y - (k + 1)) else 0) =
          ∑ y ∈ Finset.Ico (k + 1) M, g (k + 1) * f (y - (k + 1)) := by
        rw [← Finset.sum_filter]
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      have hshift2 :
          ∑ y ∈ Finset.Ico (k + 1) M, f (y - (k + 1)) =
          ∑ i ∈ range (M - (k + 1)), f i := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show k + 1 + i - (k + 1) = i by omega]
      have hle1 : ∑ i ∈ range (M - (k + 1)), f i ≤ 1 :=
        sum_le_hasSum (range (M - (k + 1))) (fun i _ => hf0 i) hfs
      calc (∑ y ∈ range M, if k < y then g (k + 1) * f (y - (k + 1)) else 0)
          = g (k + 1) * ∑ y ∈ Finset.Ico (k + 1) M, f (y - (k + 1)) := by
            rw [hfilter, Finset.mul_sum]
        _ = g (k + 1) * ∑ i ∈ range (M - (k + 1)), f i := by rw [hshift2]
        _ ≤ g (k + 1) * 1 := mul_le_mul_of_nonneg_left hle1 (hg0 _)
        _ = g (k + 1) := mul_one _
    calc ∑ k ∈ range M, ∑ y ∈ range M,
          (if k < y then g (k + 1) * f (y - (k + 1)) else 0)
        ≤ ∑ k ∈ range M, g (k + 1) := Finset.sum_le_sum hinner
      _ ≤ 1 - g 0 := hgtail M
  have hAsummable : Summable A := summable_of_sum_range_le hAnn hAbound
  have htsumA : ∑' y, A y ≤ 1 - g 0 := Real.tsum_le_of_sum_range_le hAnn hAbound
  have hpoint : ∀ y, |conv g f y - f y| ≤ A y + (1 - g 0) * f y := by
    intro y
    rw [hconv y]
    have h1 : A y + g 0 * f y - f y = A y - (1 - g 0) * f y := by ring
    rw [h1]
    have h2 : |A y - (1 - g 0) * f y| ≤ |A y| + |(1 - g 0) * f y| := by
      calc |A y - (1 - g 0) * f y|
          = |A y + -((1 - g 0) * f y)| := by rw [sub_eq_add_neg]
        _ ≤ |A y| + |-((1 - g 0) * f y)| := abs_add_le _ _
        _ = |A y| + |(1 - g 0) * f y| := by rw [abs_neg]
    rw [abs_of_nonneg (hAnn y),
      abs_of_nonneg (mul_nonneg (by linarith) (hf0 y))] at h2
    exact h2
  have hRHSsummable : Summable (fun y => A y + (1 - g 0) * f y) :=
    hAsummable.add (hfs.summable.mul_left (1 - g 0))
  have hLHSsummable : Summable (fun y => |conv g f y - f y|) :=
    Summable.of_nonneg_of_le (fun y => abs_nonneg _) hpoint hRHSsummable
  calc ∑' y, |conv g f y - f y|
      ≤ ∑' y, (A y + (1 - g 0) * f y) :=
        Summable.tsum_le_tsum hpoint hLHSsummable hRHSsummable
    _ = (∑' y, A y) + (1 - g 0) * ∑' y, f y := by
        rw [Summable.tsum_add hAsummable (hfs.summable.mul_left (1 - g 0)),
          tsum_mul_left]
    _ = (∑' y, A y) + (1 - g 0) := by rw [hfs.tsum_eq, mul_one]
    _ ≤ (1 - g 0) + (1 - g 0) := by linarith
    _ = 2 * (1 - g 0) := by ring

/-- l1 distance from one kernel row to the Poisson(1) law, in terms of
the survival probability. -/
theorem point_l1 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) :
    ∑' y, |K p x y - poi 1 y| ≤
      2 * (1 - (1 - p) ^ x) + 2 * (1 - Real.exp (-p)) := by
  have h1p : (0 : ℝ) ≤ 1 - p := by linarith
  -- leg one: the kernel row against its own immigration field
  have hleg1 : ∑' y, |K p x y - poi (1 - p) y| ≤ 2 * (1 - (1 - p) ^ x) := by
    have h := conv_l1_bound (bin x p) (poi (1 - p))
      (bin_nonneg x hp0 hp1) (hasSum_bin x p)
      (poi_nonneg h1p) (hasSum_poi (1 - p))
    rwa [bin_apply_zero] at h
  -- leg two: the immigration field against Poisson(1)
  have hleg2 : ∑' y, |poi (1 - p) y - poi 1 y| ≤ 2 * (1 - Real.exp (-p)) := by
    have hconv1 : conv (poi p) (poi (1 - p)) = poi 1 := by
      funext m
      rw [poi_conv]
      congr 1
      ring
    have h := conv_l1_bound (poi p) (poi (1 - p))
      (poi_nonneg hp0) (hasSum_poi p)
      (poi_nonneg h1p) (hasSum_poi (1 - p))
    rw [hconv1] at h
    have hpoi_p0 : poi p 0 = Real.exp (-p) := by
      unfold poi
      simp
    rw [hpoi_p0] at h
    calc ∑' y, |poi (1 - p) y - poi 1 y|
        = ∑' y, |poi 1 y - poi (1 - p) y| := by
          refine tsum_congr fun y => ?_
          rw [abs_sub_comm]
      _ ≤ 2 * (1 - Real.exp (-p)) := h
  -- summabilities for the triangle inequality
  have hsK : Summable (fun y => |K p x y - poi (1 - p) y|) :=
    ((hasSum_K p x).summable.sub (hasSum_poi (1 - p)).summable).abs
  have hs2 : Summable (fun y => |poi (1 - p) y - poi 1 y|) :=
    ((hasSum_poi (1 - p)).summable.sub (hasSum_poi 1).summable).abs
  have hsL : Summable (fun y => |K p x y - poi 1 y|) :=
    ((hasSum_K p x).summable.sub (hasSum_poi 1).summable).abs
  have htriangle : ∑' y, |K p x y - poi 1 y| ≤
      (∑' y, |K p x y - poi (1 - p) y|) + ∑' y, |poi (1 - p) y - poi 1 y| := by
    have hpt : ∀ y, |K p x y - poi 1 y| ≤
        |K p x y - poi (1 - p) y| + |poi (1 - p) y - poi 1 y| := by
      intro y
      have := abs_sub_le (K p x y) (poi (1 - p) y) (poi 1 y)
      linarith
    calc ∑' y, |K p x y - poi 1 y|
        ≤ ∑' y, (|K p x y - poi (1 - p) y| + |poi (1 - p) y - poi 1 y|) :=
          Summable.tsum_le_tsum hpt hsL (hsK.add hs2)
      _ = (∑' y, |K p x y - poi (1 - p) y|) +
            ∑' y, |poi (1 - p) y - poi 1 y| := Summable.tsum_add hsK hs2
  linarith

/-- **Point attainment with the explicit rate.** Each kernel row at
time `t` is within `2 * (x + 1) * exp (-t)` of the Poisson(1) law in
the l1 metric. -/
theorem Kt_l1 {t : ℝ} (ht : 0 ≤ t) (x : ℕ) :
    ∑' y, |Kt t x y - poi 1 y| ≤ 2 * ((x : ℝ) + 1) * Real.exp (-t) := by
  set p := Real.exp (-t) with hp
  have hp0 : 0 < p := Real.exp_pos _
  have hp1 : p ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -t ≤ 0 by linarith)
    rwa [Real.exp_zero] at h
  have h := point_l1 (le_of_lt hp0) hp1 x
  have hbin : 1 - (1 - p) ^ x ≤ (x : ℝ) * p := by
    have hber := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith) x
    rw [show (1 : ℝ) + -p = 1 - p by ring] at hber
    nlinarith [hber]
  have hexp : 1 - Real.exp (-p) ≤ p := by
    have := Real.add_one_le_exp (-p)
    linarith
  calc ∑' y, |Kt t x y - poi 1 y|
      ≤ 2 * (1 - (1 - p) ^ x) + 2 * (1 - Real.exp (-p)) := h
    _ ≤ 2 * ((x : ℝ) * p) + 2 * p := by
        have h1 : 2 * (1 - (1 - p) ^ x) ≤ 2 * ((x : ℝ) * p) := by linarith
        have h2 : 2 * (1 - Real.exp (-p)) ≤ 2 * p := by linarith
        linarith
    _ = 2 * ((x : ℝ) + 1) * p := by ring

/-! ## Attainment from lawful initial data -/

/-- Evolution of a finitely supported initial distribution. -/
def evolve (μ : ℕ → ℝ) (N : ℕ) (t : ℝ) (y : ℕ) : ℝ :=
  ∑ x ∈ range N, μ x * Kt t x y

/-- **The untruncated attainment organ.** Every finitely supported
initial distribution on the untruncated ledger-counted chain is carried
to the normalized inverse-factorial (Poisson(1)) law, with l1 (twice
total-variation) distance at most `2 * (first moment + 1) * exp (-t)`.
The truncation scoping named by the truncated organ's honest-scope note
is removed: this is the untruncated chain, one statement, all of `Nat`. -/
theorem attainment (μ : ℕ → ℝ) (N : ℕ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμsum : ∑ x ∈ range N, μ x = 1) {t : ℝ} (ht : 0 ≤ t) :
    ∑' y, |evolve μ N t y - poi 1 y| ≤
      2 * (∑ x ∈ range N, μ x * ((x : ℝ) + 1)) * Real.exp (-t) := by
  have hdiff : ∀ y, evolve μ N t y - poi 1 y =
      ∑ x ∈ range N, μ x * (Kt t x y - poi 1 y) := by
    intro y
    unfold evolve
    rw [Finset.sum_congr rfl (fun x _ => mul_sub (μ x) (Kt t x y) (poi 1 y)),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  have hpoint : ∀ y, |evolve μ N t y - poi 1 y| ≤
      ∑ x ∈ range N, μ x * |Kt t x y - poi 1 y| := by
    intro y
    rw [hdiff y]
    calc |∑ x ∈ range N, μ x * (Kt t x y - poi 1 y)|
        ≤ ∑ x ∈ range N, |μ x * (Kt t x y - poi 1 y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ range N, μ x * |Kt t x y - poi 1 y| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
  have hsx : ∀ x, Summable (fun y => |Kt t x y - poi 1 y|) := fun x =>
    ((hasSum_Kt t x).summable.sub (hasSum_poi 1).summable).abs
  have hsRHS : Summable (fun y => ∑ x ∈ range N, μ x * |Kt t x y - poi 1 y|) :=
    summable_sum fun x _ => (hsx x).mul_left (μ x)
  have hsLHS : Summable (fun y => |evolve μ N t y - poi 1 y|) :=
    Summable.of_nonneg_of_le (fun y => abs_nonneg _) hpoint hsRHS
  have hswap : ∑' y, ∑ x ∈ range N, μ x * |Kt t x y - poi 1 y| =
      ∑ x ∈ range N, μ x * ∑' y, |Kt t x y - poi 1 y| := by
    have h := (hasSum_sum (s := range N)
      (f := fun x y => μ x * |Kt t x y - poi 1 y|)
      (a := fun x => μ x * ∑' y, |Kt t x y - poi 1 y|)
      (fun x _ => ((hsx x).hasSum).mul_left (μ x))).tsum_eq
    exact h
  calc ∑' y, |evolve μ N t y - poi 1 y|
      ≤ ∑' y, ∑ x ∈ range N, μ x * |Kt t x y - poi 1 y| :=
        Summable.tsum_le_tsum hpoint hsLHS hsRHS
    _ = ∑ x ∈ range N, μ x * ∑' y, |Kt t x y - poi 1 y| := hswap
    _ ≤ ∑ x ∈ range N, μ x * (2 * ((x : ℝ) + 1) * Real.exp (-t)) := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact mul_le_mul_of_nonneg_left (Kt_l1 ht x) (hμ0 x)
    _ = 2 * (∑ x ∈ range N, μ x * ((x : ℝ) + 1)) * Real.exp (-t) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- **Attainment in the limit.** The l1 distance from the evolved state
to the inverse-factorial law tends to zero. -/
theorem attainment_tendsto (μ : ℕ → ℝ) (N : ℕ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμsum : ∑ x ∈ range N, μ x = 1) :
    Filter.Tendsto (fun t => ∑' y, |evolve μ N t y - poi 1 y|)
      Filter.atTop (nhds 0) := by
  have hC : Filter.Tendsto
      (fun t : ℝ => 2 * (∑ x ∈ range N, μ x * ((x : ℝ) + 1)) * Real.exp (-t))
      Filter.atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (2 * (∑ x ∈ range N, μ x * ((x : ℝ) + 1)))
    simpa using h
  refine squeeze_zero' ?_ ?_ hC
  · filter_upwards with t
    exact tsum_nonneg fun y => abs_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact attainment μ N hμ0 hμsum ht

/-! ## Gates: the organ has content -/

/-- The initial distance is strictly positive: the empty-ledger point
mass is genuinely far from the inverse-factorial law at time zero, so
attainment moves something real (the gate fires on content, not on a
vacuously-zero distance). -/
theorem initial_distance_pos :
    0 < ∑' y, |Kt 0 0 y - poi 1 y| := by
  have hs : Summable (fun y => |Kt 0 0 y - poi 1 y|) :=
    ((hasSum_Kt 0 0).summable.sub (hasSum_poi 1).summable).abs
  have hexp1 : Real.exp (-1 : ℝ) < 1 := by
    have h := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at h
  have hterm : (1 : ℝ) - Real.exp (-1) = |Kt 0 0 0 - poi 1 0| := by
    rw [Kt_zero, if_pos rfl]
    unfold poi
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    rw [abs_of_nonneg (by linarith)]
  have hle : |Kt 0 0 0 - poi 1 0| ≤ ∑' y, |Kt 0 0 y - poi 1 y| :=
    hs.le_tsum 0 fun b _ => abs_nonneg _
  rw [← hterm] at hle
  linarith

/-- The bound is non-vacuous: past the explicit mixing time
`log (x + 1)` it says something strictly stronger than the trivial
l1 bound `2` between probability laws. -/
theorem gate_fires (x : ℕ) {t : ℝ} (ht : Real.log ((x : ℝ) + 1) < t) :
    2 * ((x : ℝ) + 1) * Real.exp (-t) < 2 := by
  have hx1 : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have h1 : Real.exp (-t) < Real.exp (-Real.log ((x : ℝ) + 1)) :=
    Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-Real.log ((x : ℝ) + 1)) = ((x : ℝ) + 1)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hx1]
  rw [h2] at h1
  have hpos : (0 : ℝ) < 2 * ((x : ℝ) + 1) := by positivity
  calc 2 * ((x : ℝ) + 1) * Real.exp (-t)
      < 2 * ((x : ℝ) + 1) * ((x : ℝ) + 1)⁻¹ :=
        mul_lt_mul_of_pos_left h1 hpos
    _ = 2 := by field_simp

end

end LedgerCountedUntruncated
end SevenGaps
end Gravity
end IndisputableMonolith
