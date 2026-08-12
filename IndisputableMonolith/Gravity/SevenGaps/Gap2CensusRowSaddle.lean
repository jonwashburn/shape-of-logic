import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusDsumSaddle
import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusOneSidedRate

/-!
# Gap 2 / C11 / A52: two-sided row-mass concentration at the true Laplace saddle

The A48 concentration theorem (`tendsto_smallMass_div_m0sum_zero`) splits the
row mass at the scale `n² = c·log c`, which is polynomially far below the true
Laplace saddle `n*` (where `n*·log n* = 2c`, so `n* ~ 2c/log c`).  The A51
`dsum_saddle` squeeze only needed a constant per-cell bound, so that scale
sufficed.  The sharp rate's `nvar_sharp` field needs a *first-order*
evaluation of the mass-weighted mean of `c/n`, and that mean is `(log c)/2`
only if the mass concentrates where `c/n ≈ (log c)/2`, i.e. in a window around
`n*`.  The A48 lower bound on `m0sum` (a single term at `saddleN = 2√(c·log c)`)
is exponentially too loose to certify that window, so this module rebuilds the
concentration at the true saddle from the row-top ratio chain.

## The mechanism

The row mass is dominated by the top term `T(n) = n^{2c}/n!` (on large rows
`wrow c n ≤ 2·T(n)/c!`).  The ratio of successive top terms is

  `T(n+1)/T(n) = (1 + 1/n)^{2c}/(n+1)`,

which is *antitone* in `n` and crosses `1` at the saddle (`log` of it is
`2c·log(1+1/n) − log(n+1) ≈ 2c/n − log n`, zero at `n·log n ≈ 2c`).  Two
explicit reference points bracket the saddle with a certified margin:

* `refLo = ⌊2c/log c⌋` is provably *below* the saddle: there the ratio is
  `≥ exp(2c/n)/n ≥ c/refLo ≥ (log c)/2 > 1`, so the top term grows
  geometrically up to `refLo`.
* `refHi = ⌈(2c/log c)(1 + 3·log log c/log c)⌉` is provably *above* the
  saddle: there the ratio is `≤ exp(2c/n)/(n+1) ≤ 1/(2·log c) < 1`, so the
  top term decays geometrically from `refHi` on.

A window `(winLo, winHi)` around the references, of relative half-width
`δ = 1/√(log c·log log c)`, then carries all but a super-polynomially small
fraction of the mass: the lower tail is bounded by a geometric chain up to
`winLo` against the single term at `refLo`, the upper tail by a geometric
chain from `winHi` against the single term at `refHi`.  On the window
`c/n ≈ (log c)/2` to first order.

All head results audit to the base triple `[propext, Classical.choice,
Quot.sound]`.
-/

namespace Gap2CensusRowSaddle

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusDsumSaddle Gap2CensusOneSidedRate Finset
open scoped Gap2CensusProductForm Nat
open Filter Topology

/-! ## Section 1: definitions -/

/-- The row top term `T(n) = n^{2c}/n!`, the `k = c` term of the row weight
without the `1/c!` factor.  On large rows `wrow c n ≤ 2·T(n)/c!`
(`wrow_le_two_wterm`). -/
noncomputable def topT (c n : ℕ) : ℝ := (n : ℝ) ^ (2 * c) / (n ! : ℝ)

/-- The log-slack of the upper reference point: `η(c) = 3·log(log c)/log c`.
This is the margin that puts `refHi` provably above the true saddle. -/
noncomputable def etaS (c : ℕ) : ℝ := 3 * Real.log (Real.log c) / Real.log c

/-- The window half-width slack: `δ(c) = 1/√(log c·log log c)`.  It is
`o(1/√(log c))` (what `resid_negligible` needs) while `c·δ² → ∞` (what the
tail chains need). -/
noncomputable def deltaS (c : ℕ) : ℝ :=
  1 / Real.sqrt (Real.log c * Real.log (Real.log c))

/-- Lower reference point `r₁ = ⌊2c/log c⌋`, provably below the true saddle. -/
noncomputable def refLo (c : ℕ) : ℕ := Nat.floor (2 * (c : ℝ) / Real.log c)

/-- Upper reference point `r₂ = ⌈(2c/log c)(1+η)⌉`, provably above the saddle. -/
noncomputable def refHi (c : ℕ) : ℕ :=
  Nat.ceil (2 * (c : ℝ) / Real.log c * (1 + etaS c))

/-- Lower window edge `⌊(2c/log c)(1−δ)⌋`. -/
noncomputable def winLo (c : ℕ) : ℕ :=
  Nat.floor (2 * (c : ℝ) / Real.log c * (1 - deltaS c))

/-- Upper window edge `⌈(2c/log c)(1+η)(1+δ)⌉`. -/
noncomputable def winHi (c : ℕ) : ℕ :=
  Nat.ceil (2 * (c : ℝ) / Real.log c * (1 + etaS c) * (1 + deltaS c))

/-! ## Section 2: analytic `Tendsto` helpers -/

/-- `log c → ∞` along the naturals. -/
theorem tendsto_log_atTop_nat :
    Tendsto (fun c : ℕ => Real.log (c : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `log log c → ∞` along the naturals. -/
theorem tendsto_log_log_atTop_nat :
    Tendsto (fun c : ℕ => Real.log (Real.log (c : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_atTop_nat

/-- `log log c / log c → 0`. -/
theorem tendsto_log_log_div_log :
    Tendsto (fun c : ℕ => Real.log (Real.log (c : ℝ)) / Real.log (c : ℝ))
      atTop (nhds 0) :=
  (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_log_atTop_nat

/-- `log c / c → 0`. -/
theorem tendsto_log_div_atTop_nat :
    Tendsto (fun c : ℕ => Real.log (c : ℝ) / (c : ℝ)) atTop (nhds 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- `√x → ∞` (not in Mathlib under this name). -/
theorem tendsto_sqrt_atTop : Tendsto Real.sqrt atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  rcases le_or_gt b 0 with hb | hb
  · exact Filter.Eventually.of_forall (fun _ => hb.trans (Real.sqrt_nonneg _))
  · filter_upwards [eventually_ge_atTop (b ^ 2)] with x hx
    exact (Real.le_sqrt hb.le (le_trans (sq_nonneg b) hx)).2 hx

/-- `η(c) → 0`. -/
theorem tendsto_etaS_zero : Tendsto etaS atTop (nhds 0) := by
  have h2 : Tendsto (fun c : ℕ => (3 : ℝ) * (Real.log (Real.log (c : ℝ)) / Real.log (c : ℝ)))
      atTop (nhds (3 * 0)) :=
    tendsto_const_nhds.mul tendsto_log_log_div_log
  rw [mul_zero] at h2
  have h3 : etaS = fun c : ℕ =>
      (3 : ℝ) * (Real.log (Real.log (c : ℝ)) / Real.log (c : ℝ)) := by
    funext c
    rw [etaS, mul_div_assoc]
  rw [h3]
  exact h2

/-- `δ(c) → 0`. -/
theorem tendsto_deltaS_zero : Tendsto deltaS atTop (nhds 0) := by
  have hprod : Tendsto (fun c : ℕ => Real.log (c : ℝ) * Real.log (Real.log (c : ℝ)))
      atTop atTop :=
    tendsto_log_atTop_nat.atTop_mul_atTop₀ tendsto_log_log_atTop_nat
  have hsqrt : Tendsto (fun c : ℕ => Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))))
      atTop atTop :=
    tendsto_sqrt_atTop.comp hprod
  have h : deltaS = fun c : ℕ =>
      (Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))))⁻¹ := by
    funext c
    rw [deltaS, one_div]
  rw [h]
  exact tendsto_inv_atTop_zero.comp hsqrt

/-- `δ(c) > 0` eventually (for `c ≥ 3`, where `log c > 1`). -/
theorem deltaS_pos_eventually : ∀ᶠ c : ℕ in atTop, 0 < deltaS c := by
  filter_upwards [eventually_ge_atTop 3] with c hc
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hLL : (0 : ℝ) < Real.log (Real.log (c : ℝ)) := Real.log_pos hL1
  exact div_pos one_pos (Real.sqrt_pos.2 (mul_pos hL hLL))

/-! ## Section 3: the two-sided `log(1+x)` inequalities -/

/-- Upper bound: `log(1+x) ≤ x` for `x > −1` (from `log y ≤ y − 1`). -/
theorem log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x by linarith)
  simpa using h

/-- Lower bound: `x/(1+x) ≤ log(1+x)` for `x ≥ 0` (from `log y ≤ y − 1` at
`y = 1/(1+x)`). -/
theorem div_one_add_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + x) by positivity)
  rw [Real.log_div one_ne_zero h1.ne', Real.log_one, zero_sub] at h2
  have h3 : 1 / (1 + x) - 1 = -(x / (1 + x)) := by
    field_simp
    ring
  rw [h3] at h2
  linarith

/-! ## Section 4: the row-top ratio -/

/-- The ratio identity in multiplicative form:
`T(n+1)·(n+1) = T(n)·(1+1/n)^{2c}`. -/
theorem topT_succ_mul (c n : ℕ) (hn : 1 ≤ n) :
    topT c (n + 1) * ((n : ℝ) + 1) = topT c n * (1 + 1 / (n : ℝ)) ^ (2 * c) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnfact : (((n + 1)! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have h2 : (n : ℝ) ^ (2 * c) ≠ 0 := pow_ne_zero _ hnpos.ne'
  have hfn : (n ! : ℝ) ≠ 0 := by positivity
  have hleft : topT c (n + 1) * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ (2 * c) / (n ! : ℝ) := by
    simp only [topT]
    rw [hnfact, hcast]
    field_simp
  have hright : topT c n * (1 + 1 / (n : ℝ)) ^ (2 * c)
      = ((n : ℝ) + 1) ^ (2 * c) / (n ! : ℝ) := by
    simp only [topT]
    have h1 : (1 : ℝ) + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by field_simp
    rw [h1, div_pow]
    field_simp [h2]
  rw [hleft, hright]

/-- The ratio as a real function is antitone: for `1 ≤ x ≤ y`,
`(1+1/y)^{2c}/(y+1) ≤ (1+1/x)^{2c}/(x+1)`. -/
theorem ratio_antitone {c : ℕ} {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (1 + 1 / y) ^ (2 * c) / (y + 1) ≤ (1 + 1 / x) ^ (2 * c) / (x + 1) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : (0 : ℝ) < y := by linarith
  have h1 : (1 : ℝ) + 1 / y ≤ 1 + 1 / x := by
    have hrec : (1 : ℝ) / y ≤ 1 / x := by
      rw [div_le_div_iff₀ hypos hxpos]
      nlinarith [hxy]
    linarith
  have hpow : (1 + 1 / y) ^ (2 * c) ≤ (1 + 1 / x) ^ (2 * c) :=
    pow_le_pow_left₀ (by positivity) h1 _
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < y + 1) (by positivity : (0 : ℝ) < x + 1)]
  exact mul_le_mul hpow (by linarith) (by positivity) (by positivity)

/-- Lower ratio bound: `T(n)/T(n−1) ≥ exp(2c/n)/n` for `n ≥ 2`.  Equivalently
`exp(2c/n)·T(n−1) ≤ n·T(n)`. -/
theorem exp_mul_topT_pred_le (c n : ℕ) (hn : 2 ≤ n) :
    Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c (n - 1) ≤ (n : ℝ) * topT c n := by
  have hn1 : 1 ≤ n - 1 := by omega
  have h := topT_succ_mul c (n - 1) hn1
  have hsub : (n - 1 : ℕ) + 1 = n := by omega
  rw [hsub] at h
  have hnm1p : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  rw [hnm1p] at h
  -- h : topT c n * ↑n = topT c (n-1) * (1 + 1/↑(n-1))^{2c}
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have hmpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    rw [hm1]
    linarith
  have heq : (1 / ((n - 1 : ℕ) : ℝ)) / (1 + 1 / ((n - 1 : ℕ) : ℝ)) = 1 / (n : ℝ) := by
    have hne : ((n : ℝ) - 1) ≠ 0 := by
      have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      linarith
    have h5 : (1 : ℝ) + 1 / ((n - 1 : ℕ) : ℝ) = (n : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      rw [hm1]; field_simp [hne]; ring
    rw [h5]
    field_simp [hnpos.ne', hmpos.ne']
  have hlog : 2 * (c : ℝ) / (n : ℝ) ≤ Real.log ((1 + 1 / ((n - 1 : ℕ) : ℝ)) ^ (2 * c)) := by
    rw [Real.log_pow, show ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) by push_cast; ring]
    have hbase : (0 : ℝ) ≤ (1 : ℝ) / ((n - 1 : ℕ) : ℝ) := by positivity
    have hlb := div_one_add_le_log_one_add hbase
    rw [heq] at hlb
    have h2c : (0 : ℝ) ≤ 2 * (c : ℝ) := by positivity
    calc 2 * (c : ℝ) / (n : ℝ) = (2 * (c : ℝ)) * (1 / (n : ℝ)) := by ring
      _ ≤ (2 * (c : ℝ)) * Real.log (1 + 1 / ((n - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hlb h2c
  -- exponentiate
  have hexp : Real.exp (2 * (c : ℝ) / (n : ℝ)) ≤ (1 + 1 / ((n - 1 : ℕ) : ℝ)) ^ (2 * c) := by
    have hpos : (0 : ℝ) < (1 + 1 / ((n - 1 : ℕ) : ℝ)) ^ (2 * c) := by positivity
    rw [← Real.exp_log hpos]
    exact Real.exp_monotone hlog
  -- multiply T(n-1) ≥ 0
  have hT : (0 : ℝ) ≤ topT c (n - 1) := by
    simp [topT]; positivity
  calc Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c (n - 1)
      ≤ (1 + 1 / ((n - 1 : ℕ) : ℝ)) ^ (2 * c) * topT c (n - 1) :=
        mul_le_mul_of_nonneg_right hexp hT
    _ = topT c (n - 1) * (1 + 1 / ((n - 1 : ℕ) : ℝ)) ^ (2 * c) := by ring
    _ = topT c n * (n : ℝ) := h.symm
    _ = (n : ℝ) * topT c n := by ring

/-- Upper ratio bound: `T(n+1)/T(n) ≤ exp(2c/n)/(n+1)` for `n ≥ 1`.
Equivalently `(n+1)·T(n+1) ≤ exp(2c/n)·T(n)`. -/
theorem mul_topT_succ_le_exp (c n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * topT c (n + 1) ≤ Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c n := by
  have h := topT_succ_mul c n hn
  have hlog : Real.log ((1 + 1 / (n : ℝ)) ^ (2 * c)) ≤ 2 * (c : ℝ) / (n : ℝ) := by
    rw [Real.log_pow, show ((2 * c : ℕ) : ℝ) = 2 * (c : ℝ) by push_cast; ring]
    have h1n : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (n : ℝ) :=
      log_one_add_le (show (0 : ℝ) ≤ (1 : ℝ) / (n : ℝ) by positivity)
    have h2c : (0 : ℝ) ≤ 2 * (c : ℝ) := by positivity
    calc (2 * (c : ℝ)) * Real.log (1 + 1 / (n : ℝ))
        ≤ (2 * (c : ℝ)) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left h1n h2c
      _ = 2 * (c : ℝ) / (n : ℝ) := by ring
  have hexp : (1 + 1 / (n : ℝ)) ^ (2 * c) ≤ Real.exp (2 * (c : ℝ) / (n : ℝ)) := by
    have hpos : (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ (2 * c) := by positivity
    rw [← Real.exp_log hpos]
    exact Real.exp_monotone hlog
  have hT : (0 : ℝ) ≤ topT c n := by simp [topT]; positivity
  have h' : ((n : ℝ) + 1) * topT c (n + 1) = topT c n * (1 + 1 / (n : ℝ)) ^ (2 * c) := by
    rw [mul_comm]; exact h
  calc ((n : ℝ) + 1) * topT c (n + 1)
      = topT c n * (1 + 1 / (n : ℝ)) ^ (2 * c) := h'
    _ ≤ topT c n * Real.exp (2 * (c : ℝ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp hT
    _ = Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c n := by ring

/-! ## Section 5: the reference points bracket the saddle -/

/-- `c/log c → ∞` along the naturals. -/
theorem tendsto_c_div_log_atTop :
    Tendsto (fun c : ℕ => (c : ℝ) / Real.log (c : ℝ)) atTop atTop := by
  have h := tendsto_log_div_atTop_nat
  have hpos : ∀ᶠ c : ℕ in atTop, 0 < Real.log (c : ℝ) / (c : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    exact div_pos (Real.log_pos (by exact_mod_cast (by omega))) (by positivity)
  have h2 : Tendsto (fun c : ℕ => (Real.log (c : ℝ) / (c : ℝ))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨h, hpos⟩)
  apply h2.congr'
  filter_upwards with c
  rw [inv_div]

/-- `2c/log c → ∞` along the naturals. -/
theorem tendsto_two_c_div_log_atTop :
    Tendsto (fun c : ℕ => 2 * (c : ℝ) / Real.log (c : ℝ)) atTop atTop := by
  have h := tendsto_c_div_log_atTop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)
  apply h.congr'
  filter_upwards with c
  ring

/-- `3·log log c ≤ 2·log c` eventually (i.e. `log L/L ≤ 2/3`). -/
theorem three_loglog_le_two_log :
    ∀ᶠ c : ℕ in atTop, 3 * Real.log (Real.log (c : ℝ)) ≤ 2 * Real.log (c : ℝ) := by
  have h23 : ∀ᶠ c : ℕ in atTop,
      Real.log (Real.log (c : ℝ)) / Real.log (c : ℝ) ≤ 2 / 3 :=
    tendsto_log_log_div_log.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 2 / 3))
  filter_upwards [h23, eventually_ge_atTop 3] with c hc23 hc3
  have hL : (0 : ℝ) < Real.log (c : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  rw [div_le_iff₀ hL] at hc23
  linarith

/-- `log log c / log c ≤ 1/6` eventually. -/
theorem loglog_div_log_le_sixth :
    ∀ᶠ c : ℕ in atTop,
      Real.log (Real.log (c : ℝ)) / Real.log (c : ℝ) ≤ 1 / 6 :=
  tendsto_log_log_div_log.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))

/-- `etaS c ≥ 0` for `c ≥ 3`. -/
theorem etaS_nonneg {c : ℕ} (hc : 3 ≤ c) : (0 : ℝ) ≤ etaS c := by
  have hL1 : (1 : ℝ) ≤ Real.log (c : ℝ) :=
    (one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))).le
  have hLL : (0 : ℝ) ≤ Real.log (Real.log (c : ℝ)) := Real.log_nonneg hL1
  have hL : (0 : ℝ) ≤ Real.log (c : ℝ) := by linarith
  rw [etaS]
  exact div_nonneg (mul_nonneg (by norm_num) hLL) hL

/-- `refLo c ≥ 1` eventually. -/
theorem refLo_ge_one : ∀ᶠ c : ℕ in atTop, 1 ≤ refLo c := by
  filter_upwards [tendsto_two_c_div_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with c h2cL hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  rw [refLo, Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log c)]
  exact_mod_cast h2cL

/-- `(refLo c :ℝ) ≤ 2c/log c`. -/
theorem refLo_le (c : ℕ) (hc : 2 ≤ c) :
    (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := by
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  exact Nat.floor_le (by positivity)

/-- `2c/log c − 1 < refLo c`. -/
theorem two_c_div_log_sub_one_lt_refLo (c : ℕ) :
    2 * (c : ℝ) / Real.log (c : ℝ) - 1 < (refLo c : ℝ) := by
  have h := Nat.lt_floor_add_one (2 * (c : ℝ) / Real.log (c : ℝ))
  simp only [refLo]
  linarith [h]

/-- **`refLo` is below the saddle**: `refLo·log(refLo) ≤ 2c` eventually. -/
theorem refLo_log_le :
    ∀ᶠ c : ℕ in atTop, (refLo c : ℝ) * Real.log (refLo c : ℝ) ≤ 2 * (c : ℝ) := by
  filter_upwards [eventually_ge_atTop 9, refLo_ge_one,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 1] with c hc hR1nat h2cL
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  have hL2 : (2 : ℝ) ≤ Real.log (c : ℝ) := by
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by exact_mod_cast (by omega : 9 ≤ c) : (9 : ℝ) ≤ c)
    linarith [two_lt_log_nine]
  have hR1 : (1 : ℝ) ≤ (refLo c : ℝ) := by exact_mod_cast hR1nat
  have hRle : (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := refLo_le c (by omega)
  have hlogle : Real.log (refLo c : ℝ) ≤ Real.log (2 * (c : ℝ) / Real.log (c : ℝ)) :=
    Real.log_le_log (by positivity) hRle
  have hlog2cL : Real.log (2 * (c : ℝ) / Real.log (c : ℝ))
      = Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)) := by
    rw [Real.log_div (by positivity) hL.ne', Real.log_mul (by norm_num) (by positivity)]
  have hnn : (0 : ℝ) ≤ Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)) := by
    have h1 : Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
      have := Real.log_le_sub_one_of_pos hL; linarith
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlog2le : Real.log 2 ≤ Real.log (Real.log (c : ℝ)) :=
    Real.log_le_log (by norm_num) hL2
  calc (refLo c : ℝ) * Real.log (refLo c : ℝ)
      ≤ (refLo c : ℝ) * (Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ))) :=
        mul_le_mul_of_nonneg_left (hlogle.trans_eq hlog2cL) (by positivity)
    _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ))
          * (Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ))) :=
        mul_le_mul_of_nonneg_right hRle hnn
    _ = 2 * (c : ℝ) * (1 + (Real.log 2 - Real.log (Real.log (c : ℝ))) / Real.log (c : ℝ)) := by
        field_simp; ring
    _ ≤ 2 * (c : ℝ) := by
        have hneg : (Real.log 2 - Real.log (Real.log (c : ℝ))) / Real.log (c : ℝ) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg
          · linarith [hlog2le]
          · linarith [hL]
        have h1 : (1 : ℝ) + (Real.log 2 - Real.log (Real.log (c : ℝ))) / Real.log (c : ℝ) ≤ 1 := by
          linarith [hneg]
        have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity)
        rwa [mul_one] at h2

/-- `log c ≤ 2c/refLo` eventually. -/
theorem log_le_two_c_div_refLo :
    ∀ᶠ c : ℕ in atTop, Real.log (c : ℝ) ≤ 2 * (c : ℝ) / (refLo c : ℝ) := by
  filter_upwards [eventually_ge_atTop 9, refLo_ge_one] with c hc hR1nat
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  have hRpos : (0 : ℝ) < (refLo c : ℝ) := by exact_mod_cast hR1nat
  have hRle : (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := refLo_le c (by omega)
  rw [le_div_iff₀ hRpos]
  calc Real.log (c : ℝ) * (refLo c : ℝ)
      ≤ Real.log (c : ℝ) * (2 * (c : ℝ) / Real.log (c : ℝ)) :=
        mul_le_mul_of_nonneg_left hRle hL.le
    _ = 2 * (c : ℝ) := by rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hL.ne'

/-- The ratio at `refLo` is at least `log c / 2`: `exp(2c/refLo)/refLo ≥ L/2`. -/
theorem ratio_ge_at_refLo :
    ∀ᶠ c : ℕ in atTop,
      Real.log (c : ℝ) / 2 ≤ Real.exp (2 * (c : ℝ) / (refLo c : ℝ)) / (refLo c : ℝ) := by
  filter_upwards [eventually_ge_atTop 9, refLo_ge_one, log_le_two_c_div_refLo]
    with c hc hR1nat hle
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  have hRpos : (0 : ℝ) < (refLo c : ℝ) := by exact_mod_cast hR1nat
  have hRle : (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := refLo_le c (by omega)
  have hexp : (c : ℝ) ≤ Real.exp (2 * (c : ℝ) / (refLo c : ℝ)) := by
    have h2 := Real.exp_monotone hle
    rwa [Real.exp_log (by exact_mod_cast (by omega : 0 < c))] at h2
  have h3 : Real.log (c : ℝ) / 2 ≤ (c : ℝ) / (refLo c : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hRpos]
    calc Real.log (c : ℝ) * (refLo c : ℝ)
        ≤ Real.log (c : ℝ) * (2 * (c : ℝ) / Real.log (c : ℝ)) :=
          mul_le_mul_of_nonneg_left hRle hL.le
      _ = 2 * (c : ℝ) := by rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ hL.ne'
      _ = (c : ℝ) * 2 := by ring
  calc Real.log (c : ℝ) / 2 ≤ (c : ℝ) / (refLo c : ℝ) := h3
    _ ≤ Real.exp (2 * (c : ℝ) / (refLo c : ℝ)) / (refLo c : ℝ) :=
        (div_le_div_iff_of_pos_right hRpos).2 hexp

/-- `(2c/log c)(1+η) ≤ refHi c`. -/
theorem ge_refHi (c : ℕ) :
    2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) ≤ (refHi c : ℝ) :=
  Nat.le_ceil _

/-- `refHi c ≤ (2c/log c)(1+η) + 1` for `c ≥ 3`. -/
theorem refHi_le (c : ℕ) (hc : 3 ≤ c) :
    (refHi c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) + 1 := by
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hLL : (0 : ℝ) < Real.log (Real.log (c : ℝ)) := Real.log_pos hL1
  have hnn : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) := by
    apply mul_nonneg (by positivity)
    have hη : (0 : ℝ) ≤ etaS c := div_nonneg (by positivity) hL.le
    linarith
  have h := Nat.ceil_lt_add_one hnn
  simp only [refHi]
  linarith [h]

/-- **`refHi` is above the saddle**: `2c ≤ refHi·log(refHi)` eventually. -/
theorem two_c_le_refHi_log :
    ∀ᶠ c : ℕ in atTop, 2 * (c : ℝ) ≤ (refHi c : ℝ) * Real.log (refHi c : ℝ) := by
  filter_upwards [eventually_ge_atTop 9, three_loglog_le_two_log,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 1] with c hc h32 h2cL
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ c)))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hLLpos : (0 : ℝ) < Real.log (Real.log (c : ℝ)) := Real.log_pos hL1
  have hRge : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) ≤ (refHi c : ℝ) := ge_refHi c
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg (by omega)
  have hR1 : (1 : ℝ) ≤ (refHi c : ℝ) := by
    have h1η : (1 : ℝ) ≤ 1 + etaS c := by linarith
    have h2cL1 : (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL
    calc (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL1
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) :=
          le_mul_of_one_le_right (by positivity) h1η
      _ ≤ (refHi c : ℝ) := hRge
  have hone : (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) := by
    have h1η : (1 : ℝ) ≤ 1 + etaS c := by linarith
    calc (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) :=
          le_mul_of_one_le_right (by positivity) h1η
  have hlogge : Real.log (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c))
      ≤ Real.log (refHi c : ℝ) := Real.log_le_log (by positivity) hRge
  have hlogeq : Real.log (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c))
      = Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)) + Real.log (1 + etaS c) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) hL.ne',
      Real.log_mul (by norm_num) (by positivity)]
  have hlog1η : (0 : ℝ) ≤ Real.log (1 + etaS c) := Real.log_nonneg (by linarith)
  have hA : (0 : ℝ) ≤ Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)) := by
    have h1 : Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
      have := Real.log_le_sub_one_of_pos hL; linarith
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  -- key: L ≤ (1+η)(log2 + L − logL)
  have hkey : Real.log (c : ℝ)
      ≤ (1 + etaS c) * (Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ))) := by
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hs : (0 : ℝ) ≤ Real.log (Real.log (c : ℝ)) := hLLpos.le
    have h1η : (1 : ℝ) + etaS c
        = (Real.log (c : ℝ) + 3 * Real.log (Real.log (c : ℝ))) / Real.log (c : ℝ) := by
      rw [etaS]; field_simp
    rw [h1η, div_mul_eq_mul_div, le_div_iff₀ hL]
    nlinarith [h32, hs, hlog2nn, hL.le,
      mul_le_mul_of_nonneg_left h32 hs,
      mul_nonneg hL.le hlog2nn, mul_nonneg hs hlog2nn]
  calc 2 * (c : ℝ)
      = (2 * (c : ℝ) / Real.log (c : ℝ)) * Real.log (c : ℝ) := by field_simp [hL.ne']
    _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ))
          * ((1 + etaS c) * (Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c))
          * (Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ))) := by ring
    _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c))
          * Real.log (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hlogeq]
        have : Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ))
            ≤ Real.log 2 + Real.log (c : ℝ) - Real.log (Real.log (c : ℝ)) + Real.log (1 + etaS c) :=
          by linarith [hlog1η]
        exact this
    _ ≤ (refHi c : ℝ) * Real.log (refHi c : ℝ) :=
        mul_le_mul hRge hlogge (Real.log_nonneg hone) (by positivity : (0 : ℝ) ≤ (refHi c : ℝ))

/-- `2c/refHi ≤ log c − 2 log log c` eventually. -/
theorem two_c_div_refHi_le :
    ∀ᶠ c : ℕ in atTop,
      2 * (c : ℝ) / (refHi c : ℝ) ≤ Real.log (c : ℝ) - 2 * Real.log (Real.log (c : ℝ)) := by
  filter_upwards [eventually_ge_atTop 9, loglog_div_log_le_sixth,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 1] with c hc h16 h2cL
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ c)))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hLLpos : (0 : ℝ) < Real.log (Real.log (c : ℝ)) := Real.log_pos hL1
  have hRge : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) ≤ (refHi c : ℝ) := ge_refHi c
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg (by omega)
  have h1η : (0 : ℝ) < 1 + etaS c := by linarith
  have hbase : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) := by positivity
  have h2c_refHi : 2 * (c : ℝ) / (refHi c : ℝ)
      ≤ Real.log (c : ℝ) / (1 + etaS c) := by
    have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * (c : ℝ)) hbase hRge
    -- 2c/refHi ≤ 2c/((2c/L)(1+η)) = L/(1+η)
    have heq : 2 * (c : ℝ) / (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c))
        = Real.log (c : ℝ) / (1 + etaS c) := by
      field_simp [hL.ne', h1η.ne']
    rwa [heq] at h
  have hstep : Real.log (c : ℝ) / (1 + etaS c)
      ≤ Real.log (c : ℝ) - 2 * Real.log (Real.log (c : ℝ)) := by
    have hs : (0 : ℝ) ≤ Real.log (Real.log (c : ℝ)) := hLLpos.le
    have h6 : 6 * Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
      rw [div_le_iff₀ hL] at h16
      linarith
    have h1η' : (1 : ℝ) + etaS c
        = (Real.log (c : ℝ) + 3 * Real.log (Real.log (c : ℝ))) / Real.log (c : ℝ) := by
      rw [etaS]; field_simp
    rw [div_le_iff₀ h1η, h1η', ← mul_div_assoc, le_div_iff₀ hL]
    nlinarith [h6, hs, hL.le, mul_le_mul_of_nonneg_left h6 hs]
  calc 2 * (c : ℝ) / (refHi c : ℝ) ≤ Real.log (c : ℝ) / (1 + etaS c) := h2c_refHi
    _ ≤ Real.log (c : ℝ) - 2 * Real.log (Real.log (c : ℝ)) := hstep

/-- The ratio at `refHi` is at most `1/(2 log c)`:
`exp(2c/refHi)/(refHi+1) ≤ 1/(2L)`. -/
theorem ratio_le_at_refHi :
    ∀ᶠ c : ℕ in atTop,
      Real.exp (2 * (c : ℝ) / (refHi c : ℝ)) / ((refHi c : ℝ) + 1)
        ≤ 1 / (2 * Real.log (c : ℝ)) := by
  filter_upwards [eventually_ge_atTop 9, two_c_div_refHi_le,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 1] with c hc hle h2cL
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ c)))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg (by omega)
  have hRge : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) ≤ (refHi c : ℝ) := ge_refHi c
  have h2cL1 : (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL
  have h1η : (1 : ℝ) ≤ 1 + etaS c := by linarith
  have hRpos : (0 : ℝ) < (refHi c : ℝ) := by
    calc (0 : ℝ) < 1 := one_pos
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL1
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) :=
          le_mul_of_one_le_right (by positivity) h1η
      _ ≤ (refHi c : ℝ) := hRge
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hexp : Real.exp (2 * (c : ℝ) / (refHi c : ℝ)) ≤ (c : ℝ) / (Real.log (c : ℝ)) ^ 2 := by
    have h2 := Real.exp_monotone hle
    have h3 : Real.exp (Real.log (c : ℝ) - 2 * Real.log (Real.log (c : ℝ)))
        = (c : ℝ) / (Real.log (c : ℝ)) ^ 2 := by
      rw [Real.exp_sub, Real.exp_log hcpos]
      congr 1
      rw [← Real.exp_log (pow_pos hL 2)]
      congr 1
      rw [Real.log_pow]
      norm_num
    rwa [h3] at h2
  have hR : 2 * (c : ℝ) / Real.log (c : ℝ) ≤ (refHi c : ℝ) + 1 := by
    calc 2 * (c : ℝ) / Real.log (c : ℝ)
        ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) :=
          le_mul_of_one_le_right (by positivity) h1η
      _ ≤ (refHi c : ℝ) := hRge
      _ ≤ (refHi c : ℝ) + 1 := by linarith
  have h2cLpos : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  have hR1pos : (0 : ℝ) < (refHi c : ℝ) + 1 := by positivity
  calc Real.exp (2 * (c : ℝ) / (refHi c : ℝ)) / ((refHi c : ℝ) + 1)
      ≤ ((c : ℝ) / (Real.log (c : ℝ)) ^ 2) / ((refHi c : ℝ) + 1) :=
        (div_le_div_iff_of_pos_right hR1pos).2 hexp
    _ ≤ ((c : ℝ) / (Real.log (c : ℝ)) ^ 2) / (2 * (c : ℝ) / Real.log (c : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) h2cLpos hR
    _ = 1 / (2 * Real.log (c : ℝ)) := by
        field_simp [hL.ne']

/-! ## Section 6: two-sided geometric decay of the row top

The saddle facts (`ratio_ge_at_refLo`, `ratio_le_at_refHi`) combine with the
antitonality of the exp-ratio and the `topT` bracketing to give pointwise
geometric decay of `topT` on both tails of the saddle: below `refLo` the row
top grows by a factor of at least `log c / 2` per step, and above `refHi` it
falls by a factor of at least `2·log c` per step.  These are the certificates
the tail-mass sums telescope against. -/

/-- The exp-ratio `g(n) = exp(2c/n)/n` is antitone in `n` (for `n ≥ 1`). -/
theorem expratio_antitone {c : ℕ} {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.exp (2 * (c : ℝ) / (n : ℝ)) / (n : ℝ)
      ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) / (m : ℝ) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have harg : 2 * (c : ℝ) / (n : ℝ) ≤ 2 * (c : ℝ) / (m : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hmpos hmnR
  have hexp : Real.exp (2 * (c : ℝ) / (n : ℝ)) ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) :=
    Real.exp_monotone harg
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (le_trans hm hmn)
  rw [div_le_div_iff₀ hnpos hmpos]
  calc Real.exp (2 * (c : ℝ) / (n : ℝ)) * (m : ℝ)
      ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hexp hmpos.le
    _ ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hmnR (Real.exp_pos _).le

/-- The shifted exp-ratio `exp(2c/n)/(n+1)` is antitone in `n` (for `n ≥ 1`). -/
theorem expratio2_antitone {c : ℕ} {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Real.exp (2 * (c : ℝ) / (n : ℝ)) / ((n : ℝ) + 1)
      ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) / ((m : ℝ) + 1) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have harg : 2 * (c : ℝ) / (n : ℝ) ≤ 2 * (c : ℝ) / (m : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hmpos hmnR
  have hexp : Real.exp (2 * (c : ℝ) / (n : ℝ)) ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) :=
    Real.exp_monotone harg
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  calc Real.exp (2 * (c : ℝ) / (n : ℝ)) * ((m : ℝ) + 1)
      ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (2 * (c : ℝ) / (m : ℝ)) * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- Below `refLo` the row top grows geometrically: `T(n−1) ≤ (2/log c)·T(n)`. -/
theorem topT_decay_below :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, 2 ≤ n → n ≤ refLo c →
      topT c (n - 1) ≤ (2 / Real.log (c : ℝ)) * topT c n := by
  filter_upwards [eventually_ge_atTop 9, ratio_ge_at_refLo] with c hc hratio
  intro n hn2 hnle
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp_pos : (0 : ℝ) < Real.exp (2 * (c : ℝ) / (n : ℝ)) := Real.exp_pos _
  have hg : Real.log (c : ℝ) / 2 ≤ Real.exp (2 * (c : ℝ) / (n : ℝ)) / (n : ℝ) :=
    hratio.trans (expratio_antitone hn1 hnle)
  have hrec : (n : ℝ) / Real.exp (2 * (c : ℝ) / (n : ℝ)) ≤ 2 / Real.log (c : ℝ) := by
    rw [div_le_div_iff₀ hexp_pos hL]
    rw [le_div_iff₀ hnpos] at hg
    calc (n : ℝ) * Real.log (c : ℝ) = 2 * ((Real.log (c : ℝ) / 2) * (n : ℝ)) := by ring
      _ ≤ 2 * Real.exp (2 * (c : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left hg (by norm_num)
  have hbracket := exp_mul_topT_pred_le c n hn2
  have hTpos : (0 : ℝ) ≤ topT c n := by simp [topT]; positivity
  have h1 : topT c (n - 1) ≤ (n : ℝ) * topT c n / Real.exp (2 * (c : ℝ) / (n : ℝ)) := by
    rw [le_div_iff₀ hexp_pos, mul_comm]
    exact hbracket
  calc topT c (n - 1) ≤ (n : ℝ) * topT c n / Real.exp (2 * (c : ℝ) / (n : ℝ)) := h1
    _ = topT c n * ((n : ℝ) / Real.exp (2 * (c : ℝ) / (n : ℝ))) := by ring
    _ ≤ topT c n * (2 / Real.log (c : ℝ)) := mul_le_mul_of_nonneg_left hrec hTpos
    _ = (2 / Real.log (c : ℝ)) * topT c n := by ring

/-- Above `refHi` the row top falls geometrically: `T(n+1) ≤ (1/(2 log c))·T(n)`. -/
theorem topT_decay_above :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, refHi c ≤ n →
      topT c (n + 1) ≤ (1 / (2 * Real.log (c : ℝ))) * topT c n := by
  filter_upwards [eventually_ge_atTop 9, ratio_le_at_refHi,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 1] with c hc hratio h2cL
  intro n hnle
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg (by omega)
  have hRge1 : (1 : ℝ) ≤ (refHi c : ℝ) := by
    have h1η : (1 : ℝ) ≤ 1 + etaS c := by linarith
    calc (1 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := h2cL
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) :=
          le_mul_of_one_le_right (by positivity) h1η
      _ ≤ (refHi c : ℝ) := ge_refHi c
  have hRge1nat : 1 ≤ refHi c := by exact_mod_cast hRge1
  have hn1 : 1 ≤ n := le_trans hRge1nat hnle
  have hg : Real.exp (2 * (c : ℝ) / (n : ℝ)) / ((n : ℝ) + 1)
      ≤ 1 / (2 * Real.log (c : ℝ)) :=
    (expratio2_antitone hRge1nat hnle).trans hratio
  have hbracket := mul_topT_succ_le_exp c n hn1
  have hTpos : (0 : ℝ) ≤ topT c n := by simp [topT]; positivity
  have h1 : topT c (n + 1)
      ≤ Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c n / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1), mul_comm]
    exact hbracket
  calc topT c (n + 1) ≤ Real.exp (2 * (c : ℝ) / (n : ℝ)) * topT c n / ((n : ℝ) + 1) := h1
    _ = topT c n * (Real.exp (2 * (c : ℝ) / (n : ℝ)) / ((n : ℝ) + 1)) := by ring
    _ ≤ topT c n * (1 / (2 * Real.log (c : ℝ))) := mul_le_mul_of_nonneg_left hg hTpos
    _ = (1 / (2 * Real.log (c : ℝ))) * topT c n := by ring

#print axioms ratio_ge_at_refLo
#print axioms ratio_le_at_refHi
#print axioms topT_decay_below
#print axioms topT_decay_above

end Gap2CensusRowSaddle
