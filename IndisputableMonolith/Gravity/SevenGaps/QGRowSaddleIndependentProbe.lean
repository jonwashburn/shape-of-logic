import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusRowSaddle

/-!
# Independent hostile-review probe: A52 row-saddle engine
(`Gap2CensusRowSaddle`), reviewer session `qg-a52-review`

Outside re-verification for the A52 hostile review. No proof below cites any
of the six theorems under review (`refLo_log_le`, `two_c_le_refHi_log`,
`ratio_ge_at_refLo`, `ratio_le_at_refHi`, `topT_decay_below`,
`topT_decay_above`); every check is built from the raw definitions, Mathlib,
and kernel computation. The six appear only in the `#print axioms` audits and
in the structure pins of Section 9, whose whole point is to quote them.

1. Outside-module axiom audits: the six head theorems plus the two slack
   limits (`tendsto_etaS_zero`, `tendsto_deltaS_zero`).
2. Definitional `rfl` pins of all seven definitions, including `winLo` and
   `winHi` (the worker's own probe left those two unpinned).
3. Kernel concreteness of `topT`: `topT 2 2 = 8`, `topT 3 2 = 32`,
   `topT 1 4 = 2/3`, `topT c 0 = 0` for `c ≥ 1`. Decoys refuted: `16`
   (factorial dropped), `4` (exponent `2c−1`), `32` (exponent `2c+1`).
4. `refLo`/`refHi` pinned at explicit `c` from the `log 2` decimal bounds
   alone: `refLo 2 = 5`, `refLo 8 = 7` (floor pinned against the ceil decoy
   `8`), and `refHi 2 = 0` (the ceil of a negative argument, since
   `etaS 2 < −1`).
5. The saddle bracket is EVENTUAL ONLY, witnessed in both directions: at
   `c = 2` the lower bracket fails (`5·log 5 > 4`) and the upper bracket
   collapses (`refHi 2 = 0`); at `c = 8` both sides hold
   (`7·log 7 ≤ 16 ≤ refHi 8·log(refHi 8)`).
6. Sharpest receipt: the conclusion of `topT_decay_above` is FALSE at
   `c = 2`, `n = 3`, and `refHi 2 = 0 ≤ 3` puts `n = 3` in range:
   `topT 2 4 = 32/3 > 27/(4·log 2) = (1/(2·log 2))·topT 2 3`, because
   `log 2 > 81/128`. The `∀ᶠ` quantifier is load-bearing; any universal
   reading of the report's prose is refuted here.
7. Rate honesty, independently: both factors `2/log c` and `1/(2·log c)`
   tend to `0` (proved here from `Real.tendsto_log_atTop`, not via the
   worker's probe), with explicit contraction thresholds: `c ≥ 8` gives
   `2/log c < 1` and `c ≥ 2` gives `1/(2·log c) < 1`.
8. Non-vacuity of the quantifier range: `refLo c → ∞`, so the range
   `2 ≤ n ≤ refLo c` in `topT_decay_below` is arbitrarily large, and
   `topT c n > 0` for `n ≥ 1`.
9. Structure pins: the six head theorems at their exact types.
-/

namespace QGRowSaddleIndependentProbe

open Gap2CensusRowSaddle Filter Topology

/-! ## 1. Outside-module axiom audits of the charged theorems -/

#print axioms Gap2CensusRowSaddle.refLo_log_le
#print axioms Gap2CensusRowSaddle.two_c_le_refHi_log
#print axioms Gap2CensusRowSaddle.ratio_ge_at_refLo
#print axioms Gap2CensusRowSaddle.ratio_le_at_refHi
#print axioms Gap2CensusRowSaddle.topT_decay_below
#print axioms Gap2CensusRowSaddle.topT_decay_above
#print axioms Gap2CensusRowSaddle.tendsto_etaS_zero
#print axioms Gap2CensusRowSaddle.tendsto_deltaS_zero

/-! ## 2. Definitional pins: the objects are the real ones -/

/-- `topT` really is `n^{2c}/n!`. -/
theorem topT_eq (c n : ℕ) :
    topT c n = (n : ℝ) ^ (2 * c) / (Nat.factorial n : ℝ) := rfl

/-- `etaS` really is `3·log log c/log c`. -/
theorem etaS_eq (c : ℕ) : etaS c = 3 * Real.log (Real.log c) / Real.log c := rfl

/-- `deltaS` really is `1/√(log c·log log c)`. -/
theorem deltaS_eq (c : ℕ) :
    deltaS c = 1 / Real.sqrt (Real.log c * Real.log (Real.log c)) := rfl

/-- `refLo` really is `⌊2c/log c⌋`. -/
theorem refLo_eq (c : ℕ) : refLo c = Nat.floor (2 * (c : ℝ) / Real.log c) := rfl

/-- `refHi` really is `⌈(2c/log c)(1+η)⌉`. -/
theorem refHi_eq (c : ℕ) :
    refHi c = Nat.ceil (2 * (c : ℝ) / Real.log c * (1 + etaS c)) := rfl

/-- `winLo` really is `⌊(2c/log c)(1−δ)⌋` (unpinned by the worker's probe). -/
theorem winLo_eq (c : ℕ) :
    winLo c = Nat.floor (2 * (c : ℝ) / Real.log c * (1 - deltaS c)) := rfl

/-- `winHi` really is `⌈(2c/log c)(1+η)(1+δ)⌉` (unpinned by the worker's
probe). -/
theorem winHi_eq (c : ℕ) :
    winHi c = Nat.ceil (2 * (c : ℝ) / Real.log c * (1 + etaS c) * (1 + deltaS c)) := rfl

/-! ## 3. Kernel concreteness of the row top -/

/-- `topT 2 2 = 2^4/2! = 8`. -/
theorem topT_two_two : topT 2 2 = 8 := by
  norm_num [topT, Nat.factorial]

/-- DECOY refuted: dropping the `2!` would give `16`. -/
theorem topT_two_two_ne_sixteen : topT 2 2 ≠ 16 := by
  rw [topT_two_two]; norm_num

/-- DECOY refuted: exponent `2c−1` would give `2^3/2! = 4`. -/
theorem topT_two_two_ne_four : topT 2 2 ≠ 4 := by
  rw [topT_two_two]; norm_num

/-- DECOY refuted: exponent `2c+1` would give `2^5/2! = 32`. -/
theorem topT_two_two_ne_thirtytwo : topT 2 2 ≠ 32 := by
  rw [topT_two_two]; norm_num

/-- `topT 3 2 = 2^6/2! = 32`. -/
theorem topT_three_two : topT 3 2 = 32 := by
  norm_num [topT, Nat.factorial]

/-- `topT 1 4 = 4^2/4! = 2/3`. -/
theorem topT_one_four : topT 1 4 = 2 / 3 := by
  norm_num [topT, Nat.factorial]

/-- The `n = 0` row top vanishes for `c ≥ 1`. -/
theorem topT_zero_left {c : ℕ} (hc : 1 ≤ c) : topT c 0 = 0 := by
  have h : 2 * c ≠ 0 := by omega
  simp [topT, h]

/-- Non-vacuity: `topT c n > 0` for `n ≥ 1`, so the decay bounds have
content and are not a vacuous `0 ≤ 0`. -/
theorem topT_pos (c : ℕ) {n : ℕ} (hn : 1 ≤ n) : 0 < topT c n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (pow_pos hnpos _) (Nat.cast_pos.mpr (Nat.factorial_pos n))

/-! ## 4. `refLo`/`refHi` at explicit `c`, from the `log 2` bounds alone -/

/-- `refLo 2 = ⌊4/log 2⌋ = 5`, since `5 ≤ 4/log 2 < 6` from
`2/3 < log 2 < 4/5`. -/
theorem refLo_two : refLo 2 = 5 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hL : (0 : ℝ) < Real.log 2 := by linarith
  have hunfold : refLo 2 = Nat.floor (2 * ((2 : ℕ) : ℝ) / Real.log ((2 : ℕ) : ℝ)) := rfl
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hnn : (0 : ℝ) ≤ 2 * ((2 : ℕ) : ℝ) / Real.log ((2 : ℕ) : ℝ) := by
    rw [h2]; exact div_nonneg (by norm_num) hL.le
  rw [hunfold, Nat.floor_eq_iff hnn, h2]
  have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  rw [h5]
  constructor
  · rw [le_div_iff₀ hL]
    linarith [hlog2hi]
  · rw [div_lt_iff₀ hL]
    linarith [hlog2lo]

/-- `refLo 8 = ⌊16/(3 log 2)⌋ = 7`, since `7 ≤ 16/(3 log 2) < 8` from
`2/3 < log 2 < 16/21`. -/
theorem refLo_eight : refLo 8 = 7 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog8 : Real.log ((8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    have h8 : ((8 : ℕ) : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]
    push_cast
    ring
  have hL8 : (0 : ℝ) < Real.log ((8 : ℕ) : ℝ) := by rw [hlog8]; linarith
  have hunfold : refLo 8 = Nat.floor (2 * ((8 : ℕ) : ℝ) / Real.log ((8 : ℕ) : ℝ)) := rfl
  have hnn : (0 : ℝ) ≤ 2 * ((8 : ℕ) : ℝ) / Real.log ((8 : ℕ) : ℝ) :=
    div_nonneg (by norm_num) hL8.le
  rw [hunfold, Nat.floor_eq_iff hnn, hlog8]
  have h8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
  rw [h8]
  have h7 : ((7 : ℕ) : ℝ) = 7 := by norm_num
  rw [h7]
  constructor
  · rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 * Real.log 2)]
    linarith [hlog2hi]
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 3 * Real.log 2)]
    linarith [hlog2lo]

/-- DECOY refuted: a ceil-based lower reference point would give `8` at
`c = 8`; the floor gives `7`. -/
theorem refLo_eight_ne_eight : refLo 8 ≠ 8 := by
  rw [refLo_eight]; norm_num

/-- `refHi 2 = 0`: at `c = 2` the slack `etaS 2 = 3·log log 2/log 2` is
`< −1` (because `log log 2 < −1/4` and `log 2 < 3/4`), so the ceil argument
is negative and the nat ceil is `0`. -/
theorem refHi_two : refHi 2 = 0 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hL : (0 : ℝ) < Real.log 2 := by linarith
  have hll : Real.log (Real.log 2) < -(1 / 4 : ℝ) := by
    have h1 : Real.log (Real.log 2) < Real.log (3 / 4 : ℝ) :=
      Real.log_lt_log hL (by linarith)
    have h2 : Real.log (3 / 4 : ℝ) ≤ -(1 / 4 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 4)
      linarith
    linarith
  have heta : (1 : ℝ) + etaS 2 ≤ 0 := by
    have hunfold : etaS 2 = 3 * Real.log (Real.log ((2 : ℕ) : ℝ)) / Real.log ((2 : ℕ) : ℝ) := rfl
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hunfold, h2]
    rw [show (1 : ℝ) + 3 * Real.log (Real.log 2) / Real.log 2
        = (Real.log 2 + 3 * Real.log (Real.log 2)) / Real.log 2 by
      field_simp [hL.ne']]
    apply div_nonpos_of_nonpos_of_nonneg _ hL.le
    linarith [hll, hlog2hi]
  have harg : 2 * ((2 : ℕ) : ℝ) / Real.log ((2 : ℕ) : ℝ) * (1 + etaS 2) ≤ 0 := by
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by norm_num) hL.le) heta
  have hunfold : refHi 2 = Nat.ceil (2 * ((2 : ℕ) : ℝ) / Real.log ((2 : ℕ) : ℝ) * (1 + etaS 2)) := rfl
  rw [hunfold]
  exact Nat.eq_zero_of_le_zero (Nat.ceil_le.2 (by simpa using harg))

/-! ## 5. The saddle bracket is eventual only: failure at `c = 2`, success
at `c = 8` -/

/-- At `c = 2` the lower bracket FAILS: `refLo 2 = 5` and
`5·log 5 > 5·(4/5) = 4 = 2c`, because `exp(4/5) < exp 1 < 5`. -/
theorem bracket_lower_fails_at_two :
    ¬ ((refLo 2 : ℝ) * Real.log (refLo 2 : ℝ) ≤ 2 * ((2 : ℕ) : ℝ)) := by
  rw [refLo_two]
  intro hle
  have hlog5 : (4 / 5 : ℝ) < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
    have h1 : Real.exp (4 / 5 : ℝ) < Real.exp 1 := Real.exp_strictMono (by norm_num)
    have h2 := Real.exp_one_lt_d9
    linarith
  have hcast5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hcast5, hcast2] at hle
  linarith [hle, hlog5]

/-- At `c = 8` the lower bracket HOLDS: `refLo 8 = 7` and
`7·log 7 < 7·2 = 14 ≤ 16 = 2c`, because `7 < (exp 1)^2 = exp 2`. -/
theorem bracket_lower_holds_at_eight :
    (refLo 8 : ℝ) * Real.log (refLo 8 : ℝ) ≤ 2 * ((8 : ℕ) : ℝ) := by
  rw [refLo_eight]
  have hlog7 : Real.log ((7 : ℕ) : ℝ) < 2 := by
    have he1 := Real.exp_one_gt_d9
    have he2 : Real.exp (2 : ℝ) = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h7lt : ((7 : ℕ) : ℝ) < Real.exp 2 := by
      rw [he2, pow_two]
      have h7 : ((7 : ℕ) : ℝ) = 7 := by norm_num
      rw [h7]
      have h1 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 := by
        have h2 := mul_lt_mul_of_pos_left he1 (by norm_num : (0 : ℝ) < 2.7182818283)
        have h3 := mul_lt_mul_of_pos_right he1 (Real.exp_pos 1)
        exact h2.trans h3
      norm_num at h1
      linarith [h1]
    have hlt : Real.log ((7 : ℕ) : ℝ) < Real.log (Real.exp 2) :=
      Real.log_lt_log (by norm_num) h7lt
    rwa [Real.log_exp] at hlt
  have h7mul : ((7 : ℕ) : ℝ) * Real.log ((7 : ℕ) : ℝ) < ((7 : ℕ) : ℝ) * 2 :=
    mul_lt_mul_of_pos_left hlog7 (by norm_num)
  have h16 : ((7 : ℕ) : ℝ) * 2 ≤ 2 * ((8 : ℕ) : ℝ) := by norm_num
  exact h7mul.le.trans h16

/-- At `c = 8` the upper bracket HOLDS: `refHi 8 ≥ 8` (the ceil argument is
`≥ 16/log 8 ≥ 7.6`), so `refHi 8·log(refHi 8) ≥ 8·log 8 ≥ 8·2 = 16 = 2c`. -/
theorem bracket_upper_holds_at_eight :
    2 * ((8 : ℕ) : ℝ) ≤ (refHi 8 : ℝ) * Real.log (refHi 8 : ℝ) := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hlog8 : Real.log ((8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    have h8 : ((8 : ℕ) : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]
    push_cast
    ring
  have hL8 : (0 : ℝ) < Real.log ((8 : ℕ) : ℝ) := by rw [hlog8]; linarith
  have hL8gt1 : (1 : ℝ) < Real.log ((8 : ℕ) : ℝ) := by rw [hlog8]; linarith
  have heta8 : (0 : ℝ) ≤ etaS 8 := by
    have hunfold : etaS 8 = 3 * Real.log (Real.log ((8 : ℕ) : ℝ)) / Real.log ((8 : ℕ) : ℝ) := rfl
    rw [hunfold]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hL8gt1.le)) hL8.le
  have hceil : 2 * ((8 : ℕ) : ℝ) / Real.log ((8 : ℕ) : ℝ) * (1 + etaS 8) ≤ (refHi 8 : ℝ) :=
    Nat.le_ceil _
  have h1eta : (1 : ℝ) ≤ 1 + etaS 8 := by linarith
  have hbase : 2 * ((8 : ℕ) : ℝ) / Real.log ((8 : ℕ) : ℝ) ≤ (refHi 8 : ℝ) :=
    le_trans (le_mul_of_one_le_right (div_nonneg (by norm_num) hL8.le) h1eta) hceil
  have h76 : (7.6 : ℝ) ≤ 2 * ((8 : ℕ) : ℝ) / Real.log ((8 : ℕ) : ℝ) := by
    rw [hlog8]
    have h8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
    rw [h8]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 3 * Real.log 2)]
    linarith [hlog2hi]
  have hR : (7.6 : ℝ) ≤ (refHi 8 : ℝ) := h76.trans hbase
  have hR8 : 8 ≤ refHi 8 := by
    by_contra hlt
    push_neg at hlt
    have hle7 : refHi 8 ≤ 7 := by omega
    have hle7R : (refHi 8 : ℝ) ≤ 7 := by exact_mod_cast hle7
    linarith [hR]
  have hR8R : ((8 : ℕ) : ℝ) ≤ (refHi 8 : ℝ) := by exact_mod_cast hR8
  have hlogge : Real.log ((8 : ℕ) : ℝ) ≤ Real.log (refHi 8 : ℝ) :=
    Real.log_le_log (by norm_num) hR8R
  have hlog8ge2 : (2 : ℝ) ≤ Real.log ((8 : ℕ) : ℝ) := by rw [hlog8]; linarith
  calc 2 * ((8 : ℕ) : ℝ) = ((8 : ℕ) : ℝ) * 2 := by ring
    _ ≤ ((8 : ℕ) : ℝ) * Real.log ((8 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog8ge2 (by norm_num)
    _ ≤ (refHi 8 : ℝ) * Real.log (refHi 8 : ℝ) :=
        mul_le_mul hR8R hlogge hL8.le (Nat.cast_nonneg _)

/-! ## 6. The sharpest receipt: `topT_decay_above`'s conclusion fails at
`c = 2`, with `n = 3` inside the quantifier range -/

/-- The universal reading of `topT_decay_above` is FALSE: at `c = 2` the
reference point is `refHi 2 = 0`, so `n = 3` is in range, but
`topT 2 4 = 32/3 > 27/(4·log 2) = (1/(2·log 2))·topT 2 3`, since
`128·log 2 > 128·(81/128) = 81`. The `∀ᶠ c` quantifier in the real theorem
is load-bearing. -/
theorem topT_decay_above_fails_at_c_two :
    ¬ (∀ n : ℕ, refHi 2 ≤ n → topT 2 (n + 1) ≤ (1 / (2 * Real.log 2)) * topT 2 n) := by
  intro h
  have h3 : topT 2 4 ≤ (1 / (2 * Real.log 2)) * topT 2 3 :=
    h 3 (by rw [refHi_two]; exact Nat.zero_le 3)
  have hT4 : topT 2 4 = 32 / 3 := by norm_num [topT, Nat.factorial]
  have hT3 : topT 2 3 = 27 / 2 := by norm_num [topT, Nat.factorial]
  rw [hT4, hT3] at h3
  have hL : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hstep : (32 / 3 : ℝ) * (2 * Real.log 2) ≤ 27 / 2 := by
    have hpos : (0 : ℝ) < 2 * Real.log 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right h3 hpos.le
    have hrhs : (1 / (2 * Real.log 2)) * (27 / 2 : ℝ) * (2 * Real.log 2) = 27 / 2 := by
      field_simp [hL.ne']
    rwa [hrhs] at hmul
  linarith [hstep, Real.log_two_gt_d9]

/-! ## 7. Rate honesty, independently proved -/

/-- The below-`refLo` factor `2/log c → 0` (independent proof, from
`Real.tendsto_log_atTop` only). -/
theorem indep_tendsto_two_div_log_zero :
    Tendsto (fun c : ℕ => 2 / Real.log (c : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun c : ℕ => Real.log (c : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun c : ℕ => (Real.log (c : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h2 : Tendsto (fun c : ℕ => 2 * (Real.log (c : ℝ))⁻¹) atTop (nhds (2 * 0)) :=
    hinv.const_mul 2
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards with c
  rw [div_eq_mul_inv]

/-- The above-`refHi` factor `1/(2·log c) → 0` (independent proof). -/
theorem indep_tendsto_one_div_two_log_zero :
    Tendsto (fun c : ℕ => 1 / (2 * Real.log (c : ℝ))) atTop (nhds 0) := by
  have hlog : Tendsto (fun c : ℕ => Real.log (c : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun c : ℕ => (Real.log (c : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h2 : Tendsto (fun c : ℕ => (1 / 2 : ℝ) * (Real.log (c : ℝ))⁻¹) atTop
      (nhds ((1 / 2 : ℝ) * 0)) := hinv.const_mul _
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards with c
  simp only [one_div, mul_inv]

/-- Explicit contraction threshold, below side: for `c ≥ 8`,
`2/log c < 1` (since `log c ≥ 3 log 2 > 2`). -/
theorem two_div_log_lt_one_of_eight_le {c : ℕ} (hc : 8 ≤ c) :
    2 / Real.log (c : ℝ) < 1 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : Real.log ((8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    have h8 : ((8 : ℕ) : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h8, Real.log_pow]
    push_cast
    ring
  have hle : Real.log ((8 : ℕ) : ℝ) ≤ Real.log (c : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hc
  rw [hlog8] at hle
  have h2 : (2 : ℝ) < Real.log (c : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  rw [div_lt_one hL]
  exact h2

/-- Explicit contraction threshold, above side: for `c ≥ 2`,
`1/(2·log c) < 1` (since `2·log c ≥ 2·log 2 > 1`). -/
theorem one_div_two_log_lt_one_of_two_le {c : ℕ} (hc : 2 ≤ c) :
    1 / (2 * Real.log (c : ℝ)) < 1 := by
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hle : Real.log (2 : ℝ) ≤ Real.log (c : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hc
  have h1 : (1 : ℝ) < 2 * Real.log (c : ℝ) := by linarith
  have hpos : (0 : ℝ) < 2 * Real.log (c : ℝ) := by linarith
  rw [div_lt_one hpos]
  exact h1

/-! ## 8. Non-vacuity of the quantifier range -/

/-- `refLo c → ∞`: the range `2 ≤ n ≤ refLo c` quantified over in
`topT_decay_below` is arbitrarily large, so the geometric chain has genuine
content. -/
theorem tendsto_refLo_atTop :
    Tendsto (fun c : ℕ => (refLo c : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun c : ℕ => 2 * (c : ℝ) / Real.log (c : ℝ) - 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards
      [Gap2CensusRowSaddle.tendsto_two_c_div_log_atTop.eventually_ge_atTop (b + 1)]
      with c hc
    linarith
  apply tendsto_atTop_mono _ h1
  intro c
  have h := Nat.lt_floor_add_one (2 * (c : ℝ) / Real.log (c : ℝ))
  show 2 * (c : ℝ) / Real.log (c : ℝ) - 1
      ≤ (Nat.floor (2 * (c : ℝ) / Real.log (c : ℝ)) : ℝ)
  linarith

/-! ## 9. Structure pins: the six head theorems at their exact types -/

/-- `refLo_log_le` at its exact type. -/
theorem pin_refLo_log_le :
    ∀ᶠ c : ℕ in atTop, (refLo c : ℝ) * Real.log (refLo c : ℝ) ≤ 2 * (c : ℝ) :=
  Gap2CensusRowSaddle.refLo_log_le

/-- `two_c_le_refHi_log` at its exact type. -/
theorem pin_two_c_le_refHi_log :
    ∀ᶠ c : ℕ in atTop, 2 * (c : ℝ) ≤ (refHi c : ℝ) * Real.log (refHi c : ℝ) :=
  Gap2CensusRowSaddle.two_c_le_refHi_log

/-- `ratio_ge_at_refLo` at its exact type. -/
theorem pin_ratio_ge_at_refLo :
    ∀ᶠ c : ℕ in atTop,
      Real.log (c : ℝ) / 2 ≤ Real.exp (2 * (c : ℝ) / (refLo c : ℝ)) / (refLo c : ℝ) :=
  Gap2CensusRowSaddle.ratio_ge_at_refLo

/-- `ratio_le_at_refHi` at its exact type. -/
theorem pin_ratio_le_at_refHi :
    ∀ᶠ c : ℕ in atTop,
      Real.exp (2 * (c : ℝ) / (refHi c : ℝ)) / ((refHi c : ℝ) + 1)
        ≤ 1 / (2 * Real.log (c : ℝ)) :=
  Gap2CensusRowSaddle.ratio_le_at_refHi

/-- `topT_decay_below` at its exact type. -/
theorem pin_topT_decay_below :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, 2 ≤ n → n ≤ refLo c →
      topT c (n - 1) ≤ (2 / Real.log (c : ℝ)) * topT c n :=
  Gap2CensusRowSaddle.topT_decay_below

/-- `topT_decay_above` at its exact type. -/
theorem pin_topT_decay_above :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, refHi c ≤ n →
      topT c (n + 1) ≤ (1 / (2 * Real.log (c : ℝ))) * topT c n :=
  Gap2CensusRowSaddle.topT_decay_above

/-! ## 10. Audits of this probe's own theorems -/

#print axioms QGRowSaddleIndependentProbe.topT_two_two
#print axioms QGRowSaddleIndependentProbe.topT_pos
#print axioms QGRowSaddleIndependentProbe.refLo_two
#print axioms QGRowSaddleIndependentProbe.refLo_eight
#print axioms QGRowSaddleIndependentProbe.refHi_two
#print axioms QGRowSaddleIndependentProbe.bracket_lower_fails_at_two
#print axioms QGRowSaddleIndependentProbe.bracket_lower_holds_at_eight
#print axioms QGRowSaddleIndependentProbe.bracket_upper_holds_at_eight
#print axioms QGRowSaddleIndependentProbe.topT_decay_above_fails_at_c_two
#print axioms QGRowSaddleIndependentProbe.indep_tendsto_two_div_log_zero
#print axioms QGRowSaddleIndependentProbe.indep_tendsto_one_div_two_log_zero
#print axioms QGRowSaddleIndependentProbe.two_div_log_lt_one_of_eight_le
#print axioms QGRowSaddleIndependentProbe.one_div_two_log_lt_one_of_two_le
#print axioms QGRowSaddleIndependentProbe.tendsto_refLo_atTop

end QGRowSaddleIndependentProbe
