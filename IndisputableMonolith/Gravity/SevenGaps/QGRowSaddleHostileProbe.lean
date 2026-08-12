import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusRowSaddle

/-!
# Hostile-review probe: A52 row-saddle concentration engine
(`Gap2CensusRowSaddle`)

Outside-module checks on the two-sided row-top saddle engine, written with
hostile intent: nothing here is cited from the module's own assembly where an
independent route exists, and every red test is a proved statement, not a
compile failure.

1. Re-audits of the charged head theorems, from outside.
2. Definitional pins by `rfl`: `topT`, `etaS`, `deltaS`, `refLo`, `refHi`.
3. Concreteness: `topT 2 2 = 8`, `topT 1 3 = 3/2`, `topT c 0 = 0` by kernel
   computation, with a decoy (`topT 2 2 = 16`, the value before dividing by
   `2!`) proved NOT to be the value.
4. Non-vacuity: `topT c n > 0` for `n ≥ 1`, so the decay bounds have content.
5. Red test 1: both decay factors (`2/log c` below `refLo`, `1/(2·log c)` above
   `refHi`) tend to `0`, so they are eventually STRICTLY below `1` — the
   geometric growth/decay is real, not a vacuous `≤` against a factor `≥ 1`.
6. Red test 2: the reference points genuinely bracket the saddle,
   `refLo·log refLo ≤ 2c ≤ refHi·log refHi` eventually (re-derived from the
   module's own saddle facts), so `refLo` is below and `refHi` above the root
   of `n·log n = 2c`.  A decoy that `2c ≤ refLo·log refLo` (refLo already past
   the saddle) is refuted.
7. Structure pins: the four head theorems at their exact types.
-/

namespace QGRowSaddleHostileProbe

open Gap2CensusRowSaddle Finset Filter Topology

/-! ## 1. Outside-module axiom audits of the charged head theorems -/

#print axioms Gap2CensusRowSaddle.ratio_ge_at_refLo
#print axioms Gap2CensusRowSaddle.ratio_le_at_refHi
#print axioms Gap2CensusRowSaddle.topT_decay_below
#print axioms Gap2CensusRowSaddle.topT_decay_above

/-! ## 2. Definitional pins: the objects are the real ones -/

/-- `topT` really is `n^{2c}/n!`. -/
theorem topT_eq (c n : ℕ) : topT c n = (n : ℝ) ^ (2 * c) / (Nat.factorial n : ℝ) := rfl

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

/-! ## 3. Concreteness: kernel computation of the row top -/

/-- `topT 2 2 = 2^4/2! = 8`. -/
theorem topT_two_two : topT 2 2 = 8 := by
  norm_num [topT, Nat.factorial]

/-- Decoy rejected: forgetting the `2!` would give `16`. -/
theorem topT_two_two_ne_decoy : topT 2 2 ≠ 16 := by
  rw [topT_two_two]; norm_num

/-- `topT 1 3 = 3²/3! = 3/2`. -/
theorem topT_one_three : topT 1 3 = 3 / 2 := by
  norm_num [topT, Nat.factorial]

/-- The `n = 0` row top vanishes for `c ≥ 1`: `0^{2c} = 0`. -/
theorem topT_zero_left {c : ℕ} (hc : 1 ≤ c) : topT c 0 = 0 := by
  have h : 2 * c ≠ 0 := by omega
  simp [topT, h]

/-! ## 4. Non-vacuity: the row top is strictly positive for `n ≥ 1` -/

/-- `topT c n > 0` for `n ≥ 1`, so every decay bound has content. -/
theorem topT_pos (c : ℕ) {n : ℕ} (hn : 1 ≤ n) : 0 < topT c n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (pow_pos hnpos _) (Nat.cast_pos.mpr (Nat.factorial_pos n))

/-! ## 5. Red test 1: the decay factors are genuinely `< 1`

If either decay factor were eventually `≥ 1`, the corresponding decay lemma
would be vacuous (a `≤` against a non-contracting factor).  Both tend to `0`,
so eventually they are strictly below `1`: the growth below `refLo` and the
decay above `refHi` are real. -/

/-- The below-`refLo` factor `2/log c → 0`. -/
theorem tendsto_two_div_log_zero :
    Tendsto (fun c : ℕ => 2 / Real.log (c : ℝ)) atTop (nhds 0) := by
  have h : Tendsto (fun c : ℕ => (Real.log (c : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_atTop_nat
  have h2 : Tendsto (fun c : ℕ => 2 * (Real.log (c : ℝ))⁻¹) atTop (nhds (2 * 0)) :=
    h.const_mul 2
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards with c
  rw [div_eq_mul_inv]

/-- The above-`refHi` factor `1/(2·log c) → 0`. -/
theorem tendsto_one_div_two_log_zero :
    Tendsto (fun c : ℕ => 1 / (2 * Real.log (c : ℝ))) atTop (nhds 0) := by
  have h : Tendsto (fun c : ℕ => (Real.log (c : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_atTop_nat
  have h2 : Tendsto (fun c : ℕ => (1 / 2 : ℝ) * (Real.log (c : ℝ))⁻¹) atTop
      (nhds ((1 / 2 : ℝ) * 0)) := h.const_mul _
  rw [mul_zero] at h2
  apply h2.congr'
  filter_upwards with c
  simp only [one_div, mul_inv]

/-- RED: eventually `2/log c < 1`, so the below-`refLo` "decay" is genuine
geometric growth (ratio `> 1`), not a vacuous bound. -/
theorem two_div_log_eventually_lt_one :
    ∀ᶠ c : ℕ in atTop, 2 / Real.log (c : ℝ) < 1 := by
  filter_upwards [tendsto_log_atTop_nat.eventually (eventually_gt_atTop 2)] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  rw [div_lt_one hL]
  exact hc

/-- RED: eventually `1/(2·log c) < 1`, so the above-`refHi` decay is genuine
geometric decay, not a vacuous bound. -/
theorem one_div_two_log_eventually_lt_one :
    ∀ᶠ c : ℕ in atTop, 1 / (2 * Real.log (c : ℝ)) < 1 := by
  filter_upwards [tendsto_log_atTop_nat.eventually (eventually_gt_atTop 2)] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.log (c : ℝ))]
  linarith

/-! ## 6. Red test 2: the reference points genuinely bracket the saddle

The saddle is the root of `n·log n = 2c`.  The module proves `refLo` is below
it (`refLo·log refLo ≤ 2c`) and `refHi` above it (`2c ≤ refHi·log refHi`).
Re-stated here as an independent pin, plus the refutation of the decoy that
`refLo` is already past the saddle. -/

/-- The saddle bracket, re-derived from the module's saddle facts. -/
theorem saddle_bracket :
    ∀ᶠ c : ℕ in atTop,
      (refLo c : ℝ) * Real.log (refLo c : ℝ) ≤ 2 * (c : ℝ)
        ∧ 2 * (c : ℝ) ≤ (refHi c : ℝ) * Real.log (refHi c : ℝ) :=
  (refLo_log_le.and two_c_le_refHi_log)

/-- RED: the decoy "`refLo` is already past the saddle" (`2c ≤ refLo·log refLo`)
is eventually FALSE — `refLo` is strictly below the saddle. -/
theorem refLo_not_past_saddle :
    ∀ᶠ c : ℕ in atTop, ¬ (2 * (c : ℝ) ≤ (refLo c : ℝ) * Real.log (refLo c : ℝ)) := by
  filter_upwards [tendsto_log_atTop_nat.eventually (eventually_gt_atTop 2)] with c hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hlt : 2 * (c : ℝ) / Real.log (c : ℝ) - 1 < (refLo c : ℝ) :=
    two_c_div_log_sub_one_lt_refLo c
  have hcpos : (0 : ℝ) < (c : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hc0 : (c : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg _)
    rw [hc0, Real.log_zero] at hL2
    norm_num at hL2
  have hc1 : 1 ≤ c := by exact_mod_cast hcpos
  have hcne1 : c ≠ 1 := by
    intro h1c
    rw [h1c, Nat.cast_one, Real.log_one] at hL2
    norm_num at hL2
  have hc2 : 2 ≤ c := by omega
  have hcltc : Real.log (c : ℝ) < (c : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hcpos
    linarith
  have h2cLgt2 : (2 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) := by
    rw [lt_div_iff₀ hL]
    have h := mul_lt_mul_of_pos_left hcltc (by norm_num : (0 : ℝ) < 2)
    nlinarith [h]
  have hR1 : (1 : ℝ) < (refLo c : ℝ) := by linarith [hlt, h2cLgt2]
  have hRpos : (0 : ℝ) < (refLo c : ℝ) := by linarith
  have hlogRpos : (0 : ℝ) < Real.log (refLo c : ℝ) := Real.log_pos hR1
  have hRle : (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := refLo_le c hc2
  have h2cLltc : 2 * (c : ℝ) / Real.log (c : ℝ) < (c : ℝ) := by
    rw [div_lt_iff₀ hL]
    have h := mul_lt_mul_of_pos_left hL2 hcpos
    nlinarith [h]
  have hloglt : Real.log (refLo c : ℝ) < Real.log (c : ℝ) :=
    Real.log_lt_log hRpos (hRle.trans_lt h2cLltc)
  have h2cLpos : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  intro hge
  have h1 : (refLo c : ℝ) * Real.log (refLo c : ℝ)
      ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * Real.log (refLo c : ℝ) :=
    mul_le_mul_of_nonneg_right hRle hlogRpos.le
  have h2 : (2 * (c : ℝ) / Real.log (c : ℝ)) * Real.log (refLo c : ℝ)
      < (2 * (c : ℝ) / Real.log (c : ℝ)) * Real.log (c : ℝ) :=
    mul_lt_mul_of_pos_left hloglt h2cLpos
  have h3 : (2 * (c : ℝ) / Real.log (c : ℝ)) * Real.log (c : ℝ) = 2 * (c : ℝ) := by
    field_simp [hL.ne']
  linarith [h1, h2, h3, hge]

/-! ## 7. Structure pins: the head theorems at their exact types -/

/-- `ratio_ge_at_refLo` at its exact type. -/
theorem ratio_ge_at_refLo_at_type :
    ∀ᶠ c : ℕ in atTop,
      Real.log (c : ℝ) / 2 ≤ Real.exp (2 * (c : ℝ) / (refLo c : ℝ)) / (refLo c : ℝ) :=
  ratio_ge_at_refLo

/-- `ratio_le_at_refHi` at its exact type. -/
theorem ratio_le_at_refHi_at_type :
    ∀ᶠ c : ℕ in atTop,
      Real.exp (2 * (c : ℝ) / (refHi c : ℝ)) / ((refHi c : ℝ) + 1)
        ≤ 1 / (2 * Real.log (c : ℝ)) :=
  ratio_le_at_refHi

/-- `topT_decay_below` at its exact type. -/
theorem topT_decay_below_at_type :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, 2 ≤ n → n ≤ refLo c →
      topT c (n - 1) ≤ (2 / Real.log (c : ℝ)) * topT c n :=
  topT_decay_below

/-- `topT_decay_above` at its exact type. -/
theorem topT_decay_above_at_type :
    ∀ᶠ c : ℕ in atTop, ∀ n : ℕ, refHi c ≤ n →
      topT c (n + 1) ≤ (1 / (2 * Real.log (c : ℝ))) * topT c n :=
  topT_decay_above

/-! ## 8. Audits of this probe's own theorems -/

#print axioms QGRowSaddleHostileProbe.topT_two_two
#print axioms QGRowSaddleHostileProbe.topT_pos
#print axioms QGRowSaddleHostileProbe.tendsto_two_div_log_zero
#print axioms QGRowSaddleHostileProbe.two_div_log_eventually_lt_one
#print axioms QGRowSaddleHostileProbe.saddle_bracket
#print axioms QGRowSaddleHostileProbe.refLo_not_past_saddle

end QGRowSaddleHostileProbe
