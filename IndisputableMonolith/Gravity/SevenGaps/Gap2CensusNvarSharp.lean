import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusRowSaddle

/-!
# Gap 2 / C11 / A53: the `nvar_sharp` assembly (tail summation plus window
first-order evaluation) and `resid_negligible`

The A52 engine (`Gap2CensusRowSaddle`) put two-sided geometric decay of the row
top `topT c n = n^{2c}/n!` around the true Laplace saddle at kernel strength:
`refLo`/`refHi` provably bracket the saddle, `topT` grows geometrically below
`refLo` (factor `2/log c`) and decays geometrically above `refHi` (factor
`1/(2·log c)`).  This module turns that engine into the two remaining fields of
`Gap2SharpRateGap.SharpRateGap`, closing the sharp rate

  `q(c) = (log c)/(2c²)·(1+o(1))`

unconditionally.  The argument follows the three-step plan of the A52 verdict:

1. **Tail summation.**  Iterating `topT_decay_below`/`topT_decay_above`, the
   row mass outside the window `[winLo, winHi]` is bounded by geometric series
   with ratios `2/log c` and `1/(2 log c)`, against the single-cell anchors
   `topT c refLo/c!` and `topT c refHi/c!` inside `m0sum`.  The window sits a
   factor `(1±δ)` outside the references with `δ = 1/√(log c·log log c)`, so
   each chain has `≈ (2c/log c)·δ` steps and the tails are
   super-polynomially small: `tailMassM c/m0sum c ≤ 1/c³` eventually.
2. **Window first-order evaluation.**  On the window the per-cell variance
   weight `(k/n)(1−1/n)` is squeezed: above by `c/n ≤ c/winLo`, below by
   `(1−1/n)(c−2)/n ≥ (1−1/winLo)(c−2)/winHi` (the `k`-deficit sums
   geometrically by the A51 lemma `sum_sub_cellW_le_two_wrow`).  Both window
   edges sit at `(2c/log c)(1+o(1))`, so both bounds evaluate to
   `(log c)/2·(1+o(1))`, giving `nvarSum c ~ (log c)/2·m0sum c`.
3. **Assembly.**  With `dsum c ~ c²·m0sum c` (A51) the ratio
   `nvarSum·(2c²)/(log c·dsum) → 1` is a product of two proved limits.  For
   the residual, the test function `y = (log c/(2c))·nE` in the count span
   gives `‖r(m)‖²·m0sum ≤ E[(k/n − a·k)²]·m0sum`, whose window part costs
   `ε²·(log c)²` with `ε ≤ 3δ` (hence `ε²·log c ≤ 9/log log c → 0`) and whose
   tail part is killed by the `1/c³` tail bound.  Hence
   `‖r(m)‖²·m0sum·(2c²)/(log c·dsum) → 0`.

No new axioms, no `sorry`, no `native_decide` on reals.  Head results audit to
the base triple `[propext, Classical.choice, Quot.sound]` (`#print axioms` at
the end of the file).
-/

namespace Gap2CensusNvarSharp

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2CensusVarianceSep Gap2AnomalyAsymptotics Gap2CensusOneSidedRate
  Gap2CensusDsumSaddle Gap2CensusRowSaddle Gap2SharpRateGap Finset Filter
open scoped Gap2CensusProductForm Nat
open Topology

/-! ## Section A: the window partition of the census mass -/

/-- Pointwise positivity of the window slack for `c ≥ 3` (the pointwise form of
`deltaS_pos_eventually`). -/
theorem deltaS_pos' {c : ℕ} (hc : 3 ≤ c) : 0 < deltaS c := by
  have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith
  have hLL : (0 : ℝ) < Real.log (Real.log (c : ℝ)) := Real.log_pos hL1
  exact div_pos one_pos (Real.sqrt_pos.2 (mul_pos hL hLL))

/-- Row mass strictly below the window: `Σ_{n < winLo} wrow`. -/
noncomputable def lowTailM (c : ℕ) : ℝ := ∑ n ∈ Finset.range (winLo c), wrow c n

/-- Row mass strictly above the window: `Σ_{winHi < n ≤ c} wrow`. -/
noncomputable def upTailM (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), wrow c n

/-- Row mass on the window: `Σ_{winLo ≤ n ≤ winHi} wrow`. -/
noncomputable def winMassM (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), wrow c n

/-- The total off-window mass. -/
noncomputable def tailMassM (c : ℕ) : ℝ := lowTailM c + upTailM c

/-- The lower window edge never passes the lower reference point. -/
theorem winLo_le_refLo (c : ℕ) (hc : 3 ≤ c) : winLo c ≤ refLo c := by
  apply Nat.floor_mono
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2 : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  calc 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c)
      ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) h2
    _ = 2 * (c : ℝ) / Real.log (c : ℝ) := mul_one _

/-- The upper window edge never precedes the upper reference point. -/
theorem refHi_le_winHi (c : ℕ) (hc : 3 ≤ c) : refHi c ≤ winHi c := by
  apply Nat.ceil_mono
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  calc 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c)
      = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * 1 := (mul_one _).symm
    _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (by linarith))
        linarith

/-- The floor form of the upper bound on `winLo`. -/
theorem winLo_le (c : ℕ) (hc : 3 ≤ c) (hδ1 : deltaS c ≤ 1) :
    (winLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) := by
  apply Nat.floor_le
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  exact mul_nonneg (by positivity) (by linarith)

/-- The floor form of the lower bound on `winLo`. -/
theorem lt_winLo (c : ℕ) :
    2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) - 1 < (winLo c : ℝ) := by
  have h := Nat.lt_floor_add_one (2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c))
  simp only [winLo]
  linarith [h]

/-- The ceil form of the lower bound on `winHi`. -/
theorem ge_winHi (c : ℕ) :
    2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) ≤ (winHi c : ℝ) :=
  Nat.le_ceil _

/-- The ceil form of the upper bound on `winHi`. -/
theorem winHi_le (c : ℕ) (hc : 3 ≤ c) :
    (winHi c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) + 1 := by
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hnn : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  have h := Nat.ceil_lt_add_one hnn
  simp only [winHi]
  linarith [h]

/-- The window is nonempty (its lower edge never exceeds its upper edge). -/
theorem winLo_le_winHi (c : ℕ) (hc : 3 ≤ c) (hδ1 : deltaS c ≤ 1) : winLo c ≤ winHi c := by
  have h1 := winLo_le c hc hδ1
  have h2 := ge_winHi c
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2c : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  have hle : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c)
      ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by
    calc 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c)
        ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith) h2c
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by
          have h1le : (1 : ℝ) ≤ (1 + etaS c) * (1 + deltaS c) := by
            nlinarith [hη, hδ, mul_nonneg hη hδ]
          calc 2 * (c : ℝ) / Real.log (c : ℝ) * 1
              ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * ((1 + etaS c) * (1 + deltaS c)) :=
                mul_le_mul_of_nonneg_left h1le h2c
            _ = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by ring
  exact_mod_cast h1.trans (hle.trans h2)

/-- Eventually the upper window edge lies inside the summation range. -/
theorem winHi_le_c_ev : ∀ᶠ c : ℕ in atTop, winHi c ≤ c := by
  have hη1 : ∀ᶠ c : ℕ in atTop, etaS c ≤ 1 :=
    tendsto_etaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 3, hη1, hδ1,
    tendsto_log_atTop_nat.eventually_ge_atTop 16] with c hc hη1c hδ1c hL16
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hle := winHi_le c hc
  have hprod : (1 + etaS c) * (1 + deltaS c) ≤ 4 := by nlinarith [hη, hδ, hη1c, hδ1c]
  have hmain : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c)
      ≤ 8 * (c : ℝ) / Real.log (c : ℝ) := by
    calc 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c)
        ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * 4 := by
          have h := mul_le_mul_of_nonneg_left hprod
            (div_nonneg (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity) hL.le)
          rwa [← mul_assoc] at h
      _ = 8 * (c : ℝ) / Real.log (c : ℝ) := by ring
  have hcm1 : (1 : ℝ) ≤ (c : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 2 ≤ c)
    linarith
  have h1 : 8 * (c : ℝ) ≤ ((c : ℝ) - 1) * Real.log (c : ℝ) := by
    calc 8 * (c : ℝ) ≤ 16 * ((c : ℝ) - 1) := by nlinarith [hcm1]
      _ = ((c : ℝ) - 1) * 16 := by ring
      _ ≤ ((c : ℝ) - 1) * Real.log (c : ℝ) :=
          mul_le_mul_of_nonneg_left hL16 (by linarith)
  have h8 : 8 * (c : ℝ) / Real.log (c : ℝ) ≤ (c : ℝ) - 1 := by
    rw [div_le_iff₀ hL]
    exact h1
  have hR : (winHi c : ℝ) ≤ (c : ℝ) := by linarith [hle, hmain, h8]
  exact_mod_cast hR

/-- Eventually the lower window edge is at least `1`. -/
theorem one_le_winLo_ev : ∀ᶠ c : ℕ in atTop, 1 ≤ winLo c := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 3, hδ1,
    tendsto_two_c_div_log_atTop.eventually_ge_atTop 4] with c hc hδ1c h2cL
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2 : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  apply Nat.le_floor
  rw [Nat.cast_one]
  calc (1 : ℝ) ≤ 4 * (1 / 2) := by norm_num
    _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_right h2cL (by norm_num)
    _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 - deltaS c) := by
        apply mul_le_mul_of_nonneg_left _ h2
        linarith [hδ1c]

/-- `winLo → ∞` along the naturals. -/
theorem winLo_tendsto_atTop : Tendsto (fun c : ℕ => winLo c) atTop atTop := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop 3, hδ1, one_le_winLo_ev,
    tendsto_c_div_log_atTop.eventually_ge_atTop (b + 1)] with c hc hδ1c h1 hcb
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2 : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) := by positivity
  have hlt := lt_winLo c
  have hge : (c : ℝ) / Real.log (c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - deltaS c := by linarith [hδ1c]
    calc (c : ℝ) / Real.log (c : ℝ) = (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 / 2) := by ring
      _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 - deltaS c) :=
          mul_le_mul_of_nonneg_left hhalf h2
  have hR : (b : ℝ) ≤ (winLo c : ℝ) := by
    have hcb' : ((b : ℝ) + 1) ≤ (c : ℝ) / Real.log (c : ℝ) := by exact_mod_cast hcb
    linarith [hlt, hge, hcb']
  exact_mod_cast hR

/-- The gap between the lower reference and the lower window edge, as a real
lower bound: `refLo − winLo ≥ (2c/log c)·δ − 1`. -/
theorem refLo_sub_winLo_ge (c : ℕ) (hc : 3 ≤ c) (hδ1 : deltaS c ≤ 1) :
    2 * (c : ℝ) / Real.log (c : ℝ) * deltaS c - 1 ≤ (refLo c : ℝ) - (winLo c : ℝ) := by
  have h1 := two_c_div_log_sub_one_lt_refLo c
  have h2 := winLo_le c hc hδ1
  linarith [h1, h2]

/-- The gap between the upper window edge and the upper reference, as a real
lower bound: `winHi − refHi ≥ (2c/log c)(1+η)·δ − 1`. -/
theorem winHi_sub_refHi_ge (c : ℕ) (hc : 3 ≤ c) :
    2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * deltaS c - 1
      ≤ (winHi c : ℝ) - (refHi c : ℝ) := by
  have h1 := ge_winHi c
  have h2 := refHi_le c hc
  linarith [h1, h2]

/-- The census mass splits into the three window regions. -/
theorem m0sum_eq_lowTailM_add_winMassM_add_upTailM (c : ℕ)
    (h1 : winLo c ≤ winHi c + 1) (h2 : winHi c + 1 ≤ c + 1) :
    m0sum c = lowTailM c + winMassM c + upTailM c := by
  have h12 : winLo c ≤ c + 1 := h1.trans h2
  have hsplit1 : m0sum c = lowTailM c + ∑ n ∈ Finset.Ico (winLo c) (c + 1), wrow c n := by
    have h := Finset.sum_range_add_sum_Ico (f := fun n => wrow c n) h12
    rw [m0sum, lowTailM]
    exact h.symm
  rw [hsplit1, upTailM, winMassM, add_assoc]
  congr 1
  exact (Finset.sum_Ico_consecutive (f := fun n => wrow c n) h1 h2).symm

/-! ## Section B: iterated decay chains and geometric tail sums -/

/-- Partial geometric sums with ratio at most `1/2` never exceed `2`. -/
theorem geom_sum_range_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (J : ℕ) :
    ∑ j ∈ Finset.range J, r ^ j ≤ 2 := by
  have h : ∀ J : ℕ, ∑ j ∈ Finset.range J, r ^ j ≤ 2 * (1 - r ^ J) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ]
      have hrJ : (0 : ℝ) ≤ r ^ J := pow_nonneg hr0 J
      have h2 : 2 * r ^ (J + 1) ≤ r ^ J := by
        rw [pow_succ]
        calc 2 * (r ^ J * r) = r ^ J * (2 * r) := by ring
          _ ≤ r ^ J * 1 := mul_le_mul_of_nonneg_left (by linarith) hrJ
          _ = r ^ J := mul_one _
      calc ∑ j ∈ Finset.range J, r ^ j + r ^ J
          ≤ 2 * (1 - r ^ J) + r ^ J := add_le_add ih le_rfl
        _ ≤ 2 * (1 - r ^ (J + 1)) := by linarith
  have hrJ : (0 : ℝ) ≤ r ^ J := pow_nonneg hr0 J
  exact (h J).trans (by linarith)

/-- Iterating the below-saddle decay: `topT c a ≤ (2/log c)^(b−a)·topT c b`
for `1 ≤ a ≤ b ≤ refLo`. -/
theorem topT_le_pow_below :
    ∀ᶠ c : ℕ in atTop, ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ refLo c →
      topT c a ≤ (2 / Real.log (c : ℝ)) ^ (b - a) * topT c b := by
  filter_upwards [topT_decay_below, eventually_ge_atTop 3] with c hc hc3
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hr0 : (0 : ℝ) ≤ 2 / Real.log (c : ℝ) := div_nonneg (by norm_num) hL.le
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => intro _; simp
  | succ b h_le ih =>
    intro hbb1
    have hb_ref : b ≤ refLo c := le_trans (Nat.le_succ b) hbb1
    have h2b : 2 ≤ b + 1 := by omega
    have hstep : topT c b ≤ (2 / Real.log (c : ℝ)) * topT c (b + 1) := by
      have h := hc (b + 1) h2b hbb1
      rwa [Nat.add_sub_cancel] at h
    calc topT c a ≤ (2 / Real.log (c : ℝ)) ^ (b - a) * topT c b := ih hb_ref
      _ ≤ (2 / Real.log (c : ℝ)) ^ (b - a) * ((2 / Real.log (c : ℝ)) * topT c (b + 1)) :=
          mul_le_mul_of_nonneg_left hstep (pow_nonneg hr0 _)
      _ = (2 / Real.log (c : ℝ)) ^ (b + 1 - a) * topT c (b + 1) := by
          have he : b + 1 - a = b - a + 1 := by omega
          rw [he, pow_succ]
          ring

/-- Iterating the above-saddle decay: `topT c b ≤ (1/(2 log c))^(b−a)·topT c a`
for `refHi ≤ a ≤ b`. -/
theorem topT_le_pow_above :
    ∀ᶠ c : ℕ in atTop, ∀ a b : ℕ, refHi c ≤ a → a ≤ b →
      topT c b ≤ (1 / (2 * Real.log (c : ℝ))) ^ (b - a) * topT c a := by
  filter_upwards [topT_decay_above, eventually_ge_atTop 3] with c hc hc3
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hr0 : (0 : ℝ) ≤ 1 / (2 * Real.log (c : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg zero_le_two hL.le)
  intro a b ha hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b h_le ih =>
    have hb_ref : refHi c ≤ b := le_trans ha h_le
    have hstep : topT c (b + 1) ≤ (1 / (2 * Real.log (c : ℝ))) * topT c b := hc b hb_ref
    calc topT c (b + 1) ≤ (1 / (2 * Real.log (c : ℝ))) * topT c b := hstep
      _ ≤ (1 / (2 * Real.log (c : ℝ))) * ((1 / (2 * Real.log (c : ℝ))) ^ (b - a) * topT c a) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = (1 / (2 * Real.log (c : ℝ))) ^ (b + 1 - a) * topT c a := by
          have he : b + 1 - a = b - a + 1 := by omega
          rw [he, pow_succ]
          ring

/-- The row top is nonnegative. -/
theorem topT_nonneg (c n : ℕ) : (0 : ℝ) ≤ topT c n := by
  simp only [topT]
  positivity

/-- The row top at `n = 0` vanishes for `c ≥ 1`. -/
theorem topT_zero_left (c : ℕ) (hc : 1 ≤ c) : topT c 0 = 0 := by
  simp only [topT, Nat.cast_zero]
  have h2c : 2 * c ≠ 0 := by omega
  rw [zero_pow h2c]
  simp

/-- The tail sum of the row top below the window edge:
`Σ_{n < winLo} topT c n ≤ 2·topT c winLo`. -/
theorem sum_topT_range_winLo_le :
    ∀ᶠ c : ℕ in atTop, ∑ n ∈ Finset.range (winLo c), topT c n ≤ 2 * topT c (winLo c) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hr : ∀ᶠ c : ℕ in atTop, 2 / Real.log (c : ℝ) ≤ 1 / 2 := by
    filter_upwards [tendsto_log_atTop_nat.eventually_ge_atTop 4] with c hL
    have hLpos : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL]
    rw [div_le_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 2)]
    linarith [hL]
  filter_upwards [topT_le_pow_below, hδ1, one_le_winLo_ev, eventually_ge_atTop 3, hr]
    with c hchain hδ1c h1 hc hrc
  have hW_ref : winLo c ≤ refLo c := winLo_le_refLo c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hr0 : (0 : ℝ) ≤ 2 / Real.log (c : ℝ) := div_nonneg (by norm_num) hL.le
  have hpoint : ∀ n ∈ Finset.range (winLo c + 1),
      topT c n ≤ (2 / Real.log (c : ℝ)) ^ (winLo c - n) * topT c (winLo c) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnle : n ≤ winLo c := Nat.lt_succ_iff.mp hn
    rcases eq_or_lt_of_le hnle with rfl | hnlt
    · rw [Nat.sub_self, pow_zero, one_mul]
    · rcases Nat.eq_zero_or_pos n with rfl | hn1
      · rw [topT_zero_left c (by omega : 1 ≤ c)]
        exact mul_nonneg (pow_nonneg hr0 _) (topT_nonneg c _)
      · exact hchain n (winLo c) hn1 hnle hW_ref
  calc ∑ n ∈ Finset.range (winLo c), topT c n
      ≤ ∑ n ∈ Finset.range (winLo c + 1), topT c n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        · intro i _ _
          exact topT_nonneg c i
    _ ≤ ∑ n ∈ Finset.range (winLo c + 1),
          (2 / Real.log (c : ℝ)) ^ (winLo c - n) * topT c (winLo c) :=
        Finset.sum_le_sum hpoint
    _ = (∑ n ∈ Finset.range (winLo c + 1), (2 / Real.log (c : ℝ)) ^ (winLo c - n))
          * topT c (winLo c) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * topT c (winLo c) := by
        apply mul_le_mul_of_nonneg_right _ (topT_nonneg c (winLo c))
        have hrefl : (∑ n ∈ Finset.range (winLo c + 1), (2 / Real.log (c : ℝ)) ^ (winLo c - n))
            = ∑ j ∈ Finset.range (winLo c + 1), (2 / Real.log (c : ℝ)) ^ j := by
          have key : ∀ j ∈ Finset.range (winLo c + 1),
              (2 / Real.log (c : ℝ)) ^ (winLo c - j)
                = (2 / Real.log (c : ℝ)) ^ (winLo c + 1 - 1 - j) := by
            intro j hj
            rw [Finset.mem_range] at hj
            have he : winLo c + 1 - 1 - j = winLo c - j := by omega
            rw [he]
          rw [Finset.sum_congr rfl key]
          exact Finset.sum_range_reflect (fun j => (2 / Real.log (c : ℝ)) ^ j) (winLo c + 1)
        rw [hrefl]
        exact geom_sum_range_le_two hr0 hrc _

/-- The tail sum of the row top above the window edge:
`Σ_{winHi < n ≤ c} topT c n ≤ topT c winHi / log c`. -/
theorem sum_topT_Ico_winHi_le :
    ∀ᶠ c : ℕ in atTop,
      ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), topT c n
        ≤ topT c (winHi c) / Real.log (c : ℝ) := by
  have hs : ∀ᶠ c : ℕ in atTop, 1 / (2 * Real.log (c : ℝ)) ≤ 1 / 2 := by
    filter_upwards [tendsto_log_atTop_nat.eventually_ge_atTop 1] with c hL
    have hLpos : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log (c : ℝ))
      (by norm_num : (0 : ℝ) < 2)]
    linarith [hL]
  filter_upwards [topT_le_pow_above, eventually_ge_atTop 3, hs,
    tendsto_log_atTop_nat.eventually_ge_atTop 1] with c hchain hc hsc hL1
  have hW_ref : refHi c ≤ winHi c := refHi_le_winHi c hc
  have hLpos : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL1]
  have hr0 : (0 : ℝ) ≤ 1 / (2 * Real.log (c : ℝ)) :=
    div_nonneg zero_le_one (mul_nonneg zero_le_two hLpos.le)
  have hpoint : ∀ i ∈ Finset.range (c + 1 - (winHi c + 1)),
      topT c (winHi c + 1 + i)
        ≤ (1 / (2 * Real.log (c : ℝ))) ^ (i + 1) * topT c (winHi c) := by
    intro i _
    have h := hchain (winHi c) (winHi c + 1 + i) hW_ref (by omega)
    have hexp : winHi c + 1 + i - winHi c = i + 1 := by omega
    rwa [hexp] at h
  calc ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), topT c n
      = ∑ i ∈ Finset.range (c + 1 - (winHi c + 1)), topT c (winHi c + 1 + i) := by
        rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑ i ∈ Finset.range (c + 1 - (winHi c + 1)),
          (1 / (2 * Real.log (c : ℝ))) ^ (i + 1) * topT c (winHi c) :=
        Finset.sum_le_sum hpoint
    _ = ((1 / (2 * Real.log (c : ℝ)))
          * ∑ i ∈ Finset.range (c + 1 - (winHi c + 1)), (1 / (2 * Real.log (c : ℝ))) ^ i)
          * topT c (winHi c) := by
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ, mul_comm]
    _ ≤ (1 / Real.log (c : ℝ)) * topT c (winHi c) := by
        apply mul_le_mul_of_nonneg_right _ (topT_nonneg c (winHi c))
        have h2 : (1 / (2 * Real.log (c : ℝ)))
            * ∑ i ∈ Finset.range (c + 1 - (winHi c + 1)), (1 / (2 * Real.log (c : ℝ))) ^ i
            ≤ (1 / (2 * Real.log (c : ℝ))) * 2 :=
          mul_le_mul_of_nonneg_left (geom_sum_range_le_two hr0 hsc _) hr0
        calc (1 / (2 * Real.log (c : ℝ)))
            * ∑ i ∈ Finset.range (c + 1 - (winHi c + 1)), (1 / (2 * Real.log (c : ℝ))) ^ i
            ≤ (1 / (2 * Real.log (c : ℝ))) * 2 := h2
          _ = 1 / Real.log (c : ℝ) := by
              have hLne : Real.log (c : ℝ) ≠ 0 := hLpos.ne'
              rw [mul_comm, mul_one_div]
              field_simp
    _ = topT c (winHi c) / Real.log (c : ℝ) := by ring

/-- The row top at the lower window edge against the lower reference:
`topT c winLo ≤ (2/log c)^(refLo−winLo)·topT c refLo`. -/
theorem topT_winLo_le :
    ∀ᶠ c : ℕ in atTop,
      topT c (winLo c)
        ≤ (2 / Real.log (c : ℝ)) ^ (refLo c - winLo c) * topT c (refLo c) := by
  filter_upwards [topT_le_pow_below, one_le_winLo_ev, eventually_ge_atTop 3] with c hchain h1 hc
  exact hchain (winLo c) (refLo c) h1 (winLo_le_refLo c hc) (le_refl _)

/-- The row top at the upper window edge against the upper reference:
`topT c winHi ≤ (1/(2 log c))^(winHi−refHi)·topT c refHi`. -/
theorem topT_winHi_le :
    ∀ᶠ c : ℕ in atTop,
      topT c (winHi c)
        ≤ (1 / (2 * Real.log (c : ℝ))) ^ (winHi c - refHi c) * topT c (refHi c) := by
  filter_upwards [topT_le_pow_above, eventually_ge_atTop 3] with c hchain hc
  exact hchain (refHi c) (winHi c) (le_refl _) (refHi_le_winHi c hc)

/-! ## Section C: explicit tail bounds -/

/-- `log c ≤ √c` eventually (via `log x / x → 0` at `x = √c`). -/
theorem log_le_sqrt_ev : ∀ᶠ c : ℕ in atTop, Real.log (c : ℝ) ≤ Real.sqrt (c : ℝ) := by
  have hcomp : Tendsto (fun c : ℕ => Real.sqrt (c : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun c : ℕ => Real.log (Real.sqrt (c : ℝ)) / Real.sqrt (c : ℝ)) atTop
      (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hcomp
  have h2 : ∀ᶠ c : ℕ in atTop, Real.log (Real.sqrt (c : ℝ)) / Real.sqrt (c : ℝ) ≤ 1 / 2 :=
    h.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [h2, eventually_ge_atTop 1] with c hc2 hc1
  have hs : (0 : ℝ) < Real.sqrt (c : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega))
  rw [div_le_iff₀ hs] at hc2
  have hlog : Real.log (Real.sqrt (c : ℝ)) = Real.log (c : ℝ) / 2 :=
    Real.log_sqrt (Nat.cast_nonneg _)
  rw [hlog] at hc2
  linarith [hc2, Real.sqrt_nonneg (c : ℝ)]

/-- `(log c)² ≤ c` eventually. -/
theorem log_sq_le_ev : ∀ᶠ c : ℕ in atTop, (Real.log (c : ℝ)) ^ 2 ≤ (c : ℝ) := by
  filter_upwards [log_le_sqrt_ev, eventually_ge_atTop 1] with c h hc
  have h0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega))
  calc (Real.log (c : ℝ)) ^ 2 ≤ (Real.sqrt (c : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = c := Real.sq_sqrt (Nat.cast_nonneg _)

/-- `(log c)³ ≤ c` eventually (via `log log c / log c ≤ 1/6`). -/
theorem log_cubed_le_ev : ∀ᶠ c : ℕ in atTop, (Real.log (c : ℝ)) ^ 3 ≤ (c : ℝ) := by
  filter_upwards [loglog_div_log_le_sixth, eventually_ge_atTop 3] with c h16 hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  rw [div_le_iff₀ hL] at h16
  have h1 : 3 * Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega)
  calc (Real.log (c : ℝ)) ^ 3 = Real.exp (3 * Real.log (Real.log (c : ℝ))) := by
        have h2 : Real.log ((Real.log (c : ℝ)) ^ 3) = 3 * Real.log (Real.log (c : ℝ)) := by
          rw [Real.log_pow]; push_cast; ring
        rw [← Real.exp_log (pow_pos hL 3), h2]
    _ ≤ Real.exp (Real.log (c : ℝ)) := Real.exp_le_exp.2 h1
    _ = c := Real.exp_log hcpos

/-- `(log c)⁴ ≤ c` eventually. -/
theorem log_fourth_le_ev : ∀ᶠ c : ℕ in atTop, (Real.log (c : ℝ)) ^ 4 ≤ (c : ℝ) := by
  filter_upwards [loglog_div_log_le_sixth, eventually_ge_atTop 3] with c h16 hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega))
  rw [div_le_iff₀ hL] at h16
  have h1 : 4 * Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by linarith
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega)
  calc (Real.log (c : ℝ)) ^ 4 = Real.exp (4 * Real.log (Real.log (c : ℝ))) := by
        have h2 : Real.log ((Real.log (c : ℝ)) ^ 4) = 4 * Real.log (Real.log (c : ℝ)) := by
          rw [Real.log_pow]; push_cast; ring
        rw [← Real.exp_log (pow_pos hL 4), h2]
    _ ≤ Real.exp (Real.log (c : ℝ)) := Real.exp_le_exp.2 h1
    _ = c := Real.exp_log hcpos

/-- The window gap in units of the decay exponent: `(c/log c)·δ ≥ 1` eventually. -/
theorem c_div_log_mul_delta_ge_one : ∀ᶠ c : ℕ in atTop,
    1 ≤ ((c : ℝ) / Real.log (c : ℝ)) * deltaS c := by
  filter_upwards [eventually_ge_atTop 3, log_sq_le_ev] with c hc hsq
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := hL.le
  have hL1s : (1 : ℝ) < Real.log (c : ℝ) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
  have hstep1 : Real.log (c : ℝ) ≤ (c : ℝ) / Real.log (c : ℝ) := by
    rw [le_div_iff₀ hL]
    nlinarith [hsq]
  have hloglog : Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hL
    linarith
  have hstep2 : Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))
      ≤ ((c : ℝ) / Real.log (c : ℝ)) ^ 2 := by
    calc Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))
        ≤ Real.log (c : ℝ) * Real.log (c : ℝ) := mul_le_mul_of_nonneg_left hloglog hL0
      _ ≤ ((c : ℝ) / Real.log (c : ℝ)) * ((c : ℝ) / Real.log (c : ℝ)) :=
          mul_le_mul hstep1 hstep1 hL0 (div_nonneg (Nat.cast_nonneg _) hL0)
      _ = ((c : ℝ) / Real.log (c : ℝ)) ^ 2 := (sq _).symm
  have hsp : (0 : ℝ) < Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))) :=
    Real.sqrt_pos.2 (mul_pos hL (Real.log_pos hL1s))
  have hsqrt2 : Real.sqrt (((c : ℝ) / Real.log (c : ℝ)) ^ 2) = (c : ℝ) / Real.log (c : ℝ) :=
    Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) hL0)
  calc 1 ≤ ((c : ℝ) / Real.log (c : ℝ))
        / Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))) := by
        rw [le_div_iff₀ hsp, one_mul, ← hsqrt2]
        exact Real.sqrt_le_sqrt hstep2
    _ = ((c : ℝ) / Real.log (c : ℝ)) * deltaS c := by
        rw [deltaS, mul_one_div]

/-- The exponent gap beats `3·log c + log 16`:
`(c/log c)·δ·(log log c − log 2) ≥ log 16 + 3·log c` eventually. -/
theorem c_div_log_mul_delta_mul_loglog_ge : ∀ᶠ c : ℕ in atTop,
    Real.log 16 + 3 * Real.log (c : ℝ)
      ≤ ((c : ℝ) / Real.log (c : ℝ)) * deltaS c
        * (Real.log (Real.log (c : ℝ)) - Real.log 2) := by
  have hP1 : ∀ᶠ c : ℕ in atTop, 4 * Real.log (c : ℝ)
      ≤ ((c : ℝ) / Real.log (c : ℝ)) * deltaS c := by
    filter_upwards [eventually_ge_atTop 3, log_fourth_le_ev,
      tendsto_log_atTop_nat.eventually_ge_atTop 4] with c hc h4 hL4
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := hL.le
    have hL1s : (1 : ℝ) < Real.log (c : ℝ) :=
      one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
    have hloglog : Real.log (Real.log (c : ℝ)) ≤ Real.log (c : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hL
      linarith
    have hsqrt_le : Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ)))
        ≤ Real.log (c : ℝ) := by
      calc Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ)))
          ≤ Real.sqrt (Real.log (c : ℝ) * Real.log (c : ℝ)) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hloglog hL0)
        _ = Real.log (c : ℝ) := by rw [← sq, Real.sqrt_sq hL0]
    have hsp : (0 : ℝ) < Real.sqrt (Real.log (c : ℝ) * Real.log (Real.log (c : ℝ))) :=
      Real.sqrt_pos.2 (mul_pos hL (Real.log_pos hL1s))
    have h4L3 : 4 * Real.log (c : ℝ) * (Real.log (c : ℝ)) ^ 2 ≤ (c : ℝ) := by
      have hL4' : (4 : ℝ) ≤ Real.log (c : ℝ) := hL4
      calc 4 * Real.log (c : ℝ) * (Real.log (c : ℝ)) ^ 2
          = 4 * (Real.log (c : ℝ)) ^ 3 := by ring
        _ ≤ (Real.log (c : ℝ)) ^ 4 := by
            calc 4 * (Real.log (c : ℝ)) ^ 3
                ≤ Real.log (c : ℝ) * (Real.log (c : ℝ)) ^ 3 :=
                  mul_le_mul_of_nonneg_right hL4' (pow_nonneg hL0 3)
              _ = (Real.log (c : ℝ)) ^ 4 := by ring
        _ ≤ c := h4
    have hmain : 4 * Real.log (c : ℝ) ≤ (c : ℝ) / (Real.log (c : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hL 2)]
      exact h4L3
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have heq : (c : ℝ) / Real.log (c : ℝ) * deltaS c
        = (c : ℝ) / (Real.log (c : ℝ) * Real.sqrt (Real.log (c : ℝ)
            * Real.log (Real.log (c : ℝ)))) := by
      rw [deltaS, div_mul_div_comm, mul_one]
    have hstep : (c : ℝ) / (Real.log (c : ℝ)) ^ 2
        ≤ ((c : ℝ) / Real.log (c : ℝ)) * deltaS c := by
      rw [heq, pow_two]
      exact div_le_div_of_nonneg_left hcpos.le (mul_pos hL hsp)
        (mul_le_mul_of_nonneg_left hsqrt_le hL.le)
    exact hmain.trans hstep
  have hP2 : ∀ᶠ c : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log (c : ℝ)) - Real.log 2 := by
    filter_upwards [tendsto_log_log_atTop_nat.eventually_ge_atTop 2] with c hll2
    have h2le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
    linarith [hll2, h2le]
  filter_upwards [hP1, hP2, eventually_ge_atTop 3,
    tendsto_log_atTop_nat.eventually_ge_atTop 16] with c h1 h2 hc hL16
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hfac0 : (0 : ℝ) ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) hL.le) hδ
  have hlog16le : Real.log 16 ≤ Real.log (c : ℝ) := by
    have hle16 : Real.log 16 ≤ 16 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
      linarith [h]
    linarith [hL16, hle16]
  calc Real.log 16 + 3 * Real.log (c : ℝ) ≤ 4 * Real.log (c : ℝ) := by linarith [hlog16le]
    _ ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c := h1
    _ ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c
        * (Real.log (Real.log (c : ℝ)) - Real.log 2) := by
        calc (c : ℝ) / Real.log (c : ℝ) * deltaS c
            = (c : ℝ) / Real.log (c : ℝ) * deltaS c * 1 := (mul_one _).symm
          _ ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c
              * (Real.log (Real.log (c : ℝ)) - Real.log 2) :=
              mul_le_mul_of_nonneg_left h2 hfac0

/-- The below-window geometric ratio is super-polynomially small:
`(2/log c)^(refLo−winLo) ≤ 1/(16·c³)` eventually. -/
theorem pow_ratio_small_below : ∀ᶠ c : ℕ in atTop,
    (2 / Real.log (c : ℝ)) ^ (refLo c - winLo c) ≤ 1 / (16 * (c : ℝ) ^ 3) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hgap : ∀ᶠ c : ℕ in atTop, (c : ℝ) / Real.log (c : ℝ) * deltaS c
      ≤ (refLo c : ℝ) - (winLo c : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hδ1, c_div_log_mul_delta_ge_one] with c hc hδ1c h1
    have h2 := refLo_sub_winLo_ge c hc hδ1c
    have hrel : 2 * (c : ℝ) / Real.log (c : ℝ) * deltaS c
        = 2 * ((c : ℝ) / Real.log (c : ℝ) * deltaS c) := by ring
    linarith [h1, h2, hrel]
  filter_upwards [eventually_ge_atTop 3, hδ1, hgap, c_div_log_mul_delta_mul_loglog_ge,
    tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hc hδ1c hgapc hPc hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have hr_pos : (0 : ℝ) < 2 / Real.log (c : ℝ) := div_pos (by norm_num) hL
  have hcast : ((refLo c - winLo c : ℕ) : ℝ) = (refLo c : ℝ) - (winLo c : ℝ) :=
    Nat.cast_sub (winLo_le_refLo c hc)
  have hll : (0 : ℝ) ≤ Real.log (Real.log (c : ℝ)) - Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hL2
    linarith [h]
  have hexp : ((refLo c : ℝ) - (winLo c : ℝ)) * (Real.log (Real.log (c : ℝ)) - Real.log 2)
      ≥ Real.log 16 + 3 * Real.log (c : ℝ) := by
    calc Real.log 16 + 3 * Real.log (c : ℝ)
        ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c
          * (Real.log (Real.log (c : ℝ)) - Real.log 2) := hPc
      _ ≤ ((refLo c : ℝ) - (winLo c : ℝ)) * (Real.log (Real.log (c : ℝ)) - Real.log 2) :=
          mul_le_mul_of_nonneg_right hgapc hll
  have hr_log : Real.log (2 / Real.log (c : ℝ))
      = Real.log 2 - Real.log (Real.log (c : ℝ)) := by
    rw [Real.log_div (by norm_num) hL.ne']
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have e3 : Real.exp (3 * Real.log (c : ℝ)) = (c : ℝ) ^ 3 := by
    have h2 : Real.log ((c : ℝ) ^ 3) = 3 * Real.log (c : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← Real.exp_log (pow_pos hcpos 3), h2]
  calc (2 / Real.log (c : ℝ)) ^ (refLo c - winLo c)
      = Real.exp (((refLo c - winLo c : ℕ) : ℝ) * Real.log (2 / Real.log (c : ℝ))) := by
        rw [← Real.exp_log (pow_pos hr_pos _), Real.log_pow]
    _ ≤ Real.exp (-(Real.log 16 + 3 * Real.log (c : ℝ))) := by
        apply Real.exp_le_exp.2
        rw [hr_log, hcast]
        have hid : ((refLo c : ℝ) - (winLo c : ℝ))
            * (Real.log 2 - Real.log (Real.log (c : ℝ)))
            = -(((refLo c : ℝ) - (winLo c : ℝ))
              * (Real.log (Real.log (c : ℝ)) - Real.log 2)) := by ring
        rw [hid]
        linarith [hexp]
    _ = 1 / (16 * (c : ℝ) ^ 3) := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16), e3,
          one_div]

/-- The above-window geometric ratio is super-polynomially small:
`(1/(2·log c))^(winHi−refHi) ≤ 1/(4·c³)` eventually. -/
theorem pow_ratio_small_above : ∀ᶠ c : ℕ in atTop,
    (1 / (2 * Real.log (c : ℝ))) ^ (winHi c - refHi c) ≤ 1 / (4 * (c : ℝ) ^ 3) := by
  have hgap : ∀ᶠ c : ℕ in atTop, (c : ℝ) / Real.log (c : ℝ) * deltaS c
      ≤ (winHi c : ℝ) - (refHi c : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, c_div_log_mul_delta_ge_one] with c hc h1
    have h2 := winHi_sub_refHi_ge c hc
    have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
    have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have h2c0 : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) :=
      div_nonneg (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity) hL.le
    have h2x : 2 * ((c : ℝ) / Real.log (c : ℝ) * deltaS c)
        ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * deltaS c := by
      calc 2 * ((c : ℝ) / Real.log (c : ℝ) * deltaS c)
          = (2 * (c : ℝ) / Real.log (c : ℝ)) * deltaS c := by ring
        _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 + etaS c) * deltaS c := by
            apply mul_le_mul_of_nonneg_right _ hδ
            calc (2 * (c : ℝ) / Real.log (c : ℝ))
                = (2 * (c : ℝ) / Real.log (c : ℝ)) * 1 := (mul_one _).symm
              _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 + etaS c) :=
                  mul_le_mul_of_nonneg_left (by linarith [hη]) h2c0
    linarith [h1, h2, h2x]
  filter_upwards [eventually_ge_atTop 3, hgap, c_div_log_mul_delta_mul_loglog_ge,
    tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hc hgapc hPc hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := hL.le
  have hr_pos : (0 : ℝ) < 1 / (2 * Real.log (c : ℝ)) :=
    div_pos one_pos (mul_pos (by norm_num) hL)
  have hcast : ((winHi c - refHi c : ℕ) : ℝ) = (winHi c : ℝ) - (refHi c : ℝ) :=
    Nat.cast_sub (refHi_le_winHi c hc)
  have hll : (0 : ℝ) ≤ Real.log (Real.log (c : ℝ)) - Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hL2
    linarith [h]
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h0gap : (0 : ℝ) ≤ (winHi c : ℝ) - (refHi c : ℝ) := by
    have hbase : (0 : ℝ) ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) hL0) hδ
    linarith [hgapc, hbase]
  have hexp : ((winHi c : ℝ) - (refHi c : ℝ)) * (Real.log 2 + Real.log (Real.log (c : ℝ)))
      ≥ Real.log 4 + 3 * Real.log (c : ℝ) := by
    have hge : Real.log (Real.log (c : ℝ)) - Real.log 2
        ≤ Real.log 2 + Real.log (Real.log (c : ℝ)) := by
      have h2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith [h2nn]
    calc Real.log 4 + 3 * Real.log (c : ℝ)
        ≤ Real.log 16 + 3 * Real.log (c : ℝ) := by
          have h416 : Real.log 4 ≤ Real.log 16 :=
            Real.log_le_log (by norm_num) (by norm_num)
          linarith [h416]
      _ ≤ (c : ℝ) / Real.log (c : ℝ) * deltaS c
          * (Real.log (Real.log (c : ℝ)) - Real.log 2) := hPc
      _ ≤ ((winHi c : ℝ) - (refHi c : ℝ)) * (Real.log (Real.log (c : ℝ)) - Real.log 2) :=
          mul_le_mul_of_nonneg_right hgapc hll
      _ ≤ ((winHi c : ℝ) - (refHi c : ℝ)) * (Real.log 2 + Real.log (Real.log (c : ℝ))) :=
          mul_le_mul_of_nonneg_left hge h0gap
  have hr_log : Real.log (1 / (2 * Real.log (c : ℝ)))
      = -(Real.log 2 + Real.log (Real.log (c : ℝ))) := by
    rw [Real.log_div one_ne_zero (mul_ne_zero (by norm_num) hL.ne'), Real.log_one,
      Real.log_mul (by norm_num) hL.ne', zero_sub]
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have e3 : Real.exp (3 * Real.log (c : ℝ)) = (c : ℝ) ^ 3 := by
    have h2 : Real.log ((c : ℝ) ^ 3) = 3 * Real.log (c : ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    rw [← Real.exp_log (pow_pos hcpos 3), h2]
  calc (1 / (2 * Real.log (c : ℝ))) ^ (winHi c - refHi c)
      = Real.exp (((winHi c - refHi c : ℕ) : ℝ) * Real.log (1 / (2 * Real.log (c : ℝ)))) := by
        rw [← Real.exp_log (pow_pos hr_pos _), Real.log_pow]
    _ ≤ Real.exp (-(Real.log 4 + 3 * Real.log (c : ℝ))) := by
        apply Real.exp_le_exp.2
        rw [hr_log, hcast]
        have hid : ((winHi c : ℝ) - (refHi c : ℝ))
            * (-(Real.log 2 + Real.log (Real.log (c : ℝ))))
            = -(((winHi c : ℝ) - (refHi c : ℝ))
              * (Real.log 2 + Real.log (Real.log (c : ℝ)))) := by ring
        rw [hid]
        linarith [hexp]
    _ = 1 / (4 * (c : ℝ) ^ 3) := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), e3,
          one_div]

/-- The row top over `c!` is the top cell of the row, hence at most the row. -/
theorem topT_div_fact_le_wrow (c n : ℕ) : topT c n / (Nat.factorial c : ℝ) ≤ wrow c n := by
  have h := cellW_top_le_wrow c n
  have heq : topT c n / (Nat.factorial c : ℝ) = cellW c n c := by
    have hf : (Nat.factorial c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero c)
    have hn' : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    simp only [topT, cellW]
    field_simp
  rwa [heq]

/-- The A51 row domination `wrow ≤ 2·topT/c!`, restated through `topT`. -/
theorem wrow_le_two_topT_div_fact (c n : ℕ) (hn2 : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2) :
    wrow c n ≤ 2 * topT c n / (Nat.factorial c : ℝ) := by
  have h := wrow_le_two_wterm c n hn2
  have heq : 2 * topT c n / (Nat.factorial c : ℝ)
      = 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    have hf : (Nat.factorial c : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero c)
    have hn' : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    simp only [topT]
    field_simp
  exact h.trans_eq heq.symm

/-- A single row never exceeds the total mass. -/
theorem wrow_le_m0sum (c n0 : ℕ) (h : n0 ≤ c) : wrow c n0 ≤ m0sum c :=
  Finset.single_le_sum (fun i _ => wrow_nonneg c i) (Finset.mem_range.2 (Nat.lt_succ_iff.2 h))

/-- Eventually `refLo ≤ c`. -/
theorem refLo_le_c_ev : ∀ᶠ c : ℕ in atTop, refLo c ≤ c := by
  filter_upwards [eventually_ge_atTop 3,
    tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hc hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have h1 : (refLo c : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) :=
    Nat.floor_le (div_nonneg (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity) hL.le)
  have h2 : 2 * (c : ℝ) / Real.log (c : ℝ) ≤ (c : ℝ) := by
    rw [div_le_iff₀ hL]
    calc 2 * (c : ℝ) = (c : ℝ) * 2 := by ring
      _ ≤ (c : ℝ) * Real.log (c : ℝ) := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg _)
  exact_mod_cast h1.trans h2

/-- Eventually `refHi ≤ c`. -/
theorem refHi_le_c_ev : ∀ᶠ c : ℕ in atTop, refHi c ≤ c := by
  filter_upwards [winHi_le_c_ev, eventually_ge_atTop 3] with c h hc
  exact (refHi_le_winHi c hc).trans h

/-- The lower window edge is at least `c/(2·log c)` eventually. -/
theorem winLo_ge_c_div_two_log_ev : ∀ᶠ c : ℕ in atTop,
    (c : ℝ) / (2 * Real.log (c : ℝ)) ≤ (winLo c : ℝ) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 3, hδ1, log_cubed_le_ev,
    tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hc hδ1c hcub hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2cL : (2 : ℝ) ≤ (c : ℝ) / Real.log (c : ℝ) := by
    rw [le_div_iff₀ hL]
    have h1 : 2 * Real.log (c : ℝ) ≤ (Real.log (c : ℝ)) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hL2 hL.le,
        mul_le_mul_of_nonneg_left hL2 (sq_nonneg (Real.log (c : ℝ)))]
    calc 2 * Real.log (c : ℝ) ≤ (Real.log (c : ℝ)) ^ 3 := h1
      _ ≤ c := hcub
  have hlt := lt_winLo c
  have hge1 : (c : ℝ) / Real.log (c : ℝ)
      ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) := by
    have hhalf : (1 / 2 : ℝ) ≤ 1 - deltaS c := by linarith [hδ1c]
    calc (c : ℝ) / Real.log (c : ℝ) = (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 / 2) := by ring
      _ ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) * (1 - deltaS c) :=
          mul_le_mul_of_nonneg_left hhalf
            (div_nonneg (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity) hL.le)
  have hstep : (c : ℝ) / (2 * Real.log (c : ℝ)) ≤ (c : ℝ) / Real.log (c : ℝ) - 1 := by
    have hc2L : (1 : ℝ) ≤ (c : ℝ) / (2 * Real.log (c : ℝ)) := by
      rw [le_div_iff₀ (by linarith [hL] : (0 : ℝ) < 2 * Real.log (c : ℝ))]
      calc 1 * (2 * Real.log (c : ℝ)) = 2 * Real.log (c : ℝ) := by ring
        _ ≤ (c : ℝ) := by
          have h1 : 2 * Real.log (c : ℝ) ≤ (Real.log (c : ℝ)) ^ 3 := by
            nlinarith [mul_le_mul_of_nonneg_left hL2 hL.le,
              mul_le_mul_of_nonneg_left hL2 (sq_nonneg (Real.log (c : ℝ)))]
          exact (h1.trans hcub)
    have hrel : (c : ℝ) / (2 * Real.log (c : ℝ)) = (c : ℝ) / Real.log (c : ℝ) / 2 := by
      rw [mul_comm (2 : ℝ) (Real.log (c : ℝ)), ← div_div]
    rw [hrel] at hc2L ⊢
    linarith
  linarith [hlt, hge1, hstep]

/-- The lower window edge clears the row-domination threshold: `2c ≤ winLo²`
eventually. -/
theorem winLo_sq_ge_two_c_ev : ∀ᶠ c : ℕ in atTop, 2 * (c : ℝ) ≤ (winLo c : ℝ) ^ 2 := by
  filter_upwards [winLo_ge_c_div_two_log_ev, eventually_ge_atTop 3, log_cubed_le_ev,
    tendsto_log_atTop_nat.eventually_ge_atTop 8] with c hge hc hcub hL8
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL8]
  have h2L0 : (0 : ℝ) < 2 * Real.log (c : ℝ) := by linarith
  have hsq : ((c : ℝ) / (2 * Real.log (c : ℝ))) ^ 2 ≤ (winLo c : ℝ) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) h2L0.le) hge 2
  have h8 : 8 * (Real.log (c : ℝ)) ^ 2 ≤ (c : ℝ) := by
    have h1 : 8 * (Real.log (c : ℝ)) ^ 2 ≤ (Real.log (c : ℝ)) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hL8 (sq_nonneg (Real.log (c : ℝ)))]
    exact h1.trans hcub
  have hmain : 2 * (c : ℝ) ≤ ((c : ℝ) / (2 * Real.log (c : ℝ))) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos h2L0 2)]
    nlinarith [mul_le_mul_of_nonneg_left h8 (Nat.cast_nonneg c)]
  exact hmain.trans hsq

/-- The upper window edge clears the row-domination threshold: `2c ≤ winHi²`
eventually. -/
theorem winHi_sq_ge_two_c_ev : ∀ᶠ c : ℕ in atTop, 2 * (c : ℝ) ≤ (winHi c : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 3, log_sq_le_ev,
    tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hc hsqc hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h2c0 : (0 : ℝ) ≤ 2 * (c : ℝ) / Real.log (c : ℝ) :=
    div_nonneg (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity) hL.le
  have hge : 2 * (c : ℝ) / Real.log (c : ℝ) ≤ (winHi c : ℝ) := by
    calc 2 * (c : ℝ) / Real.log (c : ℝ) = 2 * (c : ℝ) / Real.log (c : ℝ) * 1 := (mul_one _).symm
      _ ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * ((1 + etaS c) * (1 + deltaS c)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hη, hδ, mul_nonneg hη hδ]) h2c0
      _ = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by ring
      _ ≤ (winHi c : ℝ) := ge_winHi c
  have hsq : (2 * (c : ℝ) / Real.log (c : ℝ)) ^ 2 ≤ (winHi c : ℝ) ^ 2 :=
    pow_le_pow_left₀ h2c0 hge 2
  have hmain : 2 * (c : ℝ) ≤ (2 * (c : ℝ) / Real.log (c : ℝ)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (pow_pos hL 2)]
    nlinarith [mul_le_mul_of_nonneg_left hsqc (show (0 : ℝ) ≤ 2 * (c : ℝ) by positivity),
      sq_nonneg (c : ℝ)]
  exact hmain.trans hsq

/-- The below-window tail, filtered at the row-domination threshold. -/
theorem lowTailM_le_smallMass_add (c : ℕ) (hL2 : 2 ≤ Real.log (c : ℝ))
    (hwin : winLo c ≤ c + 1) :
    lowTailM c ≤ smallMass c
      + ∑ n ∈ (Finset.range (winLo c)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ 2 * (c : ℝ))),
          wrow c n := by
  have h2c : 2 * (c : ℝ) ≤ (c : ℝ) * Real.log (c : ℝ) := by
    calc 2 * (c : ℝ) = (c : ℝ) * 2 := by ring
      _ ≤ (c : ℝ) * Real.log (c : ℝ) := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg _)
  rw [lowTailM,
    ← Finset.sum_filter_add_sum_filter_not (Finset.range (winLo c))
      (fun n => (n : ℝ) ^ 2 ≤ 2 * (c : ℝ)) (fun n => wrow c n)]
  apply add_le_add_left
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [smallSet, Finset.mem_filter]
    exact ⟨Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hn.1) hwin), hn.2.trans h2c⟩
  · intro i _ _
    exact wrow_nonneg c i

/-- The below-window tail is at most the small mass plus four window-edge rows. -/
theorem lowTailM_le : ∀ᶠ c : ℕ in atTop,
    lowTailM c ≤ smallMass c + 4 * wrow c (winLo c) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [sum_topT_range_winLo_le, eventually_ge_atTop 3, one_le_winLo_ev,
    winHi_le_c_ev, tendsto_log_atTop_nat.eventually_ge_atTop 2, hδ1]
    with c hsum hc h1 hwhi hL2 hδ1c
  have hwin : winLo c ≤ c + 1 := (winLo_le_winHi c hc hδ1c).trans (Nat.le_succ_of_le hwhi)
  have hsplit := lowTailM_le_smallMass_add c hL2 hwin
  have hfactnn : (0 : ℝ) ≤ (Nat.factorial c : ℝ) := Nat.cast_nonneg _
  have hfs : ∑ n ∈ (Finset.range (winLo c)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ 2 * (c : ℝ))),
      wrow c n ≤ 4 * wrow c (winLo c) := by
    calc ∑ n ∈ (Finset.range (winLo c)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ 2 * (c : ℝ))),
          wrow c n
        ≤ ∑ n ∈ (Finset.range (winLo c)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ 2 * (c : ℝ))),
            2 * topT c n / (Nat.factorial c : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hn2 : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2 := le_of_not_ge hn.2
          exact wrow_le_two_topT_div_fact c n hn2
      _ ≤ ∑ n ∈ Finset.range (winLo c), 2 * topT c n / (Nat.factorial c : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _
          exact div_nonneg (mul_nonneg (by norm_num) (topT_nonneg c i)) hfactnn
      _ = 2 / (Nat.factorial c : ℝ) * ∑ n ∈ Finset.range (winLo c), topT c n := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ 2 / (Nat.factorial c : ℝ) * (2 * topT c (winLo c)) :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hfactnn)
      _ ≤ 4 * wrow c (winLo c) := by
          have hle := topT_div_fact_le_wrow c (winLo c)
          calc 2 / (Nat.factorial c : ℝ) * (2 * topT c (winLo c))
              = 4 * (topT c (winLo c) / (Nat.factorial c : ℝ)) := by ring
            _ ≤ 4 * wrow c (winLo c) := mul_le_mul_of_nonneg_left hle (by norm_num)
  calc lowTailM c ≤ smallMass c
        + ∑ n ∈ (Finset.range (winLo c)).filter (fun n : ℕ => ¬ ((n : ℝ) ^ 2 ≤ 2 * (c : ℝ))),
            wrow c n := hsplit
    _ ≤ smallMass c + 4 * wrow c (winLo c) := add_le_add_right hfs _

/-- The above-window tail is at most `2/log c` window-edge rows. -/
theorem upTailM_le : ∀ᶠ c : ℕ in atTop,
    upTailM c ≤ (2 / Real.log (c : ℝ)) * wrow c (winHi c) := by
  filter_upwards [sum_topT_Ico_winHi_le, eventually_ge_atTop 3, winHi_sq_ge_two_c_ev,
    tendsto_log_atTop_nat.eventually_ge_atTop 1] with c hsum hc hsq2 hL1
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL1]
  have hfactnn : (0 : ℝ) ≤ (Nat.factorial c : ℝ) := Nat.cast_nonneg _
  calc upTailM c = ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), wrow c n := rfl
    _ ≤ ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), 2 * topT c n / (Nat.factorial c : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Ico] at hn
        have hn2 : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2 := by
          have hge : (winHi c : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : winHi c ≤ n)
          calc 2 * (c : ℝ) ≤ (winHi c : ℝ) ^ 2 := hsq2
            _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hge 2
        exact wrow_le_two_topT_div_fact c n hn2
    _ = 2 / (Nat.factorial c : ℝ) * ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), topT c n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ 2 / (Nat.factorial c : ℝ) * (topT c (winHi c) / Real.log (c : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (by norm_num) hfactnn)
    _ = (2 / Real.log (c : ℝ)) * (topT c (winHi c) / (Nat.factorial c : ℝ)) := by ring
    _ ≤ (2 / Real.log (c : ℝ)) * wrow c (winHi c) :=
        mul_le_mul_of_nonneg_left (topT_div_fact_le_wrow c (winHi c))
          (div_nonneg (by norm_num) hL.le)

/-- The window-edge row below the saddle is at most `m0sum/(8c³)` eventually. -/
theorem wrow_winLo_le : ∀ᶠ c : ℕ in atTop,
    wrow c (winLo c) ≤ (1 / (8 * (c : ℝ) ^ 3)) * m0sum c := by
  filter_upwards [winLo_sq_ge_two_c_ev, topT_winLo_le, pow_ratio_small_below, refLo_le_c_ev,
    eventually_ge_atTop 3] with c hsq2 hchain hpow href hc
  have hfactnn : (0 : ℝ) ≤ (Nat.factorial c : ℝ) := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ 1 / (8 * (c : ℝ) ^ 3) := by positivity
  calc wrow c (winLo c) ≤ 2 * topT c (winLo c) / (Nat.factorial c : ℝ) :=
        wrow_le_two_topT_div_fact c (winLo c) hsq2
    _ = 2 / (Nat.factorial c : ℝ) * topT c (winLo c) := by ring
    _ ≤ 2 / (Nat.factorial c : ℝ)
        * ((2 / Real.log (c : ℝ)) ^ (refLo c - winLo c) * topT c (refLo c)) :=
        mul_le_mul_of_nonneg_left hchain (div_nonneg (by norm_num) hfactnn)
    _ ≤ 2 / (Nat.factorial c : ℝ) * ((1 / (16 * (c : ℝ) ^ 3)) * topT c (refLo c)) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hfactnn)
        exact mul_le_mul_of_nonneg_right hpow (topT_nonneg c _)
    _ = (1 / (8 * (c : ℝ) ^ 3)) * (topT c (refLo c) / (Nat.factorial c : ℝ)) := by ring
    _ ≤ (1 / (8 * (c : ℝ) ^ 3)) * wrow c (refLo c) :=
        mul_le_mul_of_nonneg_left (topT_div_fact_le_wrow c (refLo c)) hf0
    _ ≤ (1 / (8 * (c : ℝ) ^ 3)) * m0sum c :=
        mul_le_mul_of_nonneg_left (wrow_le_m0sum c (refLo c) href) hf0

/-- The window-edge row above the saddle is at most `m0sum/(2c³)` eventually. -/
theorem wrow_winHi_le : ∀ᶠ c : ℕ in atTop,
    wrow c (winHi c) ≤ (1 / (2 * (c : ℝ) ^ 3)) * m0sum c := by
  filter_upwards [winHi_sq_ge_two_c_ev, topT_winHi_le, pow_ratio_small_above, refHi_le_c_ev,
    eventually_ge_atTop 3] with c hsq2 hchain hpow href hc
  have hfactnn : (0 : ℝ) ≤ (Nat.factorial c : ℝ) := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ 1 / (2 * (c : ℝ) ^ 3) := by positivity
  calc wrow c (winHi c) ≤ 2 * topT c (winHi c) / (Nat.factorial c : ℝ) :=
        wrow_le_two_topT_div_fact c (winHi c) hsq2
    _ = 2 / (Nat.factorial c : ℝ) * topT c (winHi c) := by ring
    _ ≤ 2 / (Nat.factorial c : ℝ)
        * ((1 / (2 * Real.log (c : ℝ))) ^ (winHi c - refHi c) * topT c (refHi c)) :=
        mul_le_mul_of_nonneg_left hchain (div_nonneg (by norm_num) hfactnn)
    _ ≤ 2 / (Nat.factorial c : ℝ) * ((1 / (4 * (c : ℝ) ^ 3)) * topT c (refHi c)) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) hfactnn)
        exact mul_le_mul_of_nonneg_right hpow (topT_nonneg c _)
    _ = (1 / (2 * (c : ℝ) ^ 3)) * (topT c (refHi c) / (Nat.factorial c : ℝ)) := by ring
    _ ≤ (1 / (2 * (c : ℝ) ^ 3)) * wrow c (refHi c) :=
        mul_le_mul_of_nonneg_left (topT_div_fact_le_wrow c (refHi c)) hf0
    _ ≤ (1 / (2 * (c : ℝ) ^ 3)) * m0sum c :=
        mul_le_mul_of_nonneg_left (wrow_le_m0sum c (refHi c) href) hf0

/-- **The tail-summation theorem (A53, step 1).**  The off-window census mass is
at most the small-region mass plus `m0sum/c³`, eventually. -/
theorem tailMassM_le : ∀ᶠ c : ℕ in atTop,
    tailMassM c ≤ smallMass c + (1 / (c : ℝ) ^ 3) * m0sum c := by
  filter_upwards [lowTailM_le, upTailM_le, wrow_winLo_le, wrow_winHi_le,
    eventually_ge_atTop 3, tendsto_log_atTop_nat.eventually_ge_atTop 2]
    with c hl hu hwl hwh hc hL2
  have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
  have hm0nn : (0 : ℝ) ≤ m0sum c := (m0sum_pos c).le
  have h2L : 2 / Real.log (c : ℝ) ≤ 1 := by
    rw [div_le_one hL]; linarith [hL2]
  calc tailMassM c = lowTailM c + upTailM c := rfl
    _ ≤ (smallMass c + 4 * wrow c (winLo c))
        + (2 / Real.log (c : ℝ)) * wrow c (winHi c) := add_le_add hl hu
    _ ≤ (smallMass c + 4 * ((1 / (8 * (c : ℝ) ^ 3)) * m0sum c))
        + (2 / Real.log (c : ℝ)) * ((1 / (2 * (c : ℝ) ^ 3)) * m0sum c) := by
        apply add_le_add
        · exact add_le_add_right (mul_le_mul_of_nonneg_left hwl (by norm_num : (0 : ℝ) ≤ 4)) _
        · exact mul_le_mul_of_nonneg_left hwh (div_nonneg (by norm_num) hL.le)
    _ = smallMass c
        + (1 / (2 * (c : ℝ) ^ 3) + (2 / Real.log (c : ℝ)) * (1 / (2 * (c : ℝ) ^ 3)))
          * m0sum c := by ring
    _ ≤ smallMass c + (1 / (c : ℝ) ^ 3) * m0sum c := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_right _ hm0nn
        calc 1 / (2 * (c : ℝ) ^ 3) + (2 / Real.log (c : ℝ)) * (1 / (2 * (c : ℝ) ^ 3))
            = (1 / (2 * (c : ℝ) ^ 3)) * (1 + 2 / Real.log (c : ℝ)) := by ring
          _ ≤ (1 / (2 * (c : ℝ) ^ 3)) * 2 :=
              mul_le_mul_of_nonneg_left (by linarith [h2L]) (by positivity)
          _ = 1 / (c : ℝ) ^ 3 := by ring

/-- The off-window mass is nonnegative. -/
theorem tailMassM_nonneg (c : ℕ) : (0 : ℝ) ≤ tailMassM c := by
  rw [tailMassM]
  exact add_nonneg (Finset.sum_nonneg fun n _ => wrow_nonneg c n)
    (Finset.sum_nonneg fun n _ => wrow_nonneg c n)

/-- `1/c³ → 0` along the naturals. -/
theorem tendsto_one_div_pow_zero (p : ℕ) (hp : p ≠ 0) :
    Tendsto (fun c : ℕ => 1 / (c : ℝ) ^ p) atTop (nhds 0) := by
  have h : Tendsto (fun c : ℕ => ((c : ℝ) ^ p)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  exact h.congr' (by filter_upwards with c; rw [one_div])

/-- **The tails are negligible (A53, step 1, limit form).** -/
theorem tendsto_tailMassM_div_m0sum_zero :
    Tendsto (fun c : ℕ => tailMassM c / m0sum c) atTop (nhds 0) := by
  have hsplit : ∀ᶠ c : ℕ in atTop,
      tailMassM c / m0sum c ≤ smallMass c / m0sum c + 1 / (c : ℝ) ^ 3 := by
    filter_upwards [tailMassM_le] with c h
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    calc tailMassM c / m0sum c ≤ (smallMass c + (1 / (c : ℝ) ^ 3) * m0sum c) / m0sum c :=
          div_le_div_of_nonneg_right h hm0.le
      _ = smallMass c / m0sum c + 1 / (c : ℝ) ^ 3 := by
          field_simp [hm0.ne']
  have hzero := tendsto_smallMass_div_m0sum_zero.add (tendsto_one_div_pow_zero 3 (by norm_num))
  rw [add_zero] at hzero
  exact squeeze_zero'
    (Eventually.of_forall fun c => div_nonneg (tailMassM_nonneg c) (m0sum_pos c).le)
    hsplit hzero

/-- Any fixed polynomial multiple of the small-mass ratio dies: the A48 bound is
exponential, `smallMass/m0sum ≤ K·(c+1)·√c·(1/2)^c`. -/
theorem tendsto_pow_mul_smallMass_div_m0sum_zero (p : ℕ) :
    Tendsto (fun c : ℕ => (c : ℝ) ^ p * (smallMass c / m0sum c)) atTop (nhds 0) := by
  have he4 : ∀ᶠ c : ℕ in atTop, Real.exp 1 / (4 * Real.log (c : ℝ)) ≤ 1 / 4 := by
    have hlog : Filter.Tendsto (fun c : ℕ => Real.log (c : ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have h1 : Filter.Tendsto (fun c : ℕ => (4 * Real.log (c : ℝ))⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
    have h2 := h1.const_mul (Real.exp 1)
    have h3 : Filter.Tendsto (fun c : ℕ => Real.exp 1 / (4 * Real.log (c : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_zero] using h2
    exact h3.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hmain : ∀ᶠ c : ℕ in atTop,
      (c : ℝ) ^ p * (smallMass c / m0sum c)
        ≤ 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) ^ (p + 2) * (1 / 2 : ℝ) ^ c) := by
    filter_upwards [eventually_ge_atTop 163000,
      four_sqrt_clogc_log_le_eventually (ε := Real.log 2)
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)),
      he4, eventually_ge_atTop 1] with c hc163 hd he4c hc1
    have h := smallMass_div_m0sum_le_half_pow hc163 hd he4c
    have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
    have hsqrt_le : Real.sqrt (c : ℝ) ≤ (c : ℝ) := by
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (c : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg c), one_pow]
        exact hcR
      calc Real.sqrt (c : ℝ) = Real.sqrt (c : ℝ) * 1 := by ring
        _ ≤ Real.sqrt (c : ℝ) * Real.sqrt (c : ℝ) :=
            mul_le_mul_of_nonneg_left hsqrt1 (Real.sqrt_nonneg _)
        _ = c := Real.mul_self_sqrt (Nat.cast_nonneg _)
    have hcp1 : ((c : ℝ) + 1) ≤ 2 * (c : ℝ) := by linarith
    have hK : (0 : ℝ) ≤ Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi) := by positivity
    have hp0 : (0 : ℝ) ≤ (c : ℝ) ^ p := pow_nonneg (Nat.cast_nonneg _) _
    calc (c : ℝ) ^ p * (smallMass c / m0sum c)
        ≤ (c : ℝ) ^ p * ((Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) + 1) * Real.sqrt (c : ℝ) * (1 / 2 : ℝ) ^ c) :=
          mul_le_mul_of_nonneg_left h hp0
      _ ≤ (c : ℝ) ^ p * ((Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * (2 * (c : ℝ)) * (c : ℝ) * (1 / 2 : ℝ) ^ c) := by
          apply mul_le_mul_of_nonneg_left _ hp0
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) c)
          apply mul_le_mul _ hsqrt_le (Real.sqrt_nonneg _) _
          · exact mul_le_mul_of_nonneg_left hcp1 hK
          · exact mul_nonneg hK (by linarith)
      _ = 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
            * ((c : ℝ) ^ (p + 2) * (1 / 2 : ℝ) ^ c) := by ring
  have hzero : Tendsto (fun c : ℕ => 2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
      * ((c : ℝ) ^ (p + 2) * (1 / 2 : ℝ) ^ c)) atTop (nhds 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one (p + 2)
      (show |(1 / 2 : ℝ)| < 1 by norm_num)
    have h2 := h.const_mul (2 * (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi)))
    simpa [mul_zero] using h2
  exact squeeze_zero'
    (Eventually.of_forall fun c => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (div_nonneg (smallMass_nonneg c) (m0sum_pos c).le))
    hmain hzero

/-- `c·(tailMass/m0sum) → 0` (needed for the `nvar_sharp` upper tail). -/
theorem tendsto_c_mul_tailMassM_div_m0sum_zero :
    Tendsto (fun c : ℕ => (c : ℝ) * (tailMassM c / m0sum c)) atTop (nhds 0) := by
  have hsplit : ∀ᶠ c : ℕ in atTop,
      (c : ℝ) * (tailMassM c / m0sum c)
        ≤ (c : ℝ) * (smallMass c / m0sum c) + 1 / (c : ℝ) ^ 2 := by
    filter_upwards [tailMassM_le, eventually_ge_atTop 1] with c h hc
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega)
    calc (c : ℝ) * (tailMassM c / m0sum c)
        ≤ (c : ℝ) * ((smallMass c + (1 / (c : ℝ) ^ 3) * m0sum c) / m0sum c) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hm0.le) (Nat.cast_nonneg _)
      _ = (c : ℝ) * (smallMass c / m0sum c) + 1 / (c : ℝ) ^ 2 := by
          field_simp [hm0.ne', hcR.ne']
  have hzero := (tendsto_pow_mul_smallMass_div_m0sum_zero 1).add
    (tendsto_one_div_pow_zero 2 (by norm_num))
  rw [add_zero] at hzero
  exact squeeze_zero'
    (Eventually.of_forall fun c => mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (tailMassM_nonneg c) (m0sum_pos c).le))
    hsplit (by simpa [pow_one] using hzero)

/-- `c²·log c·(tailMass/m0sum) → 0` (needed for the `resid_negligible` tail). -/
theorem tendsto_c_sq_log_mul_tailMassM_div_m0sum_zero :
    Tendsto (fun c : ℕ => (c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c))
      atTop (nhds 0) := by
  have hsplit : ∀ᶠ c : ℕ in atTop,
      (c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c)
        ≤ (c : ℝ) ^ 3 * (smallMass c / m0sum c) + Real.log (c : ℝ) / (c : ℝ) := by
    filter_upwards [tailMassM_le, eventually_ge_atTop 3] with c h hc
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega)
    have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega))
    have hlog_le : Real.log (c : ℝ) ≤ (c : ℝ) := by
      have hsub := Real.log_le_sub_one_of_pos hcR
      linarith [hsub]
    calc (c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c)
        ≤ (c : ℝ) ^ 2 * Real.log (c : ℝ)
            * ((smallMass c + (1 / (c : ℝ) ^ 3) * m0sum c) / m0sum c) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hm0.le)
            (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hL0)
      _ = (c : ℝ) ^ 2 * Real.log (c : ℝ) * (smallMass c / m0sum c)
            + Real.log (c : ℝ) / (c : ℝ) := by
          field_simp [hm0.ne', hcR.ne']
      _ ≤ (c : ℝ) ^ 3 * (smallMass c / m0sum c) + Real.log (c : ℝ) / (c : ℝ) := by
          apply add_le_add_left
          have hs0 : (0 : ℝ) ≤ smallMass c / m0sum c :=
            div_nonneg (smallMass_nonneg c) hm0.le
          calc (c : ℝ) ^ 2 * Real.log (c : ℝ) * (smallMass c / m0sum c)
              ≤ (c : ℝ) ^ 2 * (c : ℝ) * (smallMass c / m0sum c) := by
                apply mul_le_mul_of_nonneg_right _ hs0
                exact mul_le_mul_of_nonneg_left hlog_le (pow_nonneg (Nat.cast_nonneg _) _)
            _ = (c : ℝ) ^ 3 * (smallMass c / m0sum c) := by ring
  have hzero := (tendsto_pow_mul_smallMass_div_m0sum_zero 3).add tendsto_log_div_atTop_nat
  rw [add_zero] at hzero
  exact squeeze_zero'
    (by filter_upwards with c
        have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := by
          rcases Nat.eq_zero_or_pos c with rfl | hcpos
          · simp
          · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
        exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hL0)
          (div_nonneg (tailMassM_nonneg c) (m0sum_pos c).le))
    hsplit hzero

/-! ## Section D: the window first-order machinery

On the surviving window the per-cell variance weight is `(k/n)(1−1/n)`.  Three
slack scales control the `n`-part: the A52 window half-widths `δ`, `η`, and the
floor/ceil corrections `s1 = L/(2c(1−δ))`, `s2 = L/(2c(1+η)(1+δ))` (a `1/X`
correction with `X = (2c/log c)(1±…)`).  All die; this section packages them
and evaluates `c/winLo`, `c/winHi`, `1/winLo`, `1/winHi` to first order. -/

/-- Division algebra, three-factor form. -/
theorem c_div_scale_eq3 {c L A B : ℝ} (hc : c ≠ 0) (hL : L ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    c / (2 * c / L * A * B) = (L / 2) * (1 / (A * B)) := by
  field_simp [hc, hL, hA, hB]

/-- Division algebra, four-factor form. -/
theorem c_div_scale_eq4 {c L A B C : ℝ} (hc : c ≠ 0) (hL : L ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    c / (2 * c / L * A * B * C) = (L / 2) * (1 / (A * B * C)) := by
  field_simp [hc, hL, hA, hB, hC]

/-- Division algebra: `1/a = (b/a)/b` for nonzero `a, b`. -/
theorem one_div_eq_div_div {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a = (b / a) / b := by
  field_simp [ha, hb]

/-- `1/(1−x) ≤ 1 + 2x` for `0 ≤ x ≤ 1/2`. -/
theorem inv_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : 1 / (1 - x) ≤ 1 + 2 * x := by
  have h1 : (0 : ℝ) < 1 - x := by linarith
  rw [div_le_iff₀ h1]
  nlinarith [hx0, hx]

/-- `1 − x ≤ 1/(1+x)` for `x ≥ 0`. -/
theorem one_sub_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) : 1 - x ≤ 1 / (1 + x) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  rw [le_div_iff₀ h1]
  nlinarith [hx, sq_nonneg x]

/-- The floor correction scale at the lower window edge. -/
noncomputable def s1S (c : ℕ) : ℝ := Real.log (c : ℝ) / (2 * (c : ℝ) * (1 - deltaS c))

/-- The ceil correction scale at the upper window edge. -/
noncomputable def s2S (c : ℕ) : ℝ :=
  Real.log (c : ℝ) / (2 * (c : ℝ) * (1 + etaS c) * (1 + deltaS c))

/-- `1 − δ → 1`. -/
theorem tendsto_one_sub_deltaS_one : Tendsto (fun c : ℕ => 1 - deltaS c) atTop (nhds 1) := by
  have h : Tendsto (fun c : ℕ => (1 : ℝ) - deltaS c) atTop (nhds ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub tendsto_deltaS_zero
  rwa [sub_zero] at h

/-- `s1 → 0`: the floor correction dies like `log c / c`. -/
theorem tendsto_s1S_zero : Tendsto s1S atTop (nhds 0) := by
  have hden : Tendsto (fun c : ℕ => 2 * (1 - deltaS c)) atTop (nhds 2) := by
    have h : Tendsto (fun c : ℕ => (2 : ℝ) * (1 - deltaS c)) atTop (nhds ((2 : ℝ) * 1)) :=
      tendsto_const_nhds.mul tendsto_one_sub_deltaS_one
    rwa [mul_one] at h
  have h := tendsto_log_div_atTop_nat.div hden (by norm_num : (2 : ℝ) ≠ 0)
  rw [zero_div] at h
  have hfun : s1S = fun c : ℕ => (Real.log (c : ℝ) / (c : ℝ)) / (2 * (1 - deltaS c)) := by
    funext c
    rw [s1S, div_div]
    congr 1
    ring
  rw [hfun]
  exact h

/-- The expanded denominator factor at the upper window edge tends to `2`. -/
theorem tendsto_winHi_factor_one :
    Tendsto (fun c : ℕ => 2 * (1 + etaS c) * (1 + deltaS c)) atTop (nhds 2) := by
  have h1 : Tendsto (fun c : ℕ => 1 + etaS c) atTop (nhds 1) := by
    have h : Tendsto (fun c : ℕ => (1 : ℝ) + etaS c) atTop (nhds ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add tendsto_etaS_zero
    rwa [add_zero] at h
  have h2 : Tendsto (fun c : ℕ => 1 + deltaS c) atTop (nhds 1) := by
    have h : Tendsto (fun c : ℕ => (1 : ℝ) + deltaS c) atTop (nhds ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add tendsto_deltaS_zero
    rwa [add_zero] at h
  have h3 : Tendsto (fun c : ℕ => (2 : ℝ) * (1 + etaS c) * (1 + deltaS c)) atTop
      (nhds ((2 : ℝ) * 1 * 1)) := (tendsto_const_nhds.mul h1).mul h2
  have h4 : (2 : ℝ) * 1 * 1 = 2 := by norm_num
  rwa [h4] at h3

/-- `s2 → 0`. -/
theorem tendsto_s2S_zero : Tendsto s2S atTop (nhds 0) := by
  have h := tendsto_log_div_atTop_nat.div tendsto_winHi_factor_one (by norm_num : (2 : ℝ) ≠ 0)
  rw [zero_div] at h
  have hfun : s2S = fun c : ℕ =>
      (Real.log (c : ℝ) / (c : ℝ)) / (2 * (1 + etaS c) * (1 + deltaS c)) := by
    funext c
    rw [s2S, div_div]
    congr 1
    ring
  rw [hfun]
  exact h

/-- The lower window edge dominates the shrunken reference scale times
`1 − s1`: `winLo ≥ X·(1 − s1)` eventually, `X = (2c/log c)(1−δ)`. -/
theorem winLo_ge_factor_ev : ∀ᶠ c : ℕ in atTop,
    2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) * (1 - s1S c) ≤ (winLo c : ℝ) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop 3, hδ1] with c hc hδ1c
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hA : (0 : ℝ) < 2 * (c : ℝ) * (1 - deltaS c) :=
    mul_pos (by exact_mod_cast (by omega : 0 < 2 * c)) (by linarith)
  have hXs1 : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) * s1S c = 1 := by
    rw [s1S]
    rw [show 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c)
        = (2 * (c : ℝ) * (1 - deltaS c)) / Real.log (c : ℝ) by ring]
    rw [div_mul_div_comm, mul_comm (Real.log (c : ℝ)) (2 * (c : ℝ) * (1 - deltaS c)),
      div_self (mul_pos hA hL).ne']
  have hlt := lt_winLo c
  calc 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) * (1 - s1S c)
      = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c)
          - 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) * s1S c := by ring
    _ = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) - 1 := by rw [hXs1]
    _ ≤ winLo c := hlt.le

/-- The upper window edge is dominated by the expanded reference scale times
`1 + s2`: `winHi ≤ X'·(1 + s2)` with `X' = (2c/log c)(1+η)(1+δ)`. -/
theorem winHi_le_factor_ev : ∀ᶠ c : ℕ in atTop,
    (winHi c : ℝ)
      ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) * (1 + s2S c) := by
  filter_upwards [eventually_ge_atTop 3] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hA : (0 : ℝ) < 2 * (c : ℝ) * (1 + etaS c) * (1 + deltaS c) :=
    mul_pos (mul_pos (by exact_mod_cast (by omega : 0 < 2 * c)) (by linarith)) (by linarith)
  have hle := winHi_le c hc
  have hX's2 : 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) * s2S c = 1 := by
    rw [s2S]
    rw [show 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c)
        = (2 * (c : ℝ) * (1 + etaS c) * (1 + deltaS c)) / Real.log (c : ℝ) by ring]
    rw [div_mul_div_comm, mul_comm (Real.log (c : ℝ)) _, div_self (mul_pos hA hL).ne']
  calc (winHi c : ℝ)
      ≤ 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) + 1 := hle
    _ = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c)
          + 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) * s2S c := by
        rw [hX's2]
    _ = 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) * (1 + s2S c) := by
        ring

/-- The window-edge slack at the upper edge: `ε₂ = η + δ + s₂`. -/
noncomputable def epsW (c : ℕ) : ℝ := etaS c + deltaS c + s2S c

/-- The window-edge slack at the lower edge: `ε₁ = 4δ + 4s₁`. -/
noncomputable def epsWp (c : ℕ) : ℝ := 4 * deltaS c + 4 * s1S c

/-- The combined window-edge slack: `ε = ε₂ + ε₁`. -/
noncomputable def epsD (c : ℕ) : ℝ := epsW c + epsWp c

/-- `ε₂ → 0`. -/
theorem tendsto_epsW_zero : Tendsto epsW atTop (nhds 0) := by
  have h := (tendsto_etaS_zero.add tendsto_deltaS_zero).add tendsto_s2S_zero
  simpa only [add_zero] using h

/-- `ε₁ → 0`. -/
theorem tendsto_epsWp_zero : Tendsto epsWp atTop (nhds 0) := by
  have h : Tendsto (fun c : ℕ => (4 : ℝ) * deltaS c + 4 * s1S c) atTop
      (nhds ((4 : ℝ) * 0 + 4 * 0)) :=
    (tendsto_const_nhds.mul tendsto_deltaS_zero).add
      (tendsto_const_nhds.mul tendsto_s1S_zero)
  simpa only [mul_zero, add_zero] using h

/-- The inverse lower window-edge ratio evaluated: `c/winLo ≤ (log c/2)(1 + ε₁)`
eventually. -/
theorem c_div_winLo_le_ev : ∀ᶠ c : ℕ in atTop,
    (c : ℝ) / (winLo c : ℝ) ≤ (Real.log (c : ℝ) / 2) * (1 + epsWp c) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hs11 : ∀ᶠ c : ℕ in atTop, s1S c ≤ 1 / 2 :=
    tendsto_s1S_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [winLo_ge_factor_ev, eventually_ge_atTop 3, hδ1, hs11, one_le_winLo_ev]
    with c hfac hc hδ1c hs11c h1
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hs1 : (0 : ℝ) ≤ s1S c := by
    rw [s1S]
    exact div_nonneg hL.le (mul_nonneg (by positivity) (by linarith))
  have hX0 : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) :=
    mul_pos (div_pos (by exact_mod_cast (by omega : 0 < 2 * c)) hL) (by linarith)
  have h1s1 : (0 : ℝ) < 1 - s1S c := by linarith
  have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
  have hL2 : (0 : ℝ) ≤ Real.log (c : ℝ) / 2 := div_nonneg hL.le (by norm_num)
  have hδi : 1 / (1 - deltaS c) ≤ 1 + 2 * deltaS c := inv_one_sub_le hδ hδ1c
  have hs1i : 1 / (1 - s1S c) ≤ 1 + 2 * s1S c := inv_one_sub_le hs1 hs11c
  calc (c : ℝ) / (winLo c : ℝ)
      ≤ (c : ℝ) / (2 * (c : ℝ) / Real.log (c : ℝ) * (1 - deltaS c) * (1 - s1S c)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hX0 h1s1) hfac
    _ = (Real.log (c : ℝ) / 2) * (1 / ((1 - deltaS c) * (1 - s1S c))) := by
        exact c_div_scale_eq3 (by exact_mod_cast (by omega : c ≠ 0)) hL.ne'
          (by linarith : (0 : ℝ) < 1 - deltaS c).ne' h1s1.ne'
    _ ≤ (Real.log (c : ℝ) / 2) * ((1 + 2 * deltaS c) * (1 + 2 * s1S c)) := by
        apply mul_le_mul_of_nonneg_left _ hL2
        calc 1 / ((1 - deltaS c) * (1 - s1S c))
            = (1 / (1 - deltaS c)) * (1 / (1 - s1S c)) := by
              rw [one_div, one_div, one_div, ← mul_inv]
          _ ≤ (1 + 2 * deltaS c) * (1 + 2 * s1S c) :=
              mul_le_mul hδi hs1i (div_nonneg zero_le_one h1s1.le) (by linarith)
    _ ≤ (Real.log (c : ℝ) / 2) * (1 + epsWp c) := by
        apply mul_le_mul_of_nonneg_left _ hL2
        have hprods : (0 : ℝ) ≤ deltaS c * (1 - 2 * s1S c) :=
          mul_nonneg hδ (by linarith)
        rw [epsWp]
        nlinarith [hδ, hs1, hprods]

/-- The inverse upper window-edge ratio evaluated: `(log c/2)(1 − ε₂) ≤ c/winHi`
eventually. -/
theorem c_div_winHi_ge_ev : ∀ᶠ c : ℕ in atTop,
    (Real.log (c : ℝ) / 2) * (1 - epsW c) ≤ (c : ℝ) / (winHi c : ℝ) := by
  have hη1 : ∀ᶠ c : ℕ in atTop, etaS c ≤ 1 :=
    tendsto_etaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hs21 : ∀ᶠ c : ℕ in atTop, s2S c ≤ 1 :=
    tendsto_s2S_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [winHi_le_factor_ev, eventually_ge_atTop 3, hη1, hδ1, hs21]
    with c hfac hc hη1c hδ1c hs21c
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hs2 : (0 : ℝ) ≤ s2S c := by
    rw [s2S]
    exact div_nonneg hL.le (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
  have hX'0 : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) :=
    mul_pos (mul_pos (div_pos (by exact_mod_cast (by omega : 0 < 2 * c)) hL) (by linarith))
      (by linarith)
  have hW' : (0 : ℝ) < (winHi c : ℝ) := lt_of_lt_of_le hX'0 (ge_winHi c)
  have hL2 : (0 : ℝ) ≤ Real.log (c : ℝ) / 2 := div_nonneg hL.le (by norm_num)
  have h1η : 1 - etaS c ≤ 1 / (1 + etaS c) := one_sub_le_inv_one_add hη
  have h1δ : 1 - deltaS c ≤ 1 / (1 + deltaS c) := one_sub_le_inv_one_add hδ
  have h1s2 : 1 - s2S c ≤ 1 / (1 + s2S c) := one_sub_le_inv_one_add hs2
  have hηi : (0 : ℝ) ≤ 1 - etaS c := by linarith
  have hδi : (0 : ℝ) ≤ 1 - deltaS c := by linarith
  have hs2i : (0 : ℝ) ≤ 1 - s2S c := by linarith
  calc (Real.log (c : ℝ) / 2) * (1 - epsW c)
      ≤ (Real.log (c : ℝ) / 2) * (1 / ((1 + etaS c) * (1 + deltaS c) * (1 + s2S c))) := by
        apply mul_le_mul_of_nonneg_left _ hL2
        calc 1 - epsW c
            ≤ (1 - etaS c) * (1 - deltaS c) * (1 - s2S c) := by
              rw [epsW]
              nlinarith [hη, hδ, hs2, hηi, hδi, hs2i, mul_nonneg hη hδ,
                mul_nonneg hη hs2, mul_nonneg hδ hs2,
                mul_nonneg (mul_nonneg hη hδ) hs2]
          _ ≤ (1 / (1 + etaS c)) * (1 / (1 + deltaS c)) * (1 / (1 + s2S c)) := by
              apply mul_le_mul _ h1s2 hs2i
                (mul_nonneg (div_nonneg zero_le_one (by linarith))
                  (div_nonneg zero_le_one (by linarith)))
              exact mul_le_mul h1η h1δ hδi (div_nonneg zero_le_one (by linarith))
          _ = 1 / ((1 + etaS c) * (1 + deltaS c) * (1 + s2S c)) := by
              rw [one_div, one_div, one_div, one_div, ← mul_inv, ← mul_inv]
    _ = (c : ℝ) / (2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c)
          * (1 + s2S c)) := by
        have hη1' : (0 : ℝ) < 1 + etaS c := by linarith
        have hδ1' : (0 : ℝ) < 1 + deltaS c := by linarith
        have hs21' : (0 : ℝ) < 1 + s2S c := by linarith
        exact (c_div_scale_eq4 (by exact_mod_cast (by omega : c ≠ 0)) hL.ne'
          hη1'.ne' hδ1'.ne' hs21'.ne').symm
    _ ≤ (c : ℝ) / (winHi c : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hW' hfac

/-- The `1/n` evaluation at the lower window edge. -/
theorem one_div_winLo_le_ev : ∀ᶠ c : ℕ in atTop,
    1 / (winLo c : ℝ) ≤ (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 + epsWp c) := by
  filter_upwards [c_div_winLo_le_ev, eventually_ge_atTop 1, one_le_winLo_ev] with c h hc h1
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
  calc 1 / (winLo c : ℝ) = ((c : ℝ) / (winLo c : ℝ)) / (c : ℝ) :=
        one_div_eq_div_div hW.ne' hcR.ne'
    _ ≤ (Real.log (c : ℝ) / 2 * (1 + epsWp c)) / (c : ℝ) :=
        div_le_div_of_nonneg_right h hcR.le
    _ = (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 + epsWp c) := by
        field_simp [hcR.ne']

/-- The `1/n` evaluation at the upper window edge. -/
theorem one_div_winHi_ge_ev : ∀ᶠ c : ℕ in atTop,
    (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 - epsW c) ≤ 1 / (winHi c : ℝ) := by
  filter_upwards [c_div_winHi_ge_ev, eventually_ge_atTop 3] with c h hc
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hX'0 : (0 : ℝ) < 2 * (c : ℝ) / Real.log (c : ℝ) * (1 + etaS c) * (1 + deltaS c) :=
    mul_pos (mul_pos (div_pos (by exact_mod_cast (by omega : 0 < 2 * c)) hL) (by linarith))
      (by linarith)
  have hW' : (0 : ℝ) < (winHi c : ℝ) := lt_of_lt_of_le hX'0 (ge_winHi c)
  calc (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 - epsW c)
      = (Real.log (c : ℝ) / 2 * (1 - epsW c)) / (c : ℝ) := by
        field_simp [hcR.ne']
    _ ≤ ((c : ℝ) / (winHi c : ℝ)) / (c : ℝ) := div_le_div_of_nonneg_right h hcR.le
    _ = 1 / (winHi c : ℝ) := (one_div_eq_div_div hW'.ne' hcR.ne').symm

/-- `1/winLo → 0`. -/
theorem tendsto_one_div_winLo_zero :
    Tendsto (fun c : ℕ => 1 / (winLo c : ℝ)) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp winLo_tendsto_atTop)
  exact h.congr' (by filter_upwards with c; simp only [Function.comp_apply, one_div])

/-- `(log log c)² / log c → 0` (via the square root substitution). -/
theorem tendsto_loglog_sq_div_log_zero :
    Tendsto (fun c : ℕ => (Real.log (Real.log (c : ℝ))) ^ 2 / Real.log (c : ℝ))
      atTop (nhds 0) := by
  have hcomp : Tendsto (fun c : ℕ => Real.sqrt (Real.log (c : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_log_atTop_nat
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hcomp
  have h2 := h.mul h
  rw [mul_zero] at h2
  have h3 := h2.const_mul (4 : ℝ)
  rw [mul_zero] at h3
  apply h3.congr'
  filter_upwards [eventually_ge_atTop 3] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hs : Real.log (Real.sqrt (Real.log (c : ℝ))) = Real.log (Real.log (c : ℝ)) / 2 :=
    Real.log_sqrt hL.le
  show 4 * ((Real.log (Real.sqrt (Real.log (c : ℝ))) / Real.sqrt (Real.log (c : ℝ)))
      * (Real.log (Real.sqrt (Real.log (c : ℝ))) / Real.sqrt (Real.log (c : ℝ))))
      = Real.log (Real.log (c : ℝ)) ^ 2 / Real.log (c : ℝ)
  rw [← sq, hs, div_pow, Real.sq_sqrt hL.le]
  field_simp [hL.ne']
  ring

/-- `log c · η² → 0`: `L·(3LL/L)² = 9(LL)²/L`. -/
theorem tendsto_L_mul_etaS_sq_zero :
    Tendsto (fun c : ℕ => Real.log (c : ℝ) * (etaS c) ^ 2) atTop (nhds 0) := by
  have h := tendsto_loglog_sq_div_log_zero.const_mul (9 : ℝ)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hLL : (0 : ℝ) < Real.log (Real.log (c : ℝ)) :=
    Real.log_pos (one_lt_log_three.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hc)))
  rw [etaS]
  field_simp [hL.ne', hLL.ne']
  ring

/-- `log c · δ² → 0`: `L·δ² = 1/log log c`. -/
theorem tendsto_L_mul_deltaS_sq_zero :
    Tendsto (fun c : ℕ => Real.log (c : ℝ) * (deltaS c) ^ 2) atTop (nhds 0) := by
  have h := tendsto_inv_atTop_zero.comp tendsto_log_log_atTop_nat
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with c hc
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hLL : (0 : ℝ) < Real.log (Real.log (c : ℝ)) :=
    Real.log_pos (one_lt_log_three.trans_le
      (Real.log_le_log (by norm_num) (by exact_mod_cast hc)))
  show (Real.log (Real.log (c : ℝ)))⁻¹ = Real.log (c : ℝ) * (deltaS c) ^ 2
  rw [deltaS, div_pow, one_pow, Real.sq_sqrt (mul_nonneg hL.le hLL.le), mul_one_div,
    eq_comm, div_eq_iff (mul_pos hL hLL).ne',
    mul_comm (Real.log (c : ℝ)) (Real.log (Real.log (c : ℝ))), ← mul_assoc,
    inv_mul_cancel₀ hLL.ne', one_mul]

/-- `L³/c² → 0` (via `log³ ≤ c` eventually). -/
theorem tendsto_log_cubed_div_sq_zero :
    Tendsto (fun c : ℕ => (Real.log (c : ℝ)) ^ 3 / (c : ℝ) ^ 2) atTop (nhds 0) := by
  have hbound : ∀ᶠ c : ℕ in atTop, (Real.log (c : ℝ)) ^ 3 / (c : ℝ) ^ 2 ≤ 1 / (c : ℝ) := by
    filter_upwards [log_cubed_le_ev, eventually_ge_atTop 1] with c h hc
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have h3 : 1 / (c : ℝ) * (c : ℝ) ^ 2 = (c : ℝ) := by
      rw [sq]
      field_simp [hcR.ne']
    rw [div_le_iff₀ (pow_pos hcR 2), h3]
    exact h
  have hzero : Tendsto (fun c : ℕ => 1 / (c : ℝ)) atTop (nhds 0) := by
    have h := tendsto_one_div_pow_zero 1 (by norm_num)
    exact h.congr' (by filter_upwards with c; simp only [pow_one])
  exact squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 1] with c hc
        exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))) _)
          (pow_nonneg (Nat.cast_nonneg _) _))
    hbound hzero

/-- `log c · s1² → 0`: `L·s1² = (L³/c²)/(4(1−δ)²)`. -/
theorem tendsto_L_mul_s1S_sq_zero :
    Tendsto (fun c : ℕ => Real.log (c : ℝ) * (s1S c) ^ 2) atTop (nhds 0) := by
  have hden : Tendsto (fun c : ℕ => 4 * (1 - deltaS c) ^ 2) atTop (nhds 4) := by
    have h : Tendsto (fun c : ℕ => (4 : ℝ) * (1 - deltaS c) ^ 2) atTop
        (nhds ((4 : ℝ) * 1 ^ 2)) :=
      tendsto_const_nhds.mul (tendsto_one_sub_deltaS_one.pow 2)
    have h1 : (4 : ℝ) * 1 ^ 2 = 4 := by norm_num
    rwa [h1] at h
  have h := tendsto_log_cubed_div_sq_zero.div hden (by norm_num : (4 : ℝ) ≠ 0)
  rw [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3,
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with c hc hδ1c
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have h1δ : (0 : ℝ) < 1 - deltaS c := by linarith
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  show (Real.log (c : ℝ)) ^ 3 / (c : ℝ) ^ 2 / (4 * (1 - deltaS c) ^ 2)
      = Real.log (c : ℝ) * (s1S c) ^ 2
  rw [s1S]
  field_simp [hL.ne', h1δ.ne', hcR.ne']
  ring

/-- `log c · s2² → 0`: `s2 ≤ L/(2c)` since `(1+η)(1+δ) ≥ 1`. -/
theorem tendsto_L_mul_s2S_sq_zero :
    Tendsto (fun c : ℕ => Real.log (c : ℝ) * (s2S c) ^ 2) atTop (nhds 0) := by
  have hbound : ∀ᶠ c : ℕ in atTop,
      Real.log (c : ℝ) * (s2S c) ^ 2 ≤ (Real.log (c : ℝ)) ^ 3 / (4 * (c : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop 3] with c hc
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
    have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
    have h1 : (1 : ℝ) ≤ (1 + etaS c) * (1 + deltaS c) := by nlinarith [hη, hδ, mul_nonneg hη hδ]
    have h2c : (0 : ℝ) < 2 * (c : ℝ) := by exact_mod_cast (by omega : 0 < 2 * c)
    have hs2le : s2S c ≤ Real.log (c : ℝ) / (2 * (c : ℝ)) := by
      rw [s2S]
      apply div_le_div_of_nonneg_left hL.le h2c
      calc (2 : ℝ) * (c : ℝ) = 2 * (c : ℝ) * 1 := (mul_one _).symm
        _ ≤ 2 * (c : ℝ) * ((1 + etaS c) * (1 + deltaS c)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (c : ℝ) * (1 + etaS c) * (1 + deltaS c) := by ring
    have hs2nn : (0 : ℝ) ≤ s2S c := by
      rw [s2S]
      exact div_nonneg hL.le (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
    calc Real.log (c : ℝ) * (s2S c) ^ 2
        ≤ Real.log (c : ℝ) * (Real.log (c : ℝ) / (2 * (c : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs2nn hs2le 2) hL.le
      _ = (Real.log (c : ℝ)) ^ 3 / (4 * (c : ℝ) ^ 2) := by
          rw [div_pow, mul_pow]
          ring
  have hzero : Tendsto (fun c : ℕ => (Real.log (c : ℝ)) ^ 3 / (4 * (c : ℝ) ^ 2)) atTop (nhds 0) := by
    have h := tendsto_log_cubed_div_sq_zero.const_mul (1 / 4 : ℝ)
    rw [mul_zero] at h
    exact h.congr' (by
      filter_upwards with c
      rw [mul_comm, div_mul_div_comm, mul_one, mul_comm ((c : ℝ) ^ 2) 4])
  exact squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 3] with c hc
        have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
        have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
        have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
        have hs2nn : (0 : ℝ) ≤ s2S c := by
          rw [s2S]
          exact div_nonneg hL.le (mul_nonneg (mul_nonneg (by positivity) (by linarith))
            (by linarith))
        exact mul_nonneg hL.le (pow_nonneg hs2nn _))
    hbound hzero

/-- The resid window scale: `(log c/2)·ε² → 0`. -/
theorem tendsto_L_half_mul_epsD_sq_zero :
    Tendsto (fun c : ℕ => (Real.log (c : ℝ) / 2) * (epsD c) ^ 2) atTop (nhds 0) := by
  have hbound : ∀ᶠ c : ℕ in atTop,
      (Real.log (c : ℝ) / 2) * (epsD c) ^ 2
        ≤ 2 * Real.log (c : ℝ) * ((etaS c) ^ 2 + 25 * (deltaS c) ^ 2 + (s2S c) ^ 2
            + 16 * (s1S c) ^ 2) := by
    filter_upwards [eventually_ge_atTop 1] with c hc
    have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
    have heps : epsD c = etaS c + 5 * deltaS c + s2S c + 4 * s1S c := by
      rw [epsD, epsW, epsWp]
      ring
    have hcs : (etaS c + 5 * deltaS c + s2S c + 4 * s1S c) ^ 2
        ≤ 4 * ((etaS c) ^ 2 + (5 * deltaS c) ^ 2 + (s2S c) ^ 2 + (4 * s1S c) ^ 2) := by
      nlinarith [sq_nonneg (etaS c - 5 * deltaS c), sq_nonneg (etaS c - s2S c),
        sq_nonneg (etaS c - 4 * s1S c), sq_nonneg (5 * deltaS c - s2S c),
        sq_nonneg (5 * deltaS c - 4 * s1S c), sq_nonneg (s2S c - 4 * s1S c)]
    have hL2 : (0 : ℝ) ≤ Real.log (c : ℝ) / 2 := div_nonneg hL0 (by norm_num)
    calc (Real.log (c : ℝ) / 2) * (epsD c) ^ 2
        = (Real.log (c : ℝ) / 2) * (etaS c + 5 * deltaS c + s2S c + 4 * s1S c) ^ 2 := by
          rw [heps]
      _ ≤ (Real.log (c : ℝ) / 2) * (4 * ((etaS c) ^ 2 + (5 * deltaS c) ^ 2 + (s2S c) ^ 2
            + (4 * s1S c) ^ 2)) := mul_le_mul_of_nonneg_left hcs hL2
      _ = 2 * Real.log (c : ℝ) * ((etaS c) ^ 2 + 25 * (deltaS c) ^ 2 + (s2S c) ^ 2
            + 16 * (s1S c) ^ 2) := by ring
  have hzero : Tendsto (fun c : ℕ => 2 * Real.log (c : ℝ) * ((etaS c) ^ 2
      + 25 * (deltaS c) ^ 2 + (s2S c) ^ 2 + 16 * (s1S c) ^ 2)) atTop (nhds 0) := by
    have h2 := tendsto_L_mul_deltaS_sq_zero.const_mul (25 : ℝ)
    rw [mul_zero] at h2
    have h4 := tendsto_L_mul_s1S_sq_zero.const_mul (16 : ℝ)
    rw [mul_zero] at h4
    have hsum := ((tendsto_L_mul_etaS_sq_zero.add h2).add tendsto_L_mul_s2S_sq_zero).add h4
    have hfin := hsum.const_mul (2 : ℝ)
    have h0 : (2 : ℝ) * (0 + 0 + 0 + 0) = 0 := by norm_num
    rw [h0] at hfin
    exact hfin.congr' (by filter_upwards with c; ring)
  exact squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 1] with c hc
        have hL0 : (0 : ℝ) ≤ Real.log (c : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c))
        exact mul_nonneg (div_nonneg hL0 (by norm_num)) (sq_nonneg _))
    hbound hzero

/-! ## Section E: the first-order evaluation of `nvarSum` on the window -/

/-- The row first moment in `k`: `Σ_k k·cellW c n k`. -/
noncomputable def rowF (c n : ℕ) : ℝ := ∑ k ∈ Finset.range (c + 1), (k : ℝ) * cellW c n k

theorem rowF_nonneg (c n : ℕ) : (0 : ℝ) ≤ rowF c n :=
  Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (cellW_nonneg c n k)

/-- The row first moment never exceeds `c` times the row. -/
theorem rowF_le (c n : ℕ) : rowF c n ≤ (c : ℝ) * wrow c n := by
  rw [wrow_eq_sum_cellW, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_range] at hk
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.lt_succ_iff.1 hk : (k : ℝ) ≤ c) (cellW_nonneg c n k)

/-- The row first moment is at least `(c−2)` times the row above the
row-domination threshold `2c ≤ n²`: the A51 k-deficit bound
`Σ (c−k)·cellW ≤ 2·wrow` makes `k` concentrate at the cap. -/
theorem rowF_ge (c n : ℕ) (hn : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2) :
    ((c : ℝ) - 2) * wrow c n ≤ rowF c n := by
  have h := sum_sub_cellW_le_two_wrow c n hn
  have hsplit : (c : ℝ) * wrow c n
      = rowF c n + ∑ k ∈ Finset.range (c + 1), ((c - k : ℕ) : ℝ) * cellW c n k := by
    simp only [rowF]
    rw [wrow_eq_sum_cellW, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hkc : k ≤ c := Nat.lt_succ_iff.1 hk
    rw [Nat.cast_sub hkc]
    ring
  have hwr : (0 : ℝ) ≤ wrow c n := wrow_nonneg c n
  calc ((c : ℝ) - 2) * wrow c n = (c : ℝ) * wrow c n - 2 * wrow c n := by ring
    _ ≤ rowF c n := by linarith [h, hsplit]

/-- `nvarSum` is the `(1/n)(1−1/n)`-weighted sum of the row first moments. -/
theorem nvarSum_eq_sum_rowF (c : ℕ) :
    nvarSum c = ∑ n ∈ Finset.range (c + 1),
      (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * rowF c n := by
  rw [← varSum_eq_nvarSum c]
  simp only [varSum, rowF, cellW]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The upper first-order bound: `nvarSum ≤ c·(m0sum/winLo + tailMass)`. -/
theorem nvarSum_le_ev : ∀ᶠ c : ℕ in atTop,
    nvarSum c ≤ (c : ℝ) * (m0sum c / (winLo c : ℝ) + tailMassM c) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [winHi_le_c_ev, eventually_ge_atTop 3, one_le_winLo_ev, hδ1]
    with c hwhi hc h1 hδ1c
  rw [nvarSum_eq_sum_rowF]
  have hwin : winLo c ≤ winHi c + 1 := Nat.le_succ_of_le (winLo_le_winHi c hc hδ1c)
  have hwhi2 : winHi c + 1 ≤ c + 1 := Nat.succ_le_succ hwhi
  have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
  have hterm : ∀ n : ℕ, (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * rowF c n
      ≤ (1 / (n : ℝ)) * ((c : ℝ) * wrow c n) := by
    intro n
    have hnn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have h11 : 1 - 1 / (n : ℝ) ≤ 1 := by
      have hnn' : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith
    calc (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * rowF c n
        = rowF c n * ((1 / (n : ℝ)) * (1 - 1 / (n : ℝ))) := by ring
      _ ≤ rowF c n * ((1 / (n : ℝ)) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h11 hnn) (rowF_nonneg c n)
      _ = (1 / (n : ℝ)) * rowF c n := by ring
      _ ≤ (1 / (n : ℝ)) * ((c : ℝ) * wrow c n) :=
          mul_le_mul_of_nonneg_left (rowF_le c n) hnn
  have h12 : winLo c ≤ c + 1 := hwin.trans hwhi2
  have hregions : ∀ f : ℕ → ℝ,
      ∑ n ∈ Finset.range (c + 1), f n
        = (∑ n ∈ Finset.range (winLo c), f n)
          + (∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), f n)
          + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), f n) := by
    intro f
    rw [← Finset.sum_range_add_sum_Ico f h12,
      ← Finset.sum_Ico_consecutive f hwin hwhi2, add_assoc]
  have hwin_bd : ∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), (1 / (n : ℝ)) * wrow c n
      ≤ (1 / (winLo c : ℝ)) * winMassM c := by
    rw [winMassM, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ico] at hn
    apply mul_le_mul_of_nonneg_right _ (wrow_nonneg c n)
    exact one_div_le_one_div_of_le hW (by exact_mod_cast hn.1)
  have htail_lo : ∑ n ∈ Finset.range (winLo c), (1 / (n : ℝ)) * wrow c n ≤ lowTailM c := by
    rw [lowTailM]
    apply Finset.sum_le_sum
    intro n _
    apply mul_le_of_le_one_left (wrow_nonneg c n)
    by_cases hn : n = 0
    · rw [hn, Nat.cast_zero, div_zero]
      exact zero_le_one
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
      rw [div_le_one (by linarith)]
      exact hn1
  have htail_up : ∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), (1 / (n : ℝ)) * wrow c n
      ≤ upTailM c := by
    rw [upTailM]
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_of_le_one_left (wrow_nonneg c n)
    rw [Finset.mem_Ico] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    rw [div_le_one (by linarith)]
    exact hn1
  have hsplit := m0sum_eq_lowTailM_add_winMassM_add_upTailM c hwin hwhi2
  have hlow : (0 : ℝ) ≤ lowTailM c :=
    Finset.sum_nonneg fun n _ => wrow_nonneg c n
  have hup : (0 : ℝ) ≤ upTailM c :=
    Finset.sum_nonneg fun n _ => wrow_nonneg c n
  have hwm : winMassM c ≤ m0sum c := by linarith [hsplit, hlow, hup]
  calc ∑ n ∈ Finset.range (c + 1), (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * rowF c n
      ≤ ∑ n ∈ Finset.range (c + 1), (1 / (n : ℝ)) * ((c : ℝ) * wrow c n) :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = (c : ℝ) * ∑ n ∈ Finset.range (c + 1), (1 / (n : ℝ)) * wrow c n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = (c : ℝ) * ((∑ n ∈ Finset.range (winLo c), (1 / (n : ℝ)) * wrow c n)
          + (∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), (1 / (n : ℝ)) * wrow c n)
          + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), (1 / (n : ℝ)) * wrow c n)) := by
        rw [hregions (fun n => (1 / (n : ℝ)) * wrow c n)]
    _ ≤ (c : ℝ) * ((1 / (winLo c : ℝ)) * m0sum c + tailMassM c) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have hw2 : (1 / (winLo c : ℝ)) * winMassM c ≤ (1 / (winLo c : ℝ)) * m0sum c :=
          mul_le_mul_of_nonneg_left hwm (by positivity)
        rw [tailMassM]
        linarith [htail_lo, htail_up, hwin_bd, hw2]
    _ = (c : ℝ) * (m0sum c / (winLo c : ℝ) + tailMassM c) := by ring

/-- The lower first-order bound: `(c−2)(1−1/winLo)(1/winHi)·winMass ≤ nvarSum`. -/
theorem nvarSum_ge_ev : ∀ᶠ c : ℕ in atTop,
    ((c : ℝ) - 2) * (1 - 1 / (winLo c : ℝ)) * (1 / (winHi c : ℝ)) * winMassM c
      ≤ nvarSum c := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [winHi_le_c_ev, eventually_ge_atTop 3, one_le_winLo_ev, hδ1,
    winLo_sq_ge_two_c_ev] with c hwhi hc h1 hδ1c hsq2
  rw [nvarSum_eq_sum_rowF]
  have hwin : winLo c ≤ winHi c + 1 := Nat.le_succ_of_le (winLo_le_winHi c hc hδ1c)
  have hwhi2 : winHi c + 1 ≤ c + 1 := Nat.succ_le_succ hwhi
  have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
  have hWH : (0 : ℝ) < (winHi c : ℝ) :=
    lt_of_lt_of_le hW (by exact_mod_cast winLo_le_winHi c hc hδ1c)
  have hsubset : Finset.Ico (winLo c) (winHi c + 1) ⊆ Finset.range (c + 1) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_range]
    omega
  have hnn : ∀ n ∈ Finset.range (c + 1), n ∉ Finset.Ico (winLo c) (winHi c + 1) →
      (0 : ℝ) ≤ (1 / (n : ℝ)) * (1 - 1 / (n : ℝ)) * rowF c n := by
    intro n _ _
    have hn1 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    have hn2 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · simp
      · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        have hle : (1 : ℝ) / n ≤ 1 := by
          rw [div_le_one (by linarith)]
          exact hn1'
        linarith
    exact mul_nonneg (mul_nonneg hn1 hn2) (rowF_nonneg c n)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsubset hnn)
  rw [winMassM, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hn2 : 2 * (c : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hge : (winLo c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    calc 2 * (c : ℝ) ≤ (winLo c : ℝ) ^ 2 := hsq2
      _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hge 2
  have hrow := rowF_ge c n hn2
  have hw1 : (1 : ℝ) / (winHi c : ℝ) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < n))
      (by exact_mod_cast (by omega : n ≤ winHi c))
  have hw2 : 1 - 1 / (winLo c : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have h : (1 : ℝ) / (n : ℝ) ≤ 1 / (winLo c : ℝ) :=
      one_div_le_one_div_of_le hW (by exact_mod_cast hn.1)
    linarith
  have hw2nn : (0 : ℝ) ≤ 1 - 1 / (winLo c : ℝ) := by
    have h : (1 : ℝ) / winLo c ≤ 1 := by
      rw [div_le_one hW]
      exact_mod_cast h1
    linarith
  have hc2 : (0 : ℝ) ≤ (c : ℝ) - 2 := by
    have h2 : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 2 ≤ c)
    linarith
  calc ((c : ℝ) - 2) * (1 - 1 / (winLo c : ℝ)) * (1 / (winHi c : ℝ)) * wrow c n
      = ((1 / (winHi c : ℝ)) * (1 - 1 / (winLo c : ℝ))) * (((c : ℝ) - 2) * wrow c n) := by
        ring
    _ ≤ ((1 / (n : ℝ)) * (1 - 1 / (n : ℝ))) * rowF c n := by
        have h1nR : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        have h2nR : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
          have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have hle : (1 : ℝ) / n ≤ 1 := by
            rw [div_le_one (by linarith)]
            exact h1n
          linarith
        exact mul_le_mul (mul_le_mul hw1 hw2 hw2nn h1nR) hrow
          (mul_nonneg hc2 (wrow_nonneg c n)) (mul_nonneg h1nR h2nR)

/-! ## Section F: `nvar_sharp` -/

/-- The inverse A51 ratio: `c²·m0sum/dsum → 1`. -/
theorem tendsto_c_sq_mul_m0sum_div_dsum_one :
    Tendsto (fun c : ℕ => (c : ℝ) ^ 2 * m0sum c / dsum c) atTop (nhds 1) := by
  have h := Gap2CensusDsumSaddle.dsum_saddle.inv₀ one_ne_zero
  rw [inv_one] at h
  exact h.congr' (by filter_upwards with c; rw [inv_div])

/-- **The conditional-variance numerator at the sharp rate (TARGET: `nvar_sharp`).**
`nvarSum·(2c²)/(log c·dsum) → 1`: the squeeze of the Section E bounds, with
the window edges evaluated by Section D and the tails killed by Section C. -/
theorem nvar_sharp :
    Tendsto (fun c : ℕ => nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c))
      atTop (nhds 1) := by
  have hδ1 : ∀ᶠ c : ℕ in atTop, deltaS c ≤ 1 / 2 :=
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlo : ∀ᶠ c : ℕ in atTop,
      (1 - epsW c) * (1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ))
          * (1 - tailMassM c / m0sum c)
        ≤ nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c := by
    filter_upwards [nvarSum_ge_ev, c_div_winHi_ge_ev, one_le_winLo_ev,
      eventually_ge_atTop 3, hδ1, winHi_le_c_ev,
      tendsto_tailMassM_div_m0sum_zero.eventually
        (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with c hge hwhi h1 hc hδ1c hwhic htail1
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have hwin : winLo c ≤ winHi c + 1 :=
      Nat.le_succ_of_le (winLo_le_winHi c hc (by linarith))
    have hwhi2 : winHi c + 1 ≤ c + 1 := Nat.succ_le_succ hwhic
    have hsplit := m0sum_eq_lowTailM_add_winMassM_add_upTailM c hwin hwhi2
    have hwm : winMassM c = m0sum c - tailMassM c := by
      have htm : tailMassM c = lowTailM c + upTailM c := rfl
      linarith [hsplit, htm]
    have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
    have h2L : (0 : ℝ) ≤ 2 / Real.log (c : ℝ) := by positivity
    have hstep1 : ((c : ℝ) - 2) * (1 - 1 / (winLo c : ℝ)) * (1 / (winHi c : ℝ))
          * (m0sum c - tailMassM c) * (2 / Real.log (c : ℝ)) / m0sum c
        ≤ nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c := by
      apply div_le_div_of_nonneg_right _ hm0.le
      apply mul_le_mul_of_nonneg_right _ h2L
      rw [← hwm]
      exact hge
    have hshape : ((c : ℝ) - 2) * (1 - 1 / (winLo c : ℝ)) * (1 / (winHi c : ℝ))
          * (m0sum c - tailMassM c) * (2 / Real.log (c : ℝ)) / m0sum c
        = ((c : ℝ) / (winHi c : ℝ) * (2 / Real.log (c : ℝ)))
          * (1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ)) * (1 - tailMassM c / m0sum c) := by
      rw [show 1 - tailMassM c / m0sum c = (m0sum c - tailMassM c) / m0sum c from by
        rw [sub_div, div_self hm0.ne']]
      field_simp [hL.ne', hm0.ne', hcR.ne', hW.ne']
    have hcan : (Real.log (c : ℝ) / 2) * (1 - epsW c) * (2 / Real.log (c : ℝ))
        = 1 - epsW c := by
      calc (Real.log (c : ℝ) / 2) * (1 - epsW c) * (2 / Real.log (c : ℝ))
          = (1 - epsW c) * ((Real.log (c : ℝ) / 2) * (2 / Real.log (c : ℝ))) := by ring
        _ = (1 - epsW c) * 1 := by
            congr 1
            rw [div_mul_div_comm, mul_comm (Real.log (c : ℝ)) 2,
              div_self (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hL.ne')]
        _ = 1 - epsW c := mul_one _
    have hfac : (1 - epsW c) ≤ (c : ℝ) / (winHi c : ℝ) * (2 / Real.log (c : ℝ)) := by
      have h1' := mul_le_mul_of_nonneg_right hwhi h2L
      rw [hcan] at h1'
      exact h1'
    have h11 : (0 : ℝ) ≤ 1 - 1 / (winLo c : ℝ) := by
      have hle : (1 : ℝ) / winLo c ≤ 1 := by
        rw [div_le_one hW]
        exact_mod_cast h1
      linarith
    have h2c : (0 : ℝ) ≤ 1 - 2 / (c : ℝ) := by
      have hle : (2 : ℝ) / c ≤ 1 := by
        rw [div_le_one hcR]
        exact_mod_cast (by omega : 2 ≤ c)
      linarith
    have htail0 : (0 : ℝ) ≤ 1 - tailMassM c / m0sum c := by
      have hlow : (0 : ℝ) ≤ lowTailM c := Finset.sum_nonneg fun n _ => wrow_nonneg c n
      have hup : (0 : ℝ) ≤ upTailM c := Finset.sum_nonneg fun n _ => wrow_nonneg c n
      have hwin' : (0 : ℝ) ≤ winMassM c := Finset.sum_nonneg fun n _ => wrow_nonneg c n
      have htm : tailMassM c = lowTailM c + upTailM c := rfl
      rw [sub_nonneg, div_le_one hm0]
      linarith [hsplit, htm, hlow, hup, hwin']
    calc (1 - epsW c) * (1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ))
          * (1 - tailMassM c / m0sum c)
        = (1 - epsW c) * ((1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ))
            * (1 - tailMassM c / m0sum c)) := by ring
      _ ≤ ((c : ℝ) / (winHi c : ℝ) * (2 / Real.log (c : ℝ)))
          * ((1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ)) * (1 - tailMassM c / m0sum c)) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg (mul_nonneg h2c h11) htail0)
      _ = ((c : ℝ) / (winHi c : ℝ) * (2 / Real.log (c : ℝ)))
          * (1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ)) * (1 - tailMassM c / m0sum c) := by
          ring
      _ = ((c : ℝ) - 2) * (1 - 1 / (winLo c : ℝ)) * (1 / (winHi c : ℝ))
            * (m0sum c - tailMassM c) * (2 / Real.log (c : ℝ)) / m0sum c := hshape.symm
      _ ≤ nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c := hstep1
  have hhi : ∀ᶠ c : ℕ in atTop,
      nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c
        ≤ (1 + epsWp c) + (c : ℝ) * (tailMassM c / m0sum c) := by
    filter_upwards [nvarSum_le_ev, c_div_winLo_le_ev, eventually_ge_atTop 3,
      tendsto_log_atTop_nat.eventually_ge_atTop 2] with c hle hwlo hc hL2
    have hL : (0 : ℝ) < Real.log (c : ℝ) := by linarith [hL2]
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have h2L1 : 2 / Real.log (c : ℝ) ≤ 1 := by
      rw [div_le_one hL]
      linarith [hL2]
    have htailnn : (0 : ℝ) ≤ tailMassM c / m0sum c :=
      div_nonneg (tailMassM_nonneg c) hm0.le
    calc nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c
        ≤ ((c : ℝ) * (m0sum c / (winLo c : ℝ) + tailMassM c))
            * (2 / Real.log (c : ℝ)) / m0sum c := by
          apply div_le_div_of_nonneg_right _ hm0.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hle
      _ = ((c : ℝ) / (winLo c : ℝ)) * (2 / Real.log (c : ℝ))
            + (c : ℝ) * (tailMassM c / m0sum c) * (2 / Real.log (c : ℝ)) := by
          field_simp [hm0.ne', hL.ne']
      _ ≤ (1 + epsWp c) + (c : ℝ) * (tailMassM c / m0sum c) := by
          apply add_le_add
          · have h1' := mul_le_mul_of_nonneg_right hwlo (by positivity :
              (0 : ℝ) ≤ 2 / Real.log (c : ℝ))
            have hcan : (Real.log (c : ℝ) / 2) * (1 + epsWp c) * (2 / Real.log (c : ℝ))
                = 1 + epsWp c := by
              calc (Real.log (c : ℝ) / 2) * (1 + epsWp c) * (2 / Real.log (c : ℝ))
                  = (1 + epsWp c) * ((Real.log (c : ℝ) / 2) * (2 / Real.log (c : ℝ))) := by
                    ring
                _ = (1 + epsWp c) * 1 := by
                    congr 1
                    rw [div_mul_div_comm, mul_comm (Real.log (c : ℝ)) 2,
                      div_self (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hL.ne')]
                _ = 1 + epsWp c := mul_one _
            rw [hcan] at h1'
            exact h1'
          · calc (c : ℝ) * (tailMassM c / m0sum c) * (2 / Real.log (c : ℝ))
                ≤ (c : ℝ) * (tailMassM c / m0sum c) * 1 :=
                  mul_le_mul_of_nonneg_left h2L1 (mul_nonneg (Nat.cast_nonneg _) htailnn)
              _ = (c : ℝ) * (tailMassM c / m0sum c) := mul_one _
  have hlot : Tendsto (fun c : ℕ => (1 - epsW c) * (1 - 2 / (c : ℝ))
      * (1 - 1 / (winLo c : ℝ)) * (1 - tailMassM c / m0sum c)) atTop (nhds 1) := by
    have h1 : Tendsto (fun c : ℕ => 1 - epsW c) atTop (nhds 1) := by
      have h : Tendsto (fun c : ℕ => (1 : ℝ) - epsW c) atTop (nhds ((1 : ℝ) - 0)) :=
        tendsto_const_nhds.sub tendsto_epsW_zero
      rwa [sub_zero] at h
    have h2 : Tendsto (fun c : ℕ => 1 - 2 / (c : ℝ)) atTop (nhds 1) := by
      have h2c : Tendsto (fun c : ℕ => (2 : ℝ) / (c : ℝ)) atTop (nhds 0) := by
        have h := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
        have h2' := h.const_mul (2 : ℝ)
        rw [mul_zero] at h2'
        exact h2'.congr' (by
          filter_upwards with c
          simp only [Function.comp_apply, div_eq_mul_inv])
      have h : Tendsto (fun c : ℕ => (1 : ℝ) - 2 / (c : ℝ)) atTop (nhds ((1 : ℝ) - 0)) :=
        tendsto_const_nhds.sub h2c
      rwa [sub_zero] at h
    have h3 : Tendsto (fun c : ℕ => 1 - 1 / (winLo c : ℝ)) atTop (nhds 1) := by
      have h : Tendsto (fun c : ℕ => (1 : ℝ) - 1 / (winLo c : ℝ)) atTop
          (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub tendsto_one_div_winLo_zero
      rwa [sub_zero] at h
    have h4 : Tendsto (fun c : ℕ => 1 - tailMassM c / m0sum c) atTop (nhds 1) := by
      have h : Tendsto (fun c : ℕ => (1 : ℝ) - tailMassM c / m0sum c) atTop
          (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub tendsto_tailMassM_div_m0sum_zero
      rwa [sub_zero] at h
    have h := ((h1.mul h2).mul h3).mul h4
    simpa only [sub_zero, mul_one] using h
  have hhit : Tendsto (fun c : ℕ => (1 + epsWp c) + (c : ℝ) * (tailMassM c / m0sum c))
      atTop (nhds 1) := by
    have h1 : Tendsto (fun c : ℕ => 1 + epsWp c) atTop (nhds 1) := by
      have h : Tendsto (fun c : ℕ => (1 : ℝ) + epsWp c) atTop (nhds ((1 : ℝ) + 0)) :=
        tendsto_const_nhds.add tendsto_epsWp_zero
      rwa [add_zero] at h
    have h := h1.add tendsto_c_mul_tailMassM_div_m0sum_zero
    rwa [add_zero] at h
  have hGnn : ∀ᶠ c : ℕ in atTop, (0 : ℝ) ≤ (c : ℝ) ^ 2 * m0sum c / dsum c := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (m0sum_pos c).le)
      (dsum_pos c hc).le
  have hRG : ∀ᶠ c : ℕ in atTop,
      nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
        = (nvarSum c * (2 / Real.log (c : ℝ)) / m0sum c)
          * ((c : ℝ) ^ 2 * m0sum c / dsum c) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    have hL : Real.log (c : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < c))).ne'
    have hm0 : m0sum c ≠ 0 := (m0sum_pos c).ne'
    have hd : dsum c ≠ 0 := (dsum_pos c hc).ne'
    field_simp [hL, hm0, hd]
  have hlob : ∀ᶠ c : ℕ in atTop,
      ((1 - epsW c) * (1 - 2 / (c : ℝ)) * (1 - 1 / (winLo c : ℝ))
          * (1 - tailMassM c / m0sum c))
        * ((c : ℝ) ^ 2 * m0sum c / dsum c)
        ≤ nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c) := by
    filter_upwards [hlo, hGnn, hRG] with c h1 h2 h3
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have hhib : ∀ᶠ c : ℕ in atTop,
      nvarSum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
        ≤ ((1 + epsWp c) + (c : ℝ) * (tailMassM c / m0sum c))
          * ((c : ℝ) ^ 2 * m0sum c / dsum c) := by
    filter_upwards [hhi, hGnn, hRG] with c h1 h2 h3
    rw [h3]
    exact mul_le_mul_of_nonneg_right h1 h2
  have hloG := hlot.mul tendsto_c_sq_mul_m0sum_div_dsum_one
  rw [mul_one] at hloG
  have hhiG := hhit.mul tendsto_c_sq_mul_m0sum_div_dsum_one
  rw [mul_one] at hhiG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hloG hhiG hlob hhib

/-! ## Section G: `resid_negligible` -/

/-- The resid test scale: `a = (log c)/(2c)`, the first-order value of `1/n`
on the window. -/
noncomputable def aResid (c : ℕ) : ℝ := Real.log (c : ℝ) / (2 * (c : ℝ))

/-- The resid test sum: `Σ_n Σ_k (k/n − a·k)²·cellW`, the numerator of
`‖obsM − a·obsE‖²`. -/
noncomputable def residNumSum (c : ℕ) (a : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n - a * (k : ℝ)) ^ 2 * cellW c n k

/-- The resid test sum is nonnegative. -/
theorem residNumSum_nonneg (c : ℕ) (a : ℝ) : (0 : ℝ) ≤ residNumSum c a :=
  Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (sq_nonneg _) (cellW_nonneg c n k)

/-- The product-sum evaluation of the test-function distance:
`‖obsM − a·obsE‖² = residNumSum/m0sum`, following
`Gap2CensusVarianceSep.norm_sq_obsM`. -/
theorem norm_sq_sub_smul_obsE (c : ℕ) (a : ℝ) :
    ‖obsM c - a • obsE c‖ ^ 2 = residNumSum c a / m0sum c := by
  rw [← real_inner_self_eq_norm_sq, inner_apply]
  refine (expect_eq_product_sum c (fun n k _j _t =>
      (((k : ℝ) / n - a * (k : ℝ)) * ((k : ℝ) / n - a * (k : ℝ))))).trans ?_
  have hcell : ∀ n k : ℕ,
      (∑ j ∈ Finset.range (k + 1), ∑ _t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
          * (((k : ℝ) / n - a * (k : ℝ)) * ((k : ℝ) / n - a * (k : ℝ))))
      = ((c + 1 : ℕ) : ℝ) * (((k : ℝ) / n - a * (k : ℝ)) ^ 2 * cellW c n k) := by
    intro n k
    rw [sum_jt c n k (fun _ => ((k : ℝ) / n - a * (k : ℝ)) * ((k : ℝ) / n - a * (k : ℝ)))]
    congr 1
    rw [← Finset.sum_mul]
    have hm : (∑ j ∈ Finset.range (k + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        = (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := by
      rw [← Finset.sum_div, ← Nat.cast_sum, margin_count, Nat.cast_pow]
    rw [hm, sq, cellW_eq]
    ring
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => hcell n k))]
  simp_rw [← Finset.mul_sum]
  rw [← residNumSum.eq_def, censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-- The per-cell square factors: `(k/n − a·k)² = k²·(1/n − a)²`. -/
theorem sub_sq_factor (n k : ℕ) (a : ℝ) :
    ((k : ℝ) / n - a * (k : ℝ)) ^ 2 = (k : ℝ) ^ 2 * (1 / (n : ℝ) - a) ^ 2 := by
  have hid : (k : ℝ) / n - a * (k : ℝ) = (k : ℝ) * (1 / (n : ℝ) - a) := by
    rw [mul_sub, mul_one_div, mul_comm (k : ℝ) a]
  rw [hid, mul_pow]

/-- The k-second-moment bound: `residNumSum ≤ c²·Σ_n (1/n − a)²·wrow`. -/
theorem residNumSum_le (c : ℕ) (a : ℝ) :
    residNumSum c a
      ≤ (c : ℝ) ^ 2 * ∑ n ∈ Finset.range (c + 1), (1 / (n : ℝ) - a) ^ 2 * wrow c n := by
  rw [residNumSum.eq_def, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  have hstep : (∑ k ∈ Finset.range (c + 1), ((k : ℝ) / n - a * (k : ℝ)) ^ 2 * cellW c n k)
      = (1 / (n : ℝ) - a) ^ 2
          * ∑ k ∈ Finset.range (c + 1), (k : ℝ) ^ 2 * cellW c n k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [sub_sq_factor]
    ring
  rw [hstep, show (c : ℝ) ^ 2 * ((1 / (n : ℝ) - a) ^ 2 * wrow c n)
      = (1 / (n : ℝ) - a) ^ 2 * ((c : ℝ) ^ 2 * wrow c n) from by ring]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  rw [wrow_eq_sum_cellW, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_right _ (cellW_nonneg c n k)
  have hkc : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hkc) 2

/-- `ε₂ ≥ 0`. -/
theorem epsW_nonneg {c : ℕ} (hc : 3 ≤ c) : (0 : ℝ) ≤ epsW c := by
  have hη : (0 : ℝ) ≤ etaS c := etaS_nonneg hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hs2 : (0 : ℝ) ≤ s2S c := by
    rw [s2S]
    exact div_nonneg hL.le (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by linarith)) (by linarith))
  rw [epsW]
  exact add_nonneg (add_nonneg hη hδ) hs2

/-- `ε₁ ≥ 0` eventually (needs `δ ≤ 1`, which holds only for large `c`). -/
theorem epsWp_nonneg_ev : ∀ᶠ c : ℕ in atTop, (0 : ℝ) ≤ epsWp c := by
  filter_upwards [tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 3] with c hδ1 hc
  have hδ : (0 : ℝ) ≤ deltaS c := (deltaS_pos' hc).le
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have hs1 : (0 : ℝ) ≤ s1S c := by
    rw [s1S]
    exact div_nonneg hL.le
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith))
  rw [epsWp]
  linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hδ,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs1]

/-- On the window the resid test weight is at most `a²·ε_D²`:
`Σ_win (1/n − a)²·wrow ≤ (a·ε_D)²·winMass`. -/
theorem residNumSum_window_le_ev : ∀ᶠ c : ℕ in atTop,
    ∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), (1 / (n : ℝ) - aResid c) ^ 2 * wrow c n
      ≤ (aResid c * epsD c) ^ 2 * winMassM c := by
  filter_upwards [one_div_winLo_le_ev, one_div_winHi_ge_ev, eventually_ge_atTop 3,
    one_le_winLo_ev, epsWp_nonneg_ev] with c hlo hhi hc h1 hεWp
  have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
  have ha : (0 : ℝ) ≤ aResid c := div_nonneg hL.le (by positivity)
  have hεW : (0 : ℝ) ≤ epsW c := epsW_nonneg hc
  have hεD : (0 : ℝ) ≤ epsD c := add_nonneg hεW hεWp
  have hW : (0 : ℝ) < (winLo c : ℝ) := by exact_mod_cast h1
  have hle1 : epsW c ≤ epsD c := by rw [epsD]; linarith
  have hle2 : epsWp c ≤ epsD c := by rw [epsD]; linarith
  rw [winMassM, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hnlo : (winLo c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnhi : (n : ℝ) ≤ (winHi c : ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp hn.2)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hW hnlo
  have h1n_lo : 1 / (n : ℝ) ≤ 1 / (winLo c : ℝ) := one_div_le_one_div_of_le hW hnlo
  have h1n_hi : 1 / (winHi c : ℝ) ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnpos hnhi
  have hX2 : aResid c = Real.log (c : ℝ) / (2 * (c : ℝ)) := rfl
  have hub : 1 / (n : ℝ) - aResid c ≤ aResid c * epsD c := by
    have hX1 : 1 / (n : ℝ) ≤ (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 + epsWp c) :=
      le_trans h1n_lo hlo
    calc 1 / (n : ℝ) - aResid c
        ≤ (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 + epsWp c) - aResid c := by
          linarith [hX1]
      _ = (Real.log (c : ℝ) / (2 * (c : ℝ))) * epsWp c := by rw [hX2]; ring
      _ ≤ aResid c * epsD c := by
          rw [hX2]
          exact mul_le_mul_of_nonneg_left hle2 (hX2 ▸ ha)
  have hlb : -(aResid c * epsD c) ≤ 1 / (n : ℝ) - aResid c := by
    have hX1 : (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 - epsW c) ≤ 1 / (n : ℝ) :=
      le_trans hhi h1n_hi
    calc -(aResid c * epsD c)
        ≤ -((Real.log (c : ℝ) / (2 * (c : ℝ))) * epsW c) := by
          rw [hX2]
          exact neg_le_neg (mul_le_mul_of_nonneg_left hle1 (hX2 ▸ ha))
      _ = (Real.log (c : ℝ) / (2 * (c : ℝ))) * (1 - epsW c)
            - (Real.log (c : ℝ) / (2 * (c : ℝ))) := by ring
      _ ≤ 1 / (n : ℝ) - aResid c := by rw [hX2]; linarith [hX1]
  have hsq : (1 / (n : ℝ) - aResid c) ^ 2 ≤ (aResid c * epsD c) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (mul_nonneg ha hεD)]
    exact abs_le.mpr ⟨hlb, hub⟩
  exact mul_le_mul_of_nonneg_right hsq (wrow_nonneg c n)

/-- The tail evaluation: `(1/n − a)² ≤ 2/n² + 2a²` pointwise, summed to
`(2 + 2a²)·tailMass`. -/
theorem residNumSum_tail_le (c : ℕ) (a : ℝ) :
    (∑ n ∈ Finset.range (winLo c), (1 / (n : ℝ) - a) ^ 2 * wrow c n)
      + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), (1 / (n : ℝ) - a) ^ 2 * wrow c n)
      ≤ (2 + 2 * a ^ 2) * tailMassM c := by
  have hterm : ∀ n : ℕ, (1 / (n : ℝ) - a) ^ 2 * wrow c n
      ≤ (2 * (1 / (n : ℝ)) ^ 2 + 2 * a ^ 2) * wrow c n := by
    intro n
    apply mul_le_mul_of_nonneg_right _ (wrow_nonneg c n)
    nlinarith [sq_nonneg (1 / (n : ℝ) + a)]
  have hone : ∀ n : ℕ, (1 / (n : ℝ)) ^ 2 ≤ 1 := by
    intro n
    by_cases h0 : n = 0
    · rw [h0, Nat.cast_zero, div_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      norm_num
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
          _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hn1 2
      have hnp : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
      rw [div_pow, one_pow, div_le_one (pow_pos hnp 2)]
      exact hn2
  have hreg : ∀ s : Finset ℕ, ∑ n ∈ s, (1 / (n : ℝ) - a) ^ 2 * wrow c n
      ≤ (2 + 2 * a ^ 2) * ∑ n ∈ s, wrow c n := by
    intro s
    calc ∑ n ∈ s, (1 / (n : ℝ) - a) ^ 2 * wrow c n
        ≤ ∑ n ∈ s, (2 * (1 / (n : ℝ)) ^ 2 + 2 * a ^ 2) * wrow c n :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = 2 * (∑ n ∈ s, (1 / (n : ℝ)) ^ 2 * wrow c n)
            + 2 * a ^ 2 * (∑ n ∈ s, wrow c n) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ ≤ 2 * (∑ n ∈ s, wrow c n) + 2 * a ^ 2 * (∑ n ∈ s, wrow c n) := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          apply Finset.sum_le_sum
          intro n _
          exact (mul_le_mul_of_nonneg_right (hone n) (wrow_nonneg c n)).trans
            (by rw [one_mul])
      _ = (2 + 2 * a ^ 2) * ∑ n ∈ s, wrow c n := by ring
  have hsum := add_le_add (hreg (Finset.range (winLo c)))
    (hreg (Finset.Ico (winHi c + 1) (c + 1)))
  calc (∑ n ∈ Finset.range (winLo c), (1 / (n : ℝ) - a) ^ 2 * wrow c n)
        + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), (1 / (n : ℝ) - a) ^ 2 * wrow c n)
      ≤ (2 + 2 * a ^ 2) * (∑ n ∈ Finset.range (winLo c), wrow c n)
          + (2 + 2 * a ^ 2) * (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), wrow c n) := hsum
    _ = (2 + 2 * a ^ 2) * tailMassM c := by
        rw [tailMassM, lowTailM, upTailM, ← mul_add]

/-- The combined resid numerator bound, eventually. -/
theorem residNumSum_le_ev : ∀ᶠ c : ℕ in atTop,
    residNumSum c (aResid c)
      ≤ (c : ℝ) ^ 2 * ((aResid c * epsD c) ^ 2 * winMassM c
          + (2 + 2 * (aResid c) ^ 2) * tailMassM c) := by
  filter_upwards [residNumSum_window_le_ev, eventually_ge_atTop 3, one_le_winLo_ev,
    winHi_le_c_ev,
    tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with c hwin_bd hc h1 hwhi hδ1
  have hwin : winLo c ≤ winHi c + 1 := Nat.le_succ_of_le (winLo_le_winHi c hc hδ1)
  have hwhi2 : winHi c + 1 ≤ c + 1 := Nat.succ_le_succ hwhi
  have h12 : winLo c ≤ c + 1 := hwin.trans hwhi2
  have hregions : ∀ f : ℕ → ℝ,
      ∑ n ∈ Finset.range (c + 1), f n
        = (∑ n ∈ Finset.range (winLo c), f n)
          + (∑ n ∈ Finset.Ico (winLo c) (winHi c + 1), f n)
          + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1), f n) := by
    intro f
    rw [← Finset.sum_range_add_sum_Ico f h12,
      ← Finset.sum_Ico_consecutive f hwin hwhi2, add_assoc]
  have htail := residNumSum_tail_le c (aResid c)
  have h1' := residNumSum_le c (aResid c)
  rw [hregions (fun n => (1 / (n : ℝ) - aResid c) ^ 2 * wrow c n)] at h1'
  calc residNumSum c (aResid c)
      ≤ (c : ℝ) ^ 2 * ((∑ n ∈ Finset.range (winLo c),
              (1 / (n : ℝ) - aResid c) ^ 2 * wrow c n)
          + (∑ n ∈ Finset.Ico (winLo c) (winHi c + 1),
              (1 / (n : ℝ) - aResid c) ^ 2 * wrow c n)
          + (∑ n ∈ Finset.Ico (winHi c + 1) (c + 1),
              (1 / (n : ℝ) - aResid c) ^ 2 * wrow c n)) := h1'
    _ ≤ (c : ℝ) ^ 2 * ((aResid c * epsD c) ^ 2 * winMassM c
          + (2 + 2 * (aResid c) ^ 2) * tailMassM c) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
        linarith [hwin_bd, htail]

/-- `a → 0`: `a = (log c/c)/2`. -/
theorem tendsto_aResid_zero : Tendsto aResid atTop (nhds 0) := by
  have h := tendsto_log_div_atTop_nat.div tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0)
  rw [zero_div] at h
  exact h.congr' (by
    filter_upwards with c
    show Real.log (c : ℝ) / (c : ℝ) / 2 = aResid c
    rw [aResid.eq_def, div_div, mul_comm (c : ℝ) (2 : ℝ)])

/-- `a² ≤ 1` eventually. -/
theorem aResid_sq_le_one_ev : ∀ᶠ c : ℕ in atTop, (aResid c) ^ 2 ≤ 1 :=
  (tendsto_aResid_zero.pow 2).eventually (Iic_mem_nhds (by norm_num : ((0 : ℝ) ^ 2) < 1))

/-- The resid numerator at the sharp scale dies:
`residNumSum·(2/log c)/m0sum → 0`. -/
theorem tendsto_residNumSum_scale_zero :
    Tendsto (fun c : ℕ => residNumSum c (aResid c) * (2 / Real.log (c : ℝ)) / m0sum c)
      atTop (nhds 0) := by
  have hnn : ∀ᶠ c : ℕ in atTop,
      (0 : ℝ) ≤ residNumSum c (aResid c) * (2 / Real.log (c : ℝ)) / m0sum c := by
    filter_upwards [eventually_ge_atTop 3] with c hc
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    exact div_nonneg (mul_nonneg (residNumSum_nonneg c _)
      (div_nonneg (by norm_num) hL.le)) (m0sum_pos c).le
  have hbnd : ∀ᶠ c : ℕ in atTop,
      residNumSum c (aResid c) * (2 / Real.log (c : ℝ)) / m0sum c
        ≤ (Real.log (c : ℝ) / 2) * (epsD c) ^ 2
          + 8 * ((c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c)) := by
    filter_upwards [residNumSum_le_ev, eventually_ge_atTop 3, one_le_winLo_ev,
      winHi_le_c_ev, aResid_sq_le_one_ev,
      tendsto_deltaS_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with c hle hc h1 hwhi ha1 hδ1
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
    have hwin : winLo c ≤ winHi c + 1 := Nat.le_succ_of_le (winLo_le_winHi c hc hδ1)
    have hwhi2 : winHi c + 1 ≤ c + 1 := Nat.succ_le_succ hwhi
    have hsplit := m0sum_eq_lowTailM_add_winMassM_add_upTailM c hwin hwhi2
    have hlow : (0 : ℝ) ≤ lowTailM c := Finset.sum_nonneg fun n _ => wrow_nonneg c n
    have hup : (0 : ℝ) ≤ upTailM c := Finset.sum_nonneg fun n _ => wrow_nonneg c n
    have hwm : winMassM c ≤ m0sum c := by linarith [hsplit, hlow, hup]
    have hwmr : winMassM c / m0sum c ≤ 1 := by
      rw [div_le_one hm0]; exact hwm
    have htailnn : (0 : ℝ) ≤ tailMassM c / m0sum c := div_nonneg (tailMassM_nonneg c) hm0.le
    have hstep := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle
        ((div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL.le) : (0 : ℝ) ≤ 2 / Real.log (c : ℝ)))
      hm0.le
    refine hstep.trans ?_
    have h_alg1 : (c : ℝ) ^ 2 * ((aResid c * epsD c) ^ 2 * winMassM c
          + (2 + 2 * (aResid c) ^ 2) * tailMassM c)
          * (2 / Real.log (c : ℝ)) / m0sum c
        = ((Real.log (c : ℝ) / 2) * (epsD c) ^ 2 * (winMassM c / m0sum c))
          + ((4 * (c : ℝ) ^ 2 / Real.log (c : ℝ)) * (1 + (aResid c) ^ 2)
              * (tailMassM c / m0sum c)) := by
      rw [show aResid c = Real.log (c : ℝ) / (2 * (c : ℝ)) from rfl]
      field_simp [hL.ne', hm0.ne', hcR.ne']
      ring
    rw [h_alg1]
    apply add_le_add
    · have h1' : (0 : ℝ) ≤ (Real.log (c : ℝ) / 2) * (epsD c) ^ 2 :=
        mul_nonneg (div_nonneg hL.le (by norm_num)) (sq_nonneg _)
      calc (Real.log (c : ℝ) / 2) * (epsD c) ^ 2 * (winMassM c / m0sum c)
          ≤ (Real.log (c : ℝ) / 2) * (epsD c) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hwmr h1'
        _ = (Real.log (c : ℝ) / 2) * (epsD c) ^ 2 := mul_one _
    · have ha2 : 1 + (aResid c) ^ 2 ≤ 2 := by linarith [ha1]
      have hL1 : (1 : ℝ) < Real.log (c : ℝ) :=
        one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hc))
      have h4cL : (0 : ℝ) ≤ 4 * (c : ℝ) ^ 2 / Real.log (c : ℝ) :=
        div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)) hL.le
      calc (4 * (c : ℝ) ^ 2 / Real.log (c : ℝ)) * (1 + (aResid c) ^ 2)
            * (tailMassM c / m0sum c)
          ≤ (4 * (c : ℝ) ^ 2 / Real.log (c : ℝ)) * 2 * (tailMassM c / m0sum c) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha2 h4cL) htailnn
        _ = (8 * (c : ℝ) ^ 2 / Real.log (c : ℝ)) * (tailMassM c / m0sum c) := by ring
        _ ≤ 8 * ((c : ℝ) ^ 2 * Real.log (c : ℝ)) * (tailMassM c / m0sum c) := by
            apply mul_le_mul_of_nonneg_right _ htailnn
            have hLsq : (1 : ℝ) ≤ Real.log (c : ℝ) ^ 2 := by
              calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
                _ ≤ Real.log (c : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hL1.le 2
            have h8c : (0 : ℝ) ≤ 8 * (c : ℝ) ^ 2 :=
              mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)
            have hfin : (8 : ℝ) * (c : ℝ) ^ 2 ≤ 8 * (c : ℝ) ^ 2 * Real.log (c : ℝ) ^ 2 := by
              calc (8 : ℝ) * (c : ℝ) ^ 2 = 8 * (c : ℝ) ^ 2 * 1 := (mul_one _).symm
                _ ≤ 8 * (c : ℝ) ^ 2 * Real.log (c : ℝ) ^ 2 :=
                    mul_le_mul_of_nonneg_left hLsq h8c
            rw [div_le_iff₀ hL]
            calc (8 : ℝ) * (c : ℝ) ^ 2 ≤ 8 * (c : ℝ) ^ 2 * Real.log (c : ℝ) ^ 2 := hfin
              _ = 8 * ((c : ℝ) ^ 2 * Real.log (c : ℝ)) * Real.log (c : ℝ) := by ring
        _ = 8 * ((c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c)) := by ring
  have hzero : Tendsto (fun c : ℕ => (Real.log (c : ℝ) / 2) * (epsD c) ^ 2
      + 8 * ((c : ℝ) ^ 2 * Real.log (c : ℝ) * (tailMassM c / m0sum c)))
      atTop (nhds 0) := by
    have h2 := tendsto_c_sq_log_mul_tailMassM_div_m0sum_zero.const_mul (8 : ℝ)
    rw [mul_zero] at h2
    have h := tendsto_L_half_mul_epsD_sq_zero.add h2
    rwa [add_zero] at h
  exact squeeze_zero' hnn hbnd hzero

/-- **The conditional-mean residual is negligible at the sharp rate
(TARGET: `resid_negligible`).**  The test function `y = (log c/2c)·nE` in the
count span bounds `‖r(m)‖²` by `residNumSum/m0sum`, whose scaled limit is zero
against `dsum ~ c²·m0sum`. -/
theorem resid_negligible :
    Tendsto (fun c : ℕ =>
      ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)) atTop (nhds 0) := by
  have hnn : ∀ᶠ c : ℕ in atTop, (0 : ℝ) ≤
      ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hd : (0 : ℝ) < dsum c := dsum_pos c hc
    exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (m0sum_pos c).le)
      (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _)))
      (mul_nonneg hL.le hd.le)
  have hbnd : ∀ᶠ c : ℕ in atTop,
      ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
        ≤ (residNumSum c (aResid c) * (2 / Real.log (c : ℝ)) / m0sum c)
          * ((c : ℝ) ^ 2 * m0sum c / dsum c) := by
    filter_upwards [eventually_ge_atTop 2] with c hc
    have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
    have hL : (0 : ℝ) < Real.log (c : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < c))
    have hd : (0 : ℝ) < dsum c := dsum_pos c hc
    have hmem : (aResid c) • obsE c ∈ countSpan (obsV c) (obsE c) (obsT c) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have h1 := Gap2CensusVarianceSep.norm_sq_resid_le_of_mem_span c (obsM c)
      ((aResid c) • obsE c) hmem
    rw [norm_sq_sub_smul_obsE] at h1
    have h2 : ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
        * m0sum c ≤ residNumSum c (aResid c) := by
      have h2' := mul_le_mul_of_nonneg_right h1 hm0.le
      rwa [div_mul_cancel₀ _ hm0.ne'] at h2'
    have hRG : ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
          * m0sum c * (2 * (c : ℝ) ^ 2) / (Real.log c * dsum c)
        = ((‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2
            * m0sum c) * (2 / Real.log (c : ℝ)) / m0sum c)
          * ((c : ℝ) ^ 2 * m0sum c / dsum c) := by
      field_simp [hm0.ne', hL.ne', hd.ne']
    rw [hRG]
    apply mul_le_mul_of_nonneg_right _
      (div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hm0.le) hd.le)
    apply div_le_div_of_nonneg_right _ hm0.le
    apply mul_le_mul_of_nonneg_right _ (div_nonneg (by norm_num) hL.le)
    exact h2
  have hzero := tendsto_residNumSum_scale_zero.mul tendsto_c_sq_mul_m0sum_div_dsum_one
  rw [zero_mul] at hzero
  exact squeeze_zero' hnn hbnd hzero

/-! ## Section H: the unconditional sharp rate -/

/-- **The sharp-rate gap, discharged.**  All three fields are proved:
`nvar_sharp` (Section F), `resid_negligible` (Section G), and `dsum_saddle`
(A51). -/
theorem sharpRateGap_discharged : SharpRateGap :=
  ⟨nvar_sharp, resid_negligible, Gap2CensusDsumSaddle.dsum_saddle⟩

/-- **The sharp rate, unconditional (TARGET 4 closed):**
`q(c)·(2c²/log c) → 1`. -/
theorem qfrac_sharp_rate_unconditional :
    Tendsto (fun c : ℕ => qfrac c * (2 * (c : ℝ) ^ 2 / Real.log c)) atTop (nhds 1) :=
  Gap2SharpRateGap.qfrac_sharp_rate_of_gap sharpRateGap_discharged

/-- **The `(1 + o(1))` form, unconditional:** `q(c) = (log c)/(2c²)·(1+o(1))`. -/
theorem qfrac_sharp_rate_one_add_o1_unconditional :
    Tendsto (fun c : ℕ => qfrac c / (Real.log c / (2 * (c : ℝ) ^ 2))) atTop (nhds 1) :=
  Gap2SharpRateGap.qfrac_sharp_rate_one_add_o1 sharpRateGap_discharged

#print axioms nvar_sharp
#print axioms resid_negligible
#print axioms sharpRateGap_discharged
#print axioms qfrac_sharp_rate_unconditional
#print axioms qfrac_sharp_rate_one_add_o1_unconditional

end Gap2CensusNvarSharp
