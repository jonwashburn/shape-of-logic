import IndisputableMonolith.Gravity.SevenGaps.Gap2M0Asymptotics
import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusProductForm

/-!
# Hostile-review probe: A48 M0 completion (E-qg-m0-completion-hostile-review-20260801)

Independent outside-module checks on the A48 closure of `mechanismBound → 0` in
`Gap2M0Asymptotics.lean`, written by the hostile reviewer of record. This file
is NOT the worker's self-probe (`QGM0CompletionProbe.lean`); it shares no text
with it. Where the worker re-derived the finite-`c` bound, this probe instead:

1. Re-audits every A48 head theorem from outside the module.
2. Pins the definitions by `rfl`: `mechanismBound = nsum/dsum`, `m0sum` and
   `smallMass` as sums of the census row mass `wrow`, and proves
   `Σ_j cellCount n k j = n^(2k)`, closing the link between `wrow` and the
   orbit–stabilizer census weights `cellCount/(n!·k!)` of `census_identity`.
3. Non-vacuity witnesses: the target-1 ratio and `mechanismBound` are
   everywhere strictly positive, and the bulk-D left side
   `(c²/4)·(m0sum − smallMass)` is strictly positive for `c ≥ 2` (the large
   region always contains `n = c`).
4. Concreteness: `bulk_dsum_lower` at `c = 9`, the large-cell comparison at
   `(c, n) = (9, 10)`, and the A48 envelope `smallMass_div_m0sum_le_half_pow`
   instantiated at its exact stated threshold `c = 163000`, with the two side
   conditions discharged numerically.
5. Re-composition of `mechanismBound → 0` from `mechanismBound_le` and target
   1, written here, not cited from the module's own assembly.
6. Independent red test, stronger than a compile failure: the flipped bulk
   inequality and the flipped large-cell comparison are proved eventually
   FALSE (the bulk one via a strict re-derivation `bulk_dsum_lower_strict`,
   the comparison one at the witness `n = c`).
7. Structure pin: `MechanismBoundClosureGap` is `Iff.rfl`-equal to the A47
   two-conjunct form, so any weakening of the named gap breaks this file.
-/

namespace QGM0CompletionHostileProbe

open Gap2M0Asymptotics Gap2CensusProductForm Finset Filter
open scoped Topology Nat

/-! ## 1. Outside-module axiom audits of the 17 charged head theorems -/

#print axioms Gap2M0Asymptotics.tendsto_smallMass_div_m0sum_zero
#print axioms Gap2M0Asymptotics.bulk_dsum_lower
#print axioms Gap2M0Asymptotics.mechanismBoundClosureGap_holds
#print axioms Gap2M0Asymptotics.tendsto_mechanismBound_zero
#print axioms Gap2M0Asymptotics.mechanismBound_le
#print axioms Gap2M0Asymptotics.nsumLarge_le_dsum_div
#print axioms Gap2M0Asymptotics.nsum_eq_small_add_large
#print axioms Gap2M0Asymptotics.smallMass_div_m0sum_le_half_pow
#print axioms Gap2M0Asymptotics.smallMass_div_m0sum_le_envelope
#print axioms Gap2M0Asymptotics.termA_le
#print axioms Gap2M0Asymptotics.termB_le
#print axioms Gap2M0Asymptotics.properRow_ge
#print axioms Gap2M0Asymptotics.loopRow_le_properRow_div
#print axioms Gap2M0Asymptotics.stirlingU_saddlen_le_two_pow
#print axioms Gap2M0Asymptotics.log_stirlingU_saddlen_le
#print axioms Gap2M0Asymptotics.four_sqrt_clogc_log_le_eventually
#print axioms Gap2M0Asymptotics.one_mem_smallSet

/-! ## 2. Definitional pins: the tendos are about the real objects -/

/-- `mechanismBound` really is `nsum/dsum`. -/
theorem mechanismBound_eq (c : ℕ) : mechanismBound c = nsum c / dsum c := rfl

/-- `m0sum` really is the total census row mass over `range (c+1)`. -/
theorem m0sum_eq (c : ℕ) : m0sum c = ∑ n ∈ Finset.range (c + 1), wrow c n := rfl

/-- `smallMass` really is the row mass below the `c·log c` cutoff. -/
theorem smallMass_eq (c : ℕ) : smallMass c = ∑ n ∈ smallSet c, wrow c n := rfl

/-- The small region really is filtered on `n² ≤ c·log c`. -/
theorem smallSet_eq (c : ℕ) :
    smallSet c = (Finset.range (c + 1)).filter
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c) := rfl

/-- The large region really is filtered on `c·log c < n²`. -/
theorem largeSet_eq (c : ℕ) :
    largeSet c = (Finset.range (c + 1)).filter
      (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2) := rfl

/-- The census link: the cell counts of `census_identity` (orbit–stabilizer
weights `cellCount/(n!·k!)`) sum over the loop index to exactly `n^(2k)`, the
numerator of the `wrow` term. So `wrow c n` is genuinely the `(n, ·)` row of
the product-form census mass, and `m0sum`/`smallMass` are sums of it. -/
theorem cellCount_sum_eq (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), cellCount n k j) = n ^ (2 * k) := by
  have hpow : (∑ j ∈ Finset.range (k + 1),
      Nat.choose k j * n ^ j * (n ^ 2 - n) ^ (k - j))
      = (n + (n ^ 2 - n)) ^ k := by
    rw [(Commute.all n (n ^ 2 - n)).add_pow k]
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.cast_id]; ring
  have hcell : ∀ j ∈ Finset.range (k + 1),
      cellCount n k j = Nat.choose k j * n ^ j * (n ^ 2 - n) ^ (k - j) :=
    fun j _ => by rw [cellCount]; ring
  rw [Finset.sum_congr rfl hcell, hpow, add_sq_sub, ← pow_mul]

/-! ## 3. Non-vacuity witnesses -/

/-- `n = 0` is always in the small region. -/
theorem zero_mem_smallSet (c : ℕ) : 0 ∈ smallSet c := by
  show 0 ∈ (Finset.range (c + 1)).filter
    (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_range.2 (Nat.succ_pos c), ?_⟩
  rcases eq_or_ne c 0 with rfl | hc0
  · simp [Real.log_zero]
  · have hnn : (0 : ℝ) ≤ (c : ℝ) * Real.log c :=
      mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.2 hc0)))
    simpa using hnn

/-- The numerator of target 1 is everywhere strictly positive. -/
theorem smallMass_pos (c : ℕ) : 0 < smallMass c := by
  have h0 : wrow c 0 ≤ smallMass c :=
    Finset.single_le_sum (fun n _ => wrow_nonneg c n) (zero_mem_smallSet c)
  exact lt_of_lt_of_le (wrow_pos c 0) h0

/-- The target-1 sequence is everywhere strictly positive and tends to `0`:
the limit statement has content. -/
theorem ratio_pos (c : ℕ) : 0 < smallMass c / m0sum c :=
  div_pos (smallMass_pos c) (m0sum_pos c)

/-- The large-region mass identity: `m0sum − smallMass` is the row mass of the
large region. -/
theorem m0sum_sub_smallMass (c : ℕ) :
    m0sum c - smallMass c = ∑ n ∈ largeSet c, wrow c n := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (c + 1))
    (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c) (wrow c)
  have hsm : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c), wrow c n)
      = smallMass c := rfl
  have hlg : (∑ n ∈ (Finset.range (c + 1)).filter
      (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c), wrow c n)
      = ∑ n ∈ largeSet c, wrow c n := by
    apply Finset.sum_congr _ (fun _ _ => rfl)
    show (Finset.range (c + 1)).filter
        (fun n : ℕ => ¬ (n : ℝ) ^ 2 ≤ (c : ℝ) * Real.log c)
        = (Finset.range (c + 1)).filter
          (fun n : ℕ => (c : ℝ) * Real.log c < (n : ℝ) ^ 2)
    apply Finset.filter_congr
    intro n _
    exact not_le
  rw [hsm, hlg] at h
  have hm0 : m0sum c = smallMass c + ∑ n ∈ largeSet c, wrow c n := h.symm
  rw [hm0]
  ring

/-- `n = c` always satisfies the large-region inequality (for `c ≥ 2`). -/
theorem clogc_lt_sq {c : ℕ} (hc : 2 ≤ c) : (c : ℝ) * Real.log c < (c : ℝ) ^ 2 := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.2 (by omega)
  have hc1 : (c : ℝ) ≠ 1 := by exact_mod_cast (by omega : c ≠ 1)
  have hlog : Real.log (c : ℝ) < (c : ℝ) := by
    have h2 := Real.log_lt_sub_one_of_pos hcR hc1
    linarith
  calc (c : ℝ) * Real.log c < (c : ℝ) * (c : ℝ) := mul_lt_mul_of_pos_left hlog hcR
    _ = (c : ℝ) ^ 2 := by ring

/-- The large region is never empty: `n = c` is in it. -/
theorem largeSet_self_mem {c : ℕ} (hc : 2 ≤ c) : c ∈ largeSet c := by
  rw [mem_largeSet]
  exact ⟨Finset.mem_range.2 (Nat.lt_succ_self c), clogc_lt_sq hc⟩

/-- The bulk-D left side is strictly positive: the large region carries row
mass. So conjunct 1 of the named gap is a non-vacuous domination. -/
theorem largeMass_pos {c : ℕ} (hc : 2 ≤ c) : 0 < m0sum c - smallMass c := by
  rw [m0sum_sub_smallMass]
  exact Finset.sum_pos' (fun n _ => wrow_nonneg c n)
    ⟨c, largeSet_self_mem hc, wrow_pos c c⟩

/-- The numerator of `mechanismBound` is strictly positive: the `(1, 1)` cell
alone contributes `1`. -/
theorem nsum_pos {c : ℕ} (hc : 1 ≤ c) : 0 < nsum c := by
  have h1 : 1 ∈ Finset.range (c + 1) := Finset.mem_range.2 (by omega)
  have hterm : (0 : ℝ) < (loopSqSum 1 1 : ℝ) / ((1 ! : ℝ) * (1 ! : ℝ)) := by
    rw [loopSqSum_one]
    norm_num [Nat.factorial]
  have hinner : (0 : ℝ) < ∑ k ∈ Finset.range (c + 1),
      (loopSqSum 1 k : ℝ) / ((1 ! : ℝ) * (k ! : ℝ)) :=
    Finset.sum_pos' (fun k _ => div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (ffact_nonneg 1) (ffact_nonneg k))) ⟨1, h1, hterm⟩
  have hle : (∑ k ∈ Finset.range (c + 1),
      (loopSqSum 1 k : ℝ) / ((1 ! : ℝ) * (k ! : ℝ))) ≤ nsum c := by
    refine Finset.single_le_sum (f := fun n => ∑ k ∈ Finset.range (c + 1),
      (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))) ?_ h1
    intro n _
    exact Finset.sum_nonneg fun k _ => div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (ffact_nonneg n) (ffact_nonneg k))
  exact hinner.trans_le hle

/-- The target-3 sequence is everywhere strictly positive for `c ≥ 2`: the
limit statement has content. -/
theorem mechanismBound_pos {c : ℕ} (hc : 2 ≤ c) : 0 < mechanismBound c :=
  div_pos (nsum_pos (by omega)) (dsum_pos c hc)

/-! ## 4. Concreteness: the theorems applied at specific `c` -/

/-- Bulk-D at `c = 9`, the boundary of its regime. -/
theorem bulk_at_nine :
    (9 : ℝ) ^ 2 / 4 * (m0sum 9 - smallMass 9) ≤ dsum 9 :=
  bulk_dsum_lower (c := 9) le_rfl

/-- Its left side is strictly positive there. -/
theorem bulk_at_nine_pos : 0 < (9 : ℝ) ^ 2 / 4 * (m0sum 9 - smallMass 9) :=
  mul_pos (by norm_num) (largeMass_pos (c := 9) (by norm_num : 2 ≤ 9))

/-- The large-cell comparison at `(c, n) = (9, 10)`. -/
theorem comparison_at_nine :
    (∑ k ∈ Finset.range (9 + 1), (loopSqSum 10 k : ℝ) / ((10 ! : ℝ) * (k ! : ℝ)))
      ≤ (∑ k ∈ Finset.range (9 + 1),
          (properSqSum 10 k : ℝ) / ((10 ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((9 : ℝ) * Real.log 9) - 1) := by
  have hlog9 : Real.log (9 : ℝ) ≤ 8 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)).trans (by norm_num)
  have hlarge : (9 : ℝ) * Real.log 9 < (10 : ℝ) ^ 2 := by
    calc (9 : ℝ) * Real.log 9 ≤ 9 * 8 := mul_le_mul_of_nonneg_left hlog9 (by norm_num)
      _ < (10 : ℝ) ^ 2 := by norm_num
  exact loopRow_le_properRow_div (n := 10) (c := 9) (by norm_num) (by norm_num) hlarge

/-- `e ≤ 2.7` fails; what we need is the other direction: `2.7 ≤ e`, from the
degree-5 Taylor partial sum. -/
theorem exp_one_ge_27 : (2.7 : ℝ) ≤ Real.exp 1 := by
  have hs : Summable fun k : ℕ => (1 : ℝ) ^ k / (k ! : ℝ) :=
    Real.summable_pow_div_factorial 1
  have hexp : Real.exp 1 = ∑' k : ℕ, (1 : ℝ) ^ k / (k ! : ℝ) := by
    simp only [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hle : (∑ k ∈ Finset.range 6, (1 : ℝ) ^ k / (k ! : ℝ)) ≤ Real.exp 1 := by
    rw [hexp]
    exact hs.sum_le_tsum (Finset.range 6)
      (fun k _ => div_nonneg (pow_nonneg zero_le_one _) (ffact_nonneg k))
  have hsum27 : (2.7 : ℝ) ≤ ∑ k ∈ Finset.range 6, (1 : ℝ) ^ k / (k ! : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hsum27.trans hle

/-- The first side condition of the envelope at its threshold:
`e/(4·log 163000) ≤ 1/4`, i.e. `e ≤ log 163000`, since `e^e ≤ e³ ≤ 27`. -/
theorem he4_at_threshold :
    Real.exp 1 / (4 * Real.log (163000 : ℝ)) ≤ 1 / 4 := by
  have h2 : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h1 : Real.exp 1 ≤ Real.log (163000 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 163000)]
    have h4 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    calc Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.2 h2
      _ = (Real.exp 1) ^ 3 := h4
      _ ≤ (3 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 3
      _ ≤ 163000 := by norm_num
  have hpos : (0 : ℝ) < 4 * Real.log (163000 : ℝ) := by
    linarith [h1, Real.exp_pos 1]
  rw [div_le_iff₀ hpos]
  calc Real.exp 1 ≤ Real.log (163000 : ℝ) := h1
    _ = (1 / 4) * (4 * Real.log (163000 : ℝ)) := by ring

/-- The second side condition of the envelope at its threshold:
`4·√(163000·log 163000)·log 163000 ≤ (log 2)·163000`, from
`12 ≤ log 163000 < 16` (via `e < 2.7` failing the other way: `2.7 ≤ e` and
`2.7^16 > 163000`). -/
theorem hd_at_threshold :
    4 * Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ)) * Real.log (163000 : ℝ)
      ≤ Real.log 2 * (163000 : ℝ) := by
  have hlogc_hi : Real.log (163000 : ℝ) < 16 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 163000)]
    have h16 : Real.exp 16 = (Real.exp 1) ^ 16 := by
      rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h16]
    calc (163000 : ℝ) < (2.7 : ℝ) ^ 16 := by norm_num
      _ ≤ (Real.exp 1) ^ 16 := pow_le_pow_left₀ (by norm_num) exp_one_ge_27 16
  have hX : (163000 : ℝ) * Real.log (163000 : ℝ) ≤ 2608000 :=
    calc (163000 : ℝ) * Real.log (163000 : ℝ)
        ≤ 163000 * 16 := mul_le_mul_of_nonneg_left hlogc_hi.le (by norm_num)
      _ = 2608000 := by norm_num
  have hsqrt : Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ)) ≤ 1615 := by
    rw [show (1615 : ℝ) = Real.sqrt (1615 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hX.trans (by norm_num))
  have hlog_nn : (0 : ℝ) ≤ Real.log (163000 : ℝ) := Real.log_nonneg (by norm_num)
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ)) :=
    Real.sqrt_nonneg _
  calc 4 * Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ)) * Real.log (163000 : ℝ)
      ≤ 4 * 1615 * 16 := by
        have hcore : 4 * Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ))
            ≤ 4 * 1615 := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
        have := mul_le_mul hcore hlogc_hi.le hlog_nn (by norm_num : (0 : ℝ) ≤ 4 * 1615)
        calc 4 * Real.sqrt ((163000 : ℝ) * Real.log (163000 : ℝ)) * Real.log (163000 : ℝ)
            ≤ (4 * 1615) * 16 := this
          _ = 4 * 1615 * 16 := by ring
    _ = 103360 := by norm_num
    _ ≤ Real.log 2 * 163000 := by linarith [Real.log_two_gt_d9]

/-- The A48 envelope instantiated at its exact stated threshold `c = 163000`:
a fully concrete numerical bound on the target-1 ratio. -/
theorem envelope_at_threshold :
    smallMass 163000 / m0sum 163000
      ≤ (Real.exp 1 + 2 * Real.exp 1 / Real.sqrt (2 * Real.pi))
        * ((163000 : ℝ) + 1) * Real.sqrt (163000 : ℝ) * (1 / 2 : ℝ) ^ 163000 :=
  smallMass_div_m0sum_le_half_pow (c := 163000) le_rfl hd_at_threshold he4_at_threshold

/-! ## 5. Independent re-composition of target 3 -/

/-- `mechanismBound → 0`, recomposed here from `mechanismBound_le` and target
1 only; the composition is written out in this file rather than citing the
module's final theorem. -/
theorem tendsto_mechanismBound_zero_recomposed :
    Filter.Tendsto (fun c : ℕ => mechanismBound c) Filter.atTop (nhds 0) := by
  have hconc : Filter.Tendsto (fun c : ℕ => smallMass c / m0sum c)
      Filter.atTop (nhds 0) := tendsto_smallMass_div_m0sum_zero
  have hs12 : ∀ᶠ c : ℕ in atTop, smallMass c / m0sum c ≤ 1 / 2 :=
    hconc.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hbound : ∀ᶠ c : ℕ in atTop,
      mechanismBound c
        ≤ 8 * (smallMass c / m0sum c)
          + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
    filter_upwards [hs12, eventually_ge_atTop 9] with c hsc hc
    exact mechanismBound_le hc hsc
  have hX : Filter.Tendsto (fun c : ℕ => (c : ℝ) * Real.log c)
      Filter.atTop Filter.atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    refine ⟨max 3 (Nat.ceil M), fun a ha => ?_⟩
    have h3 : 3 ≤ a := le_trans (le_max_left _ _) ha
    have hM : M ≤ (a : ℝ) :=
      (Nat.le_ceil M).trans (by exact_mod_cast le_trans (le_max_right _ _) ha)
    have hlog1 : (1 : ℝ) ≤ Real.log (a : ℝ) := by
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
        (by exact_mod_cast h3 : (3 : ℝ) ≤ a)
      linarith [one_lt_log_three]
    calc M ≤ (a : ℝ) * 1 := by rw [mul_one]; exact hM
      _ ≤ (a : ℝ) * Real.log (a : ℝ) :=
          mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg a)
  have hS : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c) - 1)
      Filter.atTop Filter.atTop := by
    have hsqrtT : Filter.Tendsto (fun c : ℕ => Real.sqrt ((c : ℝ) * Real.log c))
        Filter.atTop Filter.atTop := by
      rw [tendsto_atTop_atTop]
      intro M
      by_cases hM : M ≤ 0
      · exact ⟨0, fun a _ => hM.trans (Real.sqrt_nonneg _)⟩
      · push_neg at hM
        obtain ⟨i, hi⟩ := (tendsto_atTop_atTop).1 hX ((M + 1) ^ 2)
        refine ⟨max i 3, fun a ha => ?_⟩
        have h1a : 1 ≤ a :=
          le_trans (by omega : 1 ≤ 3) (le_trans (le_max_right _ _) ha)
        have h := hi a (le_trans (le_max_left _ _) ha)
        have hle : M + 1 ≤ Real.sqrt ((a : ℝ) * Real.log (a : ℝ)) :=
          (Real.le_sqrt (by linarith : (0 : ℝ) ≤ M + 1)
            (mul_nonneg (Nat.cast_nonneg _)
              (Real.log_nonneg (by exact_mod_cast h1a)))).2 h
        linarith
    have := Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) hsqrtT
    simpa [sub_eq_add_neg] using this
  have h2 : Filter.Tendsto
      (fun c : ℕ => 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1))
      Filter.atTop (nhds 0) := by
    have hinv := tendsto_inv_atTop_zero.comp hS
    simpa [one_div] using hinv
  have hupper : Filter.Tendsto
      (fun c : ℕ => 8 * (smallMass c / m0sum c)
        + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) Filter.atTop (nhds 0) := by
    have h8 : Filter.Tendsto (fun c : ℕ => 8 * (smallMass c / m0sum c))
        Filter.atTop (nhds 0) := by
      have := hconc.const_mul 8
      simpa using this
    simpa using h8.add h2
  exact squeeze_zero'
    (Eventually.of_forall fun c => div_nonneg (nsum_nonneg c) (dsum_nonneg c))
    hbound hupper

/-! ## 6. Independent red test: the flips are eventually false -/

/-- Strict bulk-D for `c ≥ 10`: the coefficient `(9/32)·c·(c−1)` strictly
beats `c²/4`, and the large region carries mass, so the domination is strict.
Re-derived here from the banked per-row pieces. -/
theorem bulk_dsum_lower_strict {c : ℕ} (hc : 10 ≤ c) :
    (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) < dsum c := by
  have hrow : ∀ n ∈ largeSet c,
      (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
        ≤ ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
    fun n hn => properRow_ge
      (by have := largeSet_n_ge_five (by omega : 9 ≤ c) hn; omega) (by omega)
  have hlog2 : (2 : ℝ) ≤ Real.log (c : ℝ) := by
    have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by exact_mod_cast (by omega : 9 ≤ c) : (9 : ℝ) ≤ c)
    linarith [two_lt_log_nine]
  have hw : ∀ n ∈ largeSet c,
      wrow c n ≤ 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    intro n hn
    apply wrow_le_two_wterm
    rw [mem_largeSet] at hn
    have hlt : (2 : ℝ) * c < (n : ℝ) ^ 2 := calc
      (2 : ℝ) * c = (c : ℝ) * 2 := by ring
      _ ≤ (c : ℝ) * Real.log (c : ℝ) :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ < (n : ℝ) ^ 2 := hn.2
    exact hlt.le
  have hsplit := m0sum_sub_smallMass c
  have h1 : (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
      ≤ dsum c := by
    calc (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
          * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ)))
        = ∑ n ∈ largeSet c, (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
          * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ largeSet c, ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
        Finset.sum_le_sum hrow
      _ ≤ ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx => Finset.mem_of_mem_filter x hx)
          fun n _ _ => Finset.sum_nonneg fun k _ => div_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))
      _ = dsum c := rfl
  have h2 : m0sum c - smallMass c
      ≤ 2 * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
    rw [hsplit]
    calc (∑ n ∈ largeSet c, wrow c n)
        ≤ ∑ n ∈ largeSet c, 2 * ((n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) :=
        Finset.sum_le_sum hw
      _ = 2 * (∑ n ∈ largeSet c,
          (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
        rw [Finset.mul_sum]
  have hcoef : (c : ℝ) ^ 2 / 4 < (9 / 32 : ℝ) * ((c : ℝ) * ((c : ℝ) - 1)) := by
    have hcR : (10 : ℝ) ≤ c := by exact_mod_cast hc
    have hcpos : (0 : ℝ) < c := by linarith
    have h932 : 8 * (c : ℝ) ^ 2 < 9 * (c : ℝ) * ((c : ℝ) - 1) := by
      nlinarith [hcR, hcpos, mul_pos hcpos (show (0 : ℝ) < (c : ℝ) - 9 by linarith)]
    linarith [h932]
  have hcoef_nn : (0 : ℝ) ≤ (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (sub_nonneg.2 (by exact_mod_cast (by omega : 1 ≤ c) : (1 : ℝ) ≤ (c : ℝ)))
  calc (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)
      < (9 / 32 : ℝ) * ((c : ℝ) * ((c : ℝ) - 1)) * (m0sum c - smallMass c) :=
        mul_lt_mul_of_pos_right hcoef (largeMass_pos (by omega : 2 ≤ c))
    _ = (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * ((m0sum c - smallMass c) / 2) := by ring
    _ ≤ (9 / 16 : ℝ) * (c : ℝ) * ((c : ℝ) - 1)
        * (∑ n ∈ largeSet c, (n : ℝ) ^ (2 * c) / ((n ! : ℝ) * (c ! : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hcoef_nn
        linarith [h2]
    _ ≤ dsum c := h1

/-- Red test 1, independently: the flipped bulk inequality is eventually
FALSE (not merely unprovable by `exact`). -/
theorem flipped_bulk_eventually_false :
    ∀ᶠ c : ℕ in atTop,
      ¬ (dsum c ≤ (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)) := by
  filter_upwards [eventually_ge_atTop 10] with c hc
  exact not_le.2 (bulk_dsum_lower_strict hc)

/-- Per-row comparison at `n = c` with the sharp `n − 1` denominator,
re-derived from the banked per-cell mechanism bound. -/
theorem loopRow_le_properRow_div_nm1 {c : ℕ} (hc : 2 ≤ c) :
    (∑ k ∈ Finset.range (c + 1), (loopSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
      ≤ (∑ k ∈ Finset.range (c + 1),
          (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
        / ((c : ℝ) - 1) := by
  have hn1 : (0 : ℝ) < (c : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ c := by exact_mod_cast hc
    linarith
  have hterm : ∀ k ∈ Finset.range (c + 1),
      (loopSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ))
        ≤ (properSqSum c k : ℝ) / (((c ! : ℝ) * (k ! : ℝ)) * ((c : ℝ) - 1)) := by
    intro k _
    have h := loopSqSum_le_properSqSum c k hc
    have hD : (0 : ℝ) < (c ! : ℝ) * (k ! : ℝ) := mul_pos (ffact_pos _) (ffact_pos _)
    rw [div_le_div_iff₀ hD (mul_pos hD hn1)]
    calc (loopSqSum c k : ℝ) * (((c ! : ℝ) * (k ! : ℝ)) * ((c : ℝ) - 1))
        = (loopSqSum c k * ((c : ℝ) - 1)) * ((c ! : ℝ) * (k ! : ℝ)) := by ring
      _ ≤ (properSqSum c k : ℝ) * ((c ! : ℝ) * (k ! : ℝ)) :=
          mul_le_mul_of_nonneg_right h hD.le
  have e : (∑ k ∈ Finset.range (c + 1),
      (properSqSum c k : ℝ) / (((c ! : ℝ) * (k ! : ℝ)) * ((c : ℝ) - 1)))
      = (∑ k ∈ Finset.range (c + 1),
          (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
        / ((c : ℝ) - 1) := by
    have hterm2 : ∀ k ∈ Finset.range (c + 1),
        (properSqSum c k : ℝ) / (((c ! : ℝ) * (k ! : ℝ)) * ((c : ℝ) - 1))
          = (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)) / ((c : ℝ) - 1) := by
      intro k _
      rw [div_div]
    rw [Finset.sum_congr rfl hterm2,
      show (∑ k ∈ Finset.range (c + 1),
          (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
          / ((c : ℝ) - 1)
        = (∑ k ∈ Finset.range (c + 1),
            (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
          * ((c : ℝ) - 1)⁻¹ from div_eq_mul_inv _ _,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact div_eq_mul_inv _ _
  rw [← e]
  exact Finset.sum_le_sum hterm

/-- A proper row of any `n ≥ 2` cell carries positive mass once `c ≥ 1`. -/
theorem properRow_pos {n : ℕ} (hn : 2 ≤ n) (c : ℕ) (hc : 1 ≤ c) :
    0 < ∑ k ∈ Finset.range (c + 1),
      (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) := by
  have h1 : properSqSum n 1 = n ^ 2 - n := by rw [properSqSum_eq]; simp
  have hlt : n < n ^ 2 := by
    have := Nat.mul_lt_mul_of_pos_left (by omega : 1 < n) (by omega : 0 < n)
    simpa [pow_two] using this
  have hterm : (0 : ℝ) < (properSqSum n 1 : ℝ) / ((n ! : ℝ) * (1 ! : ℝ)) := by
    rw [h1]
    exact div_pos (Nat.cast_pos.2 (Nat.sub_pos_of_lt hlt))
      (mul_pos (ffact_pos _) (ffact_pos _))
  exact Finset.sum_pos'
    (fun k _ => div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _)))
    ⟨1, Finset.mem_range.2 (by omega), hterm⟩

/-- The flipped comparison fails at the witness `n = c` for `c ≥ 10`:
`loopRow(c) ≤ properRow(c)/(c−1) < properRow(c)/(√(c·log c)−1)`. -/
theorem flipped_comparison_false_at_self {c : ℕ} (hc : 10 ≤ c) :
    ¬ ((∑ k ∈ Finset.range (c + 1),
          (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((c : ℝ) * Real.log c) - 1)
          ≤ ∑ k ∈ Finset.range (c + 1),
            (loopSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ))) := by
  have hP : 0 < ∑ k ∈ Finset.range (c + 1),
      (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)) :=
    properRow_pos (n := c) (by omega : 2 ≤ c) c (by omega : 1 ≤ c)
  have hL := loopRow_le_properRow_div_nm1 (c := c) (by omega : 2 ≤ c)
  have hsqrt1 : (1 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1), one_pow]
    exact one_lt_clogc (by omega : 3 ≤ c)
  have hsqrtlt : Real.sqrt ((c : ℝ) * Real.log c) < (c : ℝ) := by
    have hnn : (0 : ℝ) ≤ (c : ℝ) * Real.log c :=
      mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ c)))
    rw [Real.sqrt_lt hnn (Nat.cast_nonneg c)]
    exact clogc_lt_sq (by omega : 2 ≤ c)
  have hdiv : (∑ k ∈ Finset.range (c + 1),
        (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ))) / ((c : ℝ) - 1)
      < (∑ k ∈ Finset.range (c + 1),
          (properSqSum c k : ℝ) / ((c ! : ℝ) * (k ! : ℝ)))
        / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
    div_lt_div_of_pos_left hP (sub_pos.2 hsqrt1) (sub_lt_sub_right hsqrtlt 1)
  exact not_le.2 (hL.trans_lt hdiv)

/-- Red test 2, independently: the flipped large-cell comparison is eventually
FALSE, witnessed at `n = c`. -/
theorem flipped_comparison_eventually_false :
    ∀ᶠ c : ℕ in atTop,
      ¬ (∀ n ∈ Finset.range (c + 1),
          (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
            (∑ k ∈ Finset.range (c + 1),
                (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
              / (Real.sqrt ((c : ℝ) * Real.log c) - 1)
                ≤ ∑ k ∈ Finset.range (c + 1),
                  (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ))) := by
  filter_upwards [eventually_ge_atTop 10] with c hc hforall
  exact flipped_comparison_false_at_self hc
    (hforall c (Finset.mem_range.2 (Nat.lt_succ_self c))
      (clogc_lt_sq (by omega : 2 ≤ c)) (by omega : 2 ≤ c))

/-! ## 7. Structure pin: the named gap was not weakened from A47 -/

/-- `MechanismBoundClosureGap` at exactly the A47 two-conjunct form. Any
weakening of the definition breaks this `Iff.rfl`. -/
theorem closureGap_form_pin :
    MechanismBoundClosureGap ↔
      (∀ᶠ c : ℕ in atTop,
        (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) ≤ dsum c) ∧
        (∀ᶠ c : ℕ in atTop,
          ∀ n ∈ Finset.range (c + 1),
            (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
              (∑ k ∈ Finset.range (c + 1),
                  (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
                ≤ (∑ k ∈ Finset.range (c + 1),
                    (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
                  / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) := Iff.rfl

/-- The named gap, destructured at its exact type: bulk conjunct. -/
theorem gap_bulk_at_type :
    ∀ᶠ c : ℕ in atTop, (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) ≤ dsum c :=
  mechanismBoundClosureGap_holds.1

/-- The named gap, destructured at its exact type: comparison conjunct. -/
theorem gap_comparison_at_type :
    ∀ᶠ c : ℕ in atTop,
      ∀ n ∈ Finset.range (c + 1),
        (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
          (∑ k ∈ Finset.range (c + 1),
              (loopSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
            ≤ (∑ k ∈ Finset.range (c + 1),
                (properSqSum n k : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
              / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
  mechanismBoundClosureGap_holds.2

/-! ## 8. Audits of this probe's own theorems -/

#print axioms QGM0CompletionHostileProbe.cellCount_sum_eq
#print axioms QGM0CompletionHostileProbe.ratio_pos
#print axioms QGM0CompletionHostileProbe.largeMass_pos
#print axioms QGM0CompletionHostileProbe.nsum_pos
#print axioms QGM0CompletionHostileProbe.mechanismBound_pos
#print axioms QGM0CompletionHostileProbe.bulk_at_nine
#print axioms QGM0CompletionHostileProbe.comparison_at_nine
#print axioms QGM0CompletionHostileProbe.envelope_at_threshold
#print axioms QGM0CompletionHostileProbe.tendsto_mechanismBound_zero_recomposed
#print axioms QGM0CompletionHostileProbe.bulk_dsum_lower_strict
#print axioms QGM0CompletionHostileProbe.flipped_bulk_eventually_false
#print axioms QGM0CompletionHostileProbe.flipped_comparison_false_at_self
#print axioms QGM0CompletionHostileProbe.flipped_comparison_eventually_false
#print axioms QGM0CompletionHostileProbe.closureGap_form_pin

end QGM0CompletionHostileProbe
