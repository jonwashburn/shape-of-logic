import IndisputableMonolith.Gravity.SevenGaps.Gap2M0Asymptotics
import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusProductForm

/-!
# Self-hostile-review probe: A48 M0 completion

Outside-module checks on the A48 closure of `mechanismBound → 0` in
`Gap2M0Asymptotics.lean`. No edits to the campaign module. Does not import
`FullTheoryLedger`, `ConstantInventory`, or any `Gap5*` module (an independent
review is running against those).

Sections:
1. Outside-module axiom audits of every new A48 head theorem.
2. Destructuring: the three targets at their exact stated types, and the named
   gap taken apart into its two conjuncts.
3. The `n = 1` handling: `1` lies in the small region, and the `n = 1` row is
   pure numerator (`properSqSum 1 k = 0`), so the large-cell comparison (which
   needs `n ≥ 2`) never has to see it.
4. Split-scale integrity: `saddleN c = o(c / log c)`. The true Laplace saddle
   `n*` solves `n* log n* = 2c`, so `n* ~ 2c / log c` is a `Θ(c / log c)`
   scale; the split scale `saddleN c = ⌈2√(c·log c)⌉₊` is asymptotically
   negligible against it, so no step of the assembly can have identified the
   two scales.
5. Re-derivation of the final finite-`c` bound `B(c) ≤ 8·(smallMass/m0sum) +
   1/(√(c·log c) − 1)` from the banked pieces, independently of the campaign's
   own assembly lemma.
-/

namespace QGM0CompletionProbe

open Gap2M0Asymptotics Gap2CensusProductForm Filter

/-! ## 1. Outside-module axiom audits -/

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

/-! ## 2. Destructuring the three targets at their stated types -/

/-- Target 1, hypothesis-free, at the exact charged type. -/
theorem target1_stated :
    Filter.Tendsto (fun c => smallMass c / m0sum c) Filter.atTop (nhds 0) :=
  tendsto_smallMass_div_m0sum_zero

/-- Target 3, hypothesis-free, at the exact charged type. -/
theorem target3_stated :
    Filter.Tendsto (fun c => mechanismBound c) Filter.atTop (nhds 0) :=
  tendsto_mechanismBound_zero

/-- The named gap, destructured: first conjunct is bulk-D. -/
theorem gap_bulk_conjunct :
    ∀ᶠ c : ℕ in atTop,
      (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) ≤ dsum c :=
  mechanismBoundClosureGap_holds.1

/-- The named gap, destructured: second conjunct is the large-cell comparison
at the `√(c·log c)` threshold. -/
theorem gap_comparison_conjunct :
    ∀ᶠ c : ℕ in atTop,
      ∀ n ∈ Finset.range (c + 1),
        (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
          (∑ k ∈ Finset.range (c + 1),
              (loopSqSum n k : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ)))
            ≤ (∑ k ∈ Finset.range (c + 1),
                (properSqSum n k : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ)))
              / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
  mechanismBoundClosureGap_holds.2

/-! ## 3. The `n = 1` handling -/

/-- `n = 1` really is inside the small region the concentration theorem
controls, once `c ≥ 3`. -/
theorem one_lies_in_small_region {c : ℕ} (hc : 3 ≤ c) : 1 ∈ smallSet c :=
  one_mem_smallSet hc

/-- The `n = 1` row is pure numerator: it contributes nothing to `dsum`. -/
theorem n_one_pure_numerator (k : ℕ) : properSqSum 1 k = 0 := properSqSum_one k

/-- Its loop second moment is exactly the `k²` the `c²·smallMass` reduction
bounds. -/
theorem n_one_loop_sq (k : ℕ) : loopSqSum 1 k = k ^ 2 := loopSqSum_one k

/-- The banked conditional proper mean really specializes at `n = 1`: both
sides vanish, consistently with `properSqSum_one`. -/
theorem n_one_conditional_proper_vanishes (k : Nat) :
    (properSqSum 1 k : Real) / ((1 : ℕ) : Real) ^ (2 * k)
      = (((k : Real) * (1 - 1 / ((1 : ℕ) : Real))) ^ 2
        + ((k : Real) / ((1 : ℕ) : Real)) * (1 - 1 / ((1 : ℕ) : Real))) :=
  conditional_proper_sq_mean 1 k (by norm_num)

/-! ## 4. Split-scale integrity: `saddleN c = o(c / log c)` -/

/-- Helper: `4√(c·log c)·log c / c → 0`, repackaged from piece (d) of the
campaign's concentration route. -/
theorem tendsto_scale_div_c :
    Filter.Tendsto
      (fun c : ℕ => 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c / (c : ℝ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (four_sqrt_clogc_log_le_eventually (half_pos hε))
  refine ⟨max N 3, fun c hc => ?_⟩
  have hcb := hN c (le_trans (le_max_left _ _) hc)
  have hc3 : 3 ≤ c := le_trans (le_max_right _ _) hc
  have hc := hcb
  have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 (by omega)
  have hlog : (0 : ℝ) ≤ Real.log (c : ℝ) := (log_c_pos hc3).le
  have hg : (0 : ℝ) ≤ 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hlog
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hg hcR.le)]
  calc 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c / (c : ℝ)
      ≤ (ε / 2 * (c : ℝ)) / (c : ℝ) := div_le_div_of_nonneg_right hc hcR.le
    _ = ε / 2 := by rw [div_eq_iff hcR.ne']
    _ < ε := half_lt_self hε

/-- **No-identification check**: `saddleN c · log c / c → 0`, i.e. the split
scale is `o(c / log c)`. The true Laplace saddle `n*` satisfies
`n* log n* = 2c`, hence `n* ~ 2c / log c` sits on a `Θ(c / log c)` scale, and
`saddleN c / n* → 0`: the A48 assembly cannot have identified `saddleN` with
`n*`. -/
theorem saddleN_lt_lt_c_div_log :
    Filter.Tendsto (fun c : ℕ => (saddleN c : ℝ) * Real.log c / (c : ℝ))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero' _ _ tendsto_scale_div_c
  · filter_upwards [eventually_ge_atTop 3] with c hc3
    have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 (by omega)
    have hlog : (0 : ℝ) ≤ Real.log (c : ℝ) := (log_c_pos hc3).le
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog) hcR.le
  · filter_upwards [eventually_ge_atTop 3] with c hc3
    have hcR : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.2 (by omega)
    have hlog : (0 : ℝ) ≤ Real.log (c : ℝ) := (log_c_pos hc3).le
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((c : ℝ) * Real.log c) := by
      rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hcR.le hlog), one_pow]
      exact (one_lt_clogc hc3).le
    have hlt := saddleN_lt_add_one c
    have hle : (saddleN c : ℝ) ≤ 3 * Real.sqrt ((c : ℝ) * Real.log c) := by linarith
    have h1 : (saddleN c : ℝ) * Real.log c
        ≤ 4 * Real.sqrt ((c : ℝ) * Real.log c) * Real.log c := by
      calc (saddleN c : ℝ) * Real.log c
          ≤ (3 * Real.sqrt ((c : ℝ) * Real.log c)) * Real.log c :=
            mul_le_mul_of_nonneg_right hle hlog
        _ ≤ (4 * Real.sqrt ((c : ℝ) * Real.log c)) * Real.log c :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4)
                (Real.sqrt_nonneg _)) hlog
    exact div_le_div_of_nonneg_right h1 hcR.le

/-! ## 5. Re-derivation of the final finite-`c` bound from the pieces -/

/-- The final `B(c)` bound, re-derived from the banked pieces (the `nsum`
split, the `c²·smallMass` reduction, the large-cell comparison, bulk-D)
independently of the campaign's `mechanismBound_le`. If any piece drifts, this
proof breaks. -/
theorem mechanismBound_le_rederived {c : ℕ} (hc : 9 ≤ c)
    (hs : smallMass c / m0sum c ≤ 1 / 2) :
    mechanismBound c
      ≤ 8 * (smallMass c / m0sum c) + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  have hm0 := m0sum_pos c
  have hd := dsum_pos c (by omega : 2 ≤ c)
  have hsplit := nsum_eq_small_add_large c
  have hS : nsumSmall c ≤ (c : ℝ) ^ 2 * smallMass c := nsumSmall_le_c_sq_smallMass c
  have hL : nsumLarge c ≤ dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
    nsumLarge_le_dsum_div hc
  have hsm : smallMass c ≤ m0sum c / 2 := by
    rw [div_le_iff₀ hm0] at hs
    linarith
  have hsqrt1 : (1 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1), one_pow]
    exact one_lt_clogc (by omega : 3 ≤ c)
  have hbulk := bulk_dsum_lower hc
  have h8 : (c : ℝ) ^ 2 * m0sum c ≤ 8 * dsum c := by
    have h1 : (c : ℝ) ^ 2 / 4 * m0sum c - (c : ℝ) ^ 2 / 4 * smallMass c ≤ dsum c := by
      have h2 : (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c)
          = (c : ℝ) ^ 2 / 4 * m0sum c - (c : ℝ) ^ 2 / 4 * smallMass c := by ring
      rw [h2] at hbulk
      exact hbulk
    have h3 : (c : ℝ) ^ 2 / 4 * smallMass c ≤ (c : ℝ) ^ 2 / 8 * m0sum c := by
      calc (c : ℝ) ^ 2 / 4 * smallMass c
          ≤ (c : ℝ) ^ 2 / 4 * (m0sum c / 2) :=
            mul_le_mul_of_nonneg_left hsm (by positivity)
        _ = (c : ℝ) ^ 2 / 8 * m0sum c := by ring
    have h4 : (c : ℝ) ^ 2 / 8 * m0sum c ≤ dsum c := by linarith
    calc (c : ℝ) ^ 2 * m0sum c = 8 * ((c : ℝ) ^ 2 / 8 * m0sum c) := by ring
      _ ≤ 8 * dsum c := by linarith
  have hds : (0 : ℝ) < Real.sqrt ((c : ℝ) * Real.log c) - 1 := sub_pos.2 hsqrt1
  calc mechanismBound c = (nsumSmall c + nsumLarge c) / dsum c := by
        unfold mechanismBound
        rw [hsplit]
    _ = nsumSmall c / dsum c + nsumLarge c / dsum c := add_div _ _ _
    _ ≤ (c : ℝ) ^ 2 * smallMass c / dsum c
        + (dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) / dsum c :=
        add_le_add (div_le_div_of_nonneg_right hS hd.le)
          (div_le_div_of_nonneg_right hL hd.le)
    _ ≤ 8 * smallMass c / m0sum c + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
        apply add_le_add
        · rcases eq_or_lt_of_le (smallMass_nonneg c) with hsm0 | hsmpos
          · rw [← hsm0]
            simp
          · rw [div_le_div_iff₀ hd hm0]
            calc (c : ℝ) ^ 2 * smallMass c * m0sum c
                = smallMass c * ((c : ℝ) ^ 2 * m0sum c) := by ring
              _ ≤ smallMass c * (8 * dsum c) := mul_le_mul_of_nonneg_left h8 hsmpos.le
              _ = 8 * smallMass c * dsum c := by ring
        · have e : (dsum c / (Real.sqrt ((c : ℝ) * Real.log c) - 1)) / dsum c
              = 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
            rw [div_div, mul_comm _ (dsum c), ← div_div, div_self hd.ne']
          rw [e]
    _ = 8 * (smallMass c / m0sum c) + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by ring

#print axioms QGM0CompletionProbe.mechanismBound_le_rederived
#print axioms QGM0CompletionProbe.saddleN_lt_lt_c_div_log
#print axioms QGM0CompletionProbe.tendsto_scale_div_c

end QGM0CompletionProbe
