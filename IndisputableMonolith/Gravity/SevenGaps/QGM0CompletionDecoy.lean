import IndisputableMonolith.Gravity.SevenGaps.Gap2M0Asymptotics

/-!
# DECOY (A48 red test): flipped inequalities. FROZEN RECEIPT.

This file is the frozen record of the A48 red test. In its live form the three
theorems below were uncommented and the build was required to fail; it failed
with exactly the three expected errors (receipt:
`QG/attack_full_theory_20260729/a48_decoy_build.log`):

```
error: QGM0CompletionDecoy.lean:23:2: Type mismatch
  bulk_dsum_lower hc : (c^2/4)*(m0sum c - smallMass c) ≤ dsum c
  expected                : dsum c ≤ (c^2/4)*(m0sum c - smallMass c)
error: QGM0CompletionDecoy.lean:37:2: Type mismatch
  loopRow_le_properRow_div hn2 hc hlarge : loopRow ≤ properRow / (sqrt(c log c) - 1)
  expected                                 : properRow / (sqrt(c log c) - 1) ≤ loopRow
error: QGM0CompletionDecoy.lean:46:2: linarith failed to find a contradiction
```

The decoy code is preserved below in comments so the red test can be re-run by
uncommenting; this file otherwise compiles (imports only) and sits in no build
target.
-/

namespace QGM0CompletionDecoy

open Gap2M0Asymptotics Filter

/- DECOY 1: bulk-D with the direction flipped. The real theorem is
`bulk_dsum_lower : (c²/4)·(m0sum − smallMass) ≤ dsum`.

theorem decoy_bulk_dsum_upper :
    ∀ᶠ c : ℕ in atTop, dsum c ≤ (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) := by
  filter_upwards [eventually_ge_atTop 9] with c hc
  exact bulk_dsum_lower hc
-/

/- DECOY 2: the large-cell comparison with the direction flipped. The real
theorem is `loopRow_le_properRow_div`.

theorem decoy_comparison_flipped :
    ∀ᶠ c : ℕ in atTop,
      ∀ n ∈ Finset.range (c + 1),
        (c : ℝ) * Real.log c < (n : ℝ) ^ 2 → 2 ≤ n →
          (∑ k ∈ Finset.range (c + 1),
              (properSqSum n k : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ)))
              / (Real.sqrt ((c : ℝ) * Real.log c) - 1)
            ≤ ∑ k ∈ Finset.range (c + 1),
                (loopSqSum n k : ℝ) / ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ)) := by
  filter_upwards [eventually_ge_atTop 3] with c hc n _ hlarge hn2
  exact loopRow_le_properRow_div hn2 hc hlarge
-/

/- DECOY 3: even with the true theorem in hand, `linarith` cannot flip the
direction.

theorem decoy_linarith_cannot_flip :
    ∀ᶠ c : ℕ in atTop, dsum c ≤ (c : ℝ) ^ 2 / 4 * (m0sum c - smallMass c) := by
  filter_upwards [eventually_ge_atTop 9] with c hc
  have h := bulk_dsum_lower hc
  have hpos := dsum_pos c (by omega : 2 ≤ c)
  linarith
-/

end QGM0CompletionDecoy
